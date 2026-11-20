-- Prove2me | solution 1 for VWZClique.basis_transform
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T01:08:59.888172+00:00
-- url     : https://prove2.me/submissions/edbdf97d-720d-463d-9350-a04dcfda9db3

import Definitions.Def_VWZClique_Operators
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

open VWZClique OAI.MatrixMultiplication.Arithmetic
namespace VWZTransformProof

private def relabel {F I R S : Type*} (f : R → S) : Gate F I R → Gate F I S
  | .constant c => .constant c
  | .input i => .input i
  | .add i j => .add (f i) (f j)
  | .sub i j => .sub (f i) (f j)
  | .mul i j => .mul (f i) (f j)

private theorem batch {F I J : Type*} [Field F] {r : ℕ} (p : Program F I r)
    (g : J → Gate F I (Fin r)) (s : Finset J) :
    ∃ (n : ℕ) (q : Program F I n) (old : Fin r → Fin n) (out : (j : J) → j ∈ s → Fin n),
      q.cost ≤ p.cost + s.card ∧
      (∀ w i, q.eval w (old i) = p.eval w i) ∧
      ∀ w j hj, q.eval w (out j hj) = (g j).eval w (p.eval w) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨r, p, id, fun _ h => False.elim (by simp at h), by simp,
      fun _ _ => rfl, fun _ _ h => False.elim (by simp at h)⟩
  | @insert a s ha ih =>
    obtain ⟨n, q, old, out, hc, hold, hout⟩ := ih
    let gate := relabel old (g a)
    refine ⟨n+1, .step q gate, fun i => (old i).succ,
      fun j hj => if h : j = a then 0 else (out j (by simpa [h] using hj)).succ, ?_, ?_, ?_⟩
    · have hgate : gate.cost ≤ 1 := by cases hg : g a <;> simp [gate, hg, relabel, Gate.cost]
      simp only [Program.cost, Finset.card_insert_of_notMem ha]
      omega
    · exact hold
    · intro w j hj
      by_cases h : j = a
      · subst j
        simp only [dite_true, Program.eval, Fin.cases_zero]
        cases hg : g a <;> simp [gate, hg, relabel, Gate.eval, hold]
      · simpa [h, Program.eval] using hout w j (by simpa [h] using hj)

private def prepend {L : ℕ} (b : Bool × Bool) (x : PairBits L) : PairBits (L+1) :=
  (Fin.cons b.1 x.1, Fin.cons b.2 x.2)

private def splitEquiv (L : ℕ) : ((Bool × Bool) × PairBits L) ≃ PairBits (L+1) where
  toFun z := prepend z.1 z.2
  invFun x := ((x.1 0,x.2 0), (fun i => x.1 i.succ, fun i => x.2 i.succ))
  left_inv := by intro z; simp [prepend]
  right_inv := by
    intro x
    apply Prod.ext <;> funext i <;> refine Fin.cases ?_ (fun k => ?_) i <;> rfl

private theorem entry_cons {L : ℕ} (j : BasisLabel (L+1)) (b : Bool × Bool) (x : PairBits L) :
    basisEntry j (prepend b x) =
    oneBit (j 0) b.1 b.2 * basisEntry (fun i => j i.succ) x := by
  simp [basisEntry, Fin.prod_univ_succ, prepend]

private def transform {F : Type*} [Field F] [CharZero F] {L : ℕ}
    (w : PairBits L → F) (j : BasisLabel L) : F := ∑ x, (basisEntry j x : F) * w x

private theorem transform_cons {F : Type*} [Field F] [CharZero F] {L : ℕ}
    (w : PairBits (L+1) → F) (j : BasisLabel (L+1)) :
    let y := fun b => transform (fun x => w (prepend b x)) (fun i => j i.succ)
    transform w j = if j 0 = 0 then y (false,false) else if j 0 = 1 then y (true,true)
      else if j 0 = 2 then y (false,true) + y (true,false) else y (false,true) - y (true,false) := by
  dsimp only
  have h : transform w j = ∑ b : Bool × Bool, (oneBit (j 0) b.1 b.2 : F) *
        transform (fun x => w (prepend b x)) (fun i => j i.succ) := by
    unfold transform
    rw [← (splitEquiv L).sum_comp, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b _
    change (∑ x, (basisEntry j (prepend b x) : F) * _) = _
    simp_rw [entry_cons, Rat.cast_mul, mul_assoc]
    rw [Finset.mul_sum]
    rfl
  rw [h, Fintype.sum_prod_type]
  generalize j 0 = k
  fin_cases k <;> simp [oneBit] <;> ring

private theorem build {F : Type*} [Field F] [CharZero F] (I : Type) (L : ℕ) :
    ∀ (A : Type) [Fintype A] (ι : A → PairBits L → I),
    ∃ (r : ℕ) (p : Program F I r) (out : A → BasisLabel L → Fin r),
      p.cost ≤ (L + 1) * 4^L * Fintype.card A ∧ ∀ w a j,
        p.eval w (out a j) = transform (fun x => w (ι a x)) j := by
  classical
  induction L with
  | zero =>
    intro A _ ι
    let z : PairBits 0 := (Fin.elim0,Fin.elim0)
    obtain ⟨r, p, _, out, hc, _, he⟩ := batch (F := F) (I := I) Program.nil
      (fun a : A => Gate.input (ι a z)) Finset.univ
    refine ⟨r, p, fun a _ => out a (Finset.mem_univ _), by simpa [Program.cost] using hc, ?_⟩
    intro w a j
    rw [he]
    simp only [transform, basisEntry, Finset.univ_eq_empty, Finset.prod_empty,
      Rat.cast_one, one_mul, Gate.eval]
    symm
    apply Finset.sum_eq_single z
    · intro b _ h
      exact (h (Subsingleton.elim _ _)).elim
    · simp
  | succ L ih =>
    intro A _ ι
    obtain ⟨r, p, out, hc, he⟩ := ih (A × (Bool × Bool))
      (fun a x => ι a.1 (prepend a.2 x))
    let wire (a : A) (j : BasisLabel (L+1)) (b : Bool × Bool) :=
      out (a,b) (fun i => j i.succ)
    let gate (v : A × BasisLabel (L+1)) : Gate F I (Fin r) :=
      if v.2 0 = 2 then .add (wire v.1 v.2 (false,true)) (wire v.1 v.2 (true,false))
      else .sub (wire v.1 v.2 (false,true)) (wire v.1 v.2 (true,false))
    obtain ⟨n, q, old, fresh, hcost, hold, hfresh⟩ := batch p gate Finset.univ
    refine ⟨n, q, fun a j => if j 0 = 0 then old (wire a j (false,false))
      else if j 0 = 1 then old (wire a j (true,true))
      else fresh (a,j) (Finset.mem_univ _), ?_, ?_⟩
    · calc
        q.cost ≤ p.cost + Fintype.card (A × BasisLabel (L+1)) := hcost
        _ ≤ _ := Nat.add_le_add_right hc _
        _ = _ := by simp [BasisLabel, Fintype.card_prod, pow_succ]; ring
    · intro w a j
      rw [transform_cons]
      by_cases h₀ : j 0 = 0
      · simp [h₀, hold, wire, he]
      · by_cases h₁ : j 0 = 1
        · simp [h₁, hold, wire, he]
        · by_cases h₂ : j 0 = 2 <;> simp [h₀, h₁, h₂, hfresh, gate, Gate.eval, wire, he]

end VWZTransformProof

open VWZTransformProof in
theorem solution :
    ∃ C : ℕ, ∀ (F : Type*) [Field F] [CharZero F] (L : ℕ),
      ∃ (r : ℕ) (P : Program F (PairBits L) r) (out : BasisLabel L → Fin r),
        P.cost ≤ C * (L + 1) * 4^L ∧ ∀ (w : PairBits L → F) j,
          P.eval w (out j) = ∑ x, (basisEntry j x : F) * w x := by
  refine ⟨1, ?_⟩
  intro F _ _ L
  obtain ⟨r,p,out,hc,he⟩ := build (F := F) (PairBits L) L Unit (fun _ x => x)
  exact ⟨r,p,out (),by simpa using hc,fun w j => he w () j⟩
