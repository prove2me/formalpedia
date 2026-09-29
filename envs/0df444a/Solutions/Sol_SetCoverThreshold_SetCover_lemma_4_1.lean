-- Prove2me | solution 1 for SetCoverThreshold.SetCover.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:00:40.674545+00:00
-- url     : https://prove2.me/submissions/6b728e6d-4e0b-4dc4-b647-8fbff1535661

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
import Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem
import Definitions.Def_SetCoverThreshold_SetCover_Reduction

namespace SetCoverThreshold.SetCover

open Finset

theorem aux_l41_code_bound {ℓ k : ℕ} {code : Fin k → Fin ℓ → Bool} (hcode : IsCode ℓ k code)
    {i i' : Fin k} (hii : i ≠ i') :
    ℓ ≤ 6 * (univ.filter (fun j => code i j = true ∧ code i' j = false)).card := by
  obtain ⟨hw, hd⟩ := hcode
  have h1 := hw i
  have h2 := hw i'
  have h3 := hd i i' hii
  have hdist : hammingDist (code i) (code i') =
      (univ.filter (fun j => code i j ≠ code i' j)).card := rfl
  have key : (univ.filter (fun j => code i j ≠ code i' j)).card +
      (univ.filter (fun j => code i j = true)).card
      = 2 * (univ.filter (fun j => code i j = true ∧ code i' j = false)).card +
        (univ.filter (fun j => code i' j = true)).card := by
    simp only [card_filter, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    cases code i j <;> cases code i' j <;> simp
  omega

namespace Formula5

variable (φ : Formula5)

/-- Generalized question: on `S` given by `u`, outside `S` as prover `i` would get from `y`. -/
noncomputable def aux_l41_Q {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (S : Finset (Fin ℓ)) (i : Fin k)
    (u : Fin S.card → φ.QCoord) (y : {j // j ∉ S} → Fin φ.M × Fin 3) : Fin ℓ → φ.QCoord :=
  fun j => if h : j ∈ S then u (S.equivFin ⟨j, h⟩) else
    (if code i j then Sum.inl (y ⟨j, h⟩).1 else Sum.inr (φ.var (y ⟨j, h⟩).1 (y ⟨j, h⟩).2))

theorem aux_l41_question_eq {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (S : Finset (Fin ℓ))
    (i : Fin k) (r : φ.RandomString ℓ) (y : {j // j ∉ S} → Fin φ.M × Fin 3)
    (hout : ∀ j (h : j ∉ S), r j = y ⟨j, h⟩)
    (u : Fin S.card → φ.QCoord)
    (hu : ∀ j (h : j ∈ S), (if code i j then Sum.inl (r j).1 else
      Sum.inr (φ.var (r j).1 (r j).2)) = u (S.equivFin ⟨j, h⟩)) :
    φ.question code r i = φ.aux_l41_Q code S i u y := by
  funext j
  unfold question aux_l41_Q
  by_cases h : j ∈ S
  · rw [dif_pos h, ← hu j h]
  · rw [dif_neg h, hout j h]

open Classical in
theorem aux_l41_pair (c₀ : ℝ)
    (hR : ∀ (m : ℕ) (P₁ : φ.Prover1Strategy m) (P₂ : φ.Prover2Strategy m),
      φ.twoProverAcceptFrac m P₁ P₂ ≤ (2:ℝ) ^ (-(c₀ * m)))
    {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (A : φ.KStrategy ℓ k) (i i' : Fin k)
    (S : Finset (Fin ℓ)) (hS : ∀ j ∈ S, code i j = true ∧ code i' j = false) :
    ((univ.filter (fun r : φ.RandomString ℓ => φ.Consistent code A r i i')).card : ℝ) ≤
      (2:ℝ) ^ (-(c₀ * S.card)) * Fintype.card (φ.RandomString ℓ) := by
  let f := S.equivFin
  let E : (Fin ℓ → Fin φ.M × Fin 3) ≃
      (Fin S.card → Fin φ.M × Fin 3) × ({j // j ∉ S} → Fin φ.M × Fin 3) :=
    (Equiv.piEquivPiSubtypeProd (fun j => j ∈ S) (fun _ => Fin φ.M × Fin 3)).trans
      (Equiv.prodCongr (Equiv.arrowCongr f (Equiv.refl _)) (Equiv.refl _))
  have hEin : ∀ x y j (h : j ∈ S), E.symm (x, y) j = x (f ⟨j, h⟩) := by
    intro x y j h
    simp [E, Equiv.piEquivPiSubtypeProd, Equiv.arrowCongr, h]
  have hEout : ∀ x y j (h : j ∉ S), E.symm (x, y) j = y ⟨j, h⟩ := by
    intro x y j h
    simp [E, Equiv.piEquivPiSubtypeProd, Equiv.arrowCongr, h]
  let P₁ : ({j // j ∉ S} → Fin φ.M × Fin 3) → φ.Prover1Strategy S.card := fun y cs j' =>
    (A i (φ.aux_l41_Q code S i (fun j'' => Sum.inl (cs j'')) y)).1 (f.symm j').1
  let P₂ : ({j // j ∉ S} → Fin φ.M × Fin 3) → φ.Prover2Strategy S.card := fun y vs j' =>
    (A i' (φ.aux_l41_Q code S i' (fun j'' => Sum.inr (vs j'')) y)).1 (f.symm j').1 0
  have hsub : ∀ y, (univ.filter (fun x : Fin S.card → Fin φ.M × Fin 3 =>
      φ.Consistent code A (E.symm (x, y)) i i')) ⊆
      univ.filter (fun x => φ.TwoProverAccepts (P₁ y) (P₂ y) x) := by
    intro y x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    have hq1 : φ.question code (E.symm (x, y)) i =
        φ.aux_l41_Q code S i (fun j'' => Sum.inl (φ.clausesOf x j'')) y := by
      apply φ.aux_l41_question_eq code S i _ y (hEout x y)
      intro j h
      simp [(hS j h).1, hEin x y j h, clausesOf, f]
    have hq2 : φ.question code (E.symm (x, y)) i' =
        φ.aux_l41_Q code S i' (fun j'' => Sum.inr (φ.distVars x j'')) y := by
      apply φ.aux_l41_question_eq code S i' _ y (hEout x y)
      intro j h
      simp [(hS j h).2, hEin x y j h, distVars, f]
    intro j'
    have hjj : (f.symm j').1 ∈ S := (f.symm j').2
    have hfj : f ⟨(f.symm j').1, hjj⟩ = j' := by simp
    have hrj : E.symm (x, y) (f.symm j').1 = x j' := by rw [hEin x y _ hjj, hfj]
    constructor
    · have hcan := (A i (φ.aux_l41_Q code S i (fun j'' => Sum.inl (φ.clausesOf x j'')) y)).2
        (f.symm j').1
      have hQ : φ.aux_l41_Q code S i (fun j'' => Sum.inl (φ.clausesOf x j'')) y (f.symm j').1 =
          Sum.inl (x j').1 := by
        unfold aux_l41_Q
        rw [dif_pos hjj]
        simp only [f] at hfj
        rw [hfj]
        rfl
      rw [hQ] at hcan
      exact hcan
    · unfold Consistent at hx
      have hc := congrFun hx (f.symm j').1
      rw [hq1, hq2] at hc
      unfold inducedAssignment at hc
      rw [if_pos (hS _ hjj).1, if_neg (by simp [(hS _ hjj).2]), hrj] at hc
      exact hc
  have hN : (0:ℝ) < Fintype.card (Fin S.card → Fin φ.M × Fin 3) := by
    have : Nonempty (Fin S.card → Fin φ.M × Fin 3) := ⟨fun _ => (⟨0, φ.M_pos⟩, 0)⟩
    exact_mod_cast Fintype.card_pos
  have hy : ∀ y, ((univ.filter (fun x : Fin S.card → Fin φ.M × Fin 3 =>
      φ.Consistent code A (E.symm (x, y)) i i')).card : ℝ) ≤
      (2:ℝ) ^ (-(c₀ * S.card)) * Fintype.card (Fin S.card → Fin φ.M × Fin 3) := by
    intro y
    have h1 := hR S.card (P₁ y) (P₂ y)
    unfold twoProverAcceptFrac at h1
    rw [div_le_iff₀ hN] at h1
    refine le_trans ?_ h1
    exact_mod_cast card_le_card (hsub y)
  have hcount : (univ.filter (fun r : φ.RandomString ℓ => φ.Consistent code A r i i')).card =
      ∑ y : {j // j ∉ S} → Fin φ.M × Fin 3, (univ.filter (fun x : Fin S.card → Fin φ.M × Fin 3 =>
        φ.Consistent code A (E.symm (x, y)) i i')).card := by
    rw [card_filter]
    rw [Fintype.sum_equiv E _ (fun p => if φ.Consistent code A (E.symm p) i i' then 1 else 0)
      (by intro r; simp)]
    rw [Fintype.sum_prod_type_right]
    simp only [card_filter]
  calc ((univ.filter (fun r : φ.RandomString ℓ => φ.Consistent code A r i i')).card : ℝ)
      = ∑ y : {j // j ∉ S} → Fin φ.M × Fin 3,
          ((univ.filter (fun x : Fin S.card → Fin φ.M × Fin 3 =>
            φ.Consistent code A (E.symm (x, y)) i i')).card : ℝ) := by
        rw [hcount]; push_cast; rfl
    _ ≤ ∑ y : {j // j ∉ S} → Fin φ.M × Fin 3,
          (2:ℝ) ^ (-(c₀ * S.card)) * Fintype.card (Fin S.card → Fin φ.M × Fin 3) :=
        sum_le_sum (fun y _ => hy y)
    _ = (2:ℝ) ^ (-(c₀ * S.card)) * Fintype.card (φ.RandomString ℓ) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        rw [show Fintype.card (φ.RandomString ℓ) =
          Fintype.card ((Fin S.card → Fin φ.M × Fin 3) × ({j // j ∉ S} → Fin φ.M × Fin 3)) from
            Fintype.card_congr E, Fintype.card_prod]
        push_cast; ring

/-- Canonical answer bits from a truth assignment. -/
def aux_l41_cb (τ : ℕ → Bool) : φ.QCoord → Fin 3 → Bool
  | Sum.inl c => fun p => τ (φ.var c p : ℕ)
  | Sum.inr v => fun p => if p = 0 then τ (v : ℕ) else false

theorem aux_l41_cb_can (τ : ℕ → Bool) (hτ : ∀ C ∈ φ.toCNF, ∃ l ∈ C, τ l.2 = l.1)
    (x : φ.QCoord) : φ.CoordCanonical x (φ.aux_l41_cb τ x) := by
  cases x with
  | inl c =>
    have hmem : (List.ofFn fun p : Fin 3 => ((φ.clause c p).1, ((φ.clause c p).2 : ℕ))) ∈
        φ.toCNF := by
      unfold toCNF
      exact List.mem_ofFn.mpr ⟨c, rfl⟩
    obtain ⟨l, hl, hl'⟩ := hτ _ hmem
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hl
    exact ⟨p, hl'⟩
  | inr v => exact ⟨rfl, rfl⟩

theorem aux_l41_ind (τ : ℕ → Bool) {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool)
    (r : φ.RandomString ℓ) (i : Fin k) :
    φ.inducedAssignment code r i (fun j => φ.aux_l41_cb τ (φ.question code r i j)) =
      fun j => τ (φ.var (r j).1 (r j).2 : ℕ) := by
  funext j
  unfold inducedAssignment question
  cases h : code i j <;> simp [h, aux_l41_cb]

theorem aux_l41_weak (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hR : ∀ (m : ℕ) (P₁ : φ.Prover1Strategy m) (P₂ : φ.Prover2Strategy m),
      φ.twoProverAcceptFrac m P₁ P₂ ≤ (2:ℝ) ^ (-(c₀ * m)))
    {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (hcode : IsCode ℓ k code) (A : φ.KStrategy ℓ k) :
    φ.weakAcceptFrac code A ≤ (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(c₀ / 6 * ℓ)) := by
  classical
  have hN : (0:ℝ) < Fintype.card (φ.RandomString ℓ) := by
    have : Nonempty (φ.RandomString ℓ) := ⟨fun _ => (⟨0, φ.M_pos⟩, 0)⟩
    exact_mod_cast Fintype.card_pos
  have hpair : ∀ p ∈ (Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2)),
      ((Finset.univ.filter (fun r : φ.RandomString ℓ =>
        φ.Consistent code A r p.1 p.2)).card : ℝ) ≤
        (2:ℝ) ^ (-(c₀ / 6 * ℓ)) * Fintype.card (φ.RandomString ℓ) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have h1 := φ.aux_l41_pair c₀ hR code A p.1 p.2
      (Finset.univ.filter (fun j => code p.1 j = true ∧ code p.2 j = false))
      (fun j hj => by simpa using hj)
    have h2 := aux_l41_code_bound hcode hp
    refine le_trans (le_of_eq_of_le ?_ h1) (mul_le_mul_of_nonneg_right ?_ hN.le)
    · congr 1
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (ℓ:ℝ) ≤ 6 * ((Finset.univ.filter
        (fun j => code p.1 j = true ∧ code p.2 j = false)).card : ℝ) := by
      exact_mod_cast h2
    nlinarith
  unfold Formula5.weakAcceptFrac
  rw [div_le_iff₀ hN]
  calc ((Finset.univ.filter (fun r : φ.RandomString ℓ => φ.WeakAccept code A r)).card : ℝ)
      ≤ (((Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2)).biUnion
          (fun p => Finset.univ.filter (fun r : φ.RandomString ℓ =>
            φ.Consistent code A r p.1 p.2))).card : ℝ) := by
        apply Nat.cast_le.mpr
        apply Finset.card_le_card
        intro r hr
        rw [Finset.mem_filter] at hr
        obtain ⟨_, i, i', hne, hc⟩ := hr
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(i, i'), hne, hc⟩
    _ ≤ ∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2),
          ((Finset.univ.filter (fun r : φ.RandomString ℓ =>
            φ.Consistent code A r p.1 p.2)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2),
          (2:ℝ) ^ (-(c₀ / 6 * ℓ)) * Fintype.card (φ.RandomString ℓ) :=
        Finset.sum_le_sum hpair
    _ = ((Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2)).card : ℝ) *
          ((2:ℝ) ^ (-(c₀ / 6 * ℓ)) * Fintype.card (φ.RandomString ℓ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k : ℝ) ^ 2 * ((2:ℝ) ^ (-(c₀ / 6 * ℓ)) * Fintype.card (φ.RandomString ℓ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : (Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2)).card ≤ k ^ 2 := by
          refine le_trans (Finset.card_filter_le _ _) ?_
          simp [Finset.card_univ, Fintype.card_prod, sq]
        exact_mod_cast this
    _ = (k : ℝ) ^ 2 * (2:ℝ) ^ (-(c₀ / 6 * ℓ)) * Fintype.card (φ.RandomString ℓ) := by ring


theorem aux_l41_pqcard {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (hcode : IsCode ℓ k code)
    (i : Fin k) : Fintype.card (φ.ProverQuestion code i) = φ.numQuestions ℓ := by
  classical
  have e : Fintype.card (φ.ProverQuestion code i) =
      (univ.filter (fun q : Fin ℓ → φ.QCoord => ∀ j, (q j).isLeft = code i j)).card :=
    Fintype.card_subtype _
  rw [e]
  have h2 : univ.filter (fun q : Fin ℓ → φ.QCoord => ∀ j, (q j).isLeft = code i j) =
      Fintype.piFinset (fun j => univ.filter (fun x : φ.QCoord => x.isLeft = code i j)) := by
    ext q; simp [Fintype.mem_piFinset]
  rw [h2, Fintype.card_piFinset]
  have hc : ∀ j, (univ.filter (fun x : φ.QCoord => x.isLeft = code i j)).card =
      if code i j = true then φ.M else φ.n := by
    intro j
    cases code i j <;> (rw [card_filter, Fintype.sum_sum_type]; simp)
  rw [prod_congr rfl (fun j _ => hc j), prod_ite, prod_const, prod_const]
  have h1 := hcode.1 i
  have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin ℓ)))
    (fun j => code i j = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h3
  have e1 : (Finset.univ.filter (fun j => code i j = true)).card = ℓ / 2 := by omega
  have e2 : (Finset.univ.filter (fun j => ¬ code i j = true)).card = ℓ / 2 := by omega
  rw [e1, e2, numQuestions, mul_comm]

theorem aux_l41_qpq {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (r : φ.RandomString ℓ) (i : Fin k) :
    ∀ j, (φ.question code r i j).isLeft = code i j := by
  intro j; unfold question; cases code i j <;> simp

theorem aux_l41_complete {ℓ k m d : ℕ} (code : Fin k → Fin ℓ → Bool) (hcode : IsCode ℓ k code)
    (P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d) (hsat : φ.toCNF.Satisfiable) :
    ∃ 𝒞 : Finset (φ.SetIdx code), φ.IsSCCover code P 𝒞 ∧ 𝒞.card ≤ k * φ.numQuestions ℓ := by
  classical
  obtain ⟨τ, hτ⟩ := hsat
  let ans : (i : Fin k) → (pq : φ.ProverQuestion code i) → φ.Answer pq.1 := fun i pq =>
    ⟨fun j => φ.aux_l41_cb τ (pq.1 j), fun j => φ.aux_l41_cb_can τ hτ (pq.1 j)⟩
  refine ⟨univ.image (fun p : (Σ i : Fin k, φ.ProverQuestion code i) =>
    (⟨p.1, p.2, ans p.1 p.2⟩ : φ.SetIdx code)), ?_, ?_⟩
  · rintro ⟨r, b⟩
    let α : Fin ℓ → Bool := fun j => τ (φ.var (r j).1 (r j).2 : ℕ)
    let i := (P r).part b (labelEquiv ℓ α)
    let pq : φ.ProverQuestion code i := ⟨φ.question code r i, φ.aux_l41_qpq code r i⟩
    refine ⟨⟨i, pq, ans i pq⟩, mem_image.mpr ⟨⟨i, pq⟩, mem_univ _, rfl⟩, ?_⟩
    simp only [scSet, mem_filter, mem_univ, true_and]
    refine ⟨rfl, ?_⟩
    show (P r).part b (labelEquiv ℓ (φ.inducedAssignment code r i
      (fun j => φ.aux_l41_cb τ (φ.question code r i j)))) = i
    rw [φ.aux_l41_ind τ code r i]
  · refine card_image_le.trans ?_
    rw [card_univ, Fintype.card_sigma]
    simp [φ.aux_l41_pqcard code hcode]

end Formula5

theorem aux_l41_pi1 {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, DecidableEq (α i)] (s : ∀ i, Finset (α i)) (i : ι) {a : α i} (ha : a ∈ s i) :
    ((Fintype.piFinset s).filter (fun f => f i = a)).card * (s i).card =
      (Fintype.piFinset s).card := by
  rw [Fintype.card_filter_piFinset_eq_of_mem _ _ ha, Fintype.card_piFinset,
    prod_erase_mul _ _ (mem_univ i)]

theorem aux_l41_pi2 {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, DecidableEq (α i)] (s : ∀ i, Finset (α i)) (x y : ι) (hxy : x ≠ y)
    {a : α x} {b : α y} (ha : a ∈ s x) (hb : b ∈ s y) :
    ((Fintype.piFinset s).filter (fun f => f x = a ∧ f y = b)).card * ((s x).card * (s y).card) =
      (Fintype.piFinset s).card := by
  have e : (Fintype.piFinset s).filter (fun f => f x = a ∧ f y = b) =
      (Fintype.piFinset (Function.update s x {a})).filter (fun f => f y = b) := by
    rw [Fintype.piFinset_update_singleton_eq_filter_piFinset_eq _ _ ha, filter_filter]
  have hb' : b ∈ Function.update s x {a} y := by rw [Function.update_of_ne hxy.symm]; exact hb
  have h1 := aux_l41_pi1 (Function.update s x {a}) y hb'
  rw [Function.update_of_ne hxy.symm] at h1
  have h3 : (Fintype.piFinset (Function.update s x {a})).card =
      ((Fintype.piFinset s).filter (fun f => f x = a)).card := by
    rw [Fintype.piFinset_update_singleton_eq_filter_piFinset_eq _ _ ha]
  have h2 := aux_l41_pi1 s x ha
  rw [e, ← h2, ← h3, ← h1]
  ring

namespace Formula5

variable (φ : Formula5)

def aux_l41_db : φ.QCoord → Fin 3 → Bool
  | Sum.inl c => fun p => (φ.clause c p).1
  | Sum.inr _ => fun _ => false

theorem aux_l41_db_can (x : φ.QCoord) : φ.CoordCanonical x (φ.aux_l41_db x) := by
  cases x with
  | inl c => exact ⟨0, rfl⟩
  | inr v => exact ⟨rfl, rfl⟩

def aux_l41_dflt {ℓ : ℕ} (q : Fin ℓ → φ.QCoord) : φ.Answer q :=
  ⟨fun j => φ.aux_l41_db (q j), fun j => φ.aux_l41_db_can (q j)⟩

def aux_l41_T {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (𝒞 : Finset (φ.SetIdx code))
    (p : Σ _ : Fin k, (Fin ℓ → φ.QCoord)) : Finset (φ.Answer p.2) :=
  if h : ∀ j, (p.2 j).isLeft = code p.1 j then
    (if (univ.filter (fun a : φ.Answer p.2 => (⟨p.1, ⟨p.2, h⟩, a⟩ : φ.SetIdx code) ∈ 𝒞)).Nonempty
      then univ.filter (fun a : φ.Answer p.2 => (⟨p.1, ⟨p.2, h⟩, a⟩ : φ.SetIdx code) ∈ 𝒞)
      else {φ.aux_l41_dflt p.2})
  else {φ.aux_l41_dflt p.2}

theorem aux_l41_T_ne {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (𝒞 : Finset (φ.SetIdx code))
    (p : Σ _ : Fin k, (Fin ℓ → φ.QCoord)) : (φ.aux_l41_T code 𝒞 p).Nonempty := by
  unfold aux_l41_T
  split_ifs with h1 h2
  · exact h2
  · exact singleton_nonempty _
  · exact singleton_nonempty _

theorem aux_l41_T_eq {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (𝒞 : Finset (φ.SetIdx code))
    (i : Fin k) (q : Fin ℓ → φ.QCoord) (h : ∀ j, (q j).isLeft = code i j) (a : φ.Answer q)
    (ha : (⟨i, ⟨q, h⟩, a⟩ : φ.SetIdx code) ∈ 𝒞) :
    φ.aux_l41_T code 𝒞 ⟨i, q⟩ =
      univ.filter (fun b : φ.Answer q => (⟨i, ⟨q, h⟩, b⟩ : φ.SetIdx code) ∈ 𝒞) := by
  unfold aux_l41_T
  rw [dif_pos h, if_pos ⟨a, by simpa using ha⟩]

end Formula5


lemma aux_l41_threeM (φ : Formula5) : 3 * φ.M = 5 * φ.n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun cp : Fin φ.M × Fin 3 => (φ.clause cp.1 cp.2).2)
    (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h
  rw [mul_comm, h]
  simp [φ.five, mul_comm]

lemma aux_l41_count (φ : Formula5) {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (i : Fin k)
    (q : φ.ProverQuestion code i) :
    (Finset.univ.filter (fun r : φ.RandomString ℓ => φ.question code r i = q.1)).card =
      ∏ j, (if code i j = true then 3 else 5) := by
  classical
  have : (Finset.univ.filter (fun r : φ.RandomString ℓ => φ.question code r i = q.1)) =
      Fintype.piFinset (fun j => Finset.univ.filter (fun p : Fin φ.M × Fin 3 =>
        (if code i j = true then Sum.inl p.1 else Sum.inr (φ.var p.1 p.2)) = q.1 j)) := by
    ext r
    simp [Fintype.mem_piFinset, Formula5.question, funext_iff]
  rw [this, Fintype.card_piFinset]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  have hq := q.2 j
  cases hc : code i j
  · rw [hc] at hq
    obtain ⟨v, hv⟩ : ∃ v, q.1 j = Sum.inr v := by
      cases h : q.1 j with
      | inl c => rw [h] at hq; simp at hq
      | inr v => exact ⟨v, rfl⟩
    simp only [hv, Bool.false_eq_true, if_false, Sum.inr.injEq]
    exact φ.five v
  · rw [hc] at hq
    obtain ⟨c, hcq⟩ : ∃ c, q.1 j = Sum.inl c := by
      cases h : q.1 j with
      | inl c => exact ⟨c, rfl⟩
      | inr v => rw [h] at hq; simp at hq
    simp only [hcq, if_true, Sum.inl.injEq]
    have : (Finset.univ.filter (fun p : Fin φ.M × Fin 3 => p.1 = c)) =
        ({c} : Finset (Fin φ.M)) ×ˢ (Finset.univ : Finset (Fin 3)) := by
      ext ⟨p1, p2⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        Finset.mem_singleton, and_true]
    rw [this, Finset.card_product]
    simp


theorem aux_l41_p42 (φ : Formula5) (ℓ k m : ℕ) (code : Fin k → Fin ℓ → Bool)
    (hcode : IsCode ℓ k code) (hk : 0 < k) (hm : 2 ≤ m)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (𝒞 : Finset (φ.SetIdx code))
    (h𝒞 : (𝒞.card : ℝ) ≤ (1 - δ) * k * φ.numQuestions ℓ * Real.log m) :
    δ / 2 ≤
      ((Finset.univ.filter (fun r : φ.RandomString ℓ =>
          (φ.weight code 𝒞 r : ℝ) < (1 - δ / 2) * k * Real.log m)).card : ℝ) /
        Fintype.card (φ.RandomString ℓ) := by
  classical
  obtain ⟨hw, -⟩ := hcode
  have hℓ : ℓ = 2 * (ℓ / 2) := by have := hw ⟨0, hk⟩; omega
  set a := ℓ / 2 with ha
  have hcount : ∀ (i : Fin k) (q : φ.ProverQuestion code i),
      (Finset.univ.filter (fun r : φ.RandomString ℓ => φ.question code r i = q.1)).card
        = 15 ^ a := by
    intro i q
    rw [aux_l41_count, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have h1 := hw i
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin ℓ)))
      (fun j => code i j = true)
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    have e1 : (Finset.univ.filter (fun j => code i j = true)).card = a := by omega
    have e2 : (Finset.univ.filter (fun j => ¬ code i j = true)).card = a := by omega
    rw [e1, e2, ← mul_pow]
    norm_num
  have hsum : ∑ r : φ.RandomString ℓ, φ.weight code 𝒞 r = 𝒞.card * 15 ^ a := by
    simp only [Formula5.weight, Finset.card_filter]
    rw [Finset.sum_comm]
    simp_rw [← Finset.card_filter]
    rw [Finset.sum_congr rfl (fun x _ => hcount x.1 x.2.1), Finset.sum_const, smul_eq_mul]
  have h3 := aux_l41_threeM φ
  have hMpos := φ.M_pos
  have hnpos : 0 < φ.n := by omega
  have hR : Fintype.card (φ.RandomString ℓ) = (φ.M * 3) ^ ℓ := by simp
  have hkey : 15 ^ a * φ.numQuestions ℓ = Fintype.card (φ.RandomString ℓ) := by
    rw [hR, Formula5.numQuestions, ← ha, hℓ, pow_mul, ← mul_pow, ← mul_pow]
    congr 1
    nlinarith
  -- real-valued Markov argument
  set w : φ.RandomString ℓ → ℕ := fun r => φ.weight code 𝒞 r with hwdef
  set A : ℝ := (1 - δ / 2) * k * Real.log m with hA
  set R : ℝ := (Fintype.card (φ.RandomString ℓ) : ℝ) with hRdef
  set Nq : ℝ := (φ.numQuestions ℓ : ℝ) with hNq
  have hRpos : 0 < R := by
    rw [hRdef, hR]; positivity
  have hNqpos : 0 < Nq := by
    rw [hNq, Formula5.numQuestions]; positivity
  have hlog : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set K : ℝ := (k : ℝ) * Real.log m with hK
  have hKpos : 0 < K := mul_pos hkpos hlog
  have hAK : A = (1 - δ / 2) * K := by rw [hA, hK]; ring
  have hsumR : (∑ r, (w r : ℝ)) * Nq = (𝒞.card : ℝ) * R := by
    have : ((∑ r, w r : ℕ) : ℝ) * Nq = (𝒞.card : ℝ) * R := by
      rw [hsum, hNq, hRdef, ← hkey]; push_cast; ring
    simpa using this
  have hsumle : (∑ r, (w r : ℝ)) ≤ (1 - δ) * K * R := by
    have h𝒞' : (𝒞.card : ℝ) ≤ (1 - δ) * K * Nq := by
      rw [hK]; nlinarith [h𝒞]
    have : (∑ r, (w r : ℝ)) * Nq ≤ ((1 - δ) * K * R) * Nq := by
      rw [hsumR]; nlinarith
    exact le_of_mul_le_mul_right this hNqpos
  set S := Finset.univ.filter (fun r : φ.RandomString ℓ => (w r : ℝ) < A) with hS
  set T := Finset.univ.filter (fun r : φ.RandomString ℓ => ¬ (w r : ℝ) < A) with hT
  have hST : (S.card : ℝ) + T.card = R := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun r : φ.RandomString ℓ => (w r : ℝ) < A)
    rw [Finset.card_univ] at this
    rw [hRdef, hS, hT, ← this]
    push_cast
    rfl
  have hmarkov : (T.card : ℝ) * A ≤ ∑ r, (w r : ℝ) := by
    calc (T.card : ℝ) * A = ∑ r ∈ T, A := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ T, (w r : ℝ) := Finset.sum_le_sum (fun r hr => by
          rw [hT, Finset.mem_filter] at hr; linarith [hr.2])
      _ ≤ ∑ r, (w r : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
  have hSnn : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have key : δ / 2 * R ≤ S.card := by
    have h1 : (T.card : ℝ) * (1 - δ / 2) * K ≤ (1 - δ) * K * R := by
      have := le_trans hmarkov hsumle
      rw [hAK] at this; linarith
    have h2 : (T.card : ℝ) * (1 - δ / 2) ≤ (1 - δ) * R := by
      have : ((T.card : ℝ) * (1 - δ / 2)) * K ≤ ((1 - δ) * R) * K := by linarith
      exact le_of_mul_le_mul_right this hKpos
    have hT' : (T.card : ℝ) = R - S.card := by linarith
    rw [hT'] at h2
    nlinarith
  show δ / 2 ≤ (S.card : ℝ) / R
  rw [le_div_iff₀ hRpos]
  exact key

namespace Formula5

variable (φ : Formula5)

theorem aux_l41_perr {ℓ k m d : ℕ} (code : Fin k → Fin ℓ → Bool)
    (P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d) (𝒞 : Finset (φ.SetIdx code))
    (hcov : φ.IsSCCover code P 𝒞) (r : φ.RandomString ℓ) (hr : φ.weight code 𝒞 r < d)
    (K : ℝ) (hK : (φ.weight code 𝒞 r : ℝ) ≤ K) :
    ((Fintype.piFinset (φ.aux_l41_T code 𝒞)).card : ℝ) * 4 / K ^ 2 ≤
      ((Fintype.piFinset (φ.aux_l41_T code 𝒞)).filter
        (fun σ => φ.WeakAccept code (fun i q => σ ⟨i, q⟩) r)).card := by
  classical
  set W := 𝒞.filter (fun x => φ.question code r x.1 = x.2.1.1) with hW
  have hwW : φ.weight code 𝒞 r = W.card := rfl
  set F := W.image (fun x => (labelEquiv ℓ (φ.inducedAssignment code r x.1 x.2.2.1), x.1))
    with hF
  have hFcov : ∀ b : Fin m, ∃ y ∈ F, (P r).part b y.1 = y.2 := by
    intro b
    obtain ⟨x, hx, hxs⟩ := hcov (r, b)
    simp only [scSet, mem_filter, mem_univ, true_and] at hxs
    exact ⟨_, mem_image_of_mem _ (mem_filter.mpr ⟨hx, hxs.1⟩), hxs.2⟩
  have hFlt : F.card < d := lt_of_le_of_lt card_image_le (hwW ▸ hr)
  have hnot : ¬ ∀ y ∈ F, ∀ z ∈ F, y.1 = z.1 → y = z := fun h =>
    absurd ((P r).cover_bound F h hFcov) (not_le.mpr hFlt)
  push Not at hnot
  obtain ⟨y, hy, z, hz, h1, hne⟩ := hnot
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  obtain ⟨x', hx', rfl⟩ := mem_image.mp hz
  have hind := (labelEquiv ℓ).injective h1
  have hii : x.1 ≠ x'.1 := fun h => hne (Prod.ext h1 h)
  rw [mem_filter] at hx hx'
  clear hy hz hne h1
  obtain ⟨i, ⟨q, hq⟩, a⟩ := x
  obtain ⟨i', ⟨q', hq'⟩, a'⟩ := x'
  obtain ⟨hxC, hxQ⟩ := hx
  obtain ⟨hxC', hxQ'⟩ := hx'
  simp only at hxQ hxQ' hind hii
  subst hxQ hxQ'
  set T := φ.aux_l41_T code 𝒞 with hTdef
  set X : Σ _ : Fin k, (Fin ℓ → φ.QCoord) := ⟨i, φ.question code r i⟩ with hX
  set Y : Σ _ : Fin k, (Fin ℓ → φ.QCoord) := ⟨i', φ.question code r i'⟩ with hY
  have hXY : X ≠ Y := fun h => hii (congrArg Sigma.fst h)
  set s := univ.filter (fun b : φ.Answer (φ.question code r i) =>
    (⟨i, ⟨φ.question code r i, hq⟩, b⟩ : φ.SetIdx code) ∈ 𝒞) with hs
  set s' := univ.filter (fun b : φ.Answer (φ.question code r i') =>
    (⟨i', ⟨φ.question code r i', hq'⟩, b⟩ : φ.SetIdx code) ∈ 𝒞) with hs'
  have hTX : T X = s := φ.aux_l41_T_eq code 𝒞 i _ hq a hxC
  have hTY : T Y = s' := φ.aux_l41_T_eq code 𝒞 i' _ hq' a' hxC'
  have has : a ∈ s := by simpa [s] using hxC
  have has' : a' ∈ s' := by simpa [s'] using hxC'
  have haX : a ∈ T X := by rw [hTX]; exact has
  have haY : a' ∈ T Y := by rw [hTY]; exact has'
  have hcnt := aux_l41_pi2 T X Y hXY haX haY
  have hsub : (Fintype.piFinset T).filter (fun σ => σ X = a ∧ σ Y = a') ⊆
      (Fintype.piFinset T).filter (fun σ => φ.WeakAccept code (fun i q => σ ⟨i, q⟩) r) := by
    intro σ hσ
    rw [mem_filter] at hσ ⊢
    refine ⟨hσ.1, i, i', hii, ?_⟩
    unfold Consistent
    show φ.inducedAssignment code r i (σ X).1 = φ.inducedAssignment code r i' (σ Y).1
    rw [hσ.2.1, hσ.2.2]
    exact hind
  have hst : s.card + s'.card ≤ W.card := by
    let e : φ.Answer (φ.question code r i) → φ.SetIdx code :=
      fun b => ⟨i, ⟨φ.question code r i, hq⟩, b⟩
    let e' : φ.Answer (φ.question code r i') → φ.SetIdx code :=
      fun b => ⟨i', ⟨φ.question code r i', hq'⟩, b⟩
    have he : Function.Injective e := by
      intro b1 b2 h
      have h1 := (Sigma.mk.inj_iff.mp h).2
      have h2 := (Sigma.mk.inj_iff.mp (eq_of_heq h1)).2
      exact eq_of_heq h2
    have he' : Function.Injective e' := by
      intro b1 b2 h
      have h1 := (Sigma.mk.inj_iff.mp h).2
      have h2 := (Sigma.mk.inj_iff.mp (eq_of_heq h1)).2
      exact eq_of_heq h2
    have hdisj : Disjoint (s.image e) (s'.image e') := by
      rw [disjoint_left]
      intro x hx1 hx2
      obtain ⟨b1, _, rfl⟩ := mem_image.mp hx1
      obtain ⟨b2, _, hb2⟩ := mem_image.mp hx2
      exact hii (congrArg Sigma.fst hb2).symm
    have hsubW : s.image e ∪ s'.image e' ⊆ W := by
      intro x hx
      rcases mem_union.mp hx with hx | hx
      · obtain ⟨b, hb, rfl⟩ := mem_image.mp hx
        simp only [s, mem_filter, mem_univ, true_and] at hb
        exact mem_filter.mpr ⟨hb, rfl⟩
      · obtain ⟨b, hb, rfl⟩ := mem_image.mp hx
        simp only [s', mem_filter, mem_univ, true_and] at hb
        exact mem_filter.mpr ⟨hb, rfl⟩
    have := card_le_card hsubW
    rw [card_union_of_disjoint hdisj, card_image_of_injective _ he,
      card_image_of_injective _ he'] at this
    exact this
  have ht : 1 ≤ s.card := card_pos.mpr ⟨a, has⟩
  have ht' : 1 ≤ s'.card := card_pos.mpr ⟨a', has'⟩
  rw [hTX, hTY] at hcnt
  set N := ((Fintype.piFinset T).filter (fun σ => σ X = a ∧ σ Y = a')).card with hNdef
  have hN : (N : ℝ) * ((s.card : ℝ) * s'.card) = (Fintype.piFinset T).card := by
    exact_mod_cast hcnt
  have hle : (N : ℝ) ≤ ((Fintype.piFinset T).filter
      (fun σ => φ.WeakAccept code (fun i q => σ ⟨i, q⟩) r)).card := by
    exact_mod_cast card_le_card hsub
  have hst' : (s.card : ℝ) + s'.card ≤ K := by
    have : ((s.card + s'.card : ℕ) : ℝ) ≤ W.card := by exact_mod_cast hst
    push_cast at this
    rw [hwW] at hK
    linarith
  have ht1 : (1:ℝ) ≤ s.card := by exact_mod_cast ht
  have ht1' : (1:ℝ) ≤ s'.card := by exact_mod_cast ht'
  have hKpos : 0 < K := by linarith
  rw [div_le_iff₀ (by positivity), ← hN]
  have h4 : 4 * ((s.card : ℝ) * s'.card) ≤ K ^ 2 := by
    nlinarith [sq_nonneg ((s.card : ℝ) - s'.card)]
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  calc (N : ℝ) * ((s.card : ℝ) * s'.card) * 4 = N * (4 * ((s.card : ℝ) * s'.card)) := by ring
    _ ≤ N * K ^ 2 := mul_le_mul_of_nonneg_left h4 hN0
    _ ≤ _ := mul_le_mul_of_nonneg_right hle (by positivity)


theorem aux_l41_p43 {ℓ k m d : ℕ} (code : Fin k → Fin ℓ → Bool) (hcode : IsCode ℓ k code)
    (P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < k) (hm : 2 ≤ m)
    (hd : (1 - δ / 2) * k * Real.log m ≤ d)
    (𝒞 : Finset (φ.SetIdx code)) (hcov : φ.IsSCCover code P 𝒞)
    (h𝒞 : (𝒞.card : ℝ) ≤ (1 - δ) * k * φ.numQuestions ℓ * Real.log m) :
    ∃ A : φ.KStrategy ℓ k, 2 * δ / (k * Real.log m) ^ 2 ≤ φ.weakAcceptFrac code A := by
  classical
  have hG := aux_l41_p42 φ ℓ k m code hcode hk hm δ hδ hδ1 𝒞 h𝒞
  set G := univ.filter (fun r : φ.RandomString ℓ =>
    (φ.weight code 𝒞 r : ℝ) < (1 - δ / 2) * k * Real.log m) with hGdef
  have hlog : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  set K := (k : ℝ) * Real.log m with hK
  have hKpos : 0 < K := mul_pos hkpos hlog
  set PS := Fintype.piFinset (φ.aux_l41_T code 𝒞) with hPS
  have hPSne : PS.Nonempty := Fintype.piFinset_nonempty.mpr (fun p => φ.aux_l41_T_ne code 𝒞 p)
  have hper : ∀ r ∈ G, (PS.card : ℝ) * 4 / K ^ 2 ≤
      (PS.filter (fun σ => φ.WeakAccept code (fun i q => σ ⟨i, q⟩) r)).card := by
    intro r hr
    simp only [G, mem_filter, mem_univ, true_and] at hr
    have hK1 : (1 - δ / 2) * k * Real.log m ≤ K := by
      rw [hK]; nlinarith
    apply φ.aux_l41_perr code P 𝒞 hcov r
    · have : (φ.weight code 𝒞 r : ℝ) < d := lt_of_lt_of_le hr hd
      exact_mod_cast this
    · linarith
  have hsum : ∑ σ ∈ PS, ((univ.filter (fun r => φ.WeakAccept code (fun i q => σ ⟨i, q⟩) r)).card : ℝ)
      = ∑ r, ((PS.filter (fun σ => φ.WeakAccept code (fun i q => σ ⟨i, q⟩) r)).card : ℝ) := by
    have : ∑ σ ∈ PS, (univ.filter (fun r => φ.WeakAccept code (fun i q => σ ⟨i, q⟩) r)).card
      = ∑ r, (PS.filter (fun σ => φ.WeakAccept code (fun i q => σ ⟨i, q⟩) r)).card := by
      simp only [card_filter]
      rw [sum_comm]
    exact_mod_cast this
  have hlow : (G.card : ℝ) * ((PS.card : ℝ) * 4 / K ^ 2) ≤
      ∑ r, ((PS.filter (fun σ => φ.WeakAccept code (fun i q => σ ⟨i, q⟩) r)).card : ℝ) := by
    calc (G.card : ℝ) * ((PS.card : ℝ) * 4 / K ^ 2) = ∑ r ∈ G, ((PS.card : ℝ) * 4 / K ^ 2) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ G, ((PS.filter (fun σ => φ.WeakAccept code (fun i q => σ ⟨i, q⟩) r)).card : ℝ) :=
          sum_le_sum hper
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
  obtain ⟨σ, -, hσle⟩ := exists_le_of_sum_le hPSne
    (f := fun _ => (G.card : ℝ) * 4 / K ^ 2)
    (g := fun σ => ((univ.filter (fun r => φ.WeakAccept code (fun i q => σ ⟨i, q⟩) r)).card : ℝ))
    (by
      rw [sum_const, nsmul_eq_mul, hsum]
      calc (PS.card : ℝ) * ((G.card : ℝ) * 4 / K ^ 2)
          = (G.card : ℝ) * ((PS.card : ℝ) * 4 / K ^ 2) := by ring
        _ ≤ _ := hlow)
  refine ⟨fun i q => σ ⟨i, q⟩, ?_⟩
  have hR : (0:ℝ) < Fintype.card (φ.RandomString ℓ) := by
    have : Nonempty (φ.RandomString ℓ) := ⟨fun _ => (⟨0, φ.M_pos⟩, 0)⟩
    exact_mod_cast Fintype.card_pos
  unfold weakAcceptFrac
  rw [le_div_iff₀ hR]
  have hG' : δ / 2 * Fintype.card (φ.RandomString ℓ) ≤ G.card := by
    rwa [le_div_iff₀ hR] at hG
  calc 2 * δ / K ^ 2 * Fintype.card (φ.RandomString ℓ)
      = (δ / 2 * Fintype.card (φ.RandomString ℓ)) * 4 / K ^ 2 := by ring
    _ ≤ (G.card : ℝ) * 4 / K ^ 2 := by gcongr
    _ ≤ _ := hσle

end Formula5

end SetCoverThreshold.SetCover

open SetCoverThreshold.SetCover

theorem solution (hRaz : RazRepetition) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (φ : Formula5) (ℓ k m d : ℕ) (code : Fin k → Fin ℓ → Bool), IsCode ℓ k code →
        ∀ P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d,
          (φ.toCNF.Satisfiable →
              ∃ 𝒞 : Finset (φ.SetIdx code), φ.IsSCCover code P 𝒞 ∧
                𝒞.card ≤ k * φ.numQuestions ℓ) ∧
            ∀ f : ℝ, 0 < f → (1 - f) * k * Real.log m ≤ d →
              (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(c * ℓ)) < 2 * (2 * f) / (k * Real.log m) ^ 2 →
                AtMostFracSat (1 - ε) φ.toCNF →
                  ∀ 𝒞 : Finset (φ.SetIdx code), φ.IsSCCover code P 𝒞 →
                    (1 - 2 * f) * k * φ.numQuestions ℓ * Real.log m ≤ 𝒞.card := by
  obtain ⟨c₀, hc₀, hR⟩ := hRaz ε hε
  refine ⟨c₀ / 6, by positivity, ?_⟩
  intro φ ℓ k m d code hcode P
  refine ⟨φ.aux_l41_complete code hcode P, ?_⟩
  intro f hf hd hc hφ 𝒞 hcov
  by_contra hlt
  push Not at hlt
  have hlogm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hQ0 : (0:ℝ) ≤ φ.numQuestions ℓ := Nat.cast_nonneg _
  have hcard0 : (0:ℝ) ≤ 𝒞.card := Nat.cast_nonneg _
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      simp at hlt
      linarith
    · exact h
  have hlogpos : 0 < Real.log m := by
    rcases hlogm.lt_or_eq with h | h
    · exact h
    · rw [← h] at hlt
      simp at hlt
      linarith
  have hm : 2 ≤ m := by
    by_contra h'
    push Not at h'
    interval_cases m <;> simp at hlogpos
  have hf1 : 2 * f < 1 := by
    by_contra h'
    push Not at h'
    have : (1 - 2 * f) * k * φ.numQuestions ℓ * Real.log m ≤ 0 := by
      have h1 : (1 - 2 * f) ≤ 0 := by linarith
      have h2 : (0:ℝ) ≤ k * φ.numQuestions ℓ * Real.log m := by positivity
      have : (1 - 2 * f) * k * φ.numQuestions ℓ * Real.log m =
          (1 - 2 * f) * (k * φ.numQuestions ℓ * Real.log m) := by ring
      rw [this]
      exact mul_nonpos_of_nonpos_of_nonneg h1 h2
    linarith
  obtain ⟨A, hA⟩ := φ.aux_l41_p43 code hcode P (2 * f) (by linarith) (by linarith) hk hm
    (by rw [show 1 - 2 * f / 2 = 1 - f by ring]; exact hd) 𝒞 hcov hlt.le
  have hW := φ.aux_l41_weak c₀ hc₀ (hR φ hφ) code hcode A
  linarith

