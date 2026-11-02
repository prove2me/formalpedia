-- Prove2me | solution 1 for QAlgorithms.Nannicini.findAllMarked_knownCount
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:05:01.712464+00:00
-- url     : https://prove2.me/submissions/f3bac09e-49d5-4f13-bfa2-e257032f0e15

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
import Theorems.Thm_QAlgorithms_Nannicini_search_knownCount
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open QAlgorithms
open QAlgorithms.Nannicini

/-- Any involution on a finite type defines a unitary permutation matrix. -/
noncomputable def involMat {X : Type*} [Fintype X] [DecidableEq X] (σ : X → X) : Matrix X X ℂ :=
  Matrix.of fun x y => if x = σ y then 1 else 0

private lemma involMat_mem_unitary {X : Type*} [Fintype X] [DecidableEq X]
    (σ : X → X) (hσ : ∀ x, σ (σ x) = x) :
    involMat σ ∈ Matrix.unitaryGroup X ℂ := by
  have hsymm : ∀ x y, (x = σ y) ↔ (y = σ x) :=
    fun x y => ⟨fun h => by rw [h, hσ], fun h => by rw [h, hσ]⟩
  have hstar : star (involMat σ) = involMat σ := by
    ext x y
    simp only [Matrix.star_apply, involMat, Matrix.of_apply]
    by_cases h : x = σ y
    · have h' : y = σ x := (hsymm x y).mp h
      rw [if_pos h', if_pos h, star_one]
    · have h' : y ≠ σ x := fun hy => h ((hsymm x y).mpr hy)
      rw [if_neg h', if_neg h, star_zero]
  have hmul : involMat σ * involMat σ = 1 := by
    ext x y
    simp only [Matrix.mul_apply, involMat, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (σ y)]
    · by_cases h : x = y
      · subst h; simp [hσ]
      · have hne : x ≠ σ (σ y) := by rw [hσ]; exact h
        simp [h, hne]
    · intro z _ hz
      simp [hz]
    · simp
  rw [Matrix.mem_unitaryGroup_iff, hstar, hmul]

private lemma act_involMat {X : Type*} [Fintype X] [DecidableEq X]
    (σ : X → X) (hσ : ∀ x, σ (σ x) = x) (ψ : EuclideanSpace ℂ X) (x : X) :
    act (involMat σ) ψ x = ψ (σ x) := by
  simp only [act, involMat, Matrix.mulVec, dotProduct, Matrix.of_apply, WithLp.ofLp_toLp]
  rw [Finset.sum_eq_single (σ x)]
  · simp [hσ]
  · intro y _ hy
    have hne : x ≠ σ y := fun h => hy (by rw [h, hσ])
    simp [hne]
  · simp

section SlotMat

variable {Q Ans ι : Type*} [Fintype Q] [DecidableEq Q] [Fintype Ans] [DecidableEq Ans]
  [Fintype ι] [DecidableEq ι] {R : ι → Type*} [∀ p, Fintype (R p)] [∀ p, DecidableEq (R p)]

abbrev SState (Q Ans : Type*) {ι : Type*} (R : ι → Type*) := Q × (Ans × (∀ p : ι, R p))

def updSlot (x : SState Q Ans R) (p : ι) (z : R p) : SState Q Ans R :=
  (x.1, (x.2.1, Function.update x.2.2 p z))

private lemma updSlot_self (x : SState Q Ans R) (p : ι) :
    updSlot x p (x.2.2 p) = x := by
  rcases x with ⟨q, a, pool⟩
  simp [updSlot]

private lemma updSlot_updSlot (x : SState Q Ans R) (p : ι) (z₁ z₂ : R p) :
    updSlot (updSlot x p z₁) p z₂ = updSlot x p z₂ := by
  rcases x with ⟨q, a, pool⟩
  simp [updSlot]

private lemma updSlot_eval (x : SState Q Ans R) (p : ι) (z : R p) :
    (updSlot x p z).2.2 p = z := by
  simp [updSlot]

private lemma eq_updSlot_symm {x y : SState Q Ans R} {p : ι} :
    y = updSlot x p (y.2.2 p) ↔ x = updSlot y p (x.2.2 p) := by
  constructor <;> intro h
  · conv_lhs => rw [← updSlot_self x p]
    rw [h, updSlot_updSlot]
  · conv_lhs => rw [← updSlot_self y p]
    rw [h, updSlot_updSlot]

noncomputable def slotMat (sel : SState Q Ans R → Option ι)
    (U : SState Q Ans R → ∀ p : ι, Matrix.unitaryGroup (R p) ℂ) :
    Matrix (SState Q Ans R) (SState Q Ans R) ℂ :=
  Matrix.of fun x y =>
    match sel x with
    | none => if x = y then 1 else 0
    | some p =>
        if y = updSlot x p (y.2.2 p) then
          (U x p : Matrix (R p) (R p) ℂ) (x.2.2 p) (y.2.2 p)
        else 0

private lemma act_slotMat (sel : SState Q Ans R → Option ι)
    (U : SState Q Ans R → ∀ p : ι, Matrix.unitaryGroup (R p) ℂ)
    (ψ : EuclideanSpace ℂ (SState Q Ans R)) (x : SState Q Ans R) :
    act (slotMat sel U) ψ x =
      match sel x with
      | none => ψ x
      | some p =>
          act (U x p : Matrix (R p) (R p) ℂ) (WithLp.toLp 2 fun z => ψ (updSlot x p z)) (x.2.2 p) := by
  simp only [act, slotMat, Matrix.mulVec, dotProduct, Matrix.of_apply, WithLp.ofLp_toLp]
  cases h : sel x with
  | none =>
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  | some p =>
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    have hbij : Finset.univ.filter (fun y : SState Q Ans R => y = updSlot x p (y.2.2 p)) =
        Finset.univ.image (fun z : R p => updSlot x p z) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hy; exact ⟨y.2.2 p, hy.symm⟩
      · rintro ⟨z, rfl⟩; rw [updSlot_eval]
    rw [hbij, Finset.sum_image]
    · refine Finset.sum_congr rfl fun z _ => ?_
      rw [updSlot_eval]
    · intro z₁ _ z₂ _ hz
      have := congr_arg (fun w : SState Q Ans R => w.2.2 p) hz
      simpa [updSlot_eval] using this

private lemma slotMat_mem_unitary (sel : SState Q Ans R → Option ι)
    (U : SState Q Ans R → ∀ p : ι, Matrix.unitaryGroup (R p) ℂ)
    (hsel : ∀ x p z, sel x = some p → sel (updSlot x p z) = some p)
    (hU : ∀ x p z, sel x = some p → U (updSlot x p z) p = U x p) :
    slotMat sel U ∈ Matrix.unitaryGroup (SState Q Ans R) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext x w
  simp only [Matrix.mul_apply, Matrix.star_apply, slotMat, Matrix.of_apply, Matrix.one_apply]
  cases hx : sel x with
  | none =>
    rw [Finset.sum_eq_single x]
    · by_cases hxw : x = w
      · subst hxw; simp [hx]
      · simp only [↓reduceIte, one_mul]
        cases hw : sel w with
        | none =>
          have hwx : ¬ (w = x) := Ne.symm hxw
          simp [hwx, hxw]
        | some p =>
          have hnot : ¬ (x = updSlot w p (x.2.2 p)) := by
            intro h
            have := hsel w p (x.2.2 p) hw
            rw [← h, hx] at this
            nomatch this
          simp [hnot, hxw]
    · intro y _ hyx
      have hxy : ¬ (x = y) := Ne.symm hyx
      simp [hxy]
    · simp
  | some p =>
    have hsum : (∑ y : SState Q Ans R,
        (if y = updSlot x p (y.2.2 p) then (U x p : Matrix (R p) (R p) ℂ) (x.2.2 p) (y.2.2 p) else 0) *
        star (match sel w with
          | none => if w = y then (1 : ℂ) else 0
          | some p' => if y = updSlot w p' (y.2.2 p') then (U w p' : Matrix (R p') (R p') ℂ) (w.2.2 p') (y.2.2 p') else 0)) =
        ∑ z : R p, (U x p : Matrix (R p) (R p) ℂ) (x.2.2 p) z *
          star (match sel w with
            | none => if w = updSlot x p z then (1 : ℂ) else 0
            | some p' => if updSlot x p z = updSlot w p' ((updSlot x p z).2.2 p') then
                (U w p' : Matrix (R p') (R p') ℂ) (w.2.2 p') ((updSlot x p z).2.2 p') else 0) := by
      simp only [ite_mul, zero_mul, ← Finset.sum_filter]
      have hbij : Finset.univ.filter (fun y : SState Q Ans R => y = updSlot x p (y.2.2 p)) =
          Finset.univ.image (fun z : R p => updSlot x p z) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        exact ⟨fun hy => ⟨y.2.2 p, hy.symm⟩, by rintro ⟨z, rfl⟩; rw [updSlot_eval]⟩
      rw [hbij, Finset.sum_image]
      · refine Finset.sum_congr rfl fun z _ => ?_
        rw [updSlot_eval]
      · intro z₁ _ z₂ _ hz
        simpa [updSlot_eval] using congr_arg (fun y : SState Q Ans R => y.2.2 p) hz
    rw [hsum]
    by_cases hwx : w = updSlot x p (w.2.2 p)
    · have hw_sel : sel w = some p := by rw [hwx]; exact hsel x p (w.2.2 p) hx
      have hw_U : U w p = U x p := by rw [hwx]; exact hU x p (w.2.2 p) hx
      have hcond : ∀ z : R p, updSlot x p z = updSlot w p z := by
        intro z; rw [hwx, updSlot_updSlot]
      have hsum2 : (∑ z : R p, (U x p : Matrix (R p) (R p) ℂ) (x.2.2 p) z *
          star (match sel w with
            | none => if w = updSlot x p z then (1 : ℂ) else 0
            | some p' => if updSlot x p z = updSlot w p' ((updSlot x p z).2.2 p') then
                (U w p' : Matrix (R p') (R p') ℂ) (w.2.2 p') ((updSlot x p z).2.2 p') else 0)) =
          ((U x p : Matrix (R p) (R p) ℂ) * star (U x p : Matrix (R p) (R p) ℂ)) (x.2.2 p) (w.2.2 p) := by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [hw_sel]
        simp only [updSlot_eval, hcond z, ↓reduceIte, hw_U, Matrix.star_apply]
      rw [hsum2, Matrix.mem_unitaryGroup_iff.mp (U x p).2, Matrix.one_apply]
      by_cases hzxw : x.2.2 p = w.2.2 p
      · have h_eq : x = w := by rw [hwx, ← hzxw, updSlot_self]
        simp [h_eq]
      · have h_ne : x ≠ w := fun h => hzxw (by rw [h])
        simp [hzxw, h_ne]
    · have h_ne : x ≠ w := fun h => hwx (by rw [← h, updSlot_self])
      rw [if_neg h_ne]
      refine Finset.sum_eq_zero fun z _ => ?_
      cases hw : sel w with
      | none =>
        have h1 : w ≠ updSlot x p z := by
          intro h
          have := hsel x p z hx
          rw [← h, hw] at this
          nomatch this
        simp [h1]
      | some p' =>
        have h1 : ¬ (updSlot x p z = updSlot w p' ((updSlot x p z).2.2 p')) := by
          intro h
          have hp_eq : p' = p := by
            have hs1 := hsel x p z hx
            have hs2 := hsel w p' ((updSlot x p z).2.2 p') hw
            rw [← h, hs1] at hs2
            exact Option.some.inj hs2.symm
          subst p'
          apply hwx
          rw [eq_updSlot_symm]
          calc x = updSlot (updSlot x p z) p (x.2.2 p) := by rw [updSlot_updSlot, updSlot_self]
            _ = updSlot w p (x.2.2 p) := by rw [h, updSlot_updSlot]
        simp [h1]

end SlotMat

section SimMachine

abbrev QReg (n : ℕ) := Qubits n × Bool
abbrev Ans (n T : ℕ) := Fin T → Qubits n × Bool
abbrev SlotIdx (T t : ℕ) := Fin T × Fin t
abbrev SlotReg (n : ℕ) {T t : ℕ} (wOf : Fin t → ℕ) (p : SlotIdx T t) :=
  (Qubits n × Bool) × Fin (wOf p.2)
abbrev Pool (n T t : ℕ) (wOf : Fin t → ℕ) := ∀ p : SlotIdx T t, SlotReg n wOf p
abbrev FullState (n T t : ℕ) (wOf : Fin t → ℕ) :=
  @SState (QReg n) (Ans n T) (SlotIdx T t) (@SlotReg n T t wOf)

instance (n : ℕ) : Fintype (QReg n) := inferInstanceAs (Fintype ((Fin n → Bool) × Bool))
instance (n : ℕ) : DecidableEq (QReg n) := inferInstanceAs (DecidableEq ((Fin n → Bool) × Bool))
instance (n T : ℕ) : Fintype (Ans n T) := inferInstanceAs (Fintype (Fin T → QReg n))
instance (n T : ℕ) : DecidableEq (Ans n T) := inferInstanceAs (DecidableEq (Fin T → QReg n))
instance (T t : ℕ) : Fintype (SlotIdx T t) := inferInstanceAs (Fintype (Fin T × Fin t))
instance (T t : ℕ) : DecidableEq (SlotIdx T t) := inferInstanceAs (DecidableEq (Fin T × Fin t))
instance (n T t : ℕ) (wOf : Fin t → ℕ) (p : SlotIdx T t) : Fintype (SlotReg n wOf p) :=
  inferInstanceAs (Fintype (QReg n × Fin (wOf p.2)))
instance (n T t : ℕ) (wOf : Fin t → ℕ) (p : SlotIdx T t) : DecidableEq (SlotReg n wOf p) :=
  inferInstanceAs (DecidableEq (QReg n × Fin (wOf p.2)))
instance (n T t : ℕ) (wOf : Fin t → ℕ) : Fintype (Pool n T t wOf) :=
  inferInstanceAs (Fintype (∀ p : SlotIdx T t, SlotReg n wOf p))
instance (n T t : ℕ) (wOf : Fin t → ℕ) : DecidableEq (Pool n T t wOf) :=
  inferInstanceAs (DecidableEq (∀ p : SlotIdx T t, SlotReg n wOf p))
instance (n T t : ℕ) (wOf : Fin t → ℕ) : Fintype (FullState n T t wOf) :=
  inferInstanceAs (Fintype (QReg n × (Ans n T × Pool n T t wOf)))
instance (n T t : ℕ) (wOf : Fin t → ℕ) : DecidableEq (FullState n T t wOf) :=
  inferInstanceAs (DecidableEq (QReg n × (Ans n T × Pool n T t wOf)))

variable (n t T : ℕ) (wOf TOf : Fin t → ℕ)
  (AOf : ∀ s : Fin t, QueryAlg (Qubits n) Bool (Fin (wOf s)) (TOf s))
  (outOf : ∀ s : Fin t, (Qubits n × Bool) × Fin (wOf s) → Qubits n)

def TOfNat (s : ℕ) : ℕ :=
  if hs : 1 ≤ s ∧ s ≤ t then TOf ⟨s - 1, by omega⟩ else 0

private lemma TOfNat_eq (s : ℕ) (hs : 1 ≤ s ∧ s ≤ t) (p2 : Fin t) (hp2 : (p2 : ℕ) = s - 1) :
    TOfNat t TOf s = TOf p2 := by
  unfold TOfNat
  rw [dif_pos hs]
  congr 1
  ext; exact hp2.symm

def simStep (q : ℕ) (ans : Ans n T) (st : Finset (Qubits n) × ℕ × ℕ) :
    Finset (Qubits n) × ℕ × ℕ :=
  let S := st.1
  let q0 := st.2.1
  let τ := st.2.2
  let s := t - S.card
  if 1 ≤ s ∧ s ≤ t then
    if τ < TOfNat t TOf s then
      (S, q0, τ + 1)
    else
      let cb := if hq : q < T then ans ⟨q, hq⟩ else (0, false)
      if cb.2 && decide (cb.1 ∉ S) then
        (insert cb.1 S, q + 1, 0)
      else
        (S, q + 1, 0)
  else
    (S, q + 1, 0)

def simState : ℕ → Ans n T → Finset (Qubits n) × ℕ × ℕ
  | 0, _ => (∅, 0, 0)
  | q + 1, ans => simStep n t T TOf q ans (simState q ans)

private lemma simState_q0_add_tau (q : ℕ) (ans : Ans n T) :
    (simState n t T TOf q ans).2.1 + (simState n t T TOf q ans).2.2 = q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [simState, simStep]
    split_ifs <;> dsimp <;> omega

private lemma simState_q0_le (q : ℕ) (ans : Ans n T) :
    (simState n t T TOf q ans).2.1 ≤ q := by
  have := simState_q0_add_tau n t T TOf q ans
  omega

private lemma simState_q0_mono (q : ℕ) (ans : Ans n T) :
    (simState n t T TOf q ans).2.1 ≤ (simState n t T TOf (q + 1) ans).2.1 := by
  have hle := simState_q0_le n t T TOf q ans
  simp only [simState, simStep]
  split_ifs <;> dsimp <;> omega

private lemma simState_congr (q : ℕ) {ans₁ ans₂ : Ans n T}
    (hans : ∀ i : Fin T, (i : ℕ) < q → ans₁ i = ans₂ i) :
    simState n t T TOf q ans₁ = simState n t T TOf q ans₂ := by
  induction q with
  | zero => rfl
  | succ q ih =>
    have ih_eq := ih (fun i hi => hans i (Nat.lt_succ_of_lt hi))
    have hcb : (if hq : q < T then ans₁ ⟨q, hq⟩ else (0, false)) =
        (if hq : q < T then ans₂ ⟨q, hq⟩ else (0, false)) := by
      split_ifs with hq
      · exact hans ⟨q, hq⟩ (Nat.lt_succ_self q)
      · rfl
    simp only [simState, simStep, ih_eq, hcb]

private lemma simState_upd_ge (q : ℕ) (ans : Ans n T) (i : Fin T) (hi : q ≤ (i : ℕ))
    (cb : Qubits n × Bool) :
    simState n t T TOf q (Function.update ans i cb) = simState n t T TOf q ans := by
  apply simState_congr n t T TOf q
  intro j hj
  have hne : j ≠ i := by intro h; subst h; omega
  simp [hne]

def candOfSt (st : Finset (Qubits n) × ℕ × ℕ) (pool : Pool n T t wOf) : Qubits n :=
  let s := t - st.1.card
  if hs : 1 ≤ s ∧ s ≤ t then
    let sFin : Fin t := ⟨s - 1, by omega⟩
    if hq0 : st.2.1 < T then outOf sFin (pool (⟨st.2.1, hq0⟩, sFin)) else 0
  else 0

def candAt (q : ℕ) (ans : Ans n T) (pool : Pool n T t wOf) : Qubits n :=
  candOfSt n t T wOf outOf (simState n t T TOf q ans) pool

def expectedAnsAt (f : Qubits n → Bool) (ans : Ans n T) (pool : Pool n T t wOf) (i : Fin T) :
    Qubits n × Bool :=
  let st := simState n t T TOf (i : ℕ) ans
  let s := t - st.1.card
  if 1 ≤ s ∧ s ≤ t ∧ st.2.2 < TOfNat t TOf s then
    (0, false)
  else
    let cand := candAt n t T wOf TOf outOf (i : ℕ) ans pool
    (cand, f cand)

def mkValidAns (f : Qubits n → Bool) : ℕ → Pool n T t wOf → Ans n T
  | 0, _ => fun _ => (0, false)
  | q + 1, pool =>
      let ans := mkValidAns f q pool
      if hq : q < T then
        Function.update ans ⟨q, hq⟩ (expectedAnsAt n t T wOf TOf outOf f ans pool ⟨q, hq⟩)
      else ans

private lemma mkValidAns_ge (f : Qubits n → Bool) (q : ℕ) (pool : Pool n T t wOf)
    (i : Fin T) (hi : q ≤ (i : ℕ)) :
    mkValidAns n t T wOf TOf outOf f q pool i = (0, false) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [mkValidAns]
    split_ifs with hq
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; subst h; simp at hi
      rw [Function.update_of_ne hne, ih (by omega)]
    · exact ih (by omega)

private lemma simState_mkValidAns_step (f : Qubits n → Bool) (q : ℕ) (pool : Pool n T t wOf) :
    simState n t T TOf q (mkValidAns n t T wOf TOf outOf f (q + 1) pool) =
      simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool) := by
  simp only [mkValidAns]
  split_ifs with hq
  · exact simState_upd_ge n t T TOf q _ ⟨q, hq⟩ (le_refl q) _
  · rfl

private lemma mkValidAns_congr_pool (f : Qubits n → Bool) (q : ℕ)
    {pool₁ pool₂ : Pool n T t wOf}
    (hpool : ∀ p : SlotIdx T t,
      (p.1 : ℕ) < (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool₁)).2.1 →
        pool₁ p = pool₂ p) :
    mkValidAns n t T wOf TOf outOf f q pool₁ = mkValidAns n t T wOf TOf outOf f q pool₂ := by
  induction q with
  | zero => rfl
  | succ q ih =>
    have hstep := simState_mkValidAns_step n t T wOf TOf outOf f q pool₁
    have hmono := simState_q0_mono n t T TOf q (mkValidAns n t T wOf TOf outOf f (q + 1) pool₁)
    rw [hstep] at hmono
    have ih_eq := ih (fun p hp => hpool p (lt_of_lt_of_le hp hmono))
    simp only [mkValidAns]
    rw [← ih_eq]
    split_ifs with hq
    · congr 1
      dsimp only [expectedAnsAt, candAt, candOfSt]
      split_ifs with h_int hs hq0
      · rfl
      · have hp_eq : pool₁ (⟨(simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool₁)).2.1, hq0⟩, ⟨t - (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool₁)).1.card - 1, by omega⟩) =
            pool₂ (⟨(simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool₁)).2.1, hq0⟩, ⟨t - (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool₁)).1.card - 1, by omega⟩) := by
          apply hpool
          have hq0_le := simState_q0_le n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool₁)
          have hτ : ¬ (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool₁)).2.2 <
              TOfNat t TOf (t - (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool₁)).1.card) := by
            intro hlt; exact h_int ⟨hs.1, hs.2, hlt⟩
          simp only [simState]
          rw [hstep]
          simp only [simStep, hs, hτ, ↓reduceIte]
          split_ifs <;> dsimp <;> omega
        rw [hp_eq]
      · rfl
      · rfl
    · rfl

private lemma mkValidAns_upd_ge (f : Qubits n → Bool) (q : ℕ) (pool : Pool n T t wOf)
    (p0 : SlotIdx T t)
    (hp0 : (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool)).2.1 ≤ (p0.1 : ℕ))
    (z : SlotReg n wOf p0) :
    mkValidAns n t T wOf TOf outOf f q (Function.update pool p0 z) =
      mkValidAns n t T wOf TOf outOf f q pool := by
  symm
  apply mkValidAns_congr_pool n t T wOf TOf outOf f q
  intro p hp
  have hne : p ≠ p0 := by intro h; subst h; omega
  simp [hne]

private lemma simState_tau_le (q : ℕ) (ans : Ans n T) :
    (simState n t T TOf q ans).2.2 ≤
      TOfNat t TOf (t - (simState n t T TOf q ans).1.card) := by
  induction q with
  | zero => exact Nat.zero_le _
  | succ q ih =>
    simp only [simState, simStep]
    split_ifs <;> dsimp <;> omega

private lemma simState_between_q0 (q : ℕ) (ans : Ans n T) :
    ∀ q', (simState n t T TOf q ans).2.1 ≤ q' → q' ≤ q →
      simState n t T TOf q' ans =
        ((simState n t T TOf q ans).1, (simState n t T TOf q ans).2.1,
          q' - (simState n t T TOf q ans).2.1) := by
  induction q with
  | zero =>
    intro q' _ hq'
    have : q' = 0 := by omega
    subst this
    rfl
  | succ q ih =>
    intro q' hlo hhi
    rcases eq_or_lt_of_le hhi with rfl | hlt
    · have hadd := simState_q0_add_tau n t T TOf (q + 1) ans
      rcases hst : simState n t T TOf (q + 1) ans with ⟨S', q0', τ'⟩
      rw [hst] at hadd
      dsimp at hadd ⊢
      congr 2
      omega
    · have hq'_le : q' ≤ q := by omega
      by_cases hs_q : 1 ≤ t - (simState n t T TOf q ans).1.card ∧
          t - (simState n t T TOf q ans).1.card ≤ t
      · by_cases hτ_q : (simState n t T TOf q ans).2.2 <
            TOfNat t TOf (t - (simState n t T TOf q ans).1.card)
        · simp only [simState, simStep, hs_q, and_self, hτ_q, ↓reduceIte] at hlo ⊢
          exact ih q' hlo hq'_le
        · exfalso
          revert hlo
          simp only [simState, simStep, hs_q, and_self, hτ_q, ↓reduceIte]
          split_ifs <;> dsimp <;> omega
      · exfalso
        revert hlo
        simp only [simState, simStep, hs_q, ↓reduceIte]
        omega

private lemma simState_at_q0 (q : ℕ) (ans : Ans n T) :
    simState n t T TOf (simState n t T TOf q ans).2.1 ans =
      ((simState n t T TOf q ans).1, (simState n t T TOf q ans).2.1, 0) := by
  have h := simState_between_q0 n t T TOf q ans (simState n t T TOf q ans).2.1
    (le_refl _) (simState_q0_le n t T TOf q ans)
  simpa using h

private lemma simState_active_window (i q : ℕ) (ans : Ans n T) (hiq : i ≤ q)
    (hi : (simState n t T TOf i ans).2.1 = i)
    (hs_i : 1 ≤ t - (simState n t T TOf i ans).1.card ∧
      t - (simState n t T TOf i ans).1.card ≤ t) :
    (q ≤ i + TOfNat t TOf (t - (simState n t T TOf i ans).1.card) ∧
      simState n t T TOf q ans = ((simState n t T TOf i ans).1, i, q - i)) ∨
    (i + TOfNat t TOf (t - (simState n t T TOf i ans).1.card) <
      (simState n t T TOf q ans).2.1) := by
  induction q with
  | zero =>
    have : i = 0 := by omega
    subst this
    left
    refine ⟨by omega, ?_⟩
    have hadd := simState_q0_add_tau n t T TOf 0 ans
    exact Prod.ext rfl (Prod.ext hi (by dsimp; omega))
  | succ q ih =>
    rcases eq_or_lt_of_le hiq with rfl | hlt
    · left
      refine ⟨by omega, ?_⟩
      have hadd := simState_q0_add_tau n t T TOf (q + 1) ans
      exact Prod.ext rfl (Prod.ext hi (by dsimp; omega))
    · rcases ih (by omega) with ⟨hq_le, hst_q⟩ | hgt
      · rcases eq_or_lt_of_le hq_le with hq_eq | hq_lt
        · right
          simp only [simState, hst_q, simStep, hs_i, and_self, ↓reduceIte]
          have hτ : ¬ (q - i < TOfNat t TOf (t - (simState n t T TOf i ans).1.card)) := by omega
          simp only [hτ, ↓reduceIte]
          split_ifs <;> dsimp <;> omega
        · left
          refine ⟨by omega, ?_⟩
          simp only [simState, hst_q, simStep, hs_i, and_self, ↓reduceIte]
          have hτ : q - i < TOfNat t TOf (t - (simState n t T TOf i ans).1.card) := by omega
          simp only [hτ, ↓reduceIte]
          congr 2
          omega
      · right
        exact lt_of_lt_of_le hgt (simState_q0_mono n t T TOf q ans)

def maskF (f : Qubits n → Bool) (S : Finset (Qubits n)) (j : Qubits n) : Bool :=
  xor (f j) (decide (j ∈ S))

def slotActive (q : ℕ) (ans : Ans n T) (p : SlotIdx T t) : Prop :=
  let st_i := simState n t T TOf (p.1 : ℕ) ans
  (p.1 : ℕ) ≤ q ∧ st_i.2.1 = (p.1 : ℕ) ∧
    1 ≤ t - st_i.1.card ∧ t - st_i.1.card ≤ t ∧ (p.2 : ℕ) = t - st_i.1.card - 1

instance (q : ℕ) (ans : Ans n T) (p : SlotIdx T t) :
    Decidable (slotActive n t T TOf q ans p) := by
  unfold slotActive; infer_instance

def slotStep (q : ℕ) (ans : Ans n T) (p : SlotIdx T t) : Fin (TOf p.2 + 1) :=
  if slotActive n t T TOf q ans p then
    ⟨min (q - (p.1 : ℕ)) (TOf p.2), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  else 0

noncomputable def slotVec (f : Qubits n → Bool) (q : ℕ) (ans : Ans n T) (p : SlotIdx T t) :
    EuclideanSpace ℂ (SlotReg n wOf p) :=
  let st_i := simState n t T TOf (p.1 : ℕ) ans
  (AOf p.2).stateAt (xorOracle (maskF n f st_i.1)) (slotStep n t T TOf q ans p)

private lemma slotStep_of_ge (q : ℕ) (ans : Ans n T) (p : SlotIdx T t) (hq : q ≤ (p.1 : ℕ)) :
    slotStep n t T TOf q ans p = 0 := by
  unfold slotStep
  split_ifs
  · ext; simp [Nat.sub_eq_zero_of_le hq]
  · rfl

private lemma slotVec_of_ge (f : Qubits n → Bool) (q : ℕ) (ans : Ans n T) (p : SlotIdx T t)
    (hq : q ≤ (p.1 : ℕ)) :
    slotVec n t T wOf TOf AOf f q ans p =
      act ((AOf p.2).U 0 : Matrix _ _ ℂ) (AOf p.2).start := by
  simp only [slotVec, slotStep_of_ge n t T TOf q ans p hq, QueryAlg.stateAt, Fin.induction_zero]

private lemma slotVec_upd_ge (f : Qubits n → Bool) (q : ℕ) (ans : Ans n T)
    (i : Fin T) (hi : q ≤ (i : ℕ) + 1) (cb : Qubits n × Bool) (p : SlotIdx T t) :
    slotVec n t T wOf TOf AOf f q (Function.update ans i cb) p =
      slotVec n t T wOf TOf AOf f q ans p := by
  rcases le_or_gt q (p.1 : ℕ) with hge | hlt
  · rw [slotVec_of_ge n t T wOf TOf AOf f q _ p hge,
        slotVec_of_ge n t T wOf TOf AOf f q _ p hge]
  · have hst := simState_upd_ge n t T TOf (p.1 : ℕ) ans i (by omega) cb
    simp only [slotVec, slotStep, slotActive, hst]

private lemma slotStep_succ_of_not_active (q : ℕ) (ans : Ans n T) (p : SlotIdx T t)
    (hnot : ¬ ((p.1 : ℕ) = (simState n t T TOf q ans).2.1 ∧
      1 ≤ t - (simState n t T TOf q ans).1.card ∧
      t - (simState n t T TOf q ans).1.card ≤ t ∧
      (p.2 : ℕ) = t - (simState n t T TOf q ans).1.card - 1 ∧
      (simState n t T TOf q ans).2.2 < TOf p.2)) :
    slotStep n t T TOf (q + 1) ans p = slotStep n t T TOf q ans p := by
  rcases le_or_gt (q + 1) (p.1 : ℕ) with hge | hlt
  · rw [slotStep_of_ge n t T TOf (q + 1) ans p hge,
        slotStep_of_ge n t T TOf q ans p (by omega)]
  · have hp_le : (p.1 : ℕ) ≤ q := by omega
    have hact_iff : slotActive n t T TOf (q + 1) ans p ↔ slotActive n t T TOf q ans p := by
      simp only [slotActive]
      constructor <;> (rintro ⟨_, h2, h3, h4, h5⟩; exact ⟨by omega, h2, h3, h4, h5⟩)
    unfold slotStep
    by_cases hact : slotActive n t T TOf q ans p
    · have hact' : slotActive n t T TOf (q + 1) ans p := hact_iff.mpr hact
      rw [if_pos hact', if_pos hact]
      rcases hact with ⟨_, hi_q0, hs1, hs2, hp2⟩
      have hwin := simState_active_window n t T TOf (p.1 : ℕ) q ans hp_le hi_q0 ⟨hs1, hs2⟩
      have hTi : TOfNat t TOf (t - (simState n t T TOf (p.1 : ℕ) ans).1.card) = TOf p.2 :=
        TOfNat_eq t TOf _ ⟨hs1, hs2⟩ p.2 hp2
      rw [hTi] at hwin
      rcases hwin with ⟨hq_le, hst_q⟩ | hgt
      · have hτ_ge : TOf p.2 ≤ q - (p.1 : ℕ) := by
          by_contra hlt_τ
          apply hnot
          rw [hst_q]
          exact ⟨rfl, hs1, hs2, hp2, show q - (p.1 : ℕ) < TOf p.2 by omega⟩
        ext; simp; omega
      · have hq0_le := simState_q0_le n t T TOf q ans
        ext; simp; omega
    · have hact' : ¬ slotActive n t T TOf (q + 1) ans p := fun h => hact (hact_iff.mp h)
      rw [if_neg hact', if_neg hact]

private lemma slotVec_succ_of_not_active (f : Qubits n → Bool) (q : ℕ) (ans : Ans n T)
    (p : SlotIdx T t)
    (hnot : ¬ ((p.1 : ℕ) = (simState n t T TOf q ans).2.1 ∧
      1 ≤ t - (simState n t T TOf q ans).1.card ∧
      t - (simState n t T TOf q ans).1.card ≤ t ∧
      (p.2 : ℕ) = t - (simState n t T TOf q ans).1.card - 1 ∧
      (simState n t T TOf q ans).2.2 < TOf p.2)) :
    slotVec n t T wOf TOf AOf f (q + 1) ans p = slotVec n t T wOf TOf AOf f q ans p := by
  simp only [slotVec, slotStep_succ_of_not_active n t T TOf q ans p hnot]

private lemma slotVec_succ_active (f : Qubits n → Bool) (q : ℕ) (ans : Ans n T)
    (p : SlotIdx T t)
    (hp1 : (p.1 : ℕ) = (simState n t T TOf q ans).2.1)
    (hs : 1 ≤ t - (simState n t T TOf q ans).1.card ∧
      t - (simState n t T TOf q ans).1.card ≤ t)
    (hp2 : (p.2 : ℕ) = t - (simState n t T TOf q ans).1.card - 1)
    (hτ : (simState n t T TOf q ans).2.2 < TOf p.2) :
    slotVec n t T wOf TOf AOf f (q + 1) ans p =
      act ((AOf p.2).U (⟨(simState n t T TOf q ans).2.2, hτ⟩ : Fin (TOf p.2)).succ : Matrix _ _ ℂ)
        (act (Matrix.kronecker (xorOracle (maskF n f (simState n t T TOf q ans).1)) 1)
          (slotVec n t T wOf TOf AOf f q ans p)) := by
  have hat_q0 := simState_at_q0 n t T TOf q ans
  have hq0_add := simState_q0_add_tau n t T TOf q ans
  have hp_le : (p.1 : ℕ) ≤ q := by omega
  have hst_p1 : (simState n t T TOf (p.1 : ℕ) ans).1 = (simState n t T TOf q ans).1 := by
    rw [hp1, hat_q0]
  have hst_p21 : (simState n t T TOf (p.1 : ℕ) ans).2.1 = (p.1 : ℕ) := by
    rw [hp1, hat_q0]
  have hact_q : slotActive n t T TOf q ans p :=
    ⟨hp_le, hst_p21, by rw [hst_p1]; exact hs.1, by rw [hst_p1]; exact hs.2, by rw [hst_p1]; exact hp2⟩
  have hact_succ : slotActive n t T TOf (q + 1) ans p :=
    ⟨by omega, hst_p21, by rw [hst_p1]; exact hs.1, by rw [hst_p1]; exact hs.2, by rw [hst_p1]; exact hp2⟩
  have hstep_q : slotStep n t T TOf q ans p = (⟨(simState n t T TOf q ans).2.2, hτ⟩ : Fin (TOf p.2)).castSucc := by
    unfold slotStep
    rw [if_pos hact_q]
    ext
    simp; omega
  have hstep_succ : slotStep n t T TOf (q + 1) ans p = (⟨(simState n t T TOf q ans).2.2, hτ⟩ : Fin (TOf p.2)).succ := by
    unfold slotStep
    rw [if_pos hact_succ]
    ext
    simp; omega
  simp only [slotVec, hstep_q, hstep_succ, hst_p1]
  exact Fin.induction_succ _ _ (⟨(simState n t T TOf q ans).2.2, hτ⟩ : Fin (TOf p.2))

private lemma act_xorOracle_kronecker {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (g : α → Bool) (ψ : EuclideanSpace ℂ ((α × Bool) × β))
    (x : (α × Bool) × β) :
    act (Matrix.kronecker (xorOracle g) (1 : Matrix β β ℂ)) ψ x =
      ψ ((x.1.1, x.1.2 + g x.1.1), x.2) := by
  have h_eq : Matrix.kronecker (xorOracle g) (1 : Matrix β β ℂ) =
      involMat (fun y : (α × Bool) × β => ((y.1.1, y.1.2 + g y.1.1), y.2)) := by
    ext ⟨⟨j₁, y₁⟩, w₁⟩ ⟨⟨j₂, y₂⟩, w₂⟩
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, xorOracle, Matrix.of_apply,
      Matrix.one_apply, involMat, Prod.mk.injEq]
    by_cases hj : j₁ = j₂; swap; · simp [hj]
    by_cases hw : w₁ = w₂; swap; · simp [hw]
    subst hj hw
    cases y₁ <;> cases y₂ <;> cases g j₁ <;> simp
  rw [h_eq, act_involMat]
  intro ⟨⟨j, y⟩, w⟩
  dsimp only
  congr 2
  cases y <;> cases g j <;> rfl

private lemma act_const_mul {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℂ) (c : ℂ) (φ : EuclideanSpace ℂ α) (z₀ : α) :
    act M (WithLp.toLp 2 fun z => c * φ z) z₀ = c * act M φ z₀ := by
  simp only [act, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  ring

private lemma act_mul {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Matrix α α ℂ) (ψ : EuclideanSpace ℂ α) :
    act (A * B) ψ = act A (act B ψ) := by
  ext x
  simp [act, Matrix.mulVec_mulVec]

def activeSlotOfSt (st : Finset (Qubits n) × ℕ × ℕ) : Option (SlotIdx T t) :=
  let s := t - st.1.card
  if hs : 1 ≤ s ∧ s ≤ t then
    if st.2.2 < TOfNat t TOf s then
      if hq0 : st.2.1 < T then some (⟨st.2.1, hq0⟩, ⟨s - 1, by omega⟩) else none
    else none
  else none

def activeSlotAt (q : Fin T) (ans : Ans n T) : Option (SlotIdx T t) :=
  activeSlotOfSt n t T TOf (simState n t T TOf (q : ℕ) ans)

private lemma activeSlotAt_upd_ge (q : Fin T) (ans : Ans n T) (cb : Qubits n × Bool) :
    activeSlotAt n t T TOf q (Function.update ans q cb) = activeSlotAt n t T TOf q ans := by
  unfold activeSlotAt
  rw [simState_upd_ge n t T TOf (q : ℕ) ans q (le_refl _) cb]

private lemma candAt_upd_ge (q : Fin T) (ans : Ans n T) (pool : Pool n T t wOf)
    (cb : Qubits n × Bool) :
    candAt n t T wOf TOf outOf (q : ℕ) (Function.update ans q cb) pool =
      candAt n t T wOf TOf outOf (q : ℕ) ans pool := by
  unfold candAt
  rw [simState_upd_ge n t T TOf (q : ℕ) ans q (le_refl _) cb]

private lemma activeSlotAt_eq_some (q : Fin T) (ans : Ans n T) (p0 : SlotIdx T t)
    (h : activeSlotAt n t T TOf q ans = some p0) :
    (p0.1 : ℕ) = (simState n t T TOf (q : ℕ) ans).2.1 ∧
    (1 ≤ t - (simState n t T TOf (q : ℕ) ans).1.card ∧
      t - (simState n t T TOf (q : ℕ) ans).1.card ≤ t) ∧
    (p0.2 : ℕ) = t - (simState n t T TOf (q : ℕ) ans).1.card - 1 ∧
    (simState n t T TOf (q : ℕ) ans).2.2 < TOf p0.2 ∧
    (simState n t T TOf (q : ℕ) ans).2.2 <
      TOfNat t TOf (t - (simState n t T TOf (q : ℕ) ans).1.card) := by
  unfold activeSlotAt activeSlotOfSt at h
  dsimp only at h
  split_ifs at h with hs hτ hq0
  obtain ⟨hp1_eq, hp2_eq⟩ := Prod.mk.inj (Option.some.inj h).symm
  have hp1 : (p0.1 : ℕ) = (simState n t T TOf (q : ℕ) ans).2.1 := congr_arg Fin.val hp1_eq
  have hp2 : (p0.2 : ℕ) = t - (simState n t T TOf (q : ℕ) ans).1.card - 1 := congr_arg Fin.val hp2_eq
  have hT := TOfNat_eq t TOf _ hs p0.2 hp2
  exact ⟨hp1, hs, hp2, hT ▸ hτ, hτ⟩

private lemma activeSlotAt_eq_none (q : Fin T) (ans : Ans n T)
    (h : activeSlotAt n t T TOf q ans = none) :
    ¬ (1 ≤ t - (simState n t T TOf (q : ℕ) ans).1.card ∧
      t - (simState n t T TOf (q : ℕ) ans).1.card ≤ t ∧
      (simState n t T TOf (q : ℕ) ans).2.2 <
        TOfNat t TOf (t - (simState n t T TOf (q : ℕ) ans).1.card)) := by
  rintro ⟨hs1, hs2, hτ⟩
  have hs : 1 ≤ t - (simState n t T TOf (q : ℕ) ans).1.card ∧
      t - (simState n t T TOf (q : ℕ) ans).1.card ≤ t := ⟨hs1, hs2⟩
  have hq0_le := simState_q0_le n t T TOf (q : ℕ) ans
  have hq0 : (simState n t T TOf (q : ℕ) ans).2.1 < T := lt_of_le_of_lt hq0_le q.2
  unfold activeSlotAt activeSlotOfSt at h
  dsimp only at h
  rw [dif_pos hs, if_pos hτ, dif_pos hq0] at h
  nomatch h

def prePerm (q : Fin T) (x : FullState n T t wOf) : FullState n T t wOf :=
  match activeSlotAt n t T TOf q x.2.1 with
  | some p0 =>
      ((x.2.2 p0).1, (x.2.1, Function.update x.2.2 p0 (x.1, (x.2.2 p0).2)))
  | none =>
      let c := candAt n t T wOf TOf outOf (q : ℕ) x.2.1 x.2.2
      ((Equiv.swap 0 c x.1.1, x.1.2), x.2)

private lemma prePerm_invol (q : Fin T) (x : FullState n T t wOf) :
    prePerm n t T wOf TOf outOf q (prePerm n t T wOf TOf outOf q x) = x := by
  rcases x with ⟨⟨j, y⟩, ans, pool⟩
  unfold prePerm
  dsimp only
  cases hact : activeSlotAt n t T TOf q ans with
  | none =>
    dsimp only
    rw [hact]
    dsimp only
    rw [Equiv.swap_apply_self]
  | some p0 =>
    dsimp only
    rw [hact]
    dsimp only
    rw [Function.update_self, Function.update_idem, Prod.mk.eta, Function.update_eq_self]

def unmarkPerm (q : Fin T) (x : FullState n T t wOf) : FullState n T t wOf :=
  match activeSlotAt n t T TOf q x.2.1 with
  | some _ =>
      ((x.1.1, xor x.1.2 (decide (x.1.1 ∈ (simState n t T TOf (q : ℕ) x.2.1).1))), x.2)
  | none => x

private lemma unmarkPerm_invol (q : Fin T) (x : FullState n T t wOf) :
    unmarkPerm n t T wOf TOf q (unmarkPerm n t T wOf TOf q x) = x := by
  rcases x with ⟨⟨j, y⟩, ans, pool⟩
  unfold unmarkPerm
  dsimp only
  cases hact : activeSlotAt n t T TOf q ans with
  | none =>
    dsimp only
    rw [hact]
  | some p0 =>
    dsimp only
    rw [hact]
    dsimp only
    congr 2
    cases y <;> cases decide (j ∈ (simState n t T TOf (q : ℕ) ans).1) <;> rfl

def afterPerm (q : Fin T) (x : FullState n T t wOf) : FullState n T t wOf :=
  match activeSlotAt n t T TOf q x.2.1 with
  | some p0 =>
      ((x.2.2 p0).1, (x.2.1, Function.update x.2.2 p0 (x.1, (x.2.2 p0).2)))
  | none =>
      let c := candAt n t T wOf TOf outOf (q : ℕ) x.2.1 x.2.2
      let cb := x.2.1 q
      ((Equiv.swap 0 c x.1.1, cb.2),
        (Function.update x.2.1 q (Equiv.swap 0 c cb.1, x.1.2), x.2.2))

private lemma afterPerm_invol (q : Fin T) (x : FullState n T t wOf) :
    afterPerm n t T wOf TOf outOf q (afterPerm n t T wOf TOf outOf q x) = x := by
  rcases x with ⟨⟨j, y⟩, ans, pool⟩
  unfold afterPerm
  dsimp only
  cases hact : activeSlotAt n t T TOf q ans with
  | none =>
    dsimp only
    rw [activeSlotAt_upd_ge n t T TOf q ans _, hact]
    dsimp only
    rw [candAt_upd_ge n t T wOf TOf outOf q ans pool _, Function.update_self,
        Equiv.swap_apply_self, Equiv.swap_apply_self, Function.update_idem,
        Prod.mk.eta, Function.update_eq_self]
  | some p0 =>
    dsimp only
    rw [hact]
    dsimp only
    rw [Function.update_self, Function.update_idem, Prod.mk.eta, Function.update_eq_self]

noncomputable def stepSlotU (q : Fin T) (x : FullState n T t wOf) (p : SlotIdx T t) :
    Matrix.unitaryGroup (SlotReg n wOf p) ℂ :=
  let st := simState n t T TOf (q : ℕ) x.2.1
  if hτ : st.2.2 < TOf p.2 then
    (AOf p.2).U (⟨st.2.2, hτ⟩ : Fin (TOf p.2)).succ
  else 1

noncomputable def preMat (q : Fin T) : Matrix (FullState n T t wOf) (FullState n T t wOf) ℂ :=
  involMat (prePerm n t T wOf TOf outOf q)

private lemma preMat_mem_unitary (q : Fin T) :
    preMat n t T wOf TOf outOf q ∈ Matrix.unitaryGroup (FullState n T t wOf) ℂ :=
  involMat_mem_unitary _ (prePerm_invol n t T wOf TOf outOf q)

noncomputable def stepSlotMat (q : Fin T) : Matrix (FullState n T t wOf) (FullState n T t wOf) ℂ :=
  slotMat (fun x => activeSlotAt n t T TOf q x.2.1) (stepSlotU n t T wOf TOf AOf q)

private lemma stepSlotMat_mem_unitary (q : Fin T) :
    stepSlotMat n t T wOf TOf AOf q ∈ Matrix.unitaryGroup (FullState n T t wOf) ℂ :=
  slotMat_mem_unitary _ _ (fun _ _ _ h => h) (fun _ _ _ _ => rfl)

noncomputable def postMat (q : Fin T) : Matrix (FullState n T t wOf) (FullState n T t wOf) ℂ :=
  stepSlotMat n t T wOf TOf AOf q *
    involMat (afterPerm n t T wOf TOf outOf q) *
    involMat (unmarkPerm n t T wOf TOf q)

private lemma postMat_mem_unitary (q : Fin T) :
    postMat n t T wOf TOf AOf outOf q ∈ Matrix.unitaryGroup (FullState n T t wOf) ℂ := by
  refine Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ ?_) ?_
  · exact stepSlotMat_mem_unitary n t T wOf TOf AOf q
  · exact involMat_mem_unitary _ (afterPerm_invol n t T wOf TOf outOf q)
  · exact involMat_mem_unitary _ (unmarkPerm_invol n t T wOf TOf q)

noncomputable def simPsi (f : Qubits n → Bool) (q : ℕ) :
    EuclideanSpace ℂ (FullState n T t wOf) :=
  WithLp.toLp 2 fun x =>
    if x.1 = (0, false) ∧ x.2.1 = mkValidAns n t T wOf TOf outOf f q x.2.2 then
      ∏ p : SlotIdx T t, slotVec n t T wOf TOf AOf f q x.2.1 p (x.2.2 p)
    else 0

def oraclePerm (f : Qubits n → Bool) (x : FullState n T t wOf) : FullState n T t wOf :=
  ((x.1.1, x.1.2 + f x.1.1), x.2)

private lemma act_after_unmark_oracle_pre (f : Qubits n → Bool) (q : Fin T)
    (ψ : EuclideanSpace ℂ (FullState n T t wOf)) (x : FullState n T t wOf) :
    act (involMat (afterPerm n t T wOf TOf outOf q))
      (act (involMat (unmarkPerm n t T wOf TOf q))
        (act (Matrix.kronecker (xorOracle f)
          (1 : Matrix (Ans n T × Pool n T t wOf) (Ans n T × Pool n T t wOf) ℂ))
          (act (preMat n t T wOf TOf outOf q) ψ))) x =
      ψ (prePerm n t T wOf TOf outOf q
        (oraclePerm n t T wOf f
          (unmarkPerm n t T wOf TOf q
            (afterPerm n t T wOf TOf outOf q x)))) := by
  rw [act_involMat _ (afterPerm_invol n t T wOf TOf outOf q),
      act_involMat _ (unmarkPerm_invol n t T wOf TOf q),
      act_xorOracle_kronecker,
      preMat, act_involMat _ (prePerm_invol n t T wOf TOf outOf q)]
  rfl

private lemma compPerm_some (f : Qubits n → Bool) (q : Fin T) (x : FullState n T t wOf)
    (p0 : SlotIdx T t) (hact : activeSlotAt n t T TOf q x.2.1 = some p0)
    (z : SlotReg n wOf p0) :
    prePerm n t T wOf TOf outOf q
      (oraclePerm n t T wOf f
        (unmarkPerm n t T wOf TOf q
          (afterPerm n t T wOf TOf outOf q (updSlot x p0 z)))) =
      updSlot x p0
        ((z.1.1, z.1.2 + maskF n f (simState n t T TOf (q : ℕ) x.2.1).1 z.1.1), z.2) := by
  rcases x with ⟨⟨j, b⟩, ans, pool⟩
  rcases z with ⟨⟨zj, zb⟩, zw⟩
  dsimp only [updSlot] at hact ⊢
  unfold afterPerm unmarkPerm oraclePerm prePerm
  dsimp only
  rw [hact]
  dsimp only
  rw [hact]
  dsimp only
  rw [hact]
  dsimp only
  simp only [Function.update_self, Function.update_idem]
  have hbool : (xor zb (decide (zj ∈ (simState n t T TOf (q : ℕ) ans).1))) + f zj =
      zb + maskF n f (simState n t T TOf (q : ℕ) ans).1 zj := by
    unfold maskF
    cases zb <;> cases f zj <;> cases decide (zj ∈ (simState n t T TOf (q : ℕ) ans).1) <;> rfl
  rw [hbool]

private lemma compPerm_none (f : Qubits n → Bool) (q : Fin T) (x : FullState n T t wOf)
    (hact : activeSlotAt n t T TOf q x.2.1 = none) :
    let c := candAt n t T wOf TOf outOf (q : ℕ) x.2.1 x.2.2
    let cb := x.2.1 q
    prePerm n t T wOf TOf outOf q
      (oraclePerm n t T wOf f
        (unmarkPerm n t T wOf TOf q
          (afterPerm n t T wOf TOf outOf q x))) =
      ((x.1.1, cb.2 + f (Equiv.swap 0 c x.1.1)),
        (Function.update x.2.1 q (Equiv.swap 0 c cb.1, x.1.2), x.2.2)) := by
  rcases x with ⟨⟨j, b⟩, ans, pool⟩
  dsimp only at hact ⊢
  unfold afterPerm unmarkPerm oraclePerm prePerm
  dsimp only
  rw [hact]
  dsimp only
  rw [activeSlotAt_upd_ge n t T TOf q ans _, hact]
  dsimp only
  rw [activeSlotAt_upd_ge n t T TOf q ans _, hact]
  dsimp only
  rw [candAt_upd_ge n t T wOf TOf outOf q ans pool _, Equiv.swap_apply_self]

private lemma mkValidAns_upd_iff_of_active (f : Qubits n → Bool) (q : Fin T)
    (ans : Ans n T) (pool : Pool n T t wOf) (p0 : SlotIdx T t)
    (hp1 : (p0.1 : ℕ) = (simState n t T TOf (q : ℕ) ans).2.1)
    (z' : SlotReg n wOf p0) :
    ans = mkValidAns n t T wOf TOf outOf f (q : ℕ) (Function.update pool p0 z') ↔
      ans = mkValidAns n t T wOf TOf outOf f (q : ℕ) pool := by
  constructor <;> intro hans
  · have hle : (simState n t T TOf (q : ℕ)
        (mkValidAns n t T wOf TOf outOf f (q : ℕ) (Function.update pool p0 z'))).2.1 ≤ (p0.1 : ℕ) := by
      rw [← hans, hp1]
    have hupd := mkValidAns_upd_ge n t T wOf TOf outOf f (q : ℕ)
      (Function.update pool p0 z') p0 hle (pool p0)
    rw [Function.update_idem, Function.update_eq_self] at hupd
    rw [hans, ← hupd]
  · have hle : (simState n t T TOf (q : ℕ)
        (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)).2.1 ≤ (p0.1 : ℕ) := by
      rw [← hans, hp1]
    rw [mkValidAns_upd_ge n t T wOf TOf outOf f (q : ℕ) pool p0 hle z', ← hans]

private lemma mkValidAns_succ_iff_of_active (f : Qubits n → Bool) (q : Fin T)
    (ans : Ans n T) (pool : Pool n T t wOf) (p0 : SlotIdx T t)
    (hact : activeSlotAt n t T TOf q ans = some p0) :
    ans = mkValidAns n t T wOf TOf outOf f ((q : ℕ) + 1) pool ↔
      ans = mkValidAns n t T wOf TOf outOf f (q : ℕ) pool := by
  obtain ⟨_, hs, _, _, hτ_nat⟩ := activeSlotAt_eq_some n t T TOf q ans p0 hact
  have hcond : 1 ≤ t - (simState n t T TOf (q : ℕ) ans).1.card ∧
      t - (simState n t T TOf (q : ℕ) ans).1.card ≤ t ∧
      (simState n t T TOf (q : ℕ) ans).2.2 <
        TOfNat t TOf (t - (simState n t T TOf (q : ℕ) ans).1.card) := ⟨hs.1, hs.2, hτ_nat⟩
  constructor <;> intro hans
  · have hsim : simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) =
        simState n t T TOf (q : ℕ) ans := by
      rw [hans, simState_mkValidAns_step]
    have hexp : expectedAnsAt n t T wOf TOf outOf f
        (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) pool q = (0, false) := by
      unfold expectedAnsAt
      dsimp only
      rw [hsim, if_pos hcond]
    have hupd : mkValidAns n t T wOf TOf outOf f ((q : ℕ) + 1) pool =
        mkValidAns n t T wOf TOf outOf f (q : ℕ) pool := by
      simp only [mkValidAns, q.2, ↓reduceDIte, Fin.eta, hexp]
      exact Function.update_eq_self_iff.mpr
        (mkValidAns_ge n t T wOf TOf outOf f (q : ℕ) pool q (le_refl _)).symm
    rwa [← hupd]
  · have hexp : expectedAnsAt n t T wOf TOf outOf f ans pool q = (0, false) := by
      unfold expectedAnsAt
      dsimp only
      rw [if_pos hcond]
    simp only [mkValidAns, q.2, ↓reduceDIte, Fin.eta, ← hans, hexp]
    symm
    exact Function.update_eq_self_iff.mpr
      (by rw [hans]; exact (mkValidAns_ge n t T wOf TOf outOf f (q : ℕ) pool q (le_refl _)).symm)

private lemma valid_cond_iff_of_none (f : Qubits n → Bool) (q : Fin T)
    (j : Qubits n) (b : Bool) (ans : Ans n T) (pool : Pool n T t wOf)
    (hact : activeSlotAt n t T TOf q ans = none) :
    ((j, (ans q).2 + f (Equiv.swap 0 (candAt n t T wOf TOf outOf (q : ℕ) ans pool) j)) = (0, false) ∧
      Function.update ans q (Equiv.swap 0 (candAt n t T wOf TOf outOf (q : ℕ) ans pool) (ans q).1, b) =
        mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) ↔
    ((j, b) = (0, false) ∧
      ans = mkValidAns n t T wOf TOf outOf f ((q : ℕ) + 1) pool) := by
  have hnone := activeSlotAt_eq_none n t T TOf q ans hact
  have hexp_ans : expectedAnsAt n t T wOf TOf outOf f ans pool q =
      (candAt n t T wOf TOf outOf (q : ℕ) ans pool,
        f (candAt n t T wOf TOf outOf (q : ℕ) ans pool)) := by
    unfold expectedAnsAt
    dsimp only
    rw [if_neg hnone]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨rfl, hbool⟩ := Prod.mk.inj h1
    rw [Equiv.swap_apply_left] at hbool
    have hcb2 : (ans q).2 = f (candAt n t T wOf TOf outOf (q : ℕ) ans pool) := by
      revert hbool
      cases (ans q).2 <;> cases f (candAt n t T wOf TOf outOf (q : ℕ) ans pool) <;> decide
    have hq_eval := congr_fun h2 q
    rw [Function.update_self, mkValidAns_ge n t T wOf TOf outOf f (q : ℕ) pool q (le_refl _)] at hq_eval
    obtain ⟨hswap, rfl⟩ := Prod.mk.inj hq_eval
    have hcb1 : (ans q).1 = candAt n t T wOf TOf outOf (q : ℕ) ans pool := by
      have := congr_arg (Equiv.swap 0 (candAt n t T wOf TOf outOf (q : ℕ) ans pool)) hswap
      simpa [Equiv.swap_apply_self, Equiv.swap_apply_left] using this
    refine ⟨rfl, ?_⟩
    have hsim : simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) =
        simState n t T TOf (q : ℕ) ans := by
      rw [← h2, simState_upd_ge n t T TOf (q : ℕ) ans q (le_refl _)]
    have hexp_mk : expectedAnsAt n t T wOf TOf outOf f
        (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) pool q = ans q := by
      unfold expectedAnsAt candAt
      dsimp only
      rw [hsim]
      change expectedAnsAt n t T wOf TOf outOf f ans pool q = ans q
      rw [hexp_ans]
      exact Prod.ext hcb1.symm hcb2.symm
    rw [mkValidAns, dif_pos q.2, Fin.eta, hexp_mk, ← h2, Function.update_idem, Function.update_eq_self]
  · rintro ⟨h1, h2⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    have hsim : simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) =
        simState n t T TOf (q : ℕ) ans := by
      rw [h2, simState_mkValidAns_step]
    have hexp_mk : expectedAnsAt n t T wOf TOf outOf f
        (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) pool q =
        (candAt n t T wOf TOf outOf (q : ℕ) ans pool,
          f (candAt n t T wOf TOf outOf (q : ℕ) ans pool)) := by
      unfold expectedAnsAt candAt
      dsimp only
      rw [hsim]
      exact hexp_ans
    have hans_eq : ans = Function.update (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) q
        (candAt n t T wOf TOf outOf (q : ℕ) ans pool,
          f (candAt n t T wOf TOf outOf (q : ℕ) ans pool)) := by
      simpa [mkValidAns, q.2, ↓reduceDIte, Fin.eta, hexp_mk] using h2
    have hq_eval : ans q = (candAt n t T wOf TOf outOf (q : ℕ) ans pool,
        f (candAt n t T wOf TOf outOf (q : ℕ) ans pool)) := by
      conv_lhs => rw [hans_eq]
      rw [Function.update_self]
    rw [hq_eval]
    dsimp only
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
    have hxor : f (candAt n t T wOf TOf outOf (q : ℕ) ans pool) +
        f (candAt n t T wOf TOf outOf (q : ℕ) ans pool) = false := by
      cases f (candAt n t T wOf TOf outOf (q : ℕ) ans pool) <;> rfl
    refine ⟨Prod.ext rfl hxor, ?_⟩
    conv_lhs => rw [hans_eq]
    rw [Function.update_idem]
    exact Function.update_eq_self_iff.mpr
      (mkValidAns_ge n t T wOf TOf outOf f (q : ℕ) pool q (le_refl _)).symm

private lemma block_simPsi (f : Qubits n → Bool) (q : Fin T) :
    act (postMat n t T wOf TOf AOf outOf q)
      (act (Matrix.kronecker (xorOracle f)
        (1 : Matrix (Ans n T × Pool n T t wOf) (Ans n T × Pool n T t wOf) ℂ))
        (act (preMat n t T wOf TOf outOf q)
          (simPsi n t T wOf TOf AOf outOf f (q : ℕ)))) =
      simPsi n t T wOf TOf AOf outOf f ((q : ℕ) + 1) := by
  ext x
  rw [postMat, act_mul, act_mul, stepSlotMat, act_slotMat]
  cases hact : activeSlotAt n t T TOf q x.2.1 with
  | none =>
    dsimp only
    rw [act_after_unmark_oracle_pre, compPerm_none n t T wOf TOf outOf f q x hact]
    rcases x with ⟨⟨j, b⟩, ans, pool⟩
    dsimp only [simPsi, WithLp.ofLp_toLp]
    have hiff := valid_cond_iff_of_none n t T wOf TOf outOf f q j b ans pool hact
    by_cases hvalid : (j, b) = (0, false) ∧ ans = mkValidAns n t T wOf TOf outOf f ((q : ℕ) + 1) pool
    · rw [if_pos (hiff.mpr hvalid), if_pos hvalid]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [slotVec_upd_ge n t T wOf TOf AOf f (q : ℕ) ans q (Nat.le_succ _)]
      rw [slotVec_succ_of_not_active n t T wOf TOf AOf f (q : ℕ) ans p]
      rintro ⟨hp1, hs1, hs2, hp2, hτ⟩
      have hT := TOfNat_eq t TOf _ ⟨hs1, hs2⟩ p.2 hp2
      exact activeSlotAt_eq_none n t T TOf q ans hact ⟨hs1, hs2, hT.symm ▸ hτ⟩
    · rw [if_neg (mt hiff.mp hvalid), if_neg hvalid]
  | some p0 =>
    dsimp only
    have hfun : (fun z : SlotReg n wOf p0 =>
        act (involMat (afterPerm n t T wOf TOf outOf q))
          (act (involMat (unmarkPerm n t T wOf TOf q))
            (act (Matrix.kronecker (xorOracle f)
              (1 : Matrix (Ans n T × Pool n T t wOf) (Ans n T × Pool n T t wOf) ℂ))
              (act (preMat n t T wOf TOf outOf q)
                (simPsi n t T wOf TOf AOf outOf f (q : ℕ))))) (updSlot x p0 z)) =
        (fun z : SlotReg n wOf p0 =>
          simPsi n t T wOf TOf AOf outOf f (q : ℕ)
            (updSlot x p0
              ((z.1.1, z.1.2 + maskF n f (simState n t T TOf (q : ℕ) x.2.1).1 z.1.1), z.2))) := by
      ext z
      rw [act_after_unmark_oracle_pre, compPerm_some n t T wOf TOf outOf f q x p0 hact z]
    rw [hfun]
    rcases x with ⟨⟨j, b⟩, ans, pool⟩
    dsimp only at hact ⊢
    obtain ⟨hp1, hs, hp2, hτ, _⟩ := activeSlotAt_eq_some n t T TOf q ans p0 hact
    have hstepU : stepSlotU n t T wOf TOf AOf q ((j, b), (ans, pool)) p0 =
        (AOf p0.2).U (⟨(simState n t T TOf (q : ℕ) ans).2.2, hτ⟩ : Fin (TOf p0.2)).succ := by
      unfold stepSlotU
      dsimp only
      rw [dif_pos hτ]
    rw [hstepU]
    by_cases hvalid : (j, b) = (0, false) ∧
        ans = mkValidAns n t T wOf TOf outOf f ((q : ℕ) + 1) pool
    · have hvalid_q : (j, b) = (0, false) ∧
          ans = mkValidAns n t T wOf TOf outOf f (q : ℕ) pool :=
        ⟨hvalid.1, (mkValidAns_succ_iff_of_active n t T wOf TOf outOf f q ans pool p0 hact).mp hvalid.2⟩
      let C : ℂ := ∏ p ∈ Finset.univ.erase p0,
        slotVec n t T wOf TOf AOf f (q : ℕ) ans p (pool p)
      have hprod_z : (fun z : SlotReg n wOf p0 =>
          simPsi n t T wOf TOf AOf outOf f (q : ℕ)
            (updSlot ((j, b), (ans, pool)) p0
              ((z.1.1, z.1.2 + maskF n f (simState n t T TOf (q : ℕ) ans).1 z.1.1), z.2))) =
          (fun z : SlotReg n wOf p0 =>
            C * act (Matrix.kronecker (xorOracle (maskF n f (simState n t T TOf (q : ℕ) ans).1)) 1)
              (slotVec n t T wOf TOf AOf f (q : ℕ) ans p0) z) := by
        ext z
        dsimp only [simPsi, WithLp.ofLp_toLp, updSlot]
        have hcond_z : ((j, b) = (0, false) ∧
            ans = mkValidAns n t T wOf TOf outOf f (q : ℕ)
              (Function.update pool p0
                ((z.1.1, z.1.2 + maskF n f (simState n t T TOf (q : ℕ) ans).1 z.1.1), z.2))) :=
          ⟨hvalid_q.1, (mkValidAns_upd_iff_of_active n t T wOf TOf outOf f q ans pool p0 hp1 _).mpr hvalid_q.2⟩
        rw [if_pos hcond_z]
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p0), mul_comm]
        congr 1
        · refine Finset.prod_congr rfl fun p hp => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hp)]
        · rw [Function.update_self, act_xorOracle_kronecker]
      rw [hprod_z, act_const_mul, ← slotVec_succ_active n t T wOf TOf AOf f (q : ℕ) ans p0 hp1 hs hp2 hτ]
      dsimp only [simPsi, WithLp.ofLp_toLp]
      rw [if_pos hvalid]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p0), mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp_ne : p ≠ p0 := Finset.ne_of_mem_erase hp
      rw [slotVec_succ_of_not_active n t T wOf TOf AOf f (q : ℕ) ans p]
      rintro ⟨hp1', _, _, hp2', _⟩
      apply hp_ne
      ext
      · omega
      · omega
    · have hnot_q : ¬ ((j, b) = (0, false) ∧
          ans = mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) := by
        rintro ⟨h1, h2⟩
        exact hvalid ⟨h1, (mkValidAns_succ_iff_of_active n t T wOf TOf outOf f q ans pool p0 hact).mpr h2⟩
      have hzero_z : (fun z : SlotReg n wOf p0 =>
          simPsi n t T wOf TOf AOf outOf f (q : ℕ)
            (updSlot ((j, b), (ans, pool)) p0
              ((z.1.1, z.1.2 + maskF n f (simState n t T TOf (q : ℕ) ans).1 z.1.1), z.2))) = 0 := by
        ext z
        dsimp only [simPsi, WithLp.ofLp_toLp, updSlot, Pi.zero_apply]
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact hnot_q ⟨h1, (mkValidAns_upd_iff_of_active n t T wOf TOf outOf f q ans pool p0 hp1 _).mp h2⟩
      rw [hzero_z]
      have hzero_lp : (WithLp.toLp 2 (0 : SlotReg n wOf p0 → ℂ)) = 0 := rfl
      rw [hzero_lp]
      dsimp only [simPsi, WithLp.ofLp_toLp]
      rw [if_neg hvalid]
      simp [act]

noncomputable def simStart : EuclideanSpace ℂ (FullState n T t wOf) :=
  WithLp.toLp 2 fun x =>
    if x.1 = (0, false) ∧ x.2.1 = (fun _ => (0, false)) then
      ∏ p : SlotIdx T t, act ((AOf p.2).U 0 : Matrix _ _ ℂ) (AOf p.2).start (x.2.2 p)
    else 0

private lemma simStart_eq_simPsi_zero (f : Qubits n → Bool) :
    simStart n t T wOf TOf AOf = simPsi n t T wOf TOf AOf outOf f 0 := by
  ext x
  simp only [simStart, simPsi, mkValidAns, WithLp.ofLp_toLp]
  split_ifs with h
  · refine Finset.prod_congr rfl fun p _ => ?_
    rw [slotVec_of_ge n t T wOf TOf AOf f 0 x.2.1 p (Nat.zero_le _)]
  · rfl

private lemma simStart_unit : ‖simStart n t T wOf TOf AOf‖ = 1 := by
  let φ0 : ∀ p : SlotIdx T t, EuclideanSpace ℂ (SlotReg n wOf p) :=
    fun p => act ((AOf p.2).U 0 : Matrix _ _ ℂ) (AOf p.2).start
  have hφ0 : ∀ p : SlotIdx T t, ∑ z : SlotReg n wOf p, ‖φ0 p z‖ ^ 2 = 1 := by
    intro p
    rw [← PiLp.norm_sq_eq_of_L2]
    have hnorm := act_norm_of_mem_unitaryGroup ((AOf p.2).U 0).2 (AOf p.2).start
    rw [hnorm, (AOf p.2).start_unit, one_pow]
  have hsq : ‖simStart n t T wOf TOf AOf‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    change ∑ x : QReg n × (Ans n T × Pool n T t wOf), ‖(simStart n t T wOf TOf AOf).ofLp x‖ ^ 2 = 1
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single ((0 : Qubits n), false)]
    · rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single (fun _ : Fin T => ((0 : Qubits n), false))]
      · have hpool : (∑ pool : Pool n T t wOf,
            ‖(simStart n t T wOf TOf AOf).ofLp (((0, false), (fun _ => (0, false), pool)))‖ ^ 2) =
            ∑ pool : ∀ p : SlotIdx T t, SlotReg n wOf p, ∏ p : SlotIdx T t, ‖φ0 p (pool p)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun pool _ => ?_
          dsimp only [simStart, WithLp.ofLp_toLp]
          rw [if_pos ⟨rfl, rfl⟩, norm_prod, ← Finset.prod_pow]
        rw [hpool, ← Fintype.prod_sum (fun (p : SlotIdx T t) (z : SlotReg n wOf p) => ‖(φ0 p).ofLp z‖ ^ 2)]
        simp [hφ0]
      · intro ans _ hans
        refine Finset.sum_eq_zero fun pool _ => ?_
        dsimp only [simStart, WithLp.ofLp_toLp]
        rw [if_neg (fun h => hans h.2)]
        simp
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro qreg _ hqreg
      refine Finset.sum_eq_zero fun ap _ => ?_
      dsimp only [simStart, WithLp.ofLp_toLp]
      rw [if_neg (fun h => hqreg h.1)]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  have hnonneg : 0 ≤ ‖simStart n t T wOf TOf AOf‖ := norm_nonneg _
  rcases sq_eq_one_iff.mp hsq with h1 | h_neg
  · exact h1
  · linarith

noncomputable def simU (k : Fin (T + 1)) :
    Matrix.unitaryGroup (FullState n T t wOf) ℂ :=
  if h0 : (k : ℕ) = 0 then
    if hT : 0 < T then
      ⟨preMat n t T wOf TOf outOf ⟨0, hT⟩, preMat_mem_unitary n t T wOf TOf outOf ⟨0, hT⟩⟩
    else 1
  else
    let prev : Fin T := ⟨(k : ℕ) - 1, by omega⟩
    if hk : (k : ℕ) < T then
      ⟨preMat n t T wOf TOf outOf ⟨(k : ℕ), hk⟩ * postMat n t T wOf TOf AOf outOf prev,
        Submonoid.mul_mem _
          (preMat_mem_unitary n t T wOf TOf outOf ⟨(k : ℕ), hk⟩)
          (postMat_mem_unitary n t T wOf TOf AOf outOf prev)⟩
    else
      ⟨postMat n t T wOf TOf AOf outOf prev,
        postMat_mem_unitary n t T wOf TOf AOf outOf prev⟩

noncomputable def simAlg :
    QueryAlg (Qubits n) Bool (Ans n T × Pool n T t wOf) T where
  start := simStart n t T wOf TOf AOf
  start_unit := simStart_unit n t T wOf TOf AOf
  U := simU n t T wOf TOf AOf outOf

private lemma simU_zero :
    (simU n t T wOf TOf AOf outOf 0 : Matrix _ _ ℂ) =
      if hT : 0 < T then preMat n t T wOf TOf outOf ⟨0, hT⟩ else 1 := by
  unfold simU
  have h0 : ((0 : Fin (T + 1)) : ℕ) = 0 := rfl
  rw [dif_pos h0]
  split_ifs <;> rfl

private lemma simU_succ (i : Fin T) :
    (simU n t T wOf TOf AOf outOf i.succ : Matrix _ _ ℂ) =
      if hk : (i.succ : ℕ) < T then
        preMat n t T wOf TOf outOf ⟨(i.succ : ℕ), hk⟩ * postMat n t T wOf TOf AOf outOf i
      else
        postMat n t T wOf TOf AOf outOf i := by
  unfold simU
  have hne : ¬ ((i.succ : ℕ) = 0) := by simp
  rw [dif_neg hne]
  dsimp only
  have hprev : (⟨(i.succ : ℕ) - 1, by omega⟩ : Fin T) = i := by ext; simp
  split_ifs with hk <;> simp [hprev]

private lemma simAlg_stateAt (f : Qubits n → Bool) (k : Fin (T + 1)) :
    (simAlg n t T wOf TOf AOf outOf).stateAt (xorOracle f) k =
      if hk : (k : ℕ) < T then
        act (preMat n t T wOf TOf outOf ⟨(k : ℕ), hk⟩)
          (simPsi n t T wOf TOf AOf outOf f (k : ℕ))
      else
        simPsi n t T wOf TOf AOf outOf f (k : ℕ) := by
  induction k using Fin.induction with
  | zero =>
    dsimp only [QueryAlg.stateAt, Fin.induction_zero, simAlg]
    rw [simStart_eq_simPsi_zero n t T wOf TOf AOf outOf f, simU_zero]
    have h0 : ((0 : Fin (T + 1)) : ℕ) = 0 := rfl
    simp only [h0]
    split_ifs with hT
    · rfl
    · simp [act]
  | succ i ih =>
    have hi_lt : (i.castSucc : ℕ) < T := i.2
    rw [QueryAlg.stateAt, Fin.induction_succ, ← QueryAlg.stateAt, ih, dif_pos hi_lt]
    have hi_eta : (⟨(i.castSucc : ℕ), hi_lt⟩ : Fin T) = i := by ext; rfl
    rw [hi_eta]
    dsimp only [simAlg]
    rw [simU_succ, Fin.val_castSucc]
    split_ifs with hk
    · rw [act_mul, block_simPsi]
      rfl
    · rw [block_simPsi]
      rfl

private lemma simAlg_finalState (f : Qubits n → Bool) :
    (simAlg n t T wOf TOf AOf outOf).finalState (xorOracle f) =
      simPsi n t T wOf TOf AOf outOf f T := by
  unfold QueryAlg.finalState
  rw [simAlg_stateAt]
  simp

private lemma xorOracle_kronecker_mem_unitary {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (g : α → Bool) :
    Matrix.kronecker (xorOracle g) (1 : Matrix β β ℂ) ∈
      Matrix.unitaryGroup ((α × Bool) × β) ℂ := by
  have h_eq : Matrix.kronecker (xorOracle g) (1 : Matrix β β ℂ) =
      involMat (fun y : (α × Bool) × β => ((y.1.1, y.1.2 + g y.1.1), y.2)) := by
    ext ⟨⟨j₁, y₁⟩, w₁⟩ ⟨⟨j₂, y₂⟩, w₂⟩
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, xorOracle, Matrix.of_apply,
      Matrix.one_apply, involMat, Prod.mk.injEq]
    by_cases hj : j₁ = j₂; swap; · simp [hj]
    by_cases hw : w₁ = w₂; swap; · simp [hw]
    subst hj hw
    cases y₁ <;> cases y₂ <;> cases g j₁ <;> simp
  rw [h_eq]
  apply involMat_mem_unitary
  intro ⟨⟨j, y⟩, w⟩
  dsimp only
  congr 2
  cases y <;> cases g j <;> rfl

private lemma stateAt_xorOracle_norm {α W : Type*} [Fintype α] [DecidableEq α]
    [Fintype W] [DecidableEq W] {T' : ℕ} (A : QueryAlg α Bool W T')
    (g : α → Bool) (k : Fin (T' + 1)) :
    ‖A.stateAt (xorOracle g) k‖ = 1 := by
  induction k using Fin.induction with
  | zero =>
    dsimp only [QueryAlg.stateAt, Fin.induction_zero]
    rw [act_norm_of_mem_unitaryGroup (A.U 0).2, A.start_unit]
  | succ i ih =>
    rw [QueryAlg.stateAt, Fin.induction_succ, ← QueryAlg.stateAt]
    rw [act_norm_of_mem_unitaryGroup (A.U i.succ).2,
        act_norm_of_mem_unitaryGroup (xorOracle_kronecker_mem_unitary g), ih]

private lemma sum_slotVec_norm_sq (f : Qubits n → Bool) (q : ℕ) (ans : Ans n T)
    (p : SlotIdx T t) :
    ∑ z : SlotReg n wOf p, ‖slotVec n t T wOf TOf AOf f q ans p z‖ ^ 2 = 1 := by
  rw [← PiLp.norm_sq_eq_of_L2]
  unfold slotVec
  dsimp only
  rw [stateAt_xorOracle_norm, one_pow]

noncomputable def poolWeight (f : Qubits n → Bool) (q : ℕ) (pool : Pool n T t wOf) : ℝ :=
  ∏ p : SlotIdx T t,
    ‖slotVec n t T wOf TOf AOf f q (mkValidAns n t T wOf TOf outOf f q pool) p (pool p)‖ ^ 2

private lemma poolWeight_nonneg (f : Qubits n → Bool) (q : ℕ) (pool : Pool n T t wOf) :
    0 ≤ poolWeight n t T wOf TOf AOf outOf f q pool :=
  Finset.prod_nonneg fun _ _ => sq_nonneg _

private lemma simPsi_norm_sq (f : Qubits n → Bool) (q : ℕ) :
    ‖simPsi n t T wOf TOf AOf outOf f q‖ ^ 2 =
      ∑ pool : Pool n T t wOf, poolWeight n t T wOf TOf AOf outOf f q pool := by
  rw [PiLp.norm_sq_eq_of_L2]
  change ∑ x : QReg n × (Ans n T × Pool n T t wOf),
    ‖(simPsi n t T wOf TOf AOf outOf f q).ofLp x‖ ^ 2 = _
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single ((0 : Qubits n), false)]
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun pool _ => ?_
    rw [Finset.sum_eq_single (mkValidAns n t T wOf TOf outOf f q pool)]
    · dsimp only [simPsi, WithLp.ofLp_toLp, poolWeight]
      rw [if_pos ⟨rfl, rfl⟩, norm_prod, ← Finset.prod_pow]
    · intro ans _ hans
      dsimp only [simPsi, WithLp.ofLp_toLp]
      rw [if_neg (fun h => hans h.2)]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro qreg _ hqreg
    refine Finset.sum_eq_zero fun ap _ => ?_
    dsimp only [simPsi, WithLp.ofLp_toLp]
    rw [if_neg (fun h => hqreg h.1)]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma sum_poolWeight_eq_one (f : Qubits n → Bool) (q : ℕ) (hq : q ≤ T) :
    ∑ pool : Pool n T t wOf, poolWeight n t T wOf TOf AOf outOf f q pool = 1 := by
  rw [← simPsi_norm_sq]
  have hstate := simAlg_stateAt n t T wOf TOf AOf outOf f ⟨q, Nat.lt_succ_of_le hq⟩
  have hnorm := stateAt_xorOracle_norm (simAlg n t T wOf TOf AOf outOf) f ⟨q, Nat.lt_succ_of_le hq⟩
  rw [hstate] at hnorm
  dsimp only at hnorm
  split_ifs at hnorm with hlt
  · rw [act_norm_of_mem_unitaryGroup (preMat_mem_unitary n t T wOf TOf outOf ⟨q, hlt⟩)] at hnorm
    rw [hnorm, one_pow]
  · rw [hnorm, one_pow]

private lemma probEvent_simPsi (f : Qubits n → Bool) (q : ℕ) (P : Ans n T → Prop)
    [DecidablePred P] :
    probEvent (simPsi n t T wOf TOf AOf outOf f q) (fun x => P x.2.1) =
      ∑ pool : Pool n T t wOf,
        (if P (mkValidAns n t T wOf TOf outOf f q pool) then 1 else 0) *
          poolWeight n t T wOf TOf AOf outOf f q pool := by
  unfold probEvent prob
  simp only [ket, EuclideanSpace.inner_single_left, one_mul, starRingEnd_apply, star_one]
  rw [Finset.sum_filter]
  change ∑ x : QReg n × (Ans n T × Pool n T t wOf),
    (if P x.2.1 then ‖(simPsi n t T wOf TOf AOf outOf f q).ofLp x‖ ^ 2 else 0) = _
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single ((0 : Qubits n), false)]
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun pool _ => ?_
    rw [Finset.sum_eq_single (mkValidAns n t T wOf TOf outOf f q pool)]
    · dsimp only [simPsi, WithLp.ofLp_toLp, poolWeight]
      by_cases hP : P (mkValidAns n t T wOf TOf outOf f q pool)
      · rw [if_pos hP, if_pos ⟨rfl, rfl⟩, if_pos hP, one_mul, norm_prod, ← Finset.prod_pow]
      · rw [if_neg hP, if_neg hP, zero_mul]
    · intro ans _ hans
      dsimp only [simPsi, WithLp.ofLp_toLp]
      by_cases hP : P ans
      · rw [if_pos hP, if_neg (fun h => hans h.2)]
        simp
      · rw [if_neg hP]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro qreg _ hqreg
    refine Finset.sum_eq_zero fun ap _ => ?_
    dsimp only [simPsi, WithLp.ofLp_toLp]
    by_cases hP : P ap.1
    · rw [if_pos hP, if_neg (fun h => hqreg h.1)]
      simp
    · rw [if_neg hP]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma simState_sub_marked (f : Qubits n → Bool) (q : ℕ) (pool : Pool n T t wOf) :
    (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool)).1 ⊆
      Finset.univ.filter (fun j => f j = true) := by
  induction q with
  | zero => exact Finset.empty_subset _
  | succ q ih =>
    rw [simState, simState_mkValidAns_step]
    unfold simStep
    dsimp only
    by_cases hs : 1 ≤ t - (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool)).1.card ∧
        t - (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool)).1.card ≤ t
    · rw [if_pos hs]
      by_cases hτ : (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool)).2.2 <
          TOfNat t TOf (t - (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool)).1.card)
      · rw [if_pos hτ]; exact ih
      · rw [if_neg hτ]
        by_cases hq : q < T
        · rw [dif_pos hq]
          by_cases hnew : ((mkValidAns n t T wOf TOf outOf f (q + 1) pool ⟨q, hq⟩).2 &&
              decide ((mkValidAns n t T wOf TOf outOf f (q + 1) pool ⟨q, hq⟩).1 ∉
                (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool)).1)) = true
          · rw [if_pos hnew]
            dsimp only
            intro j hj
            rcases Finset.mem_insert.mp hj with rfl | hjS
            · simp only [Bool.and_eq_true, decide_eq_true_eq] at hnew
              have hcb : mkValidAns n t T wOf TOf outOf f (q + 1) pool ⟨q, hq⟩ =
                  expectedAnsAt n t T wOf TOf outOf f (mkValidAns n t T wOf TOf outOf f q pool) pool ⟨q, hq⟩ := by
                simp [mkValidAns, hq]
              have hexp : expectedAnsAt n t T wOf TOf outOf f (mkValidAns n t T wOf TOf outOf f q pool) pool ⟨q, hq⟩ =
                  (candAt n t T wOf TOf outOf q (mkValidAns n t T wOf TOf outOf f q pool) pool,
                    f (candAt n t T wOf TOf outOf q (mkValidAns n t T wOf TOf outOf f q pool) pool)) := by
                unfold expectedAnsAt
                dsimp only
                rw [if_neg (fun h => hτ h.2.2)]
              rw [hcb, hexp] at hnew ⊢
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnew.1⟩
            · exact ih hjS
          · rw [if_neg hnew]; exact ih
        · rw [dif_neg hq]; exact ih
    · rw [if_neg hs]; exact ih

private lemma sum_pool_swap (p0 : SlotIdx T t)
    (A B : Pool n T t wOf → SlotReg n wOf p0 → ℝ)
    (hA : ∀ pool z, A (Function.update pool p0 z) = A pool)
    (hB : ∀ pool z, B (Function.update pool p0 z) = B pool) :
    (∑ pool : Pool n T t wOf, A pool (pool p0) * (∑ z : SlotReg n wOf p0, B pool z)) =
      ∑ pool : Pool n T t wOf, B pool (pool p0) * (∑ z : SlotReg n wOf p0, A pool z) := by
  simp only [Finset.mul_sum]
  rw [← Fintype.sum_prod_type (f := fun pz : Pool n T t wOf × SlotReg n wOf p0 => A pz.1 (pz.1 p0) * B pz.1 pz.2),
      ← Fintype.sum_prod_type (f := fun pz : Pool n T t wOf × SlotReg n wOf p0 => B pz.1 (pz.1 p0) * A pz.1 pz.2)]
  let e : (Pool n T t wOf × SlotReg n wOf p0) ≃ (Pool n T t wOf × SlotReg n wOf p0) :=
    { toFun := fun pz => (Function.update pz.1 p0 pz.2, pz.1 p0)
      invFun := fun pz => (Function.update pz.1 p0 pz.2, pz.1 p0)
      left_inv := fun ⟨pool, z⟩ => by
        dsimp only
        rw [Function.update_idem, Function.update_eq_self, Function.update_self]
      right_inv := fun ⟨pool, z⟩ => by
        dsimp only
        rw [Function.update_idem, Function.update_eq_self, Function.update_self] }
  refine Fintype.sum_equiv e _ _ fun ⟨pool, z⟩ => ?_
  dsimp only [e, Equiv.coe_fn_mk]
  rw [hA pool z, hB pool z, Function.update_self, mul_comm]

def stageSlotOfSt (st : Finset (Qubits n) × ℕ × ℕ) : Option (SlotIdx T t) :=
  let s := t - st.1.card
  if hs : 1 ≤ s ∧ s ≤ t then
    if hq0 : st.2.1 < T then some (⟨st.2.1, hq0⟩, ⟨s - 1, by omega⟩) else none
  else none

def stageSlotAt (q : Fin T) (ans : Ans n T) : Option (SlotIdx T t) :=
  stageSlotOfSt n t T (simState n t T TOf (q : ℕ) ans)

private lemma stageSlotAt_eq_some (q : Fin T) (ans : Ans n T) (p0 : SlotIdx T t)
    (h : stageSlotAt n t T TOf q ans = some p0) :
    (p0.1 : ℕ) = (simState n t T TOf (q : ℕ) ans).2.1 ∧
    (1 ≤ t - (simState n t T TOf (q : ℕ) ans).1.card ∧
      t - (simState n t T TOf (q : ℕ) ans).1.card ≤ t) ∧
    (p0.2 : ℕ) = t - (simState n t T TOf (q : ℕ) ans).1.card - 1 := by
  unfold stageSlotAt stageSlotOfSt at h
  dsimp only at h
  split_ifs at h with hs hq0
  obtain ⟨hp1_eq, hp2_eq⟩ := Prod.mk.inj (Option.some.inj h).symm
  exact ⟨congr_arg Fin.val hp1_eq, hs, congr_arg Fin.val hp2_eq⟩

private lemma stageSlotAt_eq_none (q : Fin T) (ans : Ans n T)
    (h : stageSlotAt n t T TOf q ans = none) :
    t - (simState n t T TOf (q : ℕ) ans).1.card = 0 := by
  by_contra hne
  have hs : 1 ≤ t - (simState n t T TOf (q : ℕ) ans).1.card ∧
      t - (simState n t T TOf (q : ℕ) ans).1.card ≤ t := ⟨by omega, by omega⟩
  have hq0_le := simState_q0_le n t T TOf (q : ℕ) ans
  have hq0 : (simState n t T TOf (q : ℕ) ans).2.1 < T := lt_of_le_of_lt hq0_le q.2
  unfold stageSlotAt stageSlotOfSt at h
  dsimp only at h
  rw [dif_pos hs, dif_pos hq0] at h
  nomatch h

private lemma stageSlotAt_upd_iff (f : Qubits n → Bool) (q : Fin T)
    (pool : Pool n T t wOf) (p0 : SlotIdx T t) (z : SlotReg n wOf p0) :
    stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) (Function.update pool p0 z)) = some p0 ↔
      stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0 := by
  constructor <;> intro h
  · obtain ⟨hp1, _, _⟩ := stageSlotAt_eq_some n t T TOf q _ p0 h
    have hupd := mkValidAns_upd_ge n t T wOf TOf outOf f (q : ℕ)
      (Function.update pool p0 z) p0 (by omega) (pool p0)
    rw [Function.update_idem, Function.update_eq_self] at hupd
    rwa [hupd]
  · obtain ⟨hp1, _, _⟩ := stageSlotAt_eq_some n t T TOf q _ p0 h
    rw [mkValidAns_upd_ge n t T wOf TOf outOf f (q : ℕ) pool p0 (by omega) z]
    exact h

noncomputable def poolWeightErase (f : Qubits n → Bool) (q : ℕ) (pool : Pool n T t wOf)
    (p0 : SlotIdx T t) : ℝ :=
  ∏ p ∈ Finset.univ.erase p0,
    ‖slotVec n t T wOf TOf AOf f q (mkValidAns n t T wOf TOf outOf f q pool) p (pool p)‖ ^ 2

private lemma poolWeight_eq_mul_erase (f : Qubits n → Bool) (q : ℕ) (pool : Pool n T t wOf)
    (p0 : SlotIdx T t) :
    poolWeight n t T wOf TOf AOf outOf f q pool =
      ‖slotVec n t T wOf TOf AOf f q (mkValidAns n t T wOf TOf outOf f q pool) p0 (pool p0)‖ ^ 2 *
        poolWeightErase n t T wOf TOf AOf outOf f q pool p0 :=
  (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p0)).symm

private lemma poolWeightErase_upd_of_stageSlot (f : Qubits n → Bool) (q : Fin T)
    (pool : Pool n T t wOf) (p0 : SlotIdx T t)
    (h : stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0)
    (z : SlotReg n wOf p0) :
    poolWeightErase n t T wOf TOf AOf outOf f (q : ℕ) (Function.update pool p0 z) p0 =
      poolWeightErase n t T wOf TOf AOf outOf f (q : ℕ) pool p0 := by
  obtain ⟨hp1, _, _⟩ := stageSlotAt_eq_some n t T TOf q _ p0 h
  unfold poolWeightErase
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [mkValidAns_upd_ge n t T wOf TOf outOf f (q : ℕ) pool p0 (by omega) z,
      Function.update_of_ne (Finset.ne_of_mem_erase hp)]

private lemma slotVec_mkValidAns_succ (f : Qubits n → Bool) (q : ℕ) (pool : Pool n T t wOf)
    (p : SlotIdx T t) :
    slotVec n t T wOf TOf AOf f (q + 1) (mkValidAns n t T wOf TOf outOf f (q + 1) pool) p =
      slotVec n t T wOf TOf AOf f (q + 1) (mkValidAns n t T wOf TOf outOf f q pool) p := by
  simp only [mkValidAns]
  split_ifs with hq
  · exact slotVec_upd_ge n t T wOf TOf AOf f (q + 1) _ ⟨q, hq⟩ (le_refl _) _ p
  · rfl

private lemma poolWeightErase_succ_of_stageSlot (f : Qubits n → Bool) (q : Fin T)
    (pool : Pool n T t wOf) (p0 : SlotIdx T t)
    (h : stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0) :
    poolWeightErase n t T wOf TOf AOf outOf f ((q : ℕ) + 1) pool p0 =
      poolWeightErase n t T wOf TOf AOf outOf f (q : ℕ) pool p0 := by
  obtain ⟨hp1, _, hp2⟩ := stageSlotAt_eq_some n t T TOf q _ p0 h
  unfold poolWeightErase
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp_ne : p ≠ p0 := Finset.ne_of_mem_erase hp
  rw [slotVec_mkValidAns_succ, slotVec_succ_of_not_active]
  rintro ⟨hp1', _, _, hp2', _⟩
  apply hp_ne
  ext <;> omega

private lemma sum_stageSlot_some_expect (f : Qubits n → Bool) (q : Fin T) (p0 : SlotIdx T t)
    (q' : ℕ) (G : Ans n T → SlotReg n wOf p0 → ℝ) :
    (∑ pool : Pool n T t wOf,
      if stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0 then
        G (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) (pool p0) *
          ‖slotVec n t T wOf TOf AOf f q' (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) p0 (pool p0)‖ ^ 2 *
          poolWeightErase n t T wOf TOf AOf outOf f (q : ℕ) pool p0
      else 0) =
    ∑ pool : Pool n T t wOf,
      if stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0 then
        (∑ z : SlotReg n wOf p0,
          G (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) z *
            ‖slotVec n t T wOf TOf AOf f q' (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) p0 z‖ ^ 2) *
          poolWeight n t T wOf TOf AOf outOf f (q : ℕ) pool
      else 0 := by
  let A : Pool n T t wOf → SlotReg n wOf p0 → ℝ := fun pool z =>
    if stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0 then
      G (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) z *
        ‖slotVec n t T wOf TOf AOf f q' (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) p0 z‖ ^ 2 *
        poolWeightErase n t T wOf TOf AOf outOf f (q : ℕ) pool p0
    else 0
  let B : Pool n T t wOf → SlotReg n wOf p0 → ℝ := fun pool z =>
    if stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0 then
      ‖slotVec n t T wOf TOf AOf f (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) p0 z‖ ^ 2
    else 0
  have hA : ∀ pool z, A (Function.update pool p0 z) = A pool := by
    intro pool z
    ext z'
    dsimp only [A]
    by_cases h : stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0
    · have h' := (stageSlotAt_upd_iff n t T wOf TOf outOf f q pool p0 z).mpr h
      obtain ⟨hp1, _, _⟩ := stageSlotAt_eq_some n t T TOf q _ p0 h
      rw [if_pos h', if_pos h,
          mkValidAns_upd_ge n t T wOf TOf outOf f (q : ℕ) pool p0 (by omega) z,
          poolWeightErase_upd_of_stageSlot n t T wOf TOf AOf outOf f q pool p0 h z]
    · have h' := mt (stageSlotAt_upd_iff n t T wOf TOf outOf f q pool p0 z).mp h
      rw [if_neg h', if_neg h]
  have hB : ∀ pool z, B (Function.update pool p0 z) = B pool := by
    intro pool z
    ext z'
    dsimp only [B]
    by_cases h : stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0
    · have h' := (stageSlotAt_upd_iff n t T wOf TOf outOf f q pool p0 z).mpr h
      obtain ⟨hp1, _, _⟩ := stageSlotAt_eq_some n t T TOf q _ p0 h
      rw [if_pos h', if_pos h,
          mkValidAns_upd_ge n t T wOf TOf outOf f (q : ℕ) pool p0 (by omega) z]
    · have h' := mt (stageSlotAt_upd_iff n t T wOf TOf outOf f q pool p0 z).mp h
      rw [if_neg h', if_neg h]
  have hswap := sum_pool_swap n t T wOf p0 A B hA hB
  have hlhs : (∑ pool : Pool n T t wOf, A pool (pool p0) * (∑ z : SlotReg n wOf p0, B pool z)) =
      ∑ pool : Pool n T t wOf, A pool (pool p0) := by
    refine Finset.sum_congr rfl fun pool _ => ?_
    dsimp only [A, B]
    split_ifs with h
    · rw [sum_slotVec_norm_sq, mul_one]
    · ring
  have hrhs : (∑ pool : Pool n T t wOf, B pool (pool p0) * (∑ z : SlotReg n wOf p0, A pool z)) =
      ∑ pool : Pool n T t wOf,
        if stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0 then
          (∑ z : SlotReg n wOf p0,
            G (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) z *
              ‖slotVec n t T wOf TOf AOf f q' (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) p0 z‖ ^ 2) *
            poolWeight n t T wOf TOf AOf outOf f (q : ℕ) pool
        else 0 := by
    refine Finset.sum_congr rfl fun pool _ => ?_
    dsimp only [A, B]
    split_ifs with h
    · rw [← Finset.sum_mul, poolWeight_eq_mul_erase _ _ _ _ _ _ _ _ _ _ p0]
      ring
    · ring
  rw [← hlhs, hswap, hrhs]

private lemma sum_stageSlot_some_succ (f : Qubits n → Bool) (q : Fin T) (p0 : SlotIdx T t)
    (G : Ans n T → SlotReg n wOf p0 → ℝ) :
    (∑ pool : Pool n T t wOf,
      if stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0 then
        G (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) (pool p0) *
          poolWeight n t T wOf TOf AOf outOf f ((q : ℕ) + 1) pool
      else 0) =
    ∑ pool : Pool n T t wOf,
      if stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0 then
        (∑ z : SlotReg n wOf p0,
          G (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) z *
            ‖slotVec n t T wOf TOf AOf f ((q : ℕ) + 1) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) p0 z‖ ^ 2) *
          poolWeight n t T wOf TOf AOf outOf f (q : ℕ) pool
      else 0 := by
  have h1 : (∑ pool : Pool n T t wOf,
      if stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0 then
        G (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) (pool p0) *
          poolWeight n t T wOf TOf AOf outOf f ((q : ℕ) + 1) pool
      else 0) =
    ∑ pool : Pool n T t wOf,
      if stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0 then
        G (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) (pool p0) *
          ‖slotVec n t T wOf TOf AOf f ((q : ℕ) + 1) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) p0 (pool p0)‖ ^ 2 *
          poolWeightErase n t T wOf TOf AOf outOf f (q : ℕ) pool p0
      else 0 := by
    refine Finset.sum_congr rfl fun pool _ => ?_
    split_ifs with h
    · rw [poolWeight_eq_mul_erase _ _ _ _ _ _ _ _ _ _ p0,
          slotVec_mkValidAns_succ,
          poolWeightErase_succ_of_stageSlot n t T wOf TOf AOf outOf f q pool p0 h,
          mul_assoc]
    · rfl
  rw [h1, sum_stageSlot_some_expect]

noncomputable def stageCost (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m,
    if hi : i < t then 3 * ((TOf ⟨i, hi⟩ : ℝ) + 1) else 0

private lemma stageCost_zero : stageCost t TOf 0 = 0 := by
  simp [stageCost]

private lemma stageCost_nonneg (m : ℕ) : 0 ≤ stageCost t TOf m :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> positivity

private lemma stageCost_sub_one (s : ℕ) (hs : 1 ≤ s ∧ s ≤ t) :
    stageCost t TOf (s - 1) =
      stageCost t TOf s - 3 * ((TOf ⟨s - 1, by omega⟩ : ℝ) + 1) := by
  rcases s with _ | m
  · omega
  · unfold stageCost
    simp only [Nat.add_sub_cancel, Finset.sum_range_succ, dif_pos (show m < t by omega)]
    ring

private lemma stageCost_ge_of_pos (s : ℕ) (hs : 1 ≤ s ∧ s ≤ t) (τ : ℕ)
    (hτ : τ ≤ TOf ⟨s - 1, by omega⟩) :
    0 ≤ stageCost t TOf s - (τ : ℝ) := by
  have h1 := stageCost_sub_one t TOf s hs
  have h2 := stageCost_nonneg t TOf (s - 1)
  have h3 : (τ : ℝ) ≤ (TOf ⟨s - 1, by omega⟩ : ℝ) := Nat.cast_le.mpr hτ
  linarith

noncomputable def phiOfSt (st : Finset (Qubits n) × ℕ × ℕ) : ℝ :=
  if t - st.1.card = 0 then 0
  else stageCost t TOf (t - st.1.card) - (st.2.2 : ℝ)

def notDoneOfSt (st : Finset (Qubits n) × ℕ × ℕ) : ℝ :=
  if t - st.1.card = 0 then 0 else 1

private lemma phiOfSt_nonneg (q : ℕ) (ans : Ans n T) :
    0 ≤ phiOfSt n t TOf (simState n t T TOf q ans) := by
  unfold phiOfSt
  split_ifs with h0
  · exact le_rfl
  · have hs : 1 ≤ t - (simState n t T TOf q ans).1.card ∧
        t - (simState n t T TOf q ans).1.card ≤ t := ⟨by omega, by omega⟩
    have hτ := simState_tau_le n t T TOf q ans
    unfold TOfNat at hτ
    rw [dif_pos hs] at hτ
    exact stageCost_ge_of_pos t TOf _ hs _ hτ

private lemma of_stageSlotAt_none (f : Qubits n → Bool) (q : Fin T) (pool : Pool n T t wOf)
    (h : stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = none) :
    phiOfSt n t TOf (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)) = 0 ∧
    notDoneOfSt n t (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)) = 0 ∧
    phiOfSt n t TOf (simState n t T TOf ((q : ℕ) + 1) (mkValidAns n t T wOf TOf outOf f ((q : ℕ) + 1) pool)) = 0 ∧
    notDoneOfSt n t (simState n t T TOf ((q : ℕ) + 1) (mkValidAns n t T wOf TOf outOf f ((q : ℕ) + 1) pool)) = 0 := by
  have h0 : t - (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)).1.card = 0 :=
    stageSlotAt_eq_none n t T TOf q _ h
  have hs : ¬ (1 ≤ t - (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)).1.card ∧
      t - (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)).1.card ≤ t) := by
    omega
  have hstep : (simState n t T TOf ((q : ℕ) + 1) (mkValidAns n t T wOf TOf outOf f ((q : ℕ) + 1) pool)).1 =
      (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)).1 := by
    rw [simState, simState_mkValidAns_step]
    unfold simStep
    dsimp only
    rw [if_neg hs]
  have h0' : t - (simState n t T TOf ((q : ℕ) + 1) (mkValidAns n t T wOf TOf outOf f ((q : ℕ) + 1) pool)).1.card = 0 := by
    rw [hstep, h0]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [phiOfSt, notDoneOfSt, h0, h0']

private lemma sum_pool_partition_option (q : Fin T) (f : Qubits n → Bool)
    (F : Pool n T t wOf → ℝ) :
    ∑ pool : Pool n T t wOf, F pool =
      (∑ pool : Pool n T t wOf,
        if stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = none then
          F pool
        else 0) +
      ∑ p0 : SlotIdx T t, ∑ pool : Pool n T t wOf,
        if stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0 then
          F pool
        else 0 := by
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun pool _ => ?_
  cases h : stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) with
  | none => simp
  | some p0 =>
    rw [if_neg (by simp), zero_add, Finset.sum_eq_single p0]
    · simp
    · intro p _ hp
      simp [Ne.symm hp]
    · intro hp; exact absurd (Finset.mem_univ _) hp

noncomputable def failProb (f : Qubits n → Bool) (q : ℕ) : ℝ :=
  ∑ pool : Pool n T t wOf,
    notDoneOfSt n t (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool)) *
      poolWeight n t T wOf TOf AOf outOf f q pool

private lemma notDoneOfSt_succ_le (f : Qubits n → Bool) (q : ℕ) (pool : Pool n T t wOf) :
    notDoneOfSt n t (simState n t T TOf (q + 1) (mkValidAns n t T wOf TOf outOf f (q + 1) pool)) ≤
      notDoneOfSt n t (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool)) := by
  unfold notDoneOfSt
  by_cases h0 : t - (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool)).1.card = 0
  · have hs : ¬ (1 ≤ t - (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool)).1.card ∧
        t - (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool)).1.card ≤ t) := by
      omega
    have hstep : (simState n t T TOf (q + 1) (mkValidAns n t T wOf TOf outOf f (q + 1) pool)).1 =
        (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool)).1 := by
      rw [simState, simState_mkValidAns_step]
      unfold simStep
      dsimp only
      rw [if_neg hs]
    rw [hstep, if_pos h0]
  · rw [if_neg h0]
    split_ifs <;> norm_num

private lemma failProb_succ_le (f : Qubits n → Bool) (q : Fin T) :
    failProb n t T wOf TOf AOf outOf f ((q : ℕ) + 1) ≤
      failProb n t T wOf TOf AOf outOf f (q : ℕ) := by
  have hle : failProb n t T wOf TOf AOf outOf f ((q : ℕ) + 1) ≤
      ∑ pool : Pool n T t wOf,
        notDoneOfSt n t (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)) *
          poolWeight n t T wOf TOf AOf outOf f ((q : ℕ) + 1) pool := by
    unfold failProb
    refine Finset.sum_le_sum fun pool _ => ?_
    exact mul_le_mul_of_nonneg_right
      (notDoneOfSt_succ_le n t T wOf TOf outOf f (q : ℕ) pool)
      (poolWeight_nonneg n t T wOf TOf AOf outOf f ((q : ℕ) + 1) pool)
  have heq : (∑ pool : Pool n T t wOf,
        notDoneOfSt n t (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)) *
          poolWeight n t T wOf TOf AOf outOf f ((q : ℕ) + 1) pool) =
      failProb n t T wOf TOf AOf outOf f (q : ℕ) := by
    unfold failProb
    rw [sum_pool_partition_option n t T wOf TOf outOf q f
          (fun pool => notDoneOfSt n t (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)) *
            poolWeight n t T wOf TOf AOf outOf f ((q : ℕ) + 1) pool),
        sum_pool_partition_option n t T wOf TOf outOf q f
          (fun pool => notDoneOfSt n t (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)) *
            poolWeight n t T wOf TOf AOf outOf f (q : ℕ) pool)]
    refine congr_arg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun pool _ => ?_
      split_ifs with h
      · rw [(of_stageSlotAt_none n t T wOf TOf outOf f q pool h).2.1]
        ring
      · rfl
    · refine Finset.sum_congr rfl fun p0 _ => ?_
      rw [sum_stageSlot_some_succ n t T wOf TOf AOf outOf f q p0
        (fun ans _ => notDoneOfSt n t (simState n t T TOf (q : ℕ) ans))]
      refine Finset.sum_congr rfl fun pool _ => ?_
      split_ifs with h
      · rw [← Finset.mul_sum, sum_slotVec_norm_sq, mul_one]
      · rfl
  linarith

noncomputable def nextPhi (f : Qubits n → Bool) (q : Fin T) (p0 : SlotIdx T t)
    (ans : Ans n T) (z : SlotReg n wOf p0) : ℝ :=
  let st := simState n t T TOf (q : ℕ) ans
  let s := t - st.1.card
  if st.2.2 < TOfNat t TOf s then
    phiOfSt n t TOf (st.1, st.2.1, st.2.2 + 1)
  else
    let c := outOf p0.2 z
    if (f c && decide (c ∉ st.1)) = true then
      phiOfSt n t TOf (insert c st.1, (q : ℕ) + 1, 0)
    else
      phiOfSt n t TOf (st.1, (q : ℕ) + 1, 0)

private lemma phiOfSt_succ_eq_nextPhi (f : Qubits n → Bool) (q : Fin T) (p0 : SlotIdx T t)
    (pool : Pool n T t wOf)
    (h : stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0) :
    phiOfSt n t TOf (simState n t T TOf ((q : ℕ) + 1)
        (mkValidAns n t T wOf TOf outOf f ((q : ℕ) + 1) pool)) =
      nextPhi n t T wOf TOf outOf f q p0
        (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) (pool p0) := by
  unfold stageSlotAt stageSlotOfSt at h
  dsimp only at h
  split_ifs at h with hs hq0
  have hp0 := Option.some.inj h
  subst hp0
  rw [simState, simState_mkValidAns_step]
  unfold simStep nextPhi
  dsimp only
  rw [if_pos hs]
  by_cases hτ : (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)).2.2 <
      TOfNat t TOf (t - (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)).1.card)
  · rw [if_pos hτ, if_pos hτ]
  · rw [if_neg hτ, if_neg hτ, dif_pos q.2]
    have hcb : mkValidAns n t T wOf TOf outOf f ((q : ℕ) + 1) pool ⟨(q : ℕ), q.2⟩ =
        (outOf ⟨t - (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)).1.card - 1, by omega⟩
          (pool (⟨(simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)).2.1, hq0⟩,
            ⟨t - (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)).1.card - 1, by omega⟩)),
         f (outOf ⟨t - (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)).1.card - 1, by omega⟩
          (pool (⟨(simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)).2.1, hq0⟩,
            ⟨t - (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)).1.card - 1, by omega⟩)))) := by
      simp only [mkValidAns, dif_pos q.2, Function.update_self]
      unfold expectedAnsAt candAt candOfSt
      dsimp only
      rw [if_neg (fun h' => hτ h'.2.2), dif_pos hs, dif_pos hq0]
    rw [hcb]
    dsimp only
    exact apply_ite (phiOfSt n t TOf) _ _ _

private lemma slotVec_succ_at_test (f : Qubits n → Bool) (q : Fin T) (ans : Ans n T)
    (p0 : SlotIdx T t) (h : stageSlotAt n t T TOf q ans = some p0)
    (hτ : ¬ ((simState n t T TOf (q : ℕ) ans).2.2 <
      TOfNat t TOf (t - (simState n t T TOf (q : ℕ) ans).1.card))) :
    slotVec n t T wOf TOf AOf f ((q : ℕ) + 1) ans p0 =
      (AOf p0.2).finalState
        (xorOracle (maskF n f (simState n t T TOf (q : ℕ) ans).1)) := by
  obtain ⟨hp1, hs, hp2⟩ := stageSlotAt_eq_some n t T TOf q ans p0 h
  have hst_p0 := simState_at_q0 n t T TOf (q : ℕ) ans
  rw [← hp1] at hst_p0
  have hq0_le := simState_q0_le n t T TOf (q : ℕ) ans
  have hadd := simState_q0_add_tau n t T TOf (q : ℕ) ans
  have hTi := TOfNat_eq t TOf _ hs p0.2 hp2
  have hact : slotActive n t T TOf ((q : ℕ) + 1) ans p0 := by
    unfold slotActive
    rw [hst_p0]
    exact ⟨by omega, rfl, hs.1, hs.2, hp2⟩
  have hstep : slotStep n t T TOf ((q : ℕ) + 1) ans p0 = Fin.last (TOf p0.2) := by
    unfold slotStep
    rw [if_pos hact]
    ext
    simp only [Fin.val_last]
    omega
  unfold slotVec QueryAlg.finalState
  rw [hst_p0, hstep]

private lemma maskF_eq_and_not_mem (f : Qubits n → Bool) (S : Finset (Qubits n))
    (hS : S ⊆ Finset.univ.filter (fun j => f j = true)) (c : Qubits n) :
    maskF n f S c = (f c && decide (c ∉ S)) := by
  unfold maskF
  by_cases hc : c ∈ S
  · have hfc : f c = true := (Finset.mem_filter.mp (hS hc)).2
    simp [hc, hfc]
  · simp [hc]

private lemma maskF_filter_card (f : Qubits n → Bool) (S : Finset (Qubits n))
    (hf : (Finset.univ.filter (fun j => f j = true)).card = t)
    (hS : S ⊆ Finset.univ.filter (fun j => f j = true)) :
    (Finset.univ.filter (fun j => maskF n f S j = true)).card = t - S.card := by
  let M := Finset.univ.filter (fun j => f j = true)
  have h_eq : Finset.univ.filter (fun j => maskF n f S j = true) = M \ S := by
    ext j
    rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_filter,
        maskF_eq_and_not_mem n f S hS j]
    simp [Bool.and_eq_true, decide_eq_true_eq]
  have hdisj : Disjoint (M \ S) S := Finset.sdiff_disjoint
  have hunion : (M \ S) ∪ S = M := Finset.sdiff_union_of_subset hS
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, hf] at hcard
  rw [h_eq]
  omega

private lemma probEvent_eq_sum_ite {X : Type*} [Fintype X] [DecidableEq X]
    (ψ : EuclideanSpace ℂ X) (P : X → Prop) [DecidablePred P] :
    probEvent ψ P = ∑ z : X, (if P z then 1 else 0) * ‖ψ z‖ ^ 2 := by
  unfold probEvent prob
  simp only [ket, EuclideanSpace.inner_single_left, one_mul, starRingEnd_apply, star_one]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> ring

private lemma sum_nextPhi_le (f : Qubits n → Bool)
    (hf : (Finset.univ.filter (fun j => f j = true)).card = t)
    (hAOf : ∀ (s : Fin t) (g : Qubits n → Bool),
      (Finset.univ.filter (fun j => g j = true)).card = (s : ℕ) + 1 →
      2 / 3 ≤ probEvent ((AOf s).finalState (xorOracle g))
        (fun z => g (outOf s z) = true))
    (q : Fin T) (p0 : SlotIdx T t) (pool : Pool n T t wOf)
    (h : stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0) :
    (∑ z : SlotReg n wOf p0,
      nextPhi n t T wOf TOf outOf f q p0
        (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) z *
        ‖slotVec n t T wOf TOf AOf f ((q : ℕ) + 1)
          (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) p0 z‖ ^ 2) ≤
      phiOfSt n t TOf (simState n t T TOf (q : ℕ)
        (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)) -
      notDoneOfSt n t (simState n t T TOf (q : ℕ)
        (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)) := by
  set ans := mkValidAns n t T wOf TOf outOf f (q : ℕ) pool
  obtain ⟨hp1, hs, hp2⟩ := stageSlotAt_eq_some n t T TOf q ans p0 h
  have hτ_le := simState_tau_le n t T TOf (q : ℕ) ans
  have hsub : (simState n t T TOf (q : ℕ) ans).1 ⊆ Finset.univ.filter (fun j => f j = true) :=
    simState_sub_marked n t T wOf TOf outOf f (q : ℕ) pool
  have hs_ne : t - (simState n t T TOf (q : ℕ) ans).1.card ≠ 0 := by omega
  have hnotDone : notDoneOfSt n t (simState n t T TOf (q : ℕ) ans) = 1 := by
    simp [notDoneOfSt, hs_ne]
  by_cases hτ : (simState n t T TOf (q : ℕ) ans).2.2 <
      TOfNat t TOf (t - (simState n t T TOf (q : ℕ) ans).1.card)
  · have hnext : ∀ z : SlotReg n wOf p0,
        nextPhi n t T wOf TOf outOf f q p0 ans z =
          phiOfSt n t TOf (simState n t T TOf (q : ℕ) ans) - 1 := by
      intro z
      unfold nextPhi
      dsimp only
      rw [if_pos hτ]
      unfold phiOfSt
      dsimp only
      rw [if_neg hs_ne, if_neg hs_ne]
      push_cast
      ring
    simp_rw [hnext]
    rw [← Finset.mul_sum, sum_slotVec_norm_sq, mul_one, hnotDone]
  · have hTi : TOfNat t TOf (t - (simState n t T TOf (q : ℕ) ans).1.card) = TOf p0.2 :=
      TOfNat_eq t TOf _ hs p0.2 hp2
    have hτ_eq : (simState n t T TOf (q : ℕ) ans).2.2 = TOf p0.2 := by omega
    have hphi_st : phiOfSt n t TOf (simState n t T TOf (q : ℕ) ans) =
        stageCost t TOf (t - (simState n t T TOf (q : ℕ) ans).1.card) - (TOf p0.2 : ℝ) := by
      unfold phiOfSt
      rw [if_neg hs_ne, hτ_eq]
    have hnext : ∀ z : SlotReg n wOf p0,
        nextPhi n t T wOf TOf outOf f q p0 ans z =
          stageCost t TOf (t - (simState n t T TOf (q : ℕ) ans).1.card) -
            (if maskF n f (simState n t T TOf (q : ℕ) ans).1 (outOf p0.2 z) = true then 1 else 0) *
              (3 * ((TOf p0.2 : ℝ) + 1)) := by
      intro z
      unfold nextPhi
      dsimp only
      rw [if_neg hτ, ← maskF_eq_and_not_mem n f (simState n t T TOf (q : ℕ) ans).1 hsub (outOf p0.2 z)]
      by_cases hm : maskF n f (simState n t T TOf (q : ℕ) ans).1 (outOf p0.2 z) = true
      · rw [if_pos hm, if_pos hm, one_mul]
        have hc_not_mem : outOf p0.2 z ∉ (simState n t T TOf (q : ℕ) ans).1 := by
          rw [maskF_eq_and_not_mem n f (simState n t T TOf (q : ℕ) ans).1 hsub] at hm
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
          exact hm.2
        have hcard_ins : (insert (outOf p0.2 z) (simState n t T TOf (q : ℕ) ans).1).card =
            (simState n t T TOf (q : ℕ) ans).1.card + 1 := by
          rw [Finset.card_insert_eq_ite, if_neg hc_not_mem]
        have hsub_ins : t - (insert (outOf p0.2 z) (simState n t T TOf (q : ℕ) ans).1).card =
            t - (simState n t T TOf (q : ℕ) ans).1.card - 1 := by
          omega
        have hphi_ins : phiOfSt n t TOf (insert (outOf p0.2 z) (simState n t T TOf (q : ℕ) ans).1, (q : ℕ) + 1, 0) =
            stageCost t TOf (t - (simState n t T TOf (q : ℕ) ans).1.card - 1) := by
          unfold phiOfSt
          dsimp only
          rw [hsub_ins]
          split_ifs with h0
          · rw [h0, stageCost_zero]
          · simp
        have hp2_fin : (⟨t - (simState n t T TOf (q : ℕ) ans).1.card - 1, by omega⟩ : Fin t) = p0.2 := by
          ext; exact hp2.symm
        rw [hphi_ins, stageCost_sub_one t TOf (t - (simState n t T TOf (q : ℕ) ans).1.card) hs, hp2_fin]
      · rw [if_neg hm, if_neg hm, zero_mul, sub_zero]
        unfold phiOfSt
        dsimp only
        rw [if_neg hs_ne]
        simp
    have hsum_eq : (∑ z : SlotReg n wOf p0,
        nextPhi n t T wOf TOf outOf f q p0 ans z *
          ‖slotVec n t T wOf TOf AOf f ((q : ℕ) + 1) ans p0 z‖ ^ 2) =
      stageCost t TOf (t - (simState n t T TOf (q : ℕ) ans).1.card) -
        probEvent ((AOf p0.2).finalState (xorOracle (maskF n f (simState n t T TOf (q : ℕ) ans).1)))
          (fun z => maskF n f (simState n t T TOf (q : ℕ) ans).1 (outOf p0.2 z) = true) *
          (3 * ((TOf p0.2 : ℝ) + 1)) := by
      simp_rw [hnext, sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_slotVec_norm_sq, mul_one]
      congr 1
      simp_rw [mul_right_comm _ (3 * ((TOf p0.2 : ℝ) + 1))]
      rw [← Finset.sum_mul, slotVec_succ_at_test n t T wOf TOf AOf f q ans p0 h hτ,
          ← probEvent_eq_sum_ite]
    have hcard_g : (Finset.univ.filter (fun j => maskF n f (simState n t T TOf (q : ℕ) ans).1 j = true)).card =
        (p0.2 : ℕ) + 1 := by
      rw [maskF_filter_card n t f (simState n t T TOf (q : ℕ) ans).1 hf hsub]
      omega
    have hprob := hAOf p0.2 (maskF n f (simState n t T TOf (q : ℕ) ans).1) hcard_g
    have hpos : (0 : ℝ) ≤ 3 * ((TOf p0.2 : ℝ) + 1) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hprob hpos
    have hT_nonneg : (0 : ℝ) ≤ (TOf p0.2 : ℝ) := Nat.cast_nonneg _
    linarith

noncomputable def expPhi (f : Qubits n → Bool) (q : ℕ) : ℝ :=
  ∑ pool : Pool n T t wOf,
    phiOfSt n t TOf (simState n t T TOf q (mkValidAns n t T wOf TOf outOf f q pool)) *
      poolWeight n t T wOf TOf AOf outOf f q pool

private lemma expPhi_nonneg (f : Qubits n → Bool) (q : ℕ) :
    0 ≤ expPhi n t T wOf TOf AOf outOf f q :=
  Finset.sum_nonneg fun pool _ =>
    mul_nonneg (phiOfSt_nonneg n t T TOf q _)
      (poolWeight_nonneg n t T wOf TOf AOf outOf f q pool)

private lemma expPhi_zero (f : Qubits n → Bool) :
    expPhi n t T wOf TOf AOf outOf f 0 = stageCost t TOf t := by
  have hphi0 : ∀ pool : Pool n T t wOf,
      phiOfSt n t TOf (simState n t T TOf 0 (mkValidAns n t T wOf TOf outOf f 0 pool)) =
        stageCost t TOf t := by
    intro pool
    unfold phiOfSt simState
    dsimp only
    rw [Finset.card_empty, Nat.sub_zero]
    split_ifs with h0
    · unfold stageCost
      simp [h0]
    · simp
  unfold expPhi
  simp_rw [hphi0, ← Finset.mul_sum, sum_poolWeight_eq_one n t T wOf TOf AOf outOf f 0 (Nat.zero_le T),
    mul_one]

private lemma expPhi_succ_add_failProb_le (f : Qubits n → Bool)
    (hf : (Finset.univ.filter (fun j => f j = true)).card = t)
    (hAOf : ∀ (s : Fin t) (g : Qubits n → Bool),
      (Finset.univ.filter (fun j => g j = true)).card = (s : ℕ) + 1 →
      2 / 3 ≤ probEvent ((AOf s).finalState (xorOracle g))
        (fun z => g (outOf s z) = true))
    (q : Fin T) :
    expPhi n t T wOf TOf AOf outOf f ((q : ℕ) + 1) +
      failProb n t T wOf TOf AOf outOf f (q : ℕ) ≤
      expPhi n t T wOf TOf AOf outOf f (q : ℕ) := by
  suffices hle : expPhi n t T wOf TOf AOf outOf f ((q : ℕ) + 1) ≤
      ∑ pool : Pool n T t wOf,
        (phiOfSt n t TOf (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)) -
          notDoneOfSt n t (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool))) *
          poolWeight n t T wOf TOf AOf outOf f (q : ℕ) pool by
    have hsub : (∑ pool : Pool n T t wOf,
        (phiOfSt n t TOf (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)) -
          notDoneOfSt n t (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool))) *
          poolWeight n t T wOf TOf AOf outOf f (q : ℕ) pool) =
      expPhi n t T wOf TOf AOf outOf f (q : ℕ) - failProb n t T wOf TOf AOf outOf f (q : ℕ) := by
      unfold expPhi failProb
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun pool _ => by ring
    linarith
  unfold expPhi
  rw [sum_pool_partition_option n t T wOf TOf outOf q f
        (fun pool => phiOfSt n t TOf (simState n t T TOf ((q : ℕ) + 1) (mkValidAns n t T wOf TOf outOf f ((q : ℕ) + 1) pool)) *
          poolWeight n t T wOf TOf AOf outOf f ((q : ℕ) + 1) pool),
      sum_pool_partition_option n t T wOf TOf outOf q f
        (fun pool => (phiOfSt n t TOf (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool)) -
          notDoneOfSt n t (simState n t T TOf (q : ℕ) (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool))) *
          poolWeight n t T wOf TOf AOf outOf f (q : ℕ) pool)]
  refine add_le_add ?_ (Finset.sum_le_sum fun p0 _ => ?_)
  · refine Finset.sum_le_sum fun pool _ => ?_
    split_ifs with h
    · obtain ⟨h1, h2, h3, _⟩ := of_stageSlotAt_none n t T wOf TOf outOf f q pool h
      rw [h1, h2, h3]
      linarith
    · exact le_rfl
  · have hlhs : (∑ pool : Pool n T t wOf,
        if stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0 then
          phiOfSt n t TOf (simState n t T TOf ((q : ℕ) + 1)
            (mkValidAns n t T wOf TOf outOf f ((q : ℕ) + 1) pool)) *
            poolWeight n t T wOf TOf AOf outOf f ((q : ℕ) + 1) pool
        else 0) =
      ∑ pool : Pool n T t wOf,
        if stageSlotAt n t T TOf q (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) = some p0 then
          (∑ z : SlotReg n wOf p0,
            nextPhi n t T wOf TOf outOf f q p0
              (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) z *
              ‖slotVec n t T wOf TOf AOf f ((q : ℕ) + 1)
                (mkValidAns n t T wOf TOf outOf f (q : ℕ) pool) p0 z‖ ^ 2) *
            poolWeight n t T wOf TOf AOf outOf f (q : ℕ) pool
        else 0 := by
      rw [← sum_stageSlot_some_succ n t T wOf TOf AOf outOf f q p0
        (nextPhi n t T wOf TOf outOf f q p0)]
      refine Finset.sum_congr rfl fun pool _ => ?_
      split_ifs with h
      · rw [phiOfSt_succ_eq_nextPhi n t T wOf TOf outOf f q p0 pool h]
      · rfl
    rw [hlhs]
    refine Finset.sum_le_sum fun pool _ => ?_
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right
        (sum_nextPhi_le n t T wOf TOf AOf outOf f hf hAOf q p0 pool h)
        (poolWeight_nonneg n t T wOf TOf AOf outOf f (q : ℕ) pool)
    · exact le_rfl

private lemma expPhi_add_mul_failProb_le (f : Qubits n → Bool)
    (hf : (Finset.univ.filter (fun j => f j = true)).card = t)
    (hAOf : ∀ (s : Fin t) (g : Qubits n → Bool),
      (Finset.univ.filter (fun j => g j = true)).card = (s : ℕ) + 1 →
      2 / 3 ≤ probEvent ((AOf s).finalState (xorOracle g))
        (fun z => g (outOf s z) = true))
    (q : ℕ) (hq : q ≤ T) :
    expPhi n t T wOf TOf AOf outOf f q +
      (q : ℝ) * failProb n t T wOf TOf AOf outOf f q ≤
      expPhi n t T wOf TOf AOf outOf f 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hq_lt : q < T := Nat.lt_of_succ_le hq
    have ih' := ih (Nat.le_of_lt hq_lt)
    have hstep := expPhi_succ_add_failProb_le n t T wOf TOf AOf outOf f hf hAOf ⟨q, hq_lt⟩
    have hmono := failProb_succ_le n t T wOf TOf AOf outOf f ⟨q, hq_lt⟩
    have hmul : (q : ℝ) * failProb n t T wOf TOf AOf outOf f (q + 1) ≤
        (q : ℝ) * failProb n t T wOf TOf AOf outOf f q :=
      mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg q)
    push_cast
    linarith

private lemma stageCost_top_eq :
    stageCost t TOf t = ∑ s : Fin t, 3 * ((TOf s : ℝ) + 1) := by
  unfold stageCost
  rw [← Fin.sum_univ_eq_sum_range (fun i => if hi : i < t then 3 * ((TOf ⟨i, hi⟩ : ℝ) + 1) else 0)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [dif_pos s.2]

private lemma simAlg_success (f : Qubits n → Bool)
    (hf : (Finset.univ.filter (fun j => f j = true)).card = t)
    (hAOf : ∀ (s : Fin t) (g : Qubits n → Bool),
      (Finset.univ.filter (fun j => g j = true)).card = (s : ℕ) + 1 →
      2 / 3 ≤ probEvent ((AOf s).finalState (xorOracle g))
        (fun z => g (outOf s z) = true))
    (hT : T = 9 * ∑ s : Fin t, (TOf s + 1)) :
    2 / 3 ≤ probEvent ((simAlg n t T wOf TOf AOf outOf).finalState (xorOracle f))
      (fun x => (simState n t T TOf T x.2.1).1 = Finset.univ.filter (fun j => f j = true)) := by
  let M := Finset.univ.filter (fun j => f j = true)
  have hM_card : M.card = t := hf
  have hprob_eq : probEvent ((simAlg n t T wOf TOf AOf outOf).finalState (xorOracle f))
      (fun x => (simState n t T TOf T x.2.1).1 = M) =
      1 - failProb n t T wOf TOf AOf outOf f T := by
    rw [simAlg_finalState,
        probEvent_simPsi n t T wOf TOf AOf outOf f T (fun ans => (simState n t T TOf T ans).1 = M)]
    have hsum_eq : (∑ pool : Pool n T t wOf,
        (if (simState n t T TOf T (mkValidAns n t T wOf TOf outOf f T pool)).1 = M then (1 : ℝ) else 0) *
          poolWeight n t T wOf TOf AOf outOf f T pool) =
      ∑ pool : Pool n T t wOf,
        (poolWeight n t T wOf TOf AOf outOf f T pool -
          notDoneOfSt n t (simState n t T TOf T (mkValidAns n t T wOf TOf outOf f T pool)) *
            poolWeight n t T wOf TOf AOf outOf f T pool) := by
      refine Finset.sum_congr rfl fun pool _ => ?_
      set S := (simState n t T TOf T (mkValidAns n t T wOf TOf outOf f T pool)).1
      have hsub : S ⊆ M := simState_sub_marked n t T wOf TOf outOf f T pool
      have hcard_le : S.card ≤ t := by
        rw [← hM_card]
        exact Finset.card_le_card hsub
      have hiff : S = M ↔ t - S.card = 0 := by
        constructor
        · intro hSM; rw [hSM, hM_card, Nat.sub_self]
        · intro h0
          have hcard_eq : M.card ≤ S.card := by omega
          exact Finset.eq_of_subset_of_card_le hsub hcard_eq
      unfold notDoneOfSt
      by_cases hSM : S = M
      · rw [if_pos hSM, if_pos (hiff.mp hSM)]
        ring
      · rw [if_neg hSM, if_neg (mt hiff.mpr hSM)]
        ring
    rw [hsum_eq, Finset.sum_sub_distrib,
        sum_poolWeight_eq_one n t T wOf TOf AOf outOf f T (le_refl T)]
    rfl
  have hfail_le : failProb n t T wOf TOf AOf outOf f T ≤ 1 / 3 := by
    rcases Nat.eq_zero_or_pos t with rfl | ht_pos
    · have h0 : failProb n 0 T wOf TOf AOf outOf f T = 0 := by
        unfold failProb notDoneOfSt
        simp
      linarith
    · have hbound := expPhi_add_mul_failProb_le n t T wOf TOf AOf outOf f hf hAOf T (le_refl T)
      rw [expPhi_zero] at hbound
      have hnonneg := expPhi_nonneg n t T wOf TOf AOf outOf f T
      have hT_eq : (T : ℝ) = 3 * stageCost t TOf t := by
        rw [hT, stageCost_top_eq]
        push_cast
        rw [← Finset.mul_sum]
        ring
      have hT_pos : (0 : ℝ) < (T : ℝ) := by
        have hs0 : (⟨0, ht_pos⟩ : Fin t) ∈ Finset.univ := Finset.mem_univ _
        have hsum_pos : 0 < ∑ s : Fin t, (TOf s + 1) :=
          Nat.pos_of_ne_zero (by
            intro hzero
            have := Finset.sum_eq_zero_iff.mp hzero ⟨0, ht_pos⟩ hs0
            omega)
        have : 0 < T := by omega
        exact Nat.cast_pos.mpr this
      nlinarith
  linarith

end SimMachine

section ReindexAlg

variable {α β W W' : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype W] [DecidableEq W] [Fintype W'] [DecidableEq W']

def reindexEquiv (e : W ≃ W') : (α × β) × W ≃ (α × β) × W' :=
  Equiv.prodCongr (Equiv.refl (α × β)) e

noncomputable def reindexVec (e : W ≃ W') (ψ : EuclideanSpace ℂ ((α × β) × W)) :
    EuclideanSpace ℂ ((α × β) × W') :=
  WithLp.toLp 2 fun y => ψ ((reindexEquiv e).symm y)

noncomputable def reindexMat (e : W ≃ W') (M : Matrix ((α × β) × W) ((α × β) × W) ℂ) :
    Matrix ((α × β) × W') ((α × β) × W') ℂ :=
  Matrix.submatrix M (reindexEquiv e).symm (reindexEquiv e).symm

private lemma reindexVec_norm (e : W ≃ W') (ψ : EuclideanSpace ℂ ((α × β) × W)) :
    ‖reindexVec e ψ‖ = ‖ψ‖ := by
  have hsq : ‖reindexVec e ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    exact Fintype.sum_equiv (reindexEquiv e).symm
      (fun y => ‖(reindexVec e ψ).ofLp y‖ ^ 2) (fun x => ‖ψ.ofLp x‖ ^ 2) (fun _ => rfl)
  have h1 : 0 ≤ ‖reindexVec e ψ‖ := norm_nonneg _
  have h2 : 0 ≤ ‖ψ‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖reindexVec e ψ‖ - ‖ψ‖)]

private lemma reindexMat_mem_unitary (e : W ≃ W')
    {M : Matrix ((α × β) × W) ((α × β) × W) ℂ}
    (hM : M ∈ Matrix.unitaryGroup ((α × β) × W) ℂ) :
    reindexMat e M ∈ Matrix.unitaryGroup ((α × β) × W') ℂ := by
  have hstar : star (reindexMat e M) = reindexMat e (star M) := rfl
  have hmul : ∀ A B : Matrix ((α × β) × W) ((α × β) × W) ℂ,
      reindexMat e A * reindexMat e B = reindexMat e (A * B) := by
    intro A B
    ext x y
    simp only [reindexMat, Matrix.mul_apply, Matrix.submatrix_apply]
    exact Fintype.sum_equiv (reindexEquiv e).symm _ _ (fun _ => rfl)
  have hone : reindexMat e (1 : Matrix ((α × β) × W) ((α × β) × W) ℂ) = 1 := by
    ext x y
    simp [reindexMat, Matrix.one_apply, Equiv.apply_eq_iff_eq]
  rw [Matrix.mem_unitaryGroup_iff] at hM ⊢
  rw [hstar, hmul, hM, hone]

private lemma act_reindexMat (e : W ≃ W') (M : Matrix ((α × β) × W) ((α × β) × W) ℂ)
    (ψ : EuclideanSpace ℂ ((α × β) × W)) :
    act (reindexMat e M) (reindexVec e ψ) = reindexVec e (act M ψ) := by
  ext y
  simp only [act, reindexMat, reindexVec, Matrix.mulVec, dotProduct,
    Matrix.submatrix_apply, WithLp.ofLp_toLp]
  exact Fintype.sum_equiv (reindexEquiv e).symm _ _ (fun _ => rfl)

private lemma kronecker_one_eq_reindexMat (e : W ≃ W') (O : Matrix (α × β) (α × β) ℂ) :
    Matrix.kronecker O (1 : Matrix W' W' ℂ) =
      reindexMat e (Matrix.kronecker O (1 : Matrix W W ℂ)) := by
  ext ⟨q1, w1⟩ ⟨q2, w2⟩
  simp [reindexMat, reindexEquiv, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Equiv.apply_eq_iff_eq]

noncomputable def reindexAlg {T : ℕ} (e : W ≃ W') (A : QueryAlg α β W T) :
    QueryAlg α β W' T where
  start := reindexVec e A.start
  start_unit := by rw [reindexVec_norm, A.start_unit]
  U k := ⟨reindexMat e (A.U k).1, reindexMat_mem_unitary e (A.U k).2⟩

private lemma reindexAlg_stateAt {T : ℕ} (e : W ≃ W') (A : QueryAlg α β W T)
    (O : Matrix (α × β) (α × β) ℂ) (k : Fin (T + 1)) :
    (reindexAlg e A).stateAt O k = reindexVec e (A.stateAt O k) := by
  induction k using Fin.induction with
  | zero =>
    dsimp only [QueryAlg.stateAt, Fin.induction_zero, reindexAlg]
    exact act_reindexMat e (A.U 0).1 A.start
  | succ i ih =>
    rw [QueryAlg.stateAt, Fin.induction_succ, ← QueryAlg.stateAt, ih]
    dsimp only [reindexAlg]
    rw [kronecker_one_eq_reindexMat e O, act_reindexMat, act_reindexMat]
    rfl

private lemma reindexAlg_finalState {T : ℕ} (e : W ≃ W') (A : QueryAlg α β W T)
    (O : Matrix (α × β) (α × β) ℂ) :
    (reindexAlg e A).finalState O = reindexVec e (A.finalState O) :=
  reindexAlg_stateAt e A O (Fin.last T)

private lemma probEvent_reindexVec (e : W ≃ W') (ψ : EuclideanSpace ℂ ((α × β) × W))
    (P : (α × β) × W → Prop) [DecidablePred P] :
    probEvent (reindexVec e ψ) (fun y => P ((reindexEquiv e).symm y)) = probEvent ψ P := by
  rw [probEvent_eq_sum_ite, probEvent_eq_sum_ite]
  exact Fintype.sum_equiv (reindexEquiv e).symm
    (fun y => (if P ((reindexEquiv e).symm y) then 1 else 0) * ‖(reindexVec e ψ).ofLp y‖ ^ 2)
    (fun x => (if P x then 1 else 0) * ‖ψ.ofLp x‖ ^ 2)
    (fun _ => rfl)

end ReindexAlg

private lemma sum_range_inv_sqrt_le (t : ℕ) :
    (∑ k ∈ Finset.range t, 1 / Real.sqrt (((k + 1 : ℕ) : ℝ))) ≤ 2 * Real.sqrt (t : ℝ) := by
  induction t with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hsqrt_pos : 0 < Real.sqrt (((m + 1 : ℕ) : ℝ)) := Real.sqrt_pos.mpr hpos
    have hstep : 1 / Real.sqrt (((m + 1 : ℕ) : ℝ)) ≤
        2 * Real.sqrt (((m + 1 : ℕ) : ℝ)) - 2 * Real.sqrt (m : ℝ) := by
      rw [div_le_iff₀ hsqrt_pos]
      have hsq : Real.sqrt (((m + 1 : ℕ) : ℝ)) * Real.sqrt (((m + 1 : ℕ) : ℝ)) = ((m + 1 : ℕ) : ℝ) :=
        Real.mul_self_sqrt (le_of_lt hpos)
      have hprod : Real.sqrt (m : ℝ) * Real.sqrt (((m + 1 : ℕ) : ℝ)) ≤ (m : ℝ) + (1 : ℝ) / 2 := by
        have hsq1 : (Real.sqrt (m : ℝ) * Real.sqrt (((m + 1 : ℕ) : ℝ))) ^ 2 =
            (m : ℝ) * ((m : ℝ) + 1) := by
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m), Real.sq_sqrt (le_of_lt hpos)]
          push_cast; ring
        have hle_sq : (Real.sqrt (m : ℝ) * Real.sqrt (((m + 1 : ℕ) : ℝ))) ^ 2 ≤
            ((m : ℝ) + (1 : ℝ) / 2) ^ 2 := by
          rw [hsq1]
          linarith
        nlinarith [sq_nonneg ((m : ℝ) + (1 : ℝ) / 2 - Real.sqrt (m : ℝ) * Real.sqrt (((m + 1 : ℕ) : ℝ)))]
      have hexp : (2 * Real.sqrt (((m + 1 : ℕ) : ℝ)) - 2 * Real.sqrt (m : ℝ)) *
          Real.sqrt (((m + 1 : ℕ) : ℝ)) =
        2 * (Real.sqrt (((m + 1 : ℕ) : ℝ)) * Real.sqrt (((m + 1 : ℕ) : ℝ))) -
          2 * (Real.sqrt (m : ℝ) * Real.sqrt (((m + 1 : ℕ) : ℝ))) := by ring
      push_cast at hsq hprod hexp ⊢
      linarith
    linarith

noncomputable def dummyAlg (n : ℕ) : QueryAlg (Qubits n) Bool (Fin 1) 0 where
  start := ket ((0, false), 0)
  start_unit := by simp [ket, PiLp.norm_single]
  U _ := 1

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ n t : ℕ,
      ∃ (w T : ℕ) (A : QueryAlg (Qubits n) Bool (Fin w) T)
        (out : (Qubits n × Bool) × Fin w → Finset (Qubits n)),
        (T : ℝ) ≤ C * Real.sqrt ((t : ℝ) * (2 : ℝ) ^ n) ∧
        ∀ f : Qubits n → Bool, (Finset.univ.filter fun j => f j = true).card = t →
          2 / 3 ≤ probEvent (A.finalState (xorOracle f))
            fun z => out z = Finset.univ.filter fun j => f j = true := by
  obtain ⟨C₀, hC₀_pos, hsearch⟩ := QAlgorithms.Nannicini.search_knownCount
  refine ⟨18 * (C₀ + 1), by positivity, fun n t => ?_⟩
  by_cases ht : 1 ≤ t ∧ t ≤ 2 ^ n
  · have h_ex : ∀ s : Fin t,
        ∃ (w T : ℕ) (A : QueryAlg (Qubits n) Bool (Fin w) T)
          (out : (Qubits n × Bool) × Fin w → Qubits n),
          (T : ℝ) ≤ C₀ * Real.sqrt ((2 : ℝ) ^ n / (((s : ℕ) + 1 : ℕ) : ℝ)) ∧
          ∀ f : Qubits n → Bool, (Finset.univ.filter fun j => f j = true).card = (s : ℕ) + 1 →
            2 / 3 ≤ probEvent (A.finalState (xorOracle f)) fun z => f (out z) = true :=
      fun s => hsearch n ((s : ℕ) + 1) (by omega) (by omega)
    let wOf : Fin t → ℕ := fun s => Classical.choose (h_ex s)
    let h_ex1 := fun s => Classical.choose_spec (h_ex s)
    let TOf : Fin t → ℕ := fun s => Classical.choose (h_ex1 s)
    let h_ex2 := fun s => Classical.choose_spec (h_ex1 s)
    let AOf : ∀ s : Fin t, QueryAlg (Qubits n) Bool (Fin (wOf s)) (TOf s) :=
      fun s => Classical.choose (h_ex2 s)
    let h_ex3 := fun s => Classical.choose_spec (h_ex2 s)
    let outOf : ∀ s : Fin t, (Qubits n × Bool) × Fin (wOf s) → Qubits n :=
      fun s => Classical.choose (h_ex3 s)
    have hTOf : ∀ s : Fin t,
        (TOf s : ℝ) ≤ C₀ * Real.sqrt ((2 : ℝ) ^ n / (((s : ℕ) + 1 : ℕ) : ℝ)) :=
      fun s => (Classical.choose_spec (h_ex3 s)).1
    have hAOf : ∀ (s : Fin t) (g : Qubits n → Bool),
        (Finset.univ.filter (fun j => g j = true)).card = (s : ℕ) + 1 →
        2 / 3 ≤ probEvent ((AOf s).finalState (xorOracle g))
          (fun z => g (outOf s z) = true) :=
      fun s => (Classical.choose_spec (h_ex3 s)).2
    let T : ℕ := 9 * ∑ s : Fin t, (TOf s + 1)
    let W := Ans n T × Pool n T t wOf
    let w : ℕ := Fintype.card W
    let e : W ≃ Fin w := Fintype.equivFin W
    refine ⟨w, T, reindexAlg e (simAlg n t T wOf TOf AOf outOf),
      fun z => (simState n t T TOf T (e.symm z.2).1).1, ?_, ?_⟩
    · have hterm : ∀ s : Fin t,
          ((TOf s + 1 : ℕ) : ℝ) ≤
            (C₀ + 1) * Real.sqrt ((2 : ℝ) ^ n) * (1 / Real.sqrt (((s : ℕ) + 1 : ℕ) : ℝ)) := by
        intro s
        have hs_le : (s : ℕ) + 1 ≤ 2 ^ n := by omega
        have hs_le_r : (((s : ℕ) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hs_le
        have hs_pos : (0 : ℝ) < (((s : ℕ) + 1 : ℕ) : ℝ) := by positivity
        have hdiv_ge : 1 ≤ (2 : ℝ) ^ n / (((s : ℕ) + 1 : ℕ) : ℝ) :=
          (one_le_div hs_pos).mpr hs_le_r
        have hsqrt_ge : 1 ≤ Real.sqrt ((2 : ℝ) ^ n / (((s : ℕ) + 1 : ℕ) : ℝ)) := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt hdiv_ge
        have hTs := hTOf s
        have hdiv_sqrt : Real.sqrt ((2 : ℝ) ^ n / (((s : ℕ) + 1 : ℕ) : ℝ)) =
            Real.sqrt ((2 : ℝ) ^ n) * (1 / Real.sqrt (((s : ℕ) + 1 : ℕ) : ℝ)) := by
          rw [Real.sqrt_div (by positivity), div_eq_mul_one_div]
        rw [hdiv_sqrt] at hTs hsqrt_ge
        have hexp : (C₀ + 1) * Real.sqrt ((2 : ℝ) ^ n) * (1 / Real.sqrt (((s : ℕ) + 1 : ℕ) : ℝ)) =
            C₀ * (Real.sqrt ((2 : ℝ) ^ n) * (1 / Real.sqrt (((s : ℕ) + 1 : ℕ) : ℝ))) +
              Real.sqrt ((2 : ℝ) ^ n) * (1 / Real.sqrt (((s : ℕ) + 1 : ℕ) : ℝ)) := by ring
        push_cast at hTs hsqrt_ge hexp ⊢
        linarith
      have hsum_le : (∑ s : Fin t, ((TOf s + 1 : ℕ) : ℝ)) ≤
          (C₀ + 1) * Real.sqrt ((2 : ℝ) ^ n) * (2 * Real.sqrt (t : ℝ)) := by
        calc (∑ s : Fin t, ((TOf s + 1 : ℕ) : ℝ))
          _ ≤ ∑ s : Fin t, (C₀ + 1) * Real.sqrt ((2 : ℝ) ^ n) * (1 / Real.sqrt (((s : ℕ) + 1 : ℕ) : ℝ)) :=
            Finset.sum_le_sum fun s _ => hterm s
          _ = (C₀ + 1) * Real.sqrt ((2 : ℝ) ^ n) * ∑ s : Fin t, (1 / Real.sqrt (((s : ℕ) + 1 : ℕ) : ℝ)) := by
            rw [← Finset.mul_sum]
          _ = (C₀ + 1) * Real.sqrt ((2 : ℝ) ^ n) * ∑ k ∈ Finset.range t, (1 / Real.sqrt (((k + 1 : ℕ) : ℝ))) := by
            rw [Fin.sum_univ_eq_sum_range (fun k => 1 / Real.sqrt (((k + 1 : ℕ) : ℝ)))]
          _ ≤ (C₀ + 1) * Real.sqrt ((2 : ℝ) ^ n) * (2 * Real.sqrt (t : ℝ)) :=
            mul_le_mul_of_nonneg_left (sum_range_inv_sqrt_le t) (by positivity)
      have hsqrt_mul : Real.sqrt ((t : ℝ) * (2 : ℝ) ^ n) =
          Real.sqrt (t : ℝ) * Real.sqrt ((2 : ℝ) ^ n) :=
        Real.sqrt_mul (Nat.cast_nonneg t) _
      have hT_cast : (T : ℝ) = 9 * ∑ s : Fin t, ((TOf s + 1 : ℕ) : ℝ) := by
        dsimp only [T]
        push_cast
        rfl
      rw [hT_cast, hsqrt_mul]
      linarith
    · intro f hf
      rw [reindexAlg_finalState]
      have hprob := probEvent_reindexVec e
        ((simAlg n t T wOf TOf AOf outOf).finalState (xorOracle f))
        (fun x => (simState n t T TOf T x.2.1).1 = Finset.univ.filter (fun j => f j = true))
      exact le_trans (simAlg_success n t T wOf TOf AOf outOf f hf hAOf rfl) (le_of_eq hprob.symm)
  · refine ⟨1, 0, dummyAlg n, fun _ => ∅, by simp only [Nat.cast_zero]; positivity, fun f hf => ?_⟩
    rcases Nat.eq_zero_or_pos t with rfl | ht_pos
    · have hemp : Finset.univ.filter (fun j => f j = true) = ∅ :=
        Finset.card_eq_zero.mp hf
      rw [hemp, probEvent_eq_sum_ite]
      simp only [↓reduceIte, one_mul, ← PiLp.norm_sq_eq_of_L2]
      unfold QueryAlg.finalState
      rw [stateAt_xorOracle_norm (dummyAlg n) f (Fin.last 0), one_pow]
      norm_num
    · exfalso
      have hgt : 2 ^ n < t := by omega
      have hcard_le : (Finset.univ.filter (fun j => f j = true)).card ≤ 2 ^ n := by
        calc (Finset.univ.filter (fun j => f j = true)).card
          _ ≤ (Finset.univ : Finset (Qubits n)).card := Finset.card_filter_le _ _
          _ = 2 ^ n := by simp [Qubits]
      omega

