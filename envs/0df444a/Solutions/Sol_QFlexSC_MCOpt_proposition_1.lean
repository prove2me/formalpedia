-- Prove2me | solution 1 for QFlexSC.MCOpt.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T14:56:27.453797+00:00
-- url     : https://prove2.me/submissions/6f107901-1de4-4d84-80d8-edf057b265fc

import Mathlib
import Definitions.Def_QFlexSC_ZeroInv_Model
import Definitions.Def_QFlexSC_MCOpt_FOLFC

set_option autoImplicit false

namespace P4d564611

open QFlexSC.ZeroInv QFlexSC.MCOpt

/-- The standing assumptions on the QF parameters. -/
def Std (P : QFParams) : Prop :=
  ∀ q, 1 ≤ q → 0 ≤ P.αin q ∧ 0 ≤ P.αout q ∧ 0 ≤ P.ωin q ∧ P.ωin q ≤ 1 ∧
      0 ≤ P.ωout q ∧ P.ωout q ≤ 1

lemma Acum_zero (α : ℕ → ℝ) : Acum α 0 = 0 := by simp [Acum]

lemma Ωcum_zero (ω : ℕ → ℝ) : Ωcum ω 0 = 0 := by simp [Ωcum]

lemma one_add_Acum_succ (α : ℕ → ℝ) (j : ℕ) :
    1 + Acum α (j+1) = (1 + Acum α j) * (1 + α (j+1)) := by
  unfold Acum
  rw [Finset.prod_Icc_succ_top (by omega)]
  ring

lemma one_sub_Ωcum_succ (ω : ℕ → ℝ) (j : ℕ) :
    1 - Ωcum ω (j+1) = (1 - Ωcum ω j) * (1 - ω (j+1)) := by
  unfold Ωcum
  rw [Finset.prod_Icc_succ_top (by omega)]
  ring

lemma one_le_one_add_Acum (α : ℕ → ℝ) (hα : ∀ q, 1 ≤ q → 0 ≤ α q) (j : ℕ) :
    1 ≤ 1 + Acum α j := by
  induction j with
  | zero => simp [Acum_zero]
  | succ j ih =>
    rw [one_add_Acum_succ]
    have := hα (j+1) (by omega)
    nlinarith

lemma Ωcum_bounds (ω : ℕ → ℝ) (hω : ∀ q, 1 ≤ q → 0 ≤ ω q ∧ ω q ≤ 1) (j : ℕ) :
    0 ≤ 1 - Ωcum ω j ∧ 1 - Ωcum ω j ≤ 1 := by
  induction j with
  | zero => simp [Ωcum_zero]
  | succ j ih =>
    rw [one_sub_Ωcum_succ]
    obtain ⟨h1, h2⟩ := hω (j+1) (by omega)
    obtain ⟨i1, i2⟩ := ih
    constructor <;> nlinarith

lemma step_eq (l D a b R : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) (hR : 0 ≤ R) :
    max 0 (l + a * max ((D - l) / b) R - D) = l + max (D - l) (a * R) - D := by
  set q := (D - l) / b with hq
  have hDl : D - l = q * b := by rw [hq]; field_simp
  rcases le_total q R with h | h
  · rw [max_eq_right h]
    rcases le_total (D - l) (a * R) with h2 | h2
    · rw [max_eq_right h2, max_eq_right (by linarith)]
    · rw [max_eq_left h2, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h]
    have hq0 : 0 ≤ q := le_trans hR h
    have h1 : a * R ≤ D - l := by rw [hDl]; nlinarith
    rw [max_eq_left h1, max_eq_left]
    · ring
    · nlinarith

lemma feas_bounds (X a b R : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) (hR : 0 ≤ R) :
    a * max (X / b) R ≤ max X (a * R) ∧ max X (a * R) ≤ b * max (X / b) R := by
  have hXb : b * (X / b) = X := by field_simp
  constructor
  · rcases le_total (X / b) R with h | h
    · rw [max_eq_right h]; exact le_max_right _ _
    · rw [max_eq_left h]
      have hX0 : 0 ≤ X / b := le_trans hR h
      have : a * (X / b) ≤ b * (X / b) := mul_le_mul_of_nonneg_right hab hX0
      rw [hXb] at this
      exact le_trans this (le_max_left _ _)
  · apply max_le
    · calc X = b * (X / b) := hXb.symm
        _ ≤ b * max (X / b) R := mul_le_mul_of_nonneg_left (le_max_left _ _) hb.le
    · calc a * R ≤ b * R := mul_le_mul_of_nonneg_right hab hR
        _ ≤ b * max (X / b) R := mul_le_mul_of_nonneg_left (le_max_right _ _) hb.le

lemma G_mono (G : ℝ → ℝ) (hG : ConvexOn ℝ Set.univ G) (hG0 : ∀ y, G 0 ≤ G y) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) : G a ≤ G b := by
  rcases eq_or_lt_of_le (le_trans ha hab) with hb | hb
  · exact (congrArg G (by linarith : a = b)).le
  · have h1 : 0 ≤ 1 - a / b := by rw [sub_nonneg, div_le_one hb]; exact hab
    have h2 : 0 ≤ a / b := div_nonneg ha hb.le
    have key := hG.2 (Set.mem_univ 0) (Set.mem_univ b) h1 h2 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add] at key
    have e : a / b * b = a := by field_simp
    rw [e] at key
    nlinarith [mul_nonneg h1 (sub_nonneg.mpr (hG0 b))]

/-! ### One period of the MC policy and the (F-OLFC) program -/

lemma proj_zero (P : QFParams) (I : ℝ) (r F : ℕ → ℝ) : proj P I r F 0 = I := rfl

lemma proj_succ (P : QFParams) (I : ℝ) (r F : ℕ → ℝ) (j : ℕ) :
    proj P I r F (j+1) = max 0 (proj P I r F j + (1 - Ωcum P.ωin j) * mcStep P I r F j
      - (1 + Acum P.αout j) * F j) := rfl

lemma lbar_succ (P : QFParams) (I : ℝ) (r F : ℕ → ℝ) (j : ℕ) :
    lbar P I r F (j+1) = lbar P I r F j + pStar P I r F j - (1 + Acum P.αout j) * F j := rfl

lemma mcStep_ge_right (P : QFParams) (I : ℝ) (r F : ℕ → ℝ) (j : ℕ) :
    (1 - P.ωin (j+1)) * r (j+1) ≤ mcStep P I r F j := le_max_right _ _

lemma mcStep_ge_target (P : QFParams) (I : ℝ) (r F : ℕ → ℝ) (j : ℕ) :
    ((1 + Acum P.αout j) * F j - proj P I r F j) / (1 + Acum P.αin j) ≤ mcStep P I r F j :=
  le_max_left _ _

lemma proj_eq_lbar (P : QFParams) (hP : Std P) (I : ℝ) (r F : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j)
    (j : ℕ) : proj P I r F j = lbar P I r F j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hb := one_le_one_add_Acum P.αin (fun q hq => (hP q hq).1) j
    have hΩ := Ωcum_bounds P.ωin (fun q hq => ⟨(hP q hq).2.2.1, (hP q hq).2.2.2.1⟩) j
    have hω := hP (j+1) (by omega)
    have hR : 0 ≤ (1 - P.ωin (j+1)) * r (j+1) :=
      mul_nonneg (by linarith [hω.2.2.2.1]) (hr _)
    have e1 : proj P I r F (j+1) = max 0 (proj P I r F j + (1 - Ωcum P.ωin j) *
        max (((1 + Acum P.αout j) * F j - proj P I r F j) / (1 + Acum P.αin j))
          ((1 - P.ωin (j+1)) * r (j+1)) - (1 + Acum P.αout j) * F j) := rfl
    have e2 : lbar P I r F (j+1) = lbar P I r F j +
        max ((1 + Acum P.αout j) * F j - lbar P I r F j)
          ((1 - Ωcum P.ωin j) * ((1 - P.ωin (j+1)) * r (j+1))) - (1 + Acum P.αout j) * F j := by
      rw [lbar_succ, ← mul_assoc, ← one_sub_Ωcum_succ]
      rfl
    rw [e1, e2, ih]
    exact step_eq _ _ _ _ _ hΩ.1 (by linarith [hΩ.2]) (by linarith) hR

lemma stock_succ (P : QFParams) (I : ℝ) (F p : ℕ → ℝ) (j : ℕ) :
    stock P I F p (j+1) = stock P I F p j + (p (j+1) - (1 + Acum P.αout (j+1)) * F (j+1)) := by
  simp only [stock]
  rw [Finset.sum_range_succ _ (j+1)]
  ring

lemma stock_zero (P : QFParams) (I : ℝ) (F p : ℕ → ℝ) :
    stock P I F p 0 = I + (p 0 - (1 + Acum P.αout 0) * F 0) := by
  simp [stock]

lemma stock_pStar (P : QFParams) (I : ℝ) (r F : ℕ → ℝ) (j : ℕ) :
    stock P I F (pStar P I r F) j = lbar P I r F (j+1) := by
  induction j with
  | zero =>
    rw [stock_zero, lbar_succ]
    show _ = I + _ - _
    ring
  | succ j ih =>
    rw [stock_succ, ih, lbar_succ P I r F (j+1)]
    ring

lemma lbar_nonneg (P : QFParams) (I : ℝ) (r F : ℕ → ℝ) (j : ℕ) :
    0 ≤ lbar P I r F (j+1) := by
  rw [lbar_succ]
  have := le_max_left ((1 + Acum P.αout j) * F j - lbar P I r F j)
    ((1 - Ωcum P.ωin (j+1)) * r (j+1))
  unfold pStar
  linarith

lemma feas_lower (P : QFParams) (hP : Std P) (h : ℕ) (I : ℝ) (r F x p : ℕ → ℝ)
    (hfeas : Feasible P h I r F x p) (j : ℕ) (hj : j ≤ h) :
    (1 - Ωcum P.ωin (j+1)) * r (j+1) ≤ p j := by
  obtain ⟨_, ⟨hx1, _⟩, ⟨hp1, _⟩⟩ := hfeas j hj
  have hΩ := Ωcum_bounds P.ωin (fun q hq => ⟨(hP q hq).2.2.1, (hP q hq).2.2.2.1⟩) j
  rw [one_sub_Ωcum_succ, mul_assoc]
  exact le_trans (mul_le_mul_of_nonneg_left hx1 hΩ.1) hp1

lemma lbar_le_stock (P : QFParams) (hP : Std P) (h : ℕ) (I : ℝ) (r F x p : ℕ → ℝ)
    (hfeas : Feasible P h I r F x p) : ∀ j, j ≤ h → lbar P I r F (j+1) ≤ stock P I F p j := by
  intro j
  induction j with
  | zero =>
    intro hj
    have hs := (hfeas 0 hj).1
    have hL := feas_lower P hP h I r F x p hfeas 0 hj
    rw [stock_zero] at hs ⊢
    rw [lbar_succ]
    unfold pStar
    have hm : max ((1 + Acum P.αout 0) * F 0 - lbar P I r F 0) ((1 - Ωcum P.ωin (0+1)) * r (0+1))
        ≤ p 0 := by
      apply max_le
      · show (1 + Acum P.αout 0) * F 0 - I ≤ p 0
        linarith
      · exact hL
    have e0 : lbar P I r F 0 = I := rfl
    linarith
  | succ j ih =>
    intro hj
    have ih' := ih (by omega)
    have hs := (hfeas (j+1) hj).1
    have hL := feas_lower P hP h I r F x p hfeas (j+1) hj
    rw [stock_succ] at hs ⊢
    rw [lbar_succ]
    unfold pStar
    have hm : max ((1 + Acum P.αout (j+1)) * F (j+1) - lbar P I r F (j+1))
        ((1 - Ωcum P.ωin (j+1+1)) * r (j+1+1))
        ≤ stock P I F p j - lbar P I r F (j+1) + p (j+1) := by
      apply max_le
      · linarith
      · linarith
    linarith

lemma feas20 (P : QFParams) (hP : Std P) (I : ℝ) (r F : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (j : ℕ) :
    (1 - Ωcum P.ωin j) * mcStep P I r F j ≤ pStar P I r F j ∧
      pStar P I r F j ≤ (1 + Acum P.αin j) * mcStep P I r F j := by
  have hb := one_le_one_add_Acum P.αin (fun q hq => (hP q hq).1) j
  have hΩ := Ωcum_bounds P.ωin (fun q hq => ⟨(hP q hq).2.2.1, (hP q hq).2.2.2.1⟩) j
  have hω := hP (j+1) (by omega)
  have hR : 0 ≤ (1 - P.ωin (j+1)) * r (j+1) :=
    mul_nonneg (by linarith [hω.2.2.2.1]) (hr _)
  have e1 : mcStep P I r F j = max (((1 + Acum P.αout j) * F j - lbar P I r F j) /
      (1 + Acum P.αin j)) ((1 - P.ωin (j+1)) * r (j+1)) := by
    rw [← proj_eq_lbar P hP I r F hr j]
    rfl
  have e2 : pStar P I r F j = max ((1 + Acum P.αout j) * F j - lbar P I r F j)
      ((1 - Ωcum P.ωin j) * ((1 - P.ωin (j+1)) * r (j+1))) := by
    rw [← mul_assoc, ← one_sub_Ωcum_succ]
    rfl
  rw [e1, e2]
  exact feas_bounds _ _ _ _ hΩ.1 (by linarith [hΩ.2]) (by linarith) hR

/-! ### The MC run -/

lemma sched_nonneg (P : QFParams) (hP : Std P) (I₀ : ℝ) (r₀ : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (hr₀ : ∀ j, 0 ≤ r₀ j) : ∀ t j, 0 ≤ sched P I₀ r₀ f t j := by
  intro t
  induction t with
  | zero => exact hr₀
  | succ t ih =>
    intro j
    rw [sched_succ]
    have hω := hP (j+1) (by omega)
    exact le_trans (mul_nonneg (by linarith [hω.2.2.2.1]) (ih (j+1)))
      (mcStep_ge_right _ _ _ _ _)

lemma mcStep_zero_ge (P : QFParams) (I : ℝ) (r F : ℕ → ℝ) :
    F 0 - I ≤ mcStep P I r F 0 := by
  have := mcStep_ge_target P I r F 0
  rw [Acum_zero, Acum_zero, proj_zero] at this
  simpa using this

lemma inv_succ_nonneg (P : QFParams) (I₀ : ℝ) (r₀ : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (t : ℕ) :
    0 ≤ inv P I₀ r₀ f (t+1) := by
  rw [inv_succ, sched_succ]
  have := mcStep_zero_ge P (inv P I₀ r₀ f t) (sched P I₀ r₀ f t) (f (t+1))
  linarith

lemma proj_mono (P : QFParams) (hP : Std P) (I₀ : ℝ) (r₀ : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (hr₀ : ∀ j, 0 ≤ r₀ j) (hf : IROut P f) (s : ℕ) : ∀ j,
    proj P (inv P I₀ r₀ f s) (sched P I₀ r₀ f s) (f (s+1)) (j+1) ≤
      proj P (inv P I₀ r₀ f (s+1)) (sched P I₀ r₀ f (s+1)) (f (s+1+1)) j := by
  intro j
  induction j with
  | zero =>
    rw [proj_succ, proj_zero, proj_zero, Ωcum_zero, Acum_zero]
    simp only [sub_zero, add_zero, one_mul]
    have hI := inv_succ_nonneg P I₀ r₀ f s
    have e := inv_succ P I₀ r₀ f s
    have e2 := sched_succ P I₀ r₀ f s
    rw [e2] at e
    apply max_le hI
    linarith
  | succ j ih =>
    rw [proj_succ P (inv P I₀ r₀ f s), proj_succ P (inv P I₀ r₀ f (s+1))]
    apply max_le_max (le_refl 0)
    have hω := hP (j+1) (by omega)
    have hΩ := Ωcum_bounds P.ωin (fun q hq => ⟨(hP q hq).2.2.1, (hP q hq).2.2.2.1⟩) j
    have hA := one_le_one_add_Acum P.αout (fun q hq => (hP q hq).2.1) j
    have h1 : (1 - Ωcum P.ωin (j+1)) * mcStep P (inv P I₀ r₀ f s) (sched P I₀ r₀ f s) (f (s+1)) (j+1)
        ≤ (1 - Ωcum P.ωin j) *
          mcStep P (inv P I₀ r₀ f (s+1)) (sched P I₀ r₀ f (s+1)) (f (s+1+1)) j := by
      rw [one_sub_Ωcum_succ, mul_assoc, ← sched_succ]
      exact mul_le_mul_of_nonneg_left (mcStep_ge_right _ _ _ _ _) hΩ.1
    have h2 : (1 + Acum P.αout j) * f (s+1+1) j ≤
        (1 + Acum P.αout (j+1)) * f (s+1) (j+1) := by
      rw [one_add_Acum_succ, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hf (s+1) j).2 (by linarith)
    linarith

lemma IRIn_succ (P : QFParams) (hP : Std P) (I₀ : ℝ) (r₀ : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (hr₀ : ∀ j, 0 ≤ r₀ j) (hf : IROut P f) (s : ℕ) :
    IRIn P (sched P I₀ r₀ f) (s+1) := by
  intro j
  have hω := hP (j+1) (by omega)
  have hnn := sched_nonneg P hP I₀ r₀ f hr₀ (s+1) (j+1)
  rw [sched_succ P I₀ r₀ f (s+1)]
  refine ⟨mcStep_ge_right _ _ _ _ _, ?_⟩
  apply max_le
  · -- the target is below the upper input bound
    have hT := mcStep_ge_target P (inv P I₀ r₀ f s) (sched P I₀ r₀ f s) (f (s+1)) (j+1)
    rw [← sched_succ] at hT
    have hb := one_le_one_add_Acum P.αin (fun q hq => (hP q hq).1) j
    have hA := one_le_one_add_Acum P.αout (fun q hq => (hP q hq).2.1) j
    have hmono := proj_mono P hP I₀ r₀ f hr₀ hf s j
    have hfj := (hf (s+1) j).2
    rw [one_add_Acum_succ P.αin, one_add_Acum_succ P.αout] at hT
    have hbβ : 0 < (1 + Acum P.αin j) * (1 + P.αin (j+1)) := by nlinarith [hω.1]
    rw [div_le_iff₀ hbβ] at hT
    show ((1 + Acum P.αout j) * f (s+1+1) j -
        proj P (inv P I₀ r₀ f (s+1)) (sched P I₀ r₀ f (s+1)) (f (s+1+1)) j) /
        (1 + Acum P.αin j) ≤ _
    rw [div_le_iff₀ (by linarith)]
    have h2 : (1 + Acum P.αout j) * f (s+1+1) j ≤
        (1 + Acum P.αout j) * ((1 + P.αout (j+1)) * f (s+1) (j+1)) :=
      mul_le_mul_of_nonneg_left hfj (by linarith)
    nlinarith
  · nlinarith [hω.1, hω.2.2.1]

end P4d564611

open QFlexSC.MCOpt in
theorem solution (P : QFlexSC.ZeroInv.QFParams) (f : ℕ → ℕ → ℝ) (I₀ : ℝ) (r₀ : ℕ → ℝ) (h : ℕ)
    (G : ℝ → ℝ)
    (hP : ∀ q, 1 ≤ q → 0 ≤ P.αin q ∧ 0 ≤ P.αout q ∧ 0 ≤ P.ωin q ∧ P.ωin q ≤ 1 ∧
      0 ≤ P.ωout q ∧ P.ωout q ≤ 1)
    (hr₀ : ∀ j, 0 ≤ r₀ j) (hf : QFlexSC.ZeroInv.IROut P f)
    (hG : ConvexOn ℝ Set.univ G) (hG0 : ∀ y, G 0 ≤ G y) :
    (∀ t, 1 ≤ t → 0 ≤ QFlexSC.ZeroInv.inv P I₀ r₀ f t) ∧
    ∀ t, 1 ≤ t →
      QFlexSC.ZeroInv.IRIn P (QFlexSC.ZeroInv.sched P I₀ r₀ f) t ∧
      ∃ p, Feasible P h (QFlexSC.ZeroInv.inv P I₀ r₀ f t) (QFlexSC.ZeroInv.sched P I₀ r₀ f t) (f (t+1))
          (QFlexSC.ZeroInv.sched P I₀ r₀ f (t+1)) p ∧
        ∀ x' p', Feasible P h (QFlexSC.ZeroInv.inv P I₀ r₀ f t) (QFlexSC.ZeroInv.sched P I₀ r₀ f t) (f (t+1)) x' p' →
          objective G P h (QFlexSC.ZeroInv.inv P I₀ r₀ f t) (f (t+1)) p ≤
            objective G P h (QFlexSC.ZeroInv.inv P I₀ r₀ f t) (f (t+1)) p' := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    exact P4d564611.inv_succ_nonneg P I₀ r₀ f s
  · intro t ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hIR := P4d564611.IRIn_succ P hP I₀ r₀ f hr₀ hf s
    have hnn := P4d564611.sched_nonneg P hP I₀ r₀ f hr₀ (s+1)
    refine ⟨hIR, pStar P (QFlexSC.ZeroInv.inv P I₀ r₀ f (s+1))
      (QFlexSC.ZeroInv.sched P I₀ r₀ f (s+1)) (f (s+1+1)), ?_, ?_⟩
    · intro j hj
      have h20 := P4d564611.feas20 P hP (QFlexSC.ZeroInv.inv P I₀ r₀ f (s+1))
        (QFlexSC.ZeroInv.sched P I₀ r₀ f (s+1)) (f (s+1+1)) hnn j
      refine ⟨?_, hIR j, h20⟩
      rw [P4d564611.stock_pStar]
      exact P4d564611.lbar_nonneg _ _ _ _ _
    · intro x' p' hfeas
      unfold objective
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ≤ h := by rw [Finset.mem_range] at hj; omega
      rw [P4d564611.stock_pStar]
      exact P4d564611.G_mono G hG hG0 (P4d564611.lbar_nonneg _ _ _ _ _)
        (P4d564611.lbar_le_stock P hP h _ _ _ x' p' hfeas j hj')
