-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P41.classical_variational_duality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T19:08:07.729988+00:00
-- url     : https://prove2.me/submissions/143689cf-4258-4f55-b32d-b03a1a6dc8de

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P41

noncomputable section

open scoped BigOperators

namespace X6G41C

open QAlgorithms.Papers.Independent.Gap48.P41
open QAlgorithms.Papers.Independent.Dependency50.P28 (scalarPower classicalD)
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X : Type} [Fintype X]

abbrev KL (a b : X → ℝ) : EReal := classicalD (.finite 1 (by norm_num)) a b

def klSum (a b : X → ℝ) : ℝ := ∑ x, if 0 < a x then a x * Real.log (a x / b x) else 0

lemma kl_eq (a b : X → ℝ) :
    KL a b = if (∀ x, 0 < a x → 0 < b x) then ((klSum a b : ℝ) : EReal) else ⊤ := by
  simp [KL, classicalD, klSum]

lemma kl_of_supp {a b : X → ℝ} (h : ∀ x, 0 < a x → 0 < b x) : KL a b = ((klSum a b : ℝ) : EReal) := by
  rw [kl_eq, if_pos h]

lemma supp_of_kl_ne_top {a b : X → ℝ} (h : KL a b ≠ ⊤) : ∀ x, 0 < a x → 0 < b x := by
  by_contra hc
  rw [kl_eq, if_neg hc] at h
  exact h rfl

/-- Gibbs inequality. -/
lemma gibbs (a u : X → ℝ) (ha : IsLaw a) (hu0 : ∀ x, 0 ≤ u x) (hu : ∑ x, u x = 1)
    (hsupp : ∀ x, 0 < a x → 0 < u x) : 0 ≤ klSum a u := by
  have key : ∀ x, (if 0 < a x then a x * Real.log (u x / a x) else 0) ≤
      (if 0 < a x then u x else 0) - a x := by
    intro x
    split_ifs with h
    · have h1 := Real.log_le_sub_one_of_pos (div_pos (hsupp x h) h)
      have := mul_le_mul_of_nonneg_left h1 h.le
      rw [mul_sub, mul_div_cancel₀ _ h.ne', mul_one] at this
      exact this
    · have := ha.1 x
      have : a x = 0 := le_antisymm (not_lt.mp h) this
      linarith
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => key x)
  rw [Finset.sum_sub_distrib, ha.2] at hs
  have h2 : ∑ x, (if 0 < a x then u x else 0) ≤ ∑ x, u x :=
    Finset.sum_le_sum (fun x _ => by split_ifs <;> [exact le_refl _; exact hu0 x])
  have e : klSum a u = -∑ x, (if 0 < a x then a x * Real.log (u x / a x) else 0) := by
    rw [klSum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs with h
    · rw [← mul_neg, ← Real.log_inv, inv_div]
    · simp
  rw [e]
  linarith

section tilt

variable (p q : X → ℝ)

def Z (s : ℝ) : ℝ := ∑ x, scalarPower (p x) (1 + s) * scalarPower (q x) (-s)

lemma sp_pos {x t : ℝ} (hx : 0 < x) : scalarPower x t = Real.exp (t * Real.log x) := by
  rw [scalarPower, if_pos hx, Real.rpow_eq_pow, Real.rpow_def_of_pos hx, mul_comm]

lemma sp_nonneg (x t : ℝ) : 0 ≤ scalarPower x t := by
  unfold scalarPower; split_ifs with h
  · exact Real.rpow_nonneg h.le _
  · exact le_refl _

variable {p q}

lemma term_pos (hsupp : ∀ x, 0 < p x → 0 < q x) (s : ℝ) {x : X} (hx : 0 < p x) :
    0 < scalarPower (p x) (1 + s) * scalarPower (q x) (-s) := by
  rw [sp_pos hx, sp_pos (hsupp x hx)]; positivity

lemma term_zero {x : X} (hx : ¬ 0 < p x) (s : ℝ) :
    scalarPower (p x) (1 + s) * scalarPower (q x) (-s) = 0 := by
  rw [scalarPower, if_neg hx, zero_mul]

lemma Z_pos (hp : IsLaw p) (hsupp : ∀ x, 0 < p x → 0 < q x) (s : ℝ) : 0 < Z p q s := by
  obtain ⟨x, hx⟩ : ∃ x, 0 < p x := by
    by_contra h
    push Not at h
    have : ∑ x, p x = 0 := Finset.sum_eq_zero (fun x _ => le_antisymm (h x) (hp.1 x))
    rw [hp.2] at this; exact one_ne_zero this
  calc 0 < scalarPower (p x) (1 + s) * scalarPower (q x) (-s) := term_pos hsupp s hx
    _ ≤ Z p q s := Finset.single_le_sum
        (f := fun x => scalarPower (p x) (1 + s) * scalarPower (q x) (-s))
        (fun y _ => mul_nonneg (sp_nonneg _ _) (sp_nonneg _ _)) (Finset.mem_univ x)

lemma psi_eq (s : ℝ) : classicalPsi p q s = Real.log (Z p q s) := rfl

lemma tilt_apply (s : ℝ) (x : X) :
    tilt p q s x = Real.exp (-classicalPsi p q s) *
      (scalarPower (p x) (1 + s) * scalarPower (q x) (-s)) := by
  rw [tilt, mul_assoc]

lemma tilt_sum (hp : IsLaw p) (hsupp : ∀ x, 0 < p x → 0 < q x) (s : ℝ) :
    ∑ x, tilt p q s x = 1 := by
  simp only [tilt_apply, ← Finset.mul_sum]
  rw [psi_eq, Real.exp_neg, Real.exp_log (Z_pos hp hsupp s)]
  exact inv_mul_cancel₀ (Z_pos hp hsupp s).ne'

lemma tilt_nonneg (s : ℝ) (x : X) : 0 ≤ tilt p q s x := by
  rw [tilt_apply]; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (sp_nonneg _ _) (sp_nonneg _ _))

lemma tilt_pos_iff (hsupp : ∀ x, 0 < p x → 0 < q x) (s : ℝ) (x : X) :
    0 < tilt p q s x ↔ 0 < p x := by
  constructor
  · intro h
    by_contra hx
    rw [tilt_apply, term_zero hx, mul_zero] at h
    exact lt_irrefl _ h
  · intro hx
    rw [tilt_apply]; exact mul_pos (Real.exp_pos _) (term_pos hsupp s hx)

lemma tilt_law (hp : IsLaw p) (hsupp : ∀ x, 0 < p x → 0 < q x) (s : ℝ) : IsLaw (tilt p q s) :=
  ⟨tilt_nonneg s, tilt_sum hp hsupp s⟩

lemma log_tilt (hsupp : ∀ x, 0 < p x → 0 < q x) (s : ℝ) {x : X} (hx : 0 < p x) :
    Real.log (tilt p q s x) =
      -classicalPsi p q s + (1 + s) * Real.log (p x) - s * Real.log (q x) := by
  rw [tilt_apply, sp_pos hx, sp_pos (hsupp x hx), ← Real.exp_add, ← Real.exp_add,
    Real.log_exp]
  ring

/-- `D(p_s ‖ p) = s η - ψ` -/
lemma kl_tilt_p (hp : IsLaw p) (hsupp : ∀ x, 0 < p x → 0 < q x) (s : ℝ) :
    klSum (tilt p q s) p = s * tiltedLogLikelihood p q s - classicalPsi p q s := by
  have e : ∀ x, (if 0 < tilt p q s x then tilt p q s x * Real.log (tilt p q s x / p x) else 0) =
      s * (if 0 < p x then tilt p q s x * Real.log (p x / q x) else 0) -
        classicalPsi p q s * tilt p q s x := by
    intro x
    by_cases hx : 0 < p x
    · rw [if_pos ((tilt_pos_iff hsupp s x).mpr hx), if_pos hx,
        Real.log_div ((tilt_pos_iff hsupp s x).mpr hx).ne' hx.ne', log_tilt hsupp s hx,
        Real.log_div hx.ne' (hsupp x hx).ne']
      ring
    · rw [if_neg (by rwa [tilt_pos_iff hsupp s x]), if_neg hx, tilt_apply, term_zero hx]
      ring
  rw [klSum, Finset.sum_congr rfl (fun x _ => e x), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, tilt_sum hp hsupp, mul_one, tiltedLogLikelihood]

/-- `D(p_s ‖ q) = (1+s) η - ψ` -/
lemma kl_tilt_q (hp : IsLaw p) (hsupp : ∀ x, 0 < p x → 0 < q x) (s : ℝ) :
    klSum (tilt p q s) q = (1 + s) * tiltedLogLikelihood p q s - classicalPsi p q s := by
  have e : ∀ x, (if 0 < tilt p q s x then tilt p q s x * Real.log (tilt p q s x / q x) else 0) =
      (1 + s) * (if 0 < p x then tilt p q s x * Real.log (p x / q x) else 0) -
        classicalPsi p q s * tilt p q s x := by
    intro x
    by_cases hx : 0 < p x
    · rw [if_pos ((tilt_pos_iff hsupp s x).mpr hx), if_pos hx,
        Real.log_div ((tilt_pos_iff hsupp s x).mpr hx).ne' (hsupp x hx).ne', log_tilt hsupp s hx,
        Real.log_div hx.ne' (hsupp x hx).ne']
      ring
    · rw [if_neg (by rwa [tilt_pos_iff hsupp s x]), if_neg hx, tilt_apply, term_zero hx]
      ring
  rw [klSum, Finset.sum_congr rfl (fun x _ => e x), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, tilt_sum hp hsupp, mul_one, tiltedLogLikelihood]

/-- Gibbs against the tilt: `(1+s) D(a‖p) - s D(a‖q) + ψ(s) ≥ 0`. -/
lemma gibbs_tilt (hp : IsLaw p) (hsupp : ∀ x, 0 < p x → 0 < q x) (s : ℝ) (a : X → ℝ)
    (ha : IsLaw a) (hap : ∀ x, 0 < a x → 0 < p x) :
    0 ≤ (1 + s) * klSum a p - s * klSum a q + classicalPsi p q s := by
  have hg := gibbs a (tilt p q s) ha (tilt_nonneg s) (tilt_sum hp hsupp s)
    (fun x hx => (tilt_pos_iff hsupp s x).mpr (hap x hx))
  have e : klSum a (tilt p q s) = (1 + s) * klSum a p - s * klSum a q + classicalPsi p q s := by
    have e1 : ∀ x, (if 0 < a x then a x * Real.log (a x / tilt p q s x) else 0) =
        (1 + s) * (if 0 < a x then a x * Real.log (a x / p x) else 0) -
          s * (if 0 < a x then a x * Real.log (a x / q x) else 0) + classicalPsi p q s * a x := by
      intro x
      by_cases hx : 0 < a x
      · have hpx := hap x hx
        rw [if_pos hx, if_pos hx, if_pos hx,
          Real.log_div hx.ne' ((tilt_pos_iff hsupp s x).mpr hpx).ne', log_tilt hsupp s hpx,
          Real.log_div hx.ne' hpx.ne', Real.log_div hx.ne' (hsupp x hpx).ne']
        ring
      · rw [if_neg hx, if_neg hx, if_neg hx]
        have : a x = 0 := le_antisymm (not_lt.mp hx) (ha.1 x)
        rw [this]; ring
    rw [klSum, Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ha.2,
      mul_one, klSum, klSum]
  rw [← e]; exact hg

/-- Weak duality. -/
lemma weak (hp : IsLaw p) (hsupp : ∀ x, 0 < p x → 0 < q x) (r s : ℝ) (hs : 0 ≤ s)
    (a : X → ℝ) (ha : IsLaw a) (hr : KL a q ≤ (r : EReal)) :
    ((classicalG p q r s : ℝ) : EReal) ≤ KL a p + (r : EReal) - KL a q := by
  have hne : KL a q ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top r) hr
  have haq := supp_of_kl_ne_top hne
  rw [kl_of_supp haq] at hr ⊢
  have hB : klSum a q ≤ r := EReal.coe_le_coe_iff.mp hr
  by_cases hap : ∀ x, 0 < a x → 0 < p x
  · rw [kl_of_supp hap, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    have hg := gibbs_tilt hp hsupp s a ha hap
    rw [classicalG, div_mul_eq_mul_div, ← sub_div, div_le_iff₀ (by linarith)]
    nlinarith
  · rw [kl_eq, if_neg hap, EReal.top_add_coe, EReal.top_sub_coe]
    exact le_top

end tilt

end X6G41C


noncomputable section

namespace X6G41C

open QAlgorithms.Papers.Independent.Gap48.P41
open QAlgorithms.Papers.Independent.Dependency50.P28 (scalarPower classicalD)
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X : Type} [Fintype X]

theorem main (p q : X → ℝ) (hp : IsLaw p) (hq : IsLaw q) (r t : ℝ)
    (hr : KL p q < (r : EReal)) (ht : 0 < t)
    (hlevel : KL (tilt p q t) q = (r : EReal)) :
    IsLaw (tilt p q t) ∧
    IsLeast (classicalValues p q r) (KL (tilt p q t) p) ∧
    classicalMinimum p q r = KL (tilt p q t) p ∧
    classicalMinimum p q r = (classicalG p q r t : EReal) ∧
    IsGreatest (classicalDualValues p q r) (classicalMinimum p q r) ∧
    classicalMinimum p q r = ((t * tiltedLogLikelihood p q t - classicalPsi p q t : ℝ) : EReal) ∧
    r = (1 + t) * tiltedLogLikelihood p q t - classicalPsi p q t := by
  have hsupp := supp_of_kl_ne_top (ne_top_of_lt hr)
  have hlaw := tilt_law hp hsupp t
  have htq : ∀ x, 0 < tilt p q t x → 0 < q x := fun x hx =>
    hsupp x ((tilt_pos_iff hsupp t x).mp hx)
  have htp : ∀ x, 0 < tilt p q t x → 0 < p x := fun x hx => (tilt_pos_iff hsupp t x).mp hx
  have hKq : KL (tilt p q t) q = (((1 + t) * tiltedLogLikelihood p q t - classicalPsi p q t : ℝ) : EReal) := by
    rw [kl_of_supp htq, kl_tilt_q hp hsupp t]
  have hKp : KL (tilt p q t) p = ((t * tiltedLogLikelihood p q t - classicalPsi p q t : ℝ) : EReal) := by
    rw [kl_of_supp htp, kl_tilt_p hp hsupp t]
  have hrr : r = (1 + t) * tiltedLogLikelihood p q t - classicalPsi p q t := by
    rw [hKq] at hlevel; exact (EReal.coe_eq_coe_iff.mp hlevel).symm
  have hG : classicalG p q r t = t * tiltedLogLikelihood p q t - classicalPsi p q t := by
    rw [classicalG, hrr]; field_simp; ring
  have hval : KL (tilt p q t) p + (r : EReal) - KL (tilt p q t) q = KL (tilt p q t) p := by
    rw [hlevel, hKp, ← EReal.coe_add, ← EReal.coe_sub, add_sub_cancel_right]
  have hmem : KL (tilt p q t) p ∈ classicalValues p q r :=
    ⟨tilt p q t, hlaw, hlevel.le, hval.symm⟩
  have hlb : ∀ v ∈ classicalValues p q r, KL (tilt p q t) p ≤ v := by
    rintro v ⟨a, ha, har, rfl⟩
    have := weak hp hsupp r t ht.le a ha har
    rwa [hG, ← hKp] at this
  have hleast : IsLeast (classicalValues p q r) (KL (tilt p q t) p) := ⟨hmem, hlb⟩
  have hmin : classicalMinimum p q r = KL (tilt p q t) p := hleast.csInf_eq
  refine ⟨hlaw, hleast, hmin, by rw [hmin, hKp, hG], ⟨⟨t, ht.le, by rw [hmin, hKp, hG]⟩, ?_⟩,
    by rw [hmin, hKp], hrr⟩
  rintro _ ⟨s, hs, rfl⟩
  rw [hmin, ← hval]
  exact weak hp hsupp r s hs _ hlaw hlevel.le

end X6G41C


open QAlgorithms.Papers.Independent.Gap48.P41
open QAlgorithms.Papers.Independent.Dependency50.P28 (scalarPower classicalD)
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X : Type} [Fintype X]

theorem solution [Nonempty X]
    (p q : X → ℝ) (hp : IsLaw p) (hq : IsLaw q) (r t : ℝ)
    (hr : classicalD (.finite 1 (by norm_num)) p q < (r : EReal)) (ht : 0 < t)
    (hlevel : classicalD (.finite 1 (by norm_num)) (tilt p q t) q = (r : EReal)) :
    IsLaw (tilt p q t) ∧
    IsLeast (classicalValues p q r) (classicalD (.finite 1 (by norm_num)) (tilt p q t) p) ∧
    classicalMinimum p q r = classicalD (.finite 1 (by norm_num)) (tilt p q t) p ∧
    classicalMinimum p q r = (classicalG p q r t : EReal) ∧
    IsGreatest (classicalDualValues p q r) (classicalMinimum p q r) ∧
    classicalMinimum p q r = ((t * tiltedLogLikelihood p q t - classicalPsi p q t : ℝ) : EReal) ∧
    r = (1 + t) * tiltedLogLikelihood p q t - classicalPsi p q t :=
  X6G41C.main p q hp hq r t hr ht hlevel
