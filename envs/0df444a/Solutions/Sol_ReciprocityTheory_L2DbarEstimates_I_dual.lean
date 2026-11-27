-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:30:59.281455+00:00
-- url     : https://prove2.me/submissions/86fb4879-414b-4745-af42-9f05aa5f423f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_AddLogPosOfThreeQuartersLe
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_dualK_contDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_dualK_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_dualK_deriv
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_dual_dbarDot_comp_real
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_ckR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
universe u
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (n : ℕ) (M : Type u) [TopologicalSpace M]
    (hT : TwistLeviStatement n M) (hB : BasicStatement n M) : DualStatement n M := by
  intro z g ph ph2 r j ε δ hz hg hph hphL hph2 hph2L hr hj hε hδ hbd
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun x ξ => ?_, fun x ξ _ => ?_, fun x ξ _ => ?_⟩ <;> simp [dbarDot, Levi]
  obtain ⟨hB1, -, -, -⟩ := hB g ph ph2 r j ε δ hr hε hbd
  obtain ⟨-, -, hT1, hT2⟩ := hT z g ph ph2 r j ε δ hz hg hph hphL hph2 hph2L hr hj hε hδ hbd
  obtain ⟨hW, -, -, -⟩ := hT z g ph ph2 r j ε ε hz hg hph hphL hph2 hph2L hr hj hε hε hbd
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlw : SmoothR n z (lw n g ph r ε) := by
    have e : (fun y => (lw n g ph r ε y : ℂ)) = fun y => (1 / (n : ℂ)) *
        (((wgt n g ph ph2 r j ε y : ℝ) : ℂ) - (ph2 y : ℂ) - ((n : ℂ) + j) * (ph y : ℂ)) := by
      funext y
      unfold wgt
      push_cast
      field_simp
      ring
    unfold SmoothR
    rw [e]
    exact Smooth.mul _ _ _ _ (Smooth.const _ _ _)
      (Smooth.sub _ _ _ _ (Smooth.sub _ _ _ _ hW hph2) (Smooth.mul _ _ _ _ (Smooth.const _ _ _) hph))
  have hlw1 : CkR n z 1 (lw n g ph r ε) := SmoothR.ckR n z 1 _ hlw
  have hev0 : ∀ y, 0 ≤ ev n g ph r y := fun y => by unfold ev; positivity
  have hxx : ∀ y, xx n g ph r ε y = (1 + Real.log (1 + ε ^ 2)) - lw n g ph r ε y := fun y => rfl
  have htw : (fun y => (twist n g ph r ε y : ℂ)) =
      fun y => ((dualK (1 + Real.log (1 + ε ^ 2)) (lw n g ph r ε y) : ℝ) : ℂ) := by
    funext y
    rw [dualK_eq (by rw [← hxx]; linarith [(hB1 y).1])]
    unfold twist eta
    rw [hxx]
  have hevf : (fun y => (ev n g ph r y : ℂ)) =
      fun y => (((fun t => Real.exp t - ε ^ 2) (lw n g ph r ε y) : ℝ) : ℂ) := by
    funext y
    simp only
    unfold lw
    rw [Real.exp_log (by have := hev0 y; positivity)]
    push_cast
    ring
  have hnT : ∀ x ξ, ‖dbarDot n z (fun y => (twist n g ph r ε y : ℂ)) x ξ‖ =
      kap n g ph r ε x / eta n g ph r ε x * ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ := by
    intro x ξ
    rw [htw, dual_dbarDot_comp_real n z _ (dualK_contDiff _) _ hlw1,
      dualK_deriv (by rw [← hxx]; exact (hB1 x).1)]
    rw [← hxx]
    congr 1
    rw [abs_of_nonneg]
    · rfl
    · have h1 := (hB1 x).1
      have h2 := (hB1 x).2.1
      unfold eta at h2
      positivity
  have hnE : ∀ x ξ, ‖dbarDot n z (fun y => (ev n g ph r y : ℂ)) x ξ‖ =
      (ev n g ph r x + ε ^ 2) * ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ := by
    intro x ξ
    rw [hevf, dual_dbarDot_comp_real n z _ (Real.contDiff_exp.sub contDiff_const) _ hlw1]
    congr 1
    simp only [deriv_sub_const, Real.deriv_exp]
    unfold lw
    rw [Real.exp_log (by have := hev0 x; positivity), abs_of_nonneg (by have := hev0 x; positivity)]
  refine ⟨fun x ξ => ?_, fun x ξ hx => ?_, fun x ξ hx => ?_⟩
  · rw [hnT]
    set X := xx n g ph r ε x
    set E := eta n g ph r ε x
    set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖
    set Θ := (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re
    have h1 := hT1 x ξ
    have hX : 1 ≤ X := (hB1 x).1
    have hE : 1 ≤ E := (hB1 x).2.1
    have hk : kap n g ph r ε x = 1 + 1 / X := rfl
    have hb : bfun n g ph r ε x = (X + 1) ^ 2 / ((X + 1) ^ 2 + E) := rfl
    rw [hk] at h1 ⊢
    rw [hb]
    have hid : ((1 + 1 / X) / E) ^ 2 =
        (X + 1) ^ 2 / ((X + 1) ^ 2 + E) * (1 / (X ^ 2 * E) + ((1 + 1 / X) / E) ^ 2) := by
      have : X ≠ 0 := by positivity
      have : E ≠ 0 := by positivity
      have : (X + 1) ^ 2 + E ≠ 0 := by positivity
      field_simp
      ring
    rw [mul_pow, hid, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · rw [hnT]
    set X := xx n g ph r ε x
    set E := eta n g ph r ε x
    set K := kap n g ph r ε x
    set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖
    set Θ := (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re
    have h1 := hT1 x ξ
    have h2 := hT2 x ξ hx
    have hX : 1 ≤ X := (hB1 x).1
    have hE : 1 ≤ E := (hB1 x).2.1
    have hK2 : K ≤ 2 := (hB1 x).2.2.1
    have hK1 : 1 ≤ K := by
      have : K = 1 + 1 / X := rfl
      rw [this]
      have : 0 < 1 / X := by positivity
      linarith
    have hΘ : 0 ≤ Θ := le_trans (by positivity) h1
    have hE0 : 0 < E := by linarith
    calc (K / E * D) ^ 2 = K / E ^ 2 * (K * D ^ 2) := by field_simp
      _ ≤ K / E ^ 2 * (E * Θ) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = K / E * Θ := by field_simp
      _ ≤ 2 / E * Θ := mul_le_mul_of_nonneg_right (by gcongr) hΘ
  · rw [hnE]
    set E := eta n g ph r ε x
    set K := kap n g ph r ε x
    set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖
    set Θ := (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re
    have h2 := hT2 x ξ hx
    have hK1 : 1 ≤ K := by
      have : K = 1 + 1 / xx n g ph r ε x := rfl
      rw [this]
      have : 0 < 1 / xx n g ph r ε x := by have := (hB1 x).1; positivity
      linarith
    have hev := hev0 x
    have hQ : (ev n g ph r x + ε ^ 2) ^ 2 ≤ 4 * ε ^ 4 := by nlinarith
    have hD : D ^ 2 ≤ E * Θ := le_trans (le_mul_of_one_le_left (by positivity) hK1) h2
    calc ((ev n g ph r x + ε ^ 2) * D) ^ 2 = (ev n g ph r x + ε ^ 2) ^ 2 * D ^ 2 := by ring
      _ ≤ 4 * ε ^ 4 * D ^ 2 := mul_le_mul_of_nonneg_right hQ (by positivity)
      _ ≤ 4 * ε ^ 4 * (E * Θ) := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = 4 * ε ^ 4 * E * Θ := by ring
end ReciprocityTheory.L2DbarEstimates.I
