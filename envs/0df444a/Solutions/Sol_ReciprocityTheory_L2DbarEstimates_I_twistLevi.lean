-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.twistLevi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:29:55.999928+00:00
-- url     : https://prove2.me/submissions/0e31889e-dc74-4af7-b8f9-0860a9bc22fc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwistLeviA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwistLevi
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tlK_contDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_levi_formula
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_lw_smoothR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_twist_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_smoothR_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (n : ℕ) (M : Type u) [TopologicalSpace M]
    (hLog : LogLeviStatement n M) (hCh : ChainStatement n M) (hB : BasicStatement n M) :
    TwistLeviStatement n M := by
  intro z g ph ph2 r j ε δ hz hg hph hLph hph2 hLph2 hr hj hε hδ hbd
  set c := 1 + Real.log (1 + ε ^ 2) with hc
  have hlε := tl_lw_smoothR n z g ph r ε hg hph hε
  have hlδ := tl_lw_smoothR n z g ph r δ hg hph hδ
  have hwgt : SmoothR n z (wgt n g ph ph2 r j δ) :=
    SmoothR.add n z _ _ (SmoothR.add n z _ _ hph2 (SmoothR.mul n z _ _ (smoothR_const n z _) hph))
      (SmoothR.mul n z _ _ (smoothR_const n z _) hlδ)
  have htw : SmoothR n z (twist n g ph r ε) := by
    rw [tl_twist_eq n g ph r ε hr hε hbd]; exact SmoothR.comp n z _ (tlK_contDiff c) _ hlε
  obtain ⟨hB1, -, -, -⟩ := hB g ph ph2 r j ε δ hr hε hbd
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj

  have key : ∀ x ξ,
      tlKpp c (lw n g ph r ε x) * ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 +
        tlKp c (lw n g ph r ε x) * ((Levi n z (lw n g ph r ε) x ξ).re + (Levi n z ph x ξ).re) ≤
      (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re := by
    intro x ξ
    rw [tl_levi_formula n hCh z g ph ph2 r j ε δ hz hg hph hph2 hr hε hδ hbd x ξ]
    obtain ⟨hx1, he1, hk2, -⟩ := hB1 x
    have hq : tlKp c (lw n g ph r ε x) = kap n g ph r ε x / eta n g ph r ε x := rfl
    have hq0 : 0 ≤ kap n g ph r ε x / eta n g ph r ε x := by
      unfold kap; have : 0 ≤ 1 / xx n g ph r ε x := by positivity
      exact div_nonneg (by linarith) (by linarith)
    have hq2 : kap n g ph r ε x / eta n g ph r ε x ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hL2 := hLph2 x ξ
    have hL := hLph x ξ
    have hδL := (hLog z g ph r δ hz hg hph hLph hr.ne' hδ x ξ).2
    have h1 := mul_nonneg (show 0 ≤ (j : ℝ) - kap n g ph r ε x / eta n g ph r ε x by linarith) hL
    have h2 := mul_nonneg (show (0 : ℝ) ≤ n by positivity) hδL
    rw [hq]
    nlinarith
  refine ⟨hwgt, htw, ?_, ?_⟩
  · intro x ξ
    have hk := key x ξ
    have hεL := (hLog z g ph r ε hz hg hph hLph hr.ne' hε x ξ).2
    obtain ⟨hx1, he1, hk2, -⟩ := hB1 x
    have hq0 : 0 ≤ tlKp c (lw n g ph r ε x) := by
      show 0 ≤ kap n g ph r ε x / eta n g ph r ε x
      unfold kap; have : 0 ≤ 1 / xx n g ph r ε x := by positivity
      exact div_nonneg (by linarith) (by linarith)
    have := mul_nonneg hq0 hεL
    have e : tlKpp c (lw n g ph r ε x) = 1 / (xx n g ph r ε x ^ 2 * eta n g ph r ε x) +
        (kap n g ph r ε x / eta n g ph r ε x) ^ 2 := rfl
    rw [← e]
    linarith
  · intro x ξ hx
    have hk := key x ξ
    obtain ⟨hε1, hεL⟩ := hLog z g ph r ε hz hg hph hLph hr.ne' hε x ξ
    obtain ⟨hx1, he1, hk2, -⟩ := hB1 x
    set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 with hD
    set A := (Levi n z (lw n g ph r ε) x ξ).re + (Levi n z ph x ξ).re with hAdef
    have hD0 : 0 ≤ D := by positivity
    have hDA : D ≤ A := by
      have hε2 : 0 < ε ^ 2 := by positivity
      have : ε ^ 2 * D ≤ ε ^ 2 * A := hε1.trans (mul_le_mul_of_nonneg_right hx hεL)
      exact le_of_mul_le_mul_left this hε2
    have hq : tlKp c (lw n g ph r ε x) = kap n g ph r ε x / eta n g ph r ε x := rfl
    have hpp : 0 ≤ tlKpp c (lw n g ph r ε x) := by
      show 0 ≤ 1 / (xx n g ph r ε x ^ 2 * eta n g ph r ε x) + (kap n g ph r ε x / eta n g ph r ε x) ^ 2
      have : 0 ≤ 1 / (xx n g ph r ε x ^ 2 * eta n g ph r ε x) :=
        div_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith))
      positivity
    have hq0 : 0 ≤ kap n g ph r ε x / eta n g ph r ε x := by
      unfold kap; have : 0 ≤ 1 / xx n g ph r ε x := by positivity
      exact div_nonneg (by linarith) (by linarith)
    rw [hq] at hk
    have h3 : kap n g ph r ε x / eta n g ph r ε x * D ≤
        (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re := by
      have := mul_le_mul_of_nonneg_left hDA hq0
      have := mul_nonneg hpp hD0
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ eta n g ph r ε x by linarith)
    have h5 : eta n g ph r ε x * (kap n g ph r ε x / eta n g ph r ε x * D) = kap n g ph r ε x * D := by
      field_simp
    linarith
end ReciprocityTheory.L2DbarEstimates.I
