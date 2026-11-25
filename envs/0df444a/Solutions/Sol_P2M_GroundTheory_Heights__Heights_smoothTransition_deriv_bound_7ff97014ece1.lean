-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_smoothTransition_deriv_bound_7ff97014ece1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:57:41.064526+00:00
-- url     : https://prove2.me/submissions/e9e4dfdd-ddd0-4295-9f5e-9e32733dbb5f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHessDeriv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothTransition_eventually_const_a4054d9cca03

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Filter Topology
open scoped ContDiff
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv Real.smoothTransition x| ≤ C ∧
      |deriv (deriv Real.smoothTransition) x| ≤ C := by
  have hsm : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  obtain ⟨-, h1⟩ := contDiff_infty_iff_deriv.1 hsm
  obtain ⟨-, h2⟩ := contDiff_infty_iff_deriv.1 h1
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn (h1.continuous.continuousOn (s := Set.Icc (0 : ℝ) 1))
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn (h2.continuous.continuousOn (s := Set.Icc (0 : ℝ) 1))
  refine ⟨max (max C1 C2) 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have a := hC1 x hx
    have b := hC2 x hx
    rw [Real.norm_eq_abs] at a b
    exact ⟨a.trans ((le_max_left _ _).trans (le_max_left _ _)),
      b.trans ((le_max_right _ _).trans (le_max_left _ _))⟩
  · obtain ⟨c, hc⟩ := smoothTransition_eventually_const hx
    have hd := hc.deriv
    have e1 : deriv Real.smoothTransition x = 0 := by rw [hd.eq_of_nhds]; simp
    have e2 : deriv (deriv Real.smoothTransition) x = 0 := by rw [hd.deriv_eq]; simp
    rw [e1, e2, abs_zero]
    exact ⟨le_max_right _ _, le_max_right _ _⟩
end GroundTheory.Heights₂.Heights
