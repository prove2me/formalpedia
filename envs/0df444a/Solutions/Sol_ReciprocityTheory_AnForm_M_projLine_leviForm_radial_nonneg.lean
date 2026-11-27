-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projLine_leviForm_radial_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:22:45.241846+00:00
-- url     : https://prove2.me/submissions/07a65826-8351-42cf-b739-3841e9217bfa

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_leviForm_radial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {F : (Fin 1 → ℂ) → ℝ} {G G' : ℝ → ℝ} {G'' : ℝ} {y : Fin 1 → ℂ}
    (hF : ∀ᶠ w in 𝓝 y, F w = G (‖w 0‖ ^ 2))
    (hG : ∀ᶠ t in 𝓝 (‖y 0‖ ^ 2), HasDerivAt G (G' t) t)
    (hG' : HasDerivAt G' G'' (‖y 0‖ ^ 2)) (hpos : 0 ≤ G'' * ‖y 0‖ ^ 2 + G' (‖y 0‖ ^ 2))
    (v : Fin 1 → ℂ) : 0 ≤ levi F y v := by
  rw [projLine_leviForm_radial hF hG hG' v]
  exact mul_nonneg hpos (by positivity)
end ReciprocityTheory.AnForm.M
