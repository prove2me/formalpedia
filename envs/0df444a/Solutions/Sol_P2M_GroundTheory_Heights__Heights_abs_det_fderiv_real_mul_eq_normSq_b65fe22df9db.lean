-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_abs_det_fderiv_real_mul_eq_normSq_b65fe22df9db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:56.471346+00:00
-- url     : https://prove2.me/submissions/0cb42dbc-04c8-48ae-87ef-558a00f11c8c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicFibreSumInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeightedAreaFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolomorphicFibreSumInt
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_fderiv_real_eq_normSq


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
open MeasureTheory ReciprocityTheory.AnForm.A
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {d : ℕ} {Ω : Set (Fin d → ℂ)} {τ : (Fin d → ℂ) → Fin d → ℂ}
    (hΩ : IsOpen Ω) (hτ : DifferentiableOn ℂ τ Ω) (H : (Fin d → ℂ) → ℝ) :
    Set.EqOn (fun t => |(fderiv ℝ τ t).det| * H t) (fun t => Complex.normSq (jacC τ t).det * H t) Ω := by
  intro t ht
  simp only
  rw [det_fderiv_real_eq_normSq τ t (hτ.differentiableAt (hΩ.mem_nhds ht)),
    abs_of_nonneg (Complex.normSq_nonneg _)]
end GroundTheory.Heights₂.Heights
