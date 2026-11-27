-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HolomorphicFibreSumInt_proof_5e43db786638
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:57:15.687543+00:00
-- url     : https://prove2.me/submissions/a0876d3b-1c96-4ea4-b71d-e09e851dff3a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicFibreSumInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeightedAreaFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolomorphicFibreSumInt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_abs_det_fderiv_real_mul_eq_normSq_b65fe22df9db

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
namespace HolomorphicFibreSumInt
theorem _root_.solution (h : WeightedAreaFormula.Statement) :
    HolomorphicFibreSumInt.Statement := by
  intro d Ω τ H hΩ hτ hfin hint
  have heq := abs_det_fderiv_real_mul_eq_normSq hΩ hτ H
  have hint' : IntegrableOn (fun t => |(fderiv ℝ τ t).det| * H t) Ω :=
    (integrableOn_congr_fun heq hΩ.measurableSet).2 hint
  obtain ⟨h1, h2⟩ := h (Fin d → ℂ) volume Ω τ H hΩ (hτ.restrictScalars ℝ) hfin hint'
  exact ⟨h1, h2.trans (setIntegral_congr_fun hΩ.measurableSet heq)⟩
end HolomorphicFibreSumInt
end GroundTheory.Heights₂.Heights
