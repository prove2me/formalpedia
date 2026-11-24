-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeFormComparison_analyticAt_eval_3f0f1a9d1eb0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:45.529436+00:00
-- url     : https://prove2.me/submissions/aeaa18af-10b5-47d6-aca4-724ea86df596

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare

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
open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.TubeFormComparison
namespace GroundTheory.Heights₂.Heights.TubeFormComparison
theorem _root_.solution {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) :
    AnalyticAt ℂ (fun z => eval z P) y := by
  have h := AnalyticAt.aeval_mvPolynomial (𝕜 := ℂ) (f := fun z : Fin m → ℂ => z) (z := y)
    (fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) i).analyticAt y) P
  simpa [MvPolynomial.coe_aeval_eq_eval] using h
end GroundTheory.Heights₂.Heights.TubeFormComparison
