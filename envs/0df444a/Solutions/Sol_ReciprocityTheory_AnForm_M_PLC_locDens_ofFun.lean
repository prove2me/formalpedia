-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.locDens_ofFun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:31.996799+00:00
-- url     : https://prove2.me/submissions/e79635bc-b615-40be-8f43-dacc706b17c7

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AtlasIndep
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.PLC
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLC
theorem _root_.solution (A : FinHolAtlas 1 X) (v : X → ℝ) (j : Fin A.n) (y : Fin 1 → ℂ) :
    locDens A ![LocPot.ofFun v] j y = ReciprocityTheory.AnForm.maDens ![v ∘ (A.chart j).symm] y := by
  unfold locDens
  congr 1
  funext i y'
  fin_cases i
  rfl
end ReciprocityTheory.AnForm.M.PLC
