-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.maDens_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:31.908029+00:00
-- url     : https://prove2.me/submissions/05b8e8b2-f7ae-4266-bd4a-3b5962614c42

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
theorem _root_.solution (φ : Fin 1 → (Fin 1 → ℂ) → ℝ) (z : Fin 1 → ℂ) :
    ReciprocityTheory.AnForm.maDens φ z = 2 / Real.pi * (ReciprocityTheory.AnForm.hessC (φ 0) z 0 0).re := by
  have hU : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  unfold ReciprocityTheory.AnForm.maDens ReciprocityTheory.AnForm.mdisc
  rw [hU, Finset.sum_pair (by decide)]
  simp [Matrix.det_fin_one]
end ReciprocityTheory.AnForm.M.PLC
