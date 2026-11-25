-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.mInt_ofFun_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:15:03.99953+00:00
-- url     : https://prove2.me/submissions/0321b27f-eaf0-4069-8352-e2b6eb67b492

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
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLC_maDens_comp_symm_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLC_locDens_ofFun
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLC_mInt_congr

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
theorem _root_.solution (A : FinHolAtlas 1 X) (v : X → ℝ) (g g' : X → ℝ)
    (h : ∀ z ∈ tsupport v, g z = g' z) :
    mInt A ![LocPot.ofFun v] g = mInt A ![LocPot.ofFun v] g' := by
  refine mInt_congr A _ _ g g' (fun j => ?_)
  filter_upwards [MeasureTheory.ae_restrict_mem (A.chart j).open_target.measurableSet] with y hy
  by_cases hs : (A.chart j).symm y ∈ tsupport v
  · rw [h _ hs]
  · rw [locDens_ofFun, maDens_comp_symm_eq_zero _ v hy hs]
    simp
end ReciprocityTheory.AnForm.M.PLC
