-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.mInt_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:48.223984+00:00
-- url     : https://prove2.me/submissions/e70293b8-0ee4-4259-a676-f263c2f6cc1b

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
theorem _root_.solution (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X) (g g' : X → ℝ)
    (h : ∀ j, ∀ᵐ y ∂(volume.restrict (A.chart j).target),
      g ((A.chart j).symm y) * locDens A Φ j y = g' ((A.chart j).symm y) * locDens A Ψ j y) :
    mInt A Φ g = mInt A Ψ g' := by
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [h j] with y hy
    rw [mul_assoc, hy, ← mul_assoc]
  · rfl
end ReciprocityTheory.AnForm.M.PLC
