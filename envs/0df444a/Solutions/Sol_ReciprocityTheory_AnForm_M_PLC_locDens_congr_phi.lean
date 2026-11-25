-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.locDens_congr_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:36.444089+00:00
-- url     : https://prove2.me/submissions/351ff149-b4f4-41bc-969a-d6a91472c471

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
theorem _root_.solution (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X)
    (h : ∀ i a b, (Φ i).φ a b = (Ψ i).φ a b) (j : Fin A.n) (y : Fin e → ℂ) :
    locDens A Φ j y = locDens A Ψ j y := by
  simp only [locDens, h]
end ReciprocityTheory.AnForm.M.PLC
