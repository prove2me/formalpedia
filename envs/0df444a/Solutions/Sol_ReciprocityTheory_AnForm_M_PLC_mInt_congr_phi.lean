-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.mInt_congr_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:47.623239+00:00
-- url     : https://prove2.me/submissions/a2804c1c-4345-49b6-b6e4-1e7196872bad

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
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLC_locDens_congr_phi
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
theorem _root_.solution (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X)
    (h : ∀ i a b, (Φ i).φ a b = (Ψ i).φ a b) (g : X → ℝ) : mInt A Φ g = mInt A Ψ g :=
  mInt_congr A Φ Ψ g g (fun j => Filter.Eventually.of_forall (fun y => by
    rw [locDens_congr_phi A Φ Ψ h j y]))
end ReciprocityTheory.AnForm.M.PLC
