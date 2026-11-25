-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.mIntegrable_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:00.709112+00:00
-- url     : https://prove2.me/submissions/06f60c06-1f91-41db-aec5-daa77de64a33

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
theorem _root_.solution (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) {f g : X → ℝ}
    (hf : MIntegrable A Φ f) (hg : MIntegrable A Φ g) : MIntegrable A Φ (fun x => f x - g x) := by
  intro j K hK hc
  refine (MeasureTheory.Integrable.sub (hf j K hK hc) (hg j K hK hc)).congr
    (Filter.Eventually.of_forall (fun y => ?_))
  simp only [Pi.sub_apply, sub_mul]
end ReciprocityTheory.AnForm.M.PLC
