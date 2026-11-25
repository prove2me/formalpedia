-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.potSmoothOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:48.089849+00:00
-- url     : https://prove2.me/submissions/822b49ab-5c92-452d-a5d4-7412119193e0

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff ComplexOrder Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X)
    (hP : IsPotential A P) (x : X) (j : Fin A.n) :
    ContDiffOn ℝ 2 (P.φ x ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) := by
  exact (hP.1 x j).of_le (by first | exact ENat.LEInfty.out | simp | norm_num)
end ReciprocityTheory.AnForm.M
