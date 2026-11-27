-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CasG.lhol_clm_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:25:22.037686+00:00
-- url     : https://prove2.me/submissions/29ee3ada-5c3f-4319-8962-c15c65550545

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiMLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasLPsM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LholClmEventually
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasG_lhol_clm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CasG
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace ReciprocityTheory.ChartRestriction.DS.S7.CasG
theorem _root_.solution (L : E →L[ℂ] E') (X : Matrix (Fin n) (Fin n) ℂ)
    {G : Matrix (Fin n) (Fin n) ℂ → E} {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V)
    (hG : DifferentiableOn ℂ G V) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ V) :
    Lhol X (fun w => L (G w)) =ᶠ[nhds z] fun w => L (Lhol X G w) := by
  filter_upwards [hV.mem_nhds hz] with w hw
  exact lhol_clm L X (hG.differentiableAt (hV.mem_nhds hw))
end ReciprocityTheory.ChartRestriction.DS.S7.CasG
