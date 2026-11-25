-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_ratSec_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:37.098851+00:00
-- url     : https://prove2.me/submissions/8221f212-ae80-4459-b622-34748a26ab75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_Inhabit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_homog_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_homog_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] [DecidableEq (Σ k, ι k)]
  {F : Type*} [Field F]
variable [DecidableEq K]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (V : Ideal (MRingOver F ι)) (p : Σ k, ι k) (hp : (X p : MRingOver F ι) ∉ V)
    (hV : (1 : MRingOver F ι) ∉ V) : IsRatSection V (Pi.single p.1 1) (X p) 1 := by
  refine ⟨Pi.single p.1 1, 0, inh_homog_X p, inh_homog_one, hp, hV, fun k => ?_⟩
  by_cases hk : k = p.1
  · subst hk; simp
  · simp [hk]
end ReciprocityTheory.ChartRestriction.G.AI.I1
