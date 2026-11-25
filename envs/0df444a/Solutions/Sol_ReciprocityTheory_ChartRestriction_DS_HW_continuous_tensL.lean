-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.continuous_tensL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:18.370792+00:00
-- url     : https://prove2.me/submissions/b40f318e-14e8-45a8-ac89-d05114ade303

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {X : Type*} [TopologicalSpace X] {m : X → Matrix ι ι ℂ} {S : X → V →L[ℂ] V}
    (hm : Continuous m) (hS : Continuous S) : Continuous fun x => tensL (m x) (S x) := by
  simp only [tensL]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (hm.matrix_elem i j).smul (continuous_const.clm_comp (hS.clm_comp continuous_const))
end ReciprocityTheory.ChartRestriction.DS.HW
