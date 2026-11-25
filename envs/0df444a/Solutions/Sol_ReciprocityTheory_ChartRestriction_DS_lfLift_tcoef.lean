-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lfLift_tcoef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:22:42.906534+00:00
-- url     : https://prove2.me/submissions/d4b89714-477f-4ad2-87ea-eddf335e8ed8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (x : LfIdx ε → N) (S : LfIdx ε) :
    tcoef ((fockBasis n).coord S.1) (lfLift ε x) = x S := by
  simp only [lfLift, map_sum, tcoef, LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.rid_tmul, Module.Basis.coord_apply, Module.Basis.repr_self]
  rw [Finset.sum_eq_single S (fun T _ hT => by
    rw [Finsupp.single_apply, if_neg (fun h => hT (Subtype.ext h)), zero_smul]) (by simp)]
  simp
end ReciprocityTheory.ChartRestriction.DS
