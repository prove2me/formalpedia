-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.fock_contractLeft_involute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:21:59.329149+00:00
-- url     : https://prove2.me/submissions/8fbc5d4b-9cdf-403f-ac31-0f0ff4939a45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA

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
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (d : Module.Dual ℂ (Fin n × Fin n → ℂ)) (x : Fock n) :
    CliffordAlgebra.contractLeft d (CliffordAlgebra.involute x) =
      -CliffordAlgebra.involute (CliffordAlgebra.contractLeft d x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | ι_mul x m hx =>
    simp only [map_mul, CliffordAlgebra.involute_ι, neg_mul, map_neg, CliffordAlgebra.contractLeft_ι_mul,
      hx, map_sub, map_smul, mul_neg]
end ReciprocityTheory.ChartRestriction.DS
