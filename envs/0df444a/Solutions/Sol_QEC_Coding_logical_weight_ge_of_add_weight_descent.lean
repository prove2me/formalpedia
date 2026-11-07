-- Prove2me | solution 1 for QEC.Coding.logical_weight_ge_of_add_weight_descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:45:01.094203+00:00
-- url     : https://prove2.me/submissions/eee93cbc-df8b-45f6-abe0-af59da0d0efc

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Theorems.Thm_QEC_Coding_mem_trivial_of_weight_lt_of_add_weight_descent

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F]
  [DecidableEq F] [Fintype ι]
namespace QEC.Coding
theorem _root_.solution
    (ambient trivial : LinearCode F ι)
    (hsub : trivial.carrier ≤ ambient.carrier) (threshold : Nat)
    (hreduce : ∀ x : Word F ι, x ∈ ambient.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ y : Word F ι, y ∈ trivial.carrier ∧
        HammingWeight (x + y) < HammingWeight x)
    (x : Word F ι) (hx : x ∈ ambient.carrier)
    (hlogical : x ∉ trivial.carrier) : threshold ≤ HammingWeight x := by
  by_contra hnot
  exact hlogical (mem_trivial_of_weight_lt_of_add_weight_descent
    ambient trivial hsub threshold hreduce x hx (Nat.lt_of_not_ge hnot))
end QEC.Coding
