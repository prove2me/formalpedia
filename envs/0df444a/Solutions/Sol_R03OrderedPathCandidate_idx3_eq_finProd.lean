-- Prove2me | solution 1 for R03OrderedPathCandidate.idx3_eq_finProd
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:52:16.707132+00:00
-- url     : https://prove2.me/submissions/6c44f99c-782e-4c2b-81cc-3f3eb1e792ec

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_f0a6fd554c_ordered_path_p3factor_candidate_v1

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace R03OrderedPathCandidate

open CubicP3Partition

universe u
variable {V : Type u}

end R03OrderedPathCandidate

open R03OrderedPathCandidate
open CubicP3Partition
universe u
variable {V : Type u}
theorem solution (k : Nat) (i : Fin k) (j : Fin 3) :
    (finProdFinEquiv (i, j) : Fin (k * 3)) = idx3 k i j := by
  simp [finProdFinEquiv, idx3, Nat.mul_comm]
