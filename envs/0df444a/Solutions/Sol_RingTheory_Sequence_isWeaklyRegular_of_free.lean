-- Prove2me | solution 1 for RingTheory.Sequence.isWeaklyRegular_of_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/19da9345-3283-5490-af50-cf2319d7e234

import Mathlib
import Theorems.Thm_RingTheory_Sequence_isWeaklyRegular_of_free_aux
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingTheory_Sequence_isWeaklyRegular_of_free

open scoped Pointwise TensorProduct

theorem solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Nontrivial M] {s : List R} :
    RingTheory.Sequence.IsWeaklyRegular M s ↔ RingTheory.Sequence.IsWeaklyRegular R s := by
  let b := Module.Free.chooseBasis R M
  have : Nontrivial R := Module.nontrivial R M
  rw [b.repr.isWeaklyRegular_congr, RingTheory.Sequence.isWeaklyRegular_of_free_aux]

end S_RingTheory_Sequence_isWeaklyRegular_of_free
end P2MW
export P2MW.S_RingTheory_Sequence_isWeaklyRegular_of_free (solution)
