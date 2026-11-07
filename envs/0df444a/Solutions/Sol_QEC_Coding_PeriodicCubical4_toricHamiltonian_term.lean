-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.toricHamiltonian_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:55:08.700472+00:00
-- url     : https://prove2.me/submissions/69f61c66-964a-4a65-a602-c3f988f95e35

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Cellulation
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution (j : Sum (Link L) (Cube L)) :
    (toricHamiltonian (L := L)).term j =
      -toQubitOperator (toricGenerator j) :=
  rfl
end QEC.Coding.PeriodicCubical4
