-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.toricHamiltonian_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:55:02.313757+00:00
-- url     : https://prove2.me/submissions/462a0806-bb54-4433-b815-27d0f103fbe2

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
theorem _root_.solution :
    (toricHamiltonian (L := L)).generators = toricGenerator :=
  rfl
end QEC.Coding.PeriodicCubical4
