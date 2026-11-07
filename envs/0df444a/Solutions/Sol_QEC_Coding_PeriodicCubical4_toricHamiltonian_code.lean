-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.toricHamiltonian_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:59.54382+00:00
-- url     : https://prove2.me/submissions/25139204-c29b-4986-be85-06f6bdbbca52

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
    (toricHamiltonian (L := L)).code = toricSourceValidCode :=
  rfl
end QEC.Coding.PeriodicCubical4
