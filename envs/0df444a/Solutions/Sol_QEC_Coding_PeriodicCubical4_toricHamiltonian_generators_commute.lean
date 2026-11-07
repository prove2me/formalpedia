-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.toricHamiltonian_generators_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:55:03.532679+00:00
-- url     : https://prove2.me/submissions/40803f35-9bb1-4159-82bf-4fcce5d63925

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Cellulation
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generators_commute


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution
    (j k : Sum (Link L) (Cube L)) :
    Commutes ((toricHamiltonian (L := L)).generators j)
      ((toricHamiltonian (L := L)).generators k) :=
  (toricHamiltonian (L := L)).generators_commute j k
end QEC.Coding.PeriodicCubical4
