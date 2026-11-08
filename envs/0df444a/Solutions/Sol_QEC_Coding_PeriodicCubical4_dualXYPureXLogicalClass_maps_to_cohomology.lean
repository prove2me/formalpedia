-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.dualXYPureXLogicalClass_maps_to_cohomology
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:34:31.283661+00:00
-- url     : https://prove2.me/submissions/60f75534-38d5-4aa8-b0fe-e9691a7bb3fb

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution {L : Nat} [NeZero L]
    (x y : ZMod L) :
    (plaquetteChainComplex (L := L)).pureXLogicalQuotientEquivMiddleCohomology
        (dualXYPureXLogicalClass x y) =
      dualXYCohomologyClass x y := by
  rfl
end QEC.Coding.PeriodicCubical4
