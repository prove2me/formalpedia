-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.primalXYPureZLogicalClass_maps_to_homology
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:34:28.411976+00:00
-- url     : https://prove2.me/submissions/df25c76d-9065-45f0-ba0a-068f0c6037b2

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution {L : Nat} [NeZero L]
    (z w : ZMod L) :
    (plaquetteChainComplex (L := L)).pureZLogicalQuotientEquivMiddleHomology
        (primalXYPureZLogicalClass z w) =
      primalXYHomologyClass z w := by
  rfl
end QEC.Coding.PeriodicCubical4
