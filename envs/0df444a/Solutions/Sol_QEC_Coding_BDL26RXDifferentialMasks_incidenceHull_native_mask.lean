-- Prove2me | solution 1 for QEC.Coding.BDL26RXDifferentialMasks.incidenceHull_native_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:46:22.878904+00:00
-- url     : https://prove2.me/submissions/184c2ae9-3509-4a27-8a64-097b21d01f11

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_nativeRegion_commutes_iff_saturated
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_saturated

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXDifferentialMasks
theorem _root_.solution (h : i.val % 2 = 0)
    (A : Finset (state S i.val).presentation.Q)
    (w : Word BDL26Field (state S i.val).presentation.Q) :
    maskWord (nativeRegion S depth i h (incidenceHull S depth i A))
        (nativeDifferential S depth i w) =
      nativeDifferential S depth i (maskWord (incidenceHull S depth i A) w) :=
  (nativeRegion_commutes_iff_saturated S depth i h _).mpr
    (incidenceHull_saturated S depth i A) w
end QEC.Coding.BDL26RXDifferentialMasks
