-- Prove2me | solution 1 for QEC.Coding.BDL26RXDifferentialMasks.nativeDifferential_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:37:28.234528+00:00
-- url     : https://prove2.me/submissions/9e34596e-231e-484d-99f3-7cbd81ced769

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXDifferentialMasks
theorem _root_.solution (q : (state S i.val).presentation.Q) :
    nativeDifferential S depth i (canonicalBasisWord q) = basisImage S depth i q := rfl
end QEC.Coding.BDL26RXDifferentialMasks
