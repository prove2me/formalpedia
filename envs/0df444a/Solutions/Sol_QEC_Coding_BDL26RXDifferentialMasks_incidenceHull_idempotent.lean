-- Prove2me | solution 1 for QEC.Coding.BDL26RXDifferentialMasks.incidenceHull_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:34:52.552204+00:00
-- url     : https://prove2.me/submissions/fb726bcd-9df4-4e08-a43d-a155f158f8c0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_saturated
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_eq_iff

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXDifferentialMasks
theorem _root_.solution (A : Finset (state S i.val).presentation.Q) :
    incidenceHull S depth i (incidenceHull S depth i A) = incidenceHull S depth i A :=
  (incidenceHull_eq_iff S depth i _).mpr (incidenceHull_saturated S depth i A)
end QEC.Coding.BDL26RXDifferentialMasks
