-- Prove2me | solution 1 for QEC.Coding.BDL26RXDifferentialMasks.nativeDifferential_connector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:47:44.30933+00:00
-- url     : https://prove2.me/submissions/3b45603e-29d0-48fd-9e10-267d26bce1a6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_nativeDifferential_exterior
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_connector_exterior
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_connector_parent_none


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXDifferentialMasks
theorem _root_.solution (h : i.val % 2 = 0)
    (q : (state S i.val).presentation.Q)
    (w : Word BDL26Field (state S i.val).presentation.Q) :
    parent S (i.val+1) (Vertex.z (connector S depth i h q)) = none ∧
      nativeDifferential S depth i w (connector S depth i h q) = 0 :=
  ⟨connector_parent_none S depth i h q,
    nativeDifferential_exterior S depth i h w _ (connector_exterior S depth i h q)⟩
end QEC.Coding.BDL26RXDifferentialMasks
