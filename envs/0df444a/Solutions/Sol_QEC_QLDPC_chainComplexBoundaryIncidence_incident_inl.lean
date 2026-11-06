-- Prove2me | solution 1 for QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:20:25.897244+00:00
-- url     : https://prove2.me/submissions/91a27ab3-40e4-4780-8fdc-fd11ad98a848

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core

set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC
namespace QEC.QLDPC
theorem _root_.solution
    {F : Type u} {ι κ lambda : Type v} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData F (Coding.Word F κ) (Coding.Word F ι)
      (Coding.Word F lambda)) (k : κ) (q : ι) :
    (chainComplexBoundaryIncidence K).incident (Sum.inl k) q ↔
      (Coding.wordLinearMapTranspose K.boundary1
        (Coding.canonicalBasisWord (F := F) k)) q ≠ 0 :=
  Iff.rfl
end QEC.QLDPC
