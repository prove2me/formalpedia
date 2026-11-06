-- Prove2me | solution 1 for QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:20:13.095204+00:00
-- url     : https://prove2.me/submissions/563cadff-15b3-4af7-af31-23710844dd27

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
      (Coding.Word F lambda)) (l : lambda) (q : ι) :
    (chainComplexBoundaryIncidence K).incident (Sum.inr l) q ↔
      (K.boundary2 (Coding.canonicalBasisWord (F := F) l)) q ≠ 0 :=
  Iff.rfl
end QEC.QLDPC
