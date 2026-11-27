-- Prove2me | solution 1 for P2M_GlobalTheory_AlgConn_isProper_two__665268f9db81
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:51:39.116435+00:00
-- url     : https://prove2.me/submissions/45555ca1-25d3-4f03-90ee-e221b0839268

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClopenBasicOpenSpecProdSelfFirstIdempotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.AlgConn
namespace GlobalTheory.AlgConn
theorem _root_.solution (O : Type) [CommRing O] : IsProper (twoπ O) := by
  haveI : IsFinite (twoπ O) := (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  infer_instance
end GlobalTheory.AlgConn
