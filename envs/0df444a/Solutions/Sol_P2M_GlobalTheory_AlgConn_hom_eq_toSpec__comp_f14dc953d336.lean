-- Prove2me | solution 1 for P2M_GlobalTheory_AlgConn_hom_eq_toSpec__comp_f14dc953d336
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:50:20.139545+00:00
-- url     : https://prove2.me/submissions/26dc0214-4970-4116-80a7-82cacb6f2b64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClopenBasicOpenSpecProdSelfFirstIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentOfClopen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentEqOfBasicOpenEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomExtSpecProdSelfOfBasicOpenPreimageEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AlgConn
namespace GlobalTheory.AlgConn
theorem _root_.solution {T : Scheme.{0}} {A : CommRingCat.{0}} (h : T ⟶ Spec A) :
    h = T.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso A).inv ≫ h.appTop) := by
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
end GlobalTheory.AlgConn
