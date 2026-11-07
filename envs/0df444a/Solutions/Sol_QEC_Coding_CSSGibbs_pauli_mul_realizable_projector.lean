-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.pauli_mul_realizable_projector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:50:33.248471+00:00
-- url     : https://prove2.me/submissions/db4d3055-8dae-4eb0-ae18-5626913f1dbc

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Theorems.Thm_QEC_Coding_CSSGibbs_pauli_mul_projector_add
import Theorems.Thm_QEC_Coding_CSSGibbs_embedding_translation

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_22196e9987_17
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_22196e9987_18
namespace QEC.Coding.CSSGibbs
theorem _root_.solution (E : Binary ι) (s : Realizable P Q) :
    toHermitianQubitOperator E * projector P Q horth (realizableEmbedding P Q s) =
      projector P Q horth (realizableEmbedding P Q (jointTranslation P Q E s)) *
        toHermitianQubitOperator E := by
  rw [embedding_translation P Q horth]
  exact pauli_mul_projector_add P Q horth E _
end QEC.Coding.CSSGibbs
