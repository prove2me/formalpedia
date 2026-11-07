-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.pauli_mul_projector_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:48:10.498602+00:00
-- url     : https://prove2.me/submissions/c794e65f-a1dc-4496-a0cd-de25d37643b2

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Theorems.Thm_QEC_Coding_CSSGibbs_transport_add
import Theorems.Thm_QEC_Coding_CSSGibbs_pauli_mul_syndromeProjector


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
theorem _root_.solution (E : Binary ι) (s : Word (ZMod 2) (Sum κP κQ)) :
    toHermitianQubitOperator E * projector P Q horth s =
      projector P Q horth
        (s + stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E) *
      toHermitianQubitOperator E := by
  have h := pauli_mul_syndromeProjector (binaryCSSParityCheckGenerators P Q)
    (checks_commute P Q horth) E (syndromeOutcome _ s)
  rw [transport_add P Q horth E s] at h
  exact h
end QEC.Coding.CSSGibbs
