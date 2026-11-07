-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.pauli_conjugate_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:40:19.344958+00:00
-- url     : https://prove2.me/submissions/c8160c3d-0287-466d-bd13-72a0fe326342

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Theorems.Thm_QEC_Coding_CSSGibbs_pauli_mul_selected
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_square


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
theorem _root_.solution (E : Binary ι) (A : Finset (Realizable P Q)) :
    toHermitianQubitOperator E * selectedProjector P Q horth A *
        toHermitianQubitOperator E =
      selectedProjector P Q horth (translatedSelection P Q E A) := by
  rw [pauli_mul_selected, mul_assoc, toHermitianQubitOperator_square, mul_one]
end QEC.Coding.CSSGibbs
