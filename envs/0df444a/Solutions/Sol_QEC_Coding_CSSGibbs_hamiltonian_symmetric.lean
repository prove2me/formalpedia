-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.hamiltonian_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:22:25.047299+00:00
-- url     : https://prove2.me/submissions/682c4beb-d47c-4d07-bd5d-6cc985086366

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_adjoint

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
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_ea4515a18e_14
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_ea4515a18e_15
namespace QEC.Coding.CSSGibbs
theorem _root_.solution : (hamiltonian P Q).IsSymmetric :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr (hamiltonian_adjoint P Q)
end QEC.Coding.CSSGibbs
