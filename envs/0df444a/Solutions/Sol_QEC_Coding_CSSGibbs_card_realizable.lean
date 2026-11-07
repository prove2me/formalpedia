-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.card_realizable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:06:43.408251+00:00
-- url     : https://prove2.me/submissions/f97697f8-bf4f-4d31-b1ea-4a2e8776c27b

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum

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
theorem _root_.solution : Fintype.card (Realizable P Q) = 2 ^ (checkRank P + checkRank Q) := by
  rw [Fintype.card_prod, Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range P),
    Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range Q), ZMod.card, pow_add]
  rfl
end QEC.Coding.CSSGibbs
