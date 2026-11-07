-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.energy_joinSyndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:22:30.511558+00:00
-- url     : https://prove2.me/submissions/fede7779-64b5-4647-a83a-1aeae24e461c

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
import Theorems.Thm_QEC_Coding_CSSGibbs_weight_joinSyndrome

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
theorem _root_.solution (u : Word (ZMod 2) κP) (v : Word (ZMod 2) κQ) :
    energy P Q (joinSyndrome u v) =
      -(Fintype.card κP + Fintype.card κQ : Nat) + 2 * (HammingWeight u + HammingWeight v : Nat) := by
  rw [energy, weight_joinSyndrome]
end QEC.Coding.CSSGibbs
