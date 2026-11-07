-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.multiplicity_mul_card_realizable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:22:29.610179+00:00
-- url     : https://prove2.me/submissions/ecb6b2c2-4a19-44a1-ba52-3f8a3a8b663e

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
import Theorems.Thm_QEC_Coding_CSSGibbs_checkRanks_le
import Theorems.Thm_QEC_Coding_CSSGibbs_card_realizable

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
include horth
namespace QEC.Coding.CSSGibbs
theorem _root_.solution :
    multiplicity P Q * Fintype.card (Realizable P Q) = 2 ^ Fintype.card ι := by
  rw [card_realizable, multiplicity, ← pow_add]
  congr 1
  have h := checkRanks_le P Q horth
  omega
end QEC.Coding.CSSGibbs
