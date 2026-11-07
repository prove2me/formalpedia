-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.checkRanks_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:23.150399+00:00
-- url     : https://prove2.me/submissions/265bbf6b-a0ef-44cf-9c3c-74cb79642492

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
import Theorems.Thm_QEC_Coding_CSSGibbs_checkRank_eq_rowDimension
import Theorems.Thm_QEC_Coding_LinearCode_dimension_add_dual_dimension_eq_length


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
theorem _root_.solution : checkRank P + checkRank Q ≤ Fintype.card ι := by
  have hle := Submodule.finrank_mono
    ((parityCheckRows_orthogonal_iff_rowCode_le_dual P Q).mp horth)
  have hd := (parityCheckRowCode Q).dimension_add_dual_dimension_eq_length
  rw [checkRank_eq_rowDimension P, checkRank_eq_rowDimension Q]
  change Dimension (parityCheckRowCode P) ≤ Dimension (parityCheckRowCode Q).dual at hle
  change Dimension (parityCheckRowCode Q) + Dimension (parityCheckRowCode Q).dual =
    Fintype.card ι at hd
  omega
end QEC.Coding.CSSGibbs
