-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.checkRank_eq_rowDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:05:23.657089+00:00
-- url     : https://prove2.me/submissions/3fee7a8b-e236-452b-93b8-fda07b6db962

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
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
namespace QEC.Coding.CSSGibbs
theorem _root_.solution : checkRank P = Dimension (parityCheckRowCode P) := by
  have h := (parityCheckRowCode P).dimension_add_dual_dimension_eq_length
  rw [parityCheckRowCode_dual_eq_kernelCode] at h
  have hk := LinearMap.finrank_range_add_finrank_ker P
  rw [finrank_word_eq_length] at hk
  change Dimension (parityCheckRowCode P) + Module.finrank (ZMod 2) (LinearMap.ker P) =
    Length (ZMod 2) ι at h
  unfold checkRank
  omega
end QEC.Coding.CSSGibbs
