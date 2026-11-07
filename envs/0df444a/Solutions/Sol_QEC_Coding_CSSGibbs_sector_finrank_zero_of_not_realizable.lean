-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.sector_finrank_zero_of_not_realizable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:38:13.538487+00:00
-- url     : https://prove2.me/submissions/c112ccc7-1e47-4b89-a414-4eefe1d6c6a2

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
import Theorems.Thm_QEC_Coding_CSSGibbs_projector_eq_zero_of_not_realizable
import Theorems.Thm_QEC_Coding_CSSGibbs_trace_projector


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
theorem _root_.solution (s : Word (ZMod 2) (Sum κP κQ))
    (hs : s ∉ realizableSyndromes P Q) : Module.finrank ℂ (sector P Q horth s) = 0 := by
  have ht := trace_projector P Q horth s
  rw [projector_eq_zero_of_not_realizable P Q horth s hs, map_zero] at ht
  exact_mod_cast ht.symm
end QEC.Coding.CSSGibbs
