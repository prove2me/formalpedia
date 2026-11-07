-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.projector_eq_zero_of_not_realizable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:55:03.187303+00:00
-- url     : https://prove2.me/submissions/6cf54c57-e9cf-442e-adb8-40cf6f92b7e1

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
import Theorems.Thm_QEC_Coding_CSSGibbs_sum_sector_finrank
import Theorems.Thm_QEC_Coding_CSSGibbs_sum_realizable_finrank
import Theorems.Thm_QEC_Coding_CSSGibbs_trace_projector
import Theorems.Thm_QEC_Coding_CSSGibbs_trace_projector_zero_iff


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
    (hs : s ∉ realizableSyndromes P Q) : projector P Q horth s = 0 := by
  have hle : Module.finrank ℂ (sector P Q horth s) + 2 ^ Fintype.card ι ≤
      2 ^ Fintype.card ι := by
    calc
      _ = ∑ t ∈ insert s (realizableSyndromes P Q), Module.finrank ℂ (sector P Q horth t) := by
        rw [Finset.sum_insert hs, sum_realizable_finrank]
      _ ≤ ∑ t, Module.finrank ℂ (sector P Q horth t) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = _ := sum_sector_finrank P Q horth
  have hr : Module.finrank ℂ (sector P Q horth s) = 0 := by omega
  apply (trace_projector_zero_iff P Q horth s).mp
  rw [trace_projector, hr, Nat.cast_zero]
end QEC.Coding.CSSGibbs
