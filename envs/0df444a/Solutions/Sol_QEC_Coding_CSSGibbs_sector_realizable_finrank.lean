-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.sector_realizable_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:48:50.400195+00:00
-- url     : https://prove2.me/submissions/6a2c3428-6c0c-4e3b-9e02-25fa11c7d887

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
import Theorems.Thm_QEC_Coding_CSSGibbs_sector_zero_finrank
import Theorems.Thm_QEC_Coding_CSSGibbs_trace_projector
import Theorems.Thm_QEC_Coding_CSSGibbs_trace_projector_realizable


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
theorem _root_.solution (u : LinearMap.range P) (v : LinearMap.range Q) :
    Module.finrank ℂ (sector P Q horth (joinSyndrome u.val v.val)) = multiplicity P Q := by
  have h := trace_projector_realizable P Q horth u v
  rw [trace_projector, trace_projector, sector_zero_finrank] at h
  exact_mod_cast h
end QEC.Coding.CSSGibbs
