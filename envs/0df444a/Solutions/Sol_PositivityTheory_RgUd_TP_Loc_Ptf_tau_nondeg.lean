-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Loc.Ptf.tau_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:11:14.261521+00:00
-- url     : https://prove2.me/submissions/6ab5707f-0ead-4da9-a026-05d3eeacc27f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_LocalTraceForms_TraceCompSmulRight
import Theorems.Thm_PositivityTheory_RgUd_TP_Loc_Ptf_xq_mul
import Theorems.Thm_PositivityTheory_RgUd_TP_Loc_Ptf_trace_comp_smulRight
import Theorems.Thm_PositivityTheory_RgUd_TP_Loc_Ptf_lam_one
import Theorems.Thm_PositivityTheory_RgUd_TP_Loc_Ptf_tau_apply
import Theorems.Thm_PositivityTheory_RgUd_TP_Loc_Ptf_eq_zero_of_xq
import Theorems.Thm_PositivityTheory_RgUd_TP_Loc_Ptf_exists_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Loc PositivityTheory.RgUd.TP.Loc.Ptf
open Classical
attribute [local instance] Ideal.Quotient.field
variable {k R V : Type*} [Field k] [CommRing R] [IsArtinianRing R] [IsReduced R] [Algebra k R]
  [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V] [FiniteDimensional k V]
namespace PositivityTheory.RgUd.TP.Loc.Ptf
theorem _root_.solution (x : V →ₗ[R] V) (h : ∀ y : V →ₗ[R] V, tau (k := k) (x * y) = 0) : x = 0 := by
  by_contra hx
  obtain ⟨I, hI⟩ : ∃ I : MaximalSpectrum R, xq I.asIdeal x ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hx (eq_zero_of_xq x hne)
  haveI := finQ k (V := V) I
  obtain ⟨w, hw⟩ : ∃ w, xq I.asIdeal x w ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hI (LinearMap.ext hne)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (R ⧸ I.asIdeal) _, φ (xq I.asIdeal x w) ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hw ((Module.forall_dual_apply_eq_zero_iff _ _).1 hne)
  obtain ⟨y, hy1, hy2⟩ := exists_lift I ((φ (xq I.asIdeal x w))⁻¹ • φ.smulRight w)
  have := h y
  rw [tau_apply, Finset.sum_eq_single I] at this
  · apply lam_one (k := k) I
    simp only [tI, xq_mul, hy1] at this
    rwa [mul_smul_comm, map_smul, trace_comp_smulRight, smul_eq_mul, inv_mul_cancel₀ hφ] at this
  · intro J _ hJ
    simp only [tI, xq_mul, hy2 J hJ, mul_zero, map_zero]
  · intro hn
    exact absurd (Finset.mem_univ I) hn
end PositivityTheory.RgUd.TP.Loc.Ptf
