-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Loc.Ptf.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:17.725985+00:00
-- url     : https://prove2.me/submissions/d0e583be-d602-45d3-9258-f83dec6a1c26

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_LocalTraceForms_TraceCompSmulRight
import Theorems.Thm_PositivityTheory_RgUd_TP_Loc_Ptf_eI_mem
import Theorems.Thm_PositivityTheory_RgUd_TP_Loc_Ptf_eI_sub_one

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
theorem _root_.solution (I : MaximalSpectrum R)
    (g : (V ⧸ (I.asIdeal • (⊤ : Submodule R V))) →ₗ[R ⧸ I.asIdeal] (V ⧸ (I.asIdeal • (⊤ : Submodule R V)))) :
    ∃ y : V →ₗ[R] V, xq I.asIdeal y = g ∧ ∀ J ≠ I, xq J.asIdeal y = 0 := by
  refine ⟨sec I ∘ₗ (g.restrictScalars R) ∘ₗ (I.asIdeal • (⊤ : Submodule R V)).mkQ, ?_, fun J hJ => ?_⟩
  · refine xq_ext _ fun v => ?_
    obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (g (Submodule.Quotient.mk v))
    rw [xq_mk]
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.restrictScalars_apply]
    rw [← hu, sec, Submodule.liftQ_apply]
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    have e : eI I • u - u = (eI I - 1) • u := by rw [sub_smul, one_smul]
    rw [e]
    exact Submodule.smul_mem_smul (eI_sub_one I) (Submodule.mem_top : u ∈ (⊤ : Submodule R V))
  · refine xq_ext _ fun v => ?_
    obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (g (Submodule.Quotient.mk v))
    rw [xq_mk]
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.restrictScalars_apply]
    rw [← hu, sec, Submodule.liftQ_apply]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul (eI_mem hJ) (Submodule.mem_top : u ∈ (⊤ : Submodule R V))
end PositivityTheory.RgUd.TP.Loc.Ptf
