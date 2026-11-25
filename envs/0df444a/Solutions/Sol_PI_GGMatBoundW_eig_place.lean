-- Prove2me | solution 1 for PI.GGMatBoundW.eig_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:59:04.823164+00:00
-- url     : https://prove2.me/submissions/9b0a4e0f-5302-42c7-b286-bbaac311db27

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_RepresentationDimensionPos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_IrreducibleOfMinimal
import Theorems.Thm_PI_GGMatBoundW_exists_irreducible_le
import Theorems.Thm_PI_GGMatBoundW_repGam_subrep
import Theorems.Thm_P2M_RH_PI_GGMatBoundW_gam_one_real_3ae542a281777c9f
import Theorems.Thm_PI_GGMatBoundW_gam_one_re_pos
import Theorems.Thm_Formalism_L2_SG_GGMirabolic_ratio_numeric
import Theorems.Thm_PI_GGConvScalarW_representation_commutes_gamma


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
namespace PI.GGMatBoundW
theorem _root_.solution (hC : ConvScalar) (hR : GenericRatio) (ψ₀ : AddChar F ℂ) (hψ : ψ₀ ≠ 1)
    (hq : 3 ≤ Fintype.card F) {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V) (c : ℂ) (w : V) (hw : w ≠ 0)
    (hc : repGam ψ₀ π w = c • w) :
    ∃ r : ℝ, c = r ∧ 0 ≤ r ∧
      r ≤ (gam ψ₀ (1 : GL (Fin k) F)).re * (1 + 3 / (Fintype.card F : ℝ)) := by
  have hcomm := PI.GGConvScalarW.representation_commutes_gamma F k ψ₀ V π
  let E : Subrepresentation π := ⟨LinearMap.ker (repGam ψ₀ π - c • LinearMap.id), by
    intro g v hv
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hv ⊢
    have h1 := congrArg (fun f => f v) (hcomm g)
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, hv, map_smul]⟩
  have hmemE : ∀ v, v ∈ E.toSubmodule ↔ repGam ψ₀ π v = c • v := by
    intro v
    simp only [E, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero]
  have hE : E ≠ ⊥ := by
    intro h
    have hwE : w ∈ E.toSubmodule := (hmemE w).mpr hc
    rw [h] at hwE
    exact hw ((Submodule.mem_bot ℂ).mp hwE)
  obtain ⟨W, hW0, hWE, hirr⟩ := exists_irreducible_le π E hE
  have hWs : W.toSubmodule ≠ ⊥ := fun h => hW0 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨u, huW, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWs
  have hu_eig : repGam ψ₀ π u = c • u := (hmemE u).mp (hWE huW)
  have hpos := gam_one_re_pos (k := k) ψ₀
  have hg1 : gam ψ₀ (1 : GL (Fin k) F) ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  have hCS := hC F k ψ₀ hψ W.toSubmodule W.toRepresentation hirr
  have hrep : repGam ψ₀ W.toRepresentation =
      gam ψ₀ (1 : GL (Fin k) F) • ((gam ψ₀ (1 : GL (Fin k) F))⁻¹ • repGam ψ₀ W.toRepresentation) := by
    rw [smul_smul, mul_inv_cancel₀ hg1, one_smul]
  rw [hCS] at hrep
  have k0 := repGam_subrep ψ₀ π W ⟨u, huW⟩
  rw [hrep, hu_eig] at k0
  have hreal := gam_one_real (k := k) ψ₀
  have hre : (gam ψ₀ (1 : GL (Fin k) F)).re =
      (Fintype.card (GL (Fin k) F) : ℝ) / (cardU F k : ℝ) := by
    rw [hreal, Complex.ofReal_re]
  by_cases hgen : Generic ψ₀ W.toRepresentation
  · rw [if_pos hgen] at k0
    have k1 : (gam ψ₀ (1 : GL (Fin k) F) *
        ((cardU F k : ℂ) / (Module.finrank ℂ W.toSubmodule : ℂ))) • u = c • u := by
      rw [← k0, mul_smul]
      rfl
    have hc_eq : c = gam ψ₀ (1 : GL (Fin k) F) *
        ((cardU F k : ℂ) / (Module.finrank ℂ W.toSubmodule : ℂ)) :=
      (smul_left_injective ℂ hu0 k1).symm
    refine ⟨(Fintype.card (GL (Fin k) F) : ℝ) / (cardU F k : ℝ) *
      ((cardU F k : ℝ) / (Module.finrank ℂ W.toSubmodule : ℝ)), ?_, by positivity, ?_⟩
    · rw [hc_eq, hreal]
      push_cast
      ring
    · rw [hre]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (hR F k ψ₀ hψ W.toSubmodule W.toRepresentation hirr hgen).trans
        (ratio_numeric k _ (by exact_mod_cast hq))
  · rw [if_neg hgen, smul_zero] at k0
    have hcu : c • u = 0 := by
      rw [← k0]
      rfl
    refine ⟨0, ?_, le_rfl, ?_⟩
    · rcases smul_eq_zero.mp hcu with h | h
      · rw [h, Complex.ofReal_zero]
      · exact absurd h hu0
    · rw [hre]
      positivity
end PI.GGMatBoundW
