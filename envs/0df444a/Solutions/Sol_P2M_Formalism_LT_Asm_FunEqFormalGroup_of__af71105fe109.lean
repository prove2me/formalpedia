-- Prove2me | solution 1 for P2M_Formalism_LT_Asm_FunEqFormalGroup_of__af71105fe109
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:53:00.825746+00:00
-- url     : https://prove2.me/submissions/ee131bec-6efe-486c-a0e9-12a880df7aeb

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MapSubtypeInjective
import Theorems.Thm_Formalism_LT_Asm_log_subst2
import Theorems.Thm_Formalism_LT_Asm_psubst_zero
import Theorems.Thm_Formalism_LT_Asm_subst_zero_eq_rescale
import Theorems.Thm_Formalism_LT_Asm_cc_subst2
import Theorems.Thm_Formalism_LT_Asm_map_subst2
import Theorems.Thm_Formalism_LT_Asm_coeff_lift
import Theorems.Thm_Formalism_LT_Asm_map_lift
import Theorems.Thm_Formalism_LT_Asm_map_subtype_injective
import Theorems.Thm_Formalism_G_LogP_subst_X0_zero_eq_rescale
import Theorems.Thm_Formalism_G_substInjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.Asm
open Formalism.G
namespace Formalism.LT.Asm
theorem _root_.solution (hg : Formalism.G.FunEqGroup.{u}) : Formalism.G.FunEqFormalGroup.{u} := by
  intro K _ _ _ p q σ hS f hf0 hf1 hfE
  obtain ⟨F, hF0, hFI, hF⟩ := hg K p q σ hS f hf0 hf1 hfE
  have hX : MvPowerSeries.coeff (Finsupp.single 0 1) F = 1 := by
    have e : F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] = MvPowerSeries.X 0 := by
      refine substInjective K (Fin 2) f _ _ hf0 hf1 (cc_subst2 F hF0 (by simp) (by simp))
        (by simp) ?_
      rw [log_subst2 f F hF0 hF (by simp) (by simp), psubst_zero f hf0, add_zero]
    have := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) e
    rw [Formalism.G.LogP.subst_X0_zero_eq_rescale, MvPowerSeries.coeff_rescale] at this
    simpa [Finsupp.prod_single_index, MvPowerSeries.coeff_X] using this
  have hY : MvPowerSeries.coeff (Finsupp.single 1 1) F = 1 := by
    have e : F.subst ![0, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] = MvPowerSeries.X 1 := by
      refine substInjective K (Fin 2) f _ _ hf0 hf1 (cc_subst2 F hF0 (by simp) (by simp))
        (by simp) ?_
      rw [log_subst2 f F hF0 hF (by simp) (by simp), psubst_zero f hf0, zero_add]
    have := congrArg (MvPowerSeries.coeff (Finsupp.single 1 1)) e
    rw [subst_zero_eq_rescale, MvPowerSeries.coeff_rescale] at this
    simpa [Finsupp.prod_single_index, MvPowerSeries.coeff_X] using this
  set F₀ := lift F hFI with hF₀
  have hF₀0 : MvPowerSeries.constantCoeff F₀ = 0 := Subtype.ext (by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_lift,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF0]
    rfl)

  have hassK : F.subst ![F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K),
      MvPowerSeries.X 1], MvPowerSeries.X 2] =
      F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K),
      F.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]] := by
    have c01 := cc_subst2 F hF0 (MvPowerSeries.constantCoeff_X (R := K) (0 : Fin 3))
      (MvPowerSeries.constantCoeff_X (R := K) (1 : Fin 3))
    have c12 := cc_subst2 F hF0 (MvPowerSeries.constantCoeff_X (R := K) (1 : Fin 3))
      (MvPowerSeries.constantCoeff_X (R := K) (2 : Fin 3))
    refine substInjective K (Fin 3) f _ _ hf0 hf1
      (cc_subst2 F hF0 c01 (by simp)) (cc_subst2 F hF0 (by simp) c12) ?_
    rw [log_subst2 f F hF0 hF c01 (by simp), log_subst2 f F hF0 hF (by simp) c12,
      log_subst2 f F hF0 hF (by simp) (by simp), log_subst2 f F hF0 hF (by simp) (by simp)]
    ring
  let G : FormalGroup (unitBall K) :=
    { toPowerSeries := F₀
      zero_constantCoeff := hF₀0
      lin_coeff_X := Subtype.ext (by rw [coeff_lift, hX]; rfl)
      lin_coeff_Y := Subtype.ext (by rw [coeff_lift, hY]; rfl)
      assoc := by
        have c01 := cc_subst2 F₀ hF₀0
          (MvPowerSeries.constantCoeff_X (R := unitBall K) (0 : Fin 3))
          (MvPowerSeries.constantCoeff_X (R := unitBall K) (1 : Fin 3))
        have c12 := cc_subst2 F₀ hF₀0
          (MvPowerSeries.constantCoeff_X (R := unitBall K) (1 : Fin 3))
          (MvPowerSeries.constantCoeff_X (R := unitBall K) (2 : Fin 3))
        apply map_subtype_injective
        rw [map_subst2 _ _ c01 (by simp), map_subst2 _ _ (by simp) c12,
          map_subst2 _ _ (by simp) (by simp), map_subst2 _ _ (by simp) (by simp)]
        simp only [MvPowerSeries.map_X, hF₀, map_lift]
        exact hassK }
  refine ⟨G, hf0, hf1, ?_⟩
  show f.subst (MvPowerSeries.map (unitBall K).subtype F₀) = atX f + atY f
  rw [hF₀, map_lift]
  exact hF
end Formalism.LT.Asm
