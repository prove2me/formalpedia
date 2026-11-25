-- Prove2me | solution 1 for PI.WGL.BrInt.rat_of_pairings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:33.192971+00:00
-- url     : https://prove2.me/submissions/f8f508de-872a-4ae2-95d6-339fb50645b5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionBrInt
import Theorems.Thm_PI_WGL_BrInt_fockF_sum_right
import Theorems.Thm_PI_WGL_BrInt_brFockF_map
import Theorems.Thm_PI_WGL_BrInt_map_ratSmul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockHerm
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockPos
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions MvPolynomial
open PI.WGL.BrInt
open Formalism.REAL Formalism.GradedWeylDivisibility
variable {σ : Type}
namespace PI.WGL.BrInt
theorem _root_.solution {ι : Type*} [Fintype ι] (β : ι → MvPolynomial σ ℚ) (G : MvPolynomial σ ℂ)
    (hG : G ∈ Submodule.span ℂ (Set.range fun i => map (algebraMap ℚ ℂ) (β i)))
    (hq : ∀ i, ∃ q : ℚ, fockF (map (algebraMap ℚ ℂ) (β i)) G = (q : ℂ)) :
    ∃ G0 ∈ Submodule.span ℚ (Set.range β), G = map (algebraMap ℚ ℂ) G0 := by
  classical
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hG
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ ℂ)
    (LinearMap.ker_eq_bot.mpr (algebraMap ℚ ℂ).injective)
  have hπq : ∀ q : ℚ, π (q : ℂ) = q := fun q => by
    have := LinearMap.congr_fun hπ q
    simpa using this
  choose r hr using hq
  set g : ι → MvPolynomial σ ℂ := fun i => map (algebraMap ℚ ℂ) (β i) with hg
  have hgg : ∀ j i, fockF (g j) (g i) = ((fockQ (β j) (β i) : ℚ) : ℂ) := fun j i =>
    brFockF_map (β j) (β i)
  have hrj : ∀ j, (r j : ℂ) = ∑ i, star (c i) * ((fockQ (β j) (β i) : ℚ) : ℂ) := by
    intro j
    rw [← hr j, fockF_sum_right]
    simp only [brFockF_map]
  have hrq : ∀ j, r j = ∑ i, fockQ (β j) (β i) * π (star (c i)) := by
    intro j
    have h1 := congrArg π (hrj j)
    rw [hπq, map_sum] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : star (c i) * ((fockQ (β j) (β i) : ℚ) : ℂ) = (fockQ (β j) (β i)) • star (c i) := by
      rw [Rat.smul_def, mul_comm]
    rw [this, LinearMap.map_smul, smul_eq_mul]
  set G0 : MvPolynomial σ ℚ := ∑ i, π (star (c i)) • β i with hG0
  have hG0m : map (algebraMap ℚ ℂ) G0 = ∑ i, ((π (star (c i)) : ℚ) : ℂ) • g i := by
    rw [hG0, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_ratSmul]
  set D : MvPolynomial σ ℂ := ∑ i, (c i - ((π (star (c i)) : ℚ) : ℂ)) • g i with hD
  have hDeq : ∑ i, c i • g i - map (algebraMap ℚ ℂ) G0 = D := by
    rw [hG0m, hD, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_smul]
  have hDj : ∀ j, fockF (g j) D = 0 := by
    intro j
    rw [hD, fockF_sum_right]
    simp only [hgg, star_sub]
    have hs : ∀ i, star (((π (star (c i)) : ℚ) : ℂ)) = ((π (star (c i)) : ℚ) : ℂ) := fun i => by simp
    simp only [hs, sub_mul, Finset.sum_sub_distrib]
    rw [← hrj j, hrq j]
    push_cast
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hDD : fockF D D = 0 := by
    have hjD : ∀ j, fockF D (g j) = 0 := fun j => by
      rw [fockHerm σ (g j) D, hDj j, star_zero]
    conv_lhs => arg 2; rw [hD]
    rw [fockF_sum_right]
    simp [hjD]
  have hD0 : D = 0 := by
    by_contra hne
    have := (fockPos σ D hne).1
    rw [hDD] at this
    simp at this
  refine ⟨G0, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [← sub_eq_zero, hDeq, hD0]
end PI.WGL.BrInt
