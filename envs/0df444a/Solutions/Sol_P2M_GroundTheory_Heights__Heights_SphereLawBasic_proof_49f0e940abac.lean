-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereLawBasic_proof_49f0e940abac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:08:32.786797+00:00
-- url     : https://prove2.me/submissions/42372454-07cc-4d79-8469-f5c666612d22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawBasic_firstRow_apply_5143842c4916
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawBasic_sphereNormalize_eq_616676863ebf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawBasic_firstRow_eq_zero_e778849ddfbb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawBasic_volume_firstRow_mem_1fba3e2dc8f5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory ProbabilityTheory
noncomputable section
open SphereLawBasic
namespace GroundTheory.Heights₂.Heights
namespace SphereLawBasic
theorem _root_.solution : SphereLawBasic.Statement := by
  intro N hN
  have hf : Measurable fun (u : Fin 1 × Fin N → ℂ) (j : Fin N) ↦
      sphereNormalize (HermNorm.std N) 1 u (0, j) := by
    unfold sphereNormalize
    simp only [HermNorm.std_norm_eq]
    fun_prop
  have hbot : (⊥ : Submodule ℂ (Fin N → ℂ)) ≠ ⊤ := by
    intro h
    have hmem : (Pi.single ⟨0, hN⟩ 1 : Fin N → ℂ) ∈ (⊥ : Submodule ℂ (Fin N → ℂ)) :=
      h ▸ Submodule.mem_top
    simpa using congrFun ((Submodule.mem_bot ℂ).mp hmem) ⟨0, hN⟩
  have h0 : ∀ᵐ u ∂(volume[|sphereBall (HermNorm.std N) 1]), firstRow N u ≠ 0 := by
    refine cond_absolutelyContinuous.ae_le ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (volume_firstRow_mem N ⊥ hbot)] with u hu
    simpa using hu
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [sphereLaw, ae_map_iff hf.aemeasurable (measurableSet_eq_fun (by fun_prop) measurable_const)]
    filter_upwards [h0] with u hu
    have hs : 0 < ∑ i, ‖u (0, i)‖ ^ 2 := lt_of_not_ge fun h ↦ hu (firstRow_eq_zero N u h)
    have key : ∀ j, ‖sphereNormalize (HermNorm.std N) 1 u (0, j)‖ ^ 2 =
        (∑ i, ‖u (0, i)‖ ^ 2)⁻¹ * ‖u (0, j)‖ ^ 2 := by
      intro j
      have e := congrFun (sphereNormalize_eq N u) j
      rw [e]
      simp only [Pi.smul_apply, smul_eq_mul, firstRow_apply, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
        Real.sq_sqrt hs.le]
    simp only [key, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hs.ne'
  · intro S hS
    have hSm : MeasurableSet (S : Set (Fin N → ℂ)) :=
      (S.restrictScalars ℝ).closed_of_finiteDimensional.measurableSet
    rw [sphereLaw, Measure.map_apply hf hSm]
    refine measure_mono_null ?_ (cond_absolutelyContinuous (volume_firstRow_mem N S hS))
    intro u hu
    simp only [Set.mem_preimage, SetLike.mem_coe] at hu
    rw [sphereNormalize_eq] at hu
    show firstRow N u ∈ S
    by_cases hc : ((√(∑ i, ‖u (0, i)‖ ^ 2) : ℝ) : ℂ) = 0
    · have hle : ∑ i, ‖u (0, i)‖ ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp (by exact_mod_cast hc)
      rw [firstRow_eq_zero N u hle]
      exact S.zero_mem
    · have := S.smul_mem ((√(∑ i, ‖u (0, i)‖ ^ 2) : ℝ) : ℂ) hu
      rwa [smul_smul, mul_inv_cancel₀ hc, one_smul] at this
end SphereLawBasic
end GroundTheory.Heights₂.Heights
