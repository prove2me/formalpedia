-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_proof_337a19539709
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:40:45.137483+00:00
-- url     : https://prove2.me/submissions/2a34afd1-176b-4268-bee8-e12a34ac358b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartZeroSet
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneousAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartZeroSet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_homogenize_c2c6fe846b43
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_linForm_717c7b580fff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_exists_segre_smul_bfffda87fde7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_segre_of_isEmpty_e030d840b915
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_proof_17ca30ede7f1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Finset
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets
open GroundTheory.Heights₂.Heights.GoodChartZeroSet
namespace GroundTheory.Heights₂.Heights.GoodChartZeroSet
theorem _root_.solution : Statement := by
  intro K _ ι _ P e m σ Ψ hP
  classical
  apply Set.Subset.antisymm
  swap
  · intro x hx q hq
    rw [projChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx
  intro x hx
  have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ projChartSet P σ Ψ, eval y q = 0) → eval x q = 0 :=
    fun q hq => hx q (by rw [projChartIdeal, mem_vanishingIdeal_iff]; exact hq)
  have hseg : ∀ z : (Σ k, ι k) → ℂ, (fun i' => segre z (σ (σ.symm i'))) = segre z := fun z => by
    funext i'; rw [Equiv.apply_symm_apply]

  have hx1 : Ψ (fun i' => x (σ.symm i')) 0 = 1 := by
    have h := hv (linForm σ Ψ - 1) (by
      rintro _ ⟨z, -, hz1, rfl⟩
      rw [map_sub, eval_linForm, map_one, hseg, hz1, sub_self])
    rw [map_sub, eval_linForm, map_one] at h
    exact sub_eq_zero.1 h
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have h0 : (fun i' => x (σ.symm i')) = 0 := funext fun i' => h _
    rw [h0, map_zero] at hx1
    exact zero_ne_one hx1

  have ha1 : IsEmpty K → x a = 1 := fun hK => by
    have h := hv (X a - 1) (by
      rintro _ ⟨z, -, -, rfl⟩
      simp [segre_of_isEmpty hK])
    simpa [sub_eq_zero] using h

  have hzero : (x a)⁻¹ • x ∈ zeroSet (segreChartIdeal P σ (σ a)) := by
    intro f hf
    rw [segreChartIdeal, mem_vanishingIdeal_iff] at hf
    have hg := hv (X a * ∑ d ∈ range (f.totalDegree + 1),
        X a ^ (f.totalDegree - d) * homogeneousComponent d f) (by
      rintro _ ⟨z, hz, -, rfl⟩
      by_cases h0 : segre z (σ a) = 0
      · simp [h0]
      · rw [eval_homogenize f le_rfl a _ h0]
        obtain ⟨z', hz', hz'e⟩ := exists_segre_smul P hP hz (inv_ne_zero h0)
          (fun hK => by rw [segre_of_isEmpty hK, inv_one])
        refine mul_eq_zero_of_right _ (hf _ ⟨z', hz', ?_, ?_⟩)
        · rw [hz'e, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ h0]
        · funext b
          rw [hz'e]
          rfl)
    rw [eval_homogenize f le_rfl a x ha] at hg
    exact (mul_eq_zero.1 hg).resolve_left (pow_ne_zero _ ha)
  rw [SegreChartZeroSet.proof K ι P m σ (σ a) hP] at hzero
  obtain ⟨z', hz', -, hz'e⟩ := hzero
  obtain ⟨z, hz, hze⟩ := exists_segre_smul P hP hz' ha ha1
  have hxz : x = fun b => segre z (σ b) := by
    funext b
    have hb := congrFun hz'e b
    simp only [Pi.smul_apply, smul_eq_mul] at hb
    rw [hze, Pi.smul_apply, smul_eq_mul, ← hb, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  refine ⟨z, hz, ?_, hxz⟩
  rw [← hseg z, ← hx1, hxz]
end GroundTheory.Heights₂.Heights.GoodChartZeroSet
