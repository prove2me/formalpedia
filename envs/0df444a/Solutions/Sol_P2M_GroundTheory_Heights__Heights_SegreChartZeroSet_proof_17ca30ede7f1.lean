-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_proof_17ca30ede7f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:37.362356+00:00
-- url     : https://prove2.me/submissions/e7842c23-0b34-4f5b-82bf-20166e9bbc95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartZeroSet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartZeroSet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_scaleAll_mem_cc6c842d0898
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_eval_liftPoly_7a6b03adb6c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_blockNonzero_4a49d0f77c5b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_segre_apply_6eeb1c8817f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_segre_chartLift_cde5bc6f2110
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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets
open GroundTheory.Heights₂.Heights.SegreChartZeroSet
namespace GroundTheory.Heights₂.Heights.SegreChartZeroSet
theorem _root_.solution : Statement := by
  intro K _ ι _ P m σ i hP
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ segreChartSet P σ i, eval y q = 0) → eval x q = 0 :=
      fun q hq => hx q (by rw [segreChartIdeal, mem_vanishingIdeal_iff]; exact hq)
    have ha : x (σ.symm i) = 1 := by
      have h := hv (X (σ.symm i) - 1) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        simp [hzi])
      rw [map_sub, eval_X, map_one] at h
      exact sub_eq_zero.1 h
    have hb : ∀ i' : (k : K) → ι k,
        x (σ.symm i') = ∏ k, x (σ.symm (Function.update i k (i' k))) := by
      intro i'
      have h := hv (X (σ.symm i') - ∏ k, X (σ.symm (Function.update i k (i' k)))) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        have hs : ∏ k, segre z (Function.update i k (i' k)) = segre z i' := by
          have h1 := congrFun (segre_chartLift σ i z hzi) i'
          simpa [segre, chartLift] using h1
        rw [map_sub, eval_X, map_prod]
        simp only [eval_X, Equiv.apply_symm_apply]
        rw [hs, sub_self])
      rw [map_sub, eval_X, map_prod] at h
      simp only [eval_X] at h
      exact sub_eq_zero.1 h
    have hc : ∀ f ∈ P, eval (chartLift σ i x) (map (Int.castRingHom ℂ) f) = 0 := by
      intro f hf
      rw [← eval_liftPoly]
      refine hv _ ?_
      rintro _ ⟨z, hz, hzi, rfl⟩
      rw [eval_liftPoly]
      have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
        have h1 : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
        rw [hzi] at h1
        exact one_ne_zero h1
      have hcl : chartLift σ i (fun a => segre z (σ a)) = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
        funext ⟨k, j⟩
        rw [chartLift_segre_apply σ i z hzi, mul_comm]
      rw [hcl]
      exact (scaleAll_mem P hP (fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz).2 f hf
    refine ⟨chartLift σ i x, ⟨chartLift_blockNonzero σ i ha, hc⟩, ?_, ?_⟩
    · show ∏ k, chartLift σ i x ⟨k, i k⟩ = 1
      simp [chartLift, ha]
    · funext a
      show x a = ∏ k, chartLift σ i x ⟨k, σ a k⟩
      simp only [chartLift]
      rw [← hb, Equiv.symm_apply_apply]
  · intro x hx q hq
    rw [segreChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx
end GroundTheory.Heights₂.Heights.SegreChartZeroSet
