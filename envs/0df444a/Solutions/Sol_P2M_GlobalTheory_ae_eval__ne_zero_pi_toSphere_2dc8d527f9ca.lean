-- Prove2me | solution 1 for P2M_GlobalTheory_ae_eval__ne_zero_pi_toSphere_2dc8d527f9ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:49:46.632032+00:00
-- url     : https://prove2.me/submissions/bd0766cf-4539-41a0-93e9-e2b107a16ffb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralLogNormLeHalfLogIntegralSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AeEvalCircleMapNeZero
import Theorems.Thm_GlobalTheory_ae_eval_circleMap_ne_zero
import Theorems.Thm_GlobalTheory_coe_sphereRotation
import Theorems.Thm_GlobalTheory_continuous_sphereRotation
import Theorems.Thm_GlobalTheory_measurePreserving_sphereRotation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_countable_mvPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_eval_psi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_psi_injective
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ae_toSphere
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_sphereRotation
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero



set_option autoImplicit false
open MeasureTheory Metric NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.MultiplicativeHeights
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] [Countable K] (sg : K →+* ℂ)
    (D N : ℕ) :
    ∀ᵐ t ∂(MeasureTheory.Measure.pi fun _ : Fin D =>
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere),
      ∀ p : MvPolynomial (Fin D × Fin (N + 1)) K, p ≠ 0 →
        MvPolynomial.eval₂ sg (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) p ≠ 0 := by
  have := NPB.countable_mvPoly (σ := Fin D × Fin (N + 1)) (R := K)
  set μ : Measure (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) :=
    Measure.pi fun _ : Fin D => (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere with hμ
  have hgen : ∀ᵐ z ∂μ, ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → MvPolynomial.eval₂ sg (blockPoint z) p ≠ 0 := by
    rw [ae_all_iff]; intro a
    rw [ae_all_iff]; intro p
    by_cases hp : IsMultiHomogeneous a p ∧ p ≠ 0
    · have hm : IsMultiHomogeneous a (MvPolynomial.map sg p) :=
        fun s hs => hp.1 s (MvPolynomial.support_map_subset _ _ hs)
      have hm0 : MvPolynomial.map sg p ≠ 0 := fun h0 =>
        hp.2 (MvPolynomial.map_injective sg sg.injective (by rw [h0, map_zero]))
      filter_upwards [ae_toSphere D (N + 1) a _ hm0 hm] with z hz _ _
      rwa [MvPolynomial.eval_map] at hz
    · exact Filter.Eventually.of_forall fun z h1 h2 => absurd ⟨h1, h2⟩ hp
  rw [ae_all_iff]; intro p
  by_cases hp : p = 0
  · exact Filter.Eventually.of_forall fun z h => absurd hp h
  set φ : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → ℂ := fun t =>
    MvPolynomial.eval₂ sg (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) p with hφ
  have hφc : Continuous φ := by
    have : φ = fun t => MvPolynomial.eval (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) (MvPolynomial.map sg p) := by
      funext t; rw [MvPolynomial.eval_map]
    rw [this]
    exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun q => by fun_prop)
  set T : (Fin (N + 1 + D) → ℝ) → (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) :=
    fun θ t i => sphereRotation (θ (Fin.natAdd (N + 1) i)) (t i) with hT
  have hTc : Continuous fun x : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) × (Fin (N + 1 + D) → ℝ) =>
      T x.2 x.1 := by
    refine continuous_pi fun i => ?_
    exact (continuous_sphereRotation (E := EuclideanSpace ℂ (Fin (N + 1)))).comp
      (f := fun x : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) × (Fin (N + 1 + D) → ℝ) =>
        (x.2 (Fin.natAdd (N + 1) i), x.1 i)) (by fun_prop)
  have hTμ : ∀ θ, MeasurePreserving (T θ) μ μ := fun θ =>
    measurePreserving_pi _ _ fun i => measurePreserving_sphereRotation (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))) _
  set q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K :=
    MvPolynomial.rename (fun r : Fin D × Fin (N + 1) => (r.1.succ, r.2)) p with hq
  have hq0 : q ≠ 0 := by
    intro h
    apply hp
    refine MvPolynomial.rename_injective (fun r : Fin D × Fin (N + 1) => (r.1.succ, r.2)) ?_
      (by rw [map_zero]; exact h)
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simpa using h
  have h1 : ∀ᵐ t ∂μ, ∀ᵐ θ ∂(volume : Measure (Fin (N + 1 + D) → ℝ)), φ (T θ t) ≠ 0 := by
    filter_upwards [hgen] with t ht
    have hq' : NPB.psi sg (blockPoint t) q ≠ 0 := fun h0 =>
      hq0 (NPB.psi_injective sg (blockPoint t) ht (by rw [h0, map_zero]))
    filter_upwards [ae_eval_circleMap_ne_zero _ _ hq'] with θ hθ
    rw [NPB.eval_psi, hq, MvPolynomial.eval₂_rename] at hθ
    convert hθ using 1
    simp only [hφ]
    congr 1
  rw [Measure.ae_ae_comm (p := fun t θ => φ (T θ t) ≠ 0)
    ((hφc.comp hTc).measurable (measurableSet_singleton 0).compl)] at h1
  have : (ae (volume : Measure (Fin (N + 1 + D) → ℝ))).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨θ, hθ⟩ := h1.exists
  have h2 : ∀ᵐ t ∂μ, φ t ≠ 0 := by
    rw [← (hTμ θ).map_eq, ae_map_iff (p := fun x => φ x ≠ 0)
      (hTμ θ).measurable.aemeasurable
      (hφc.measurable (measurableSet_singleton 0).compl)]
    exact hθ
  filter_upwards [h2] with t ht _ using ht
end GlobalTheory
