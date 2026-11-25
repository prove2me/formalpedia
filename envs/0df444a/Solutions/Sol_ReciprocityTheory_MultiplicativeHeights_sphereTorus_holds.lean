-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sphereTorus_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:31:22.95653+00:00
-- url     : https://prove2.me/submissions/a7ff0c1a-2d8d-4490-969d-7a382acc1dec

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusB
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusC
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorus
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_blockPoint_blockRot
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_blockSphereProb_coord_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_isProbabilityMeasure_sphereProb
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurePreserving_blockRot
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_norm_blockPoint_le
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_scaledTorusMean_le_torusMean


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (hInt : SphereLogIntegrableStatement) (hBasic : TorusMeanBasicStatement) :
    SphereLeTorusStatement := by
  intro B n a f hn hf hhom
  haveI : IsProbabilityMeasure (sphereProb n) := isProbabilityMeasure_sphereProb hn
  haveI : IsProbabilityMeasure (blockSphereProb B n) := by
    unfold blockSphereProb; infer_instance
  haveI : IsProbabilityMeasure ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨by simp⟩
  haveI : IsProbabilityMeasure (torusProb (Fin B × Fin n)) := by
    unfold torusProb; infer_instance

  have hh : Integrable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖)
      (blockSphereProb B n) := hInt B n a f hf hhom

  have hslice : ∀ θ : Fin B × Fin n → ℝ,
      Integrable (fun z => Real.log ‖MvPolynomial.eval
        (fun p => blockPoint z p * torusPoint θ p) f‖) (blockSphereProb B n) ∧
      ∫ z, Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖
        ∂(blockSphereProb B n) = blockSphereMean B n f ∧
      ∫ z, ‖Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖‖
        ∂(blockSphereProb B n) =
        ∫ z, ‖Real.log ‖MvPolynomial.eval (blockPoint z) f‖‖ ∂(blockSphereProb B n) := by
    intro θ
    have hmp := measurePreserving_blockRot (B := B) (n := n) θ
    have e : ∀ z, (fun p => blockPoint z p * torusPoint θ p) = blockPoint (blockRot θ z) := by
      intro z; rw [blockPoint_blockRot]
    simp only [e]
    refine ⟨?_, ?_, ?_⟩
    · have h1 : Integrable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖)
          (Measure.map (blockRot θ) (blockSphereProb B n)) := by
        rw [hmp.map_eq]; exact hh
      exact h1.comp_measurable hmp.measurable
    · have hA : AEStronglyMeasurable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖)
          (Measure.map (blockRot θ) (blockSphereProb B n)) := by
        rw [hmp.map_eq]; exact hh.aestronglyMeasurable
      have h2 := integral_map hmp.measurable.aemeasurable hA
      rw [hmp.map_eq] at h2
      exact h2.symm
    · have hA : AEStronglyMeasurable (fun z => ‖Real.log ‖MvPolynomial.eval (blockPoint z) f‖‖)
          (Measure.map (blockRot θ) (blockSphereProb B n)) := by
        rw [hmp.map_eq]; exact hh.norm.aestronglyMeasurable
      have h2 := integral_map hmp.measurable.aemeasurable hA
      rw [hmp.map_eq] at h2
      exact h2.symm

  have hcont : Continuous (fun q : BlockSphere B n × (Fin B × Fin n → ℝ) =>
      MvPolynomial.eval (fun p => blockPoint q.1 p * torusPoint q.2 p) f) := by
    refine (MvPolynomial.continuous_eval f).comp (continuous_pi fun p => ?_)
    refine Continuous.mul ?_ ?_
    · unfold blockPoint spherePoint
      fun_prop
    · unfold torusPoint
      fun_prop
  have hgm : AEStronglyMeasurable (fun q : BlockSphere B n × (Fin B × Fin n → ℝ) =>
      Real.log ‖MvPolynomial.eval (fun p => blockPoint q.1 p * torusPoint q.2 p) f‖)
      ((blockSphereProb B n).prod (torusProb (Fin B × Fin n))) :=
    (Real.measurable_log.comp hcont.norm.measurable).aestronglyMeasurable
  have hgi : Integrable (fun q : BlockSphere B n × (Fin B × Fin n → ℝ) =>
      Real.log ‖MvPolynomial.eval (fun p => blockPoint q.1 p * torusPoint q.2 p) f‖)
      ((blockSphereProb B n).prod (torusProb (Fin B × Fin n))) := by
    rw [integrable_prod_iff' hgm]
    refine ⟨Filter.Eventually.of_forall fun θ => (hslice θ).1, ?_⟩
    simp only [fun θ => (hslice θ).2.2]
    exact integrable_const _

  have hae : ∀ᵐ z ∂(blockSphereProb B n), ∀ p, blockPoint z p ≠ 0 := by
    rw [ae_iff]
    simpa [not_forall] using blockSphereProb_coord_zero (B := B) (n := n)
  calc blockSphereMean B n f
      = ∫ θ, ∫ z, Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖
          ∂(blockSphereProb B n) ∂(torusProb (Fin B × Fin n)) := by
        simp only [fun θ => (hslice θ).2.1]
        simp
    _ = ∫ z, ∫ θ, Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖
          ∂(torusProb (Fin B × Fin n)) ∂(blockSphereProb B n) :=
        (integral_integral_swap hgi).symm
    _ = ∫ z, scaledTorusMean (blockPoint z) f ∂(blockSphereProb B n) := rfl
    _ ≤ ∫ _z, torusMean f ∂(blockSphereProb B n) := by
        refine integral_mono_ae hgi.integral_prod_left (integrable_const _) ?_
        filter_upwards [hae] with z hz
        exact scaledTorusMean_le_torusMean hBasic f hf (blockPoint z) hz (norm_blockPoint_le z)
    _ = torusMean f := by simp
end ReciprocityTheory.MultiplicativeHeights
