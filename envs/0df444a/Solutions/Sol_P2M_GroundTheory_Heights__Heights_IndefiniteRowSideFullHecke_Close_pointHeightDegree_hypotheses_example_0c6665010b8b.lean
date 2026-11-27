-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_pointHeightDegree_hypotheses_example_0c6665010b8b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:58:02.42029+00:00
-- url     : https://prove2.me/submissions/f44afd0c-3e3f-4e58-87d0-cd7925fdbdb6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_ratBasis_apply_ca260be5feeb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ mCoordIdeal chartLat chartLatNm secM mcPts IsArithVar)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open AddBlockData
open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution :
    (∀ σ : ℚ →+* ℂ, ((fun _ : ℚ →+* ℂ ↦ (1 : Matrix (Fin 1) (Fin 1) ℂ)) σ).PosDef) ∧
    (∀ σ : ℚ →+* ℂ, (fun _ ↦ (1 : Matrix (Fin 1) (Fin 1) ℂ)) (ComplexEmbedding.conjugate σ) =
      (1 : Matrix (Fin 1) (Fin 1) ℂ).map (starRingEnd ℂ)) ∧
    (∀ u, (HermLine.standard (fun _ : Unit ↦ 0)).deg u = 1) ∧
    (∀ (σ : ℚ →+* ℂ) (w : Fin 1 → ℂ), w ≠ 0 →
      (HermLine.standard (fun _ : Unit ↦ 0)).metric
          (fun _ t ↦ σ (ratBasis (pairEquiv.symm t).1 : ℚ) *
            w (pairEquiv.symm t).2) =
        hermNorm 1 w) ∧
    (∀ (σ' : ℚ →+* ℂ) (x y : (HermitianBundle.standard ℚ 1).carrier),
      ((HermitianBundle.standard ℚ 1).metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 ℚ] x)
          ((1 : ComplexAt σ') ⊗ₜ[𝓞 ℚ] y) =
        star (fun j ↦ σ' (stdPhi x j : ℚ)) ⬝ᵥ
          ((1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ fun j ↦ σ' (stdPhi y j : ℚ))) ∧
    (fun _ ↦ (1 : 𝓞 ℚ) : Fin 1 → 𝓞 ℚ) ≠ 0 := by
  refine ⟨fun _ ↦ Matrix.PosDef.one, fun _ ↦ by simp, fun _ ↦ rfl, ?_, ?_, ?_⟩
  · intro σ w _
    change ∏ k : Unit, l2Norm _ = _
    rw [Fintype.prod_unique]
    generalize hp : (pairEquiv.symm 0).2 = t
    rw [Fin.fin_one_eq_zero t] at hp
    simp [l2Norm, hermNorm, ratBasis_apply, dotProduct, Complex.conj_mul', hp]
    rw [← Complex.ofReal_pow, Complex.ofReal_re, Real.sqrt_sq (norm_nonneg _)]
  · intro σ' x y
    refine (HermitianMetric.standard_inner (K := ℚ) (Fin 1) σ'
      ((1 : ComplexAt σ') ⊗ₜ[𝓞 ℚ] (x : Fin 1 → 𝓞 ℚ))
      ((1 : ComplexAt σ') ⊗ₜ[𝓞 ℚ] (y : Fin 1 → 𝓞 ℚ))).trans ?_
    show ∑ i : Fin 1, starRingEnd ℂ (σ' ((x : Fin 1 → 𝓞 ℚ) i : ℚ) * (ofComplex σ').symm 1) *
        (σ' ((y : Fin 1 → 𝓞 ℚ) i : ℚ) * (ofComplex σ').symm 1) = _
    simp [dotProduct, stdPhi, mul_comm]
    rfl
  · intro h
    have := congrFun h 0
    exact one_ne_zero this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
