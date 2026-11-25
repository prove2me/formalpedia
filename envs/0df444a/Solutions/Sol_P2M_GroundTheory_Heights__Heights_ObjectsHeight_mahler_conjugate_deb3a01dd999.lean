-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_mahler_conjugate_deb3a01dd999
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:45.407189+00:00
-- url     : https://prove2.me/submissions/463e880f-bb49-4ceb-8574-1839ba8e16ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_hermNorm_490b6c9ab1d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_integral_cond_linearEquiv_66821f484f1d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_eval_map_conjugate_4d0cfc76d7c3

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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
variable {k : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsHeight
theorem _root_.solution {K : Type*} [Field K] (h h' : HermNorm n)
    (hc : ∀ u, h'.norm (star u) = h.norm u) (σ : K →+* ℂ) (f : MvPolynomial (Fin k × Fin n) K) :
    mahler h' k (f.map (ComplexEmbedding.conjugate σ)) = mahler h k (f.map σ) := by
  have hc' : ∀ u, h'.norm u = h.norm (star u) := fun u => by rw [← hc, star_star]
  let Cj : (Fin k × Fin n → ℂ) ≃ₗ[ℝ] (Fin k × Fin n → ℂ) :=
    LinearEquiv.piCongrRight fun _ => Complex.conjAe.toLinearEquiv
  have hCj : ∀ u, Cj u = star u := fun u => rfl
  let N : (Fin k × Fin n → ℂ) → (Fin k × Fin n → ℂ) := fun u ij =>
    ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij
  let G : (Fin k × Fin n → ℂ) → ℝ := fun u => Real.log ‖eval (N u) (f.map σ)‖
  have hN : Measurable N := by
    refine measurable_pi_lambda _ fun ij => ?_
    exact ((Complex.measurable_ofReal.comp ((continuous_hermNorm h).comp
      (continuous_pi fun j => continuous_apply (ij.1, j))).measurable).inv).mul
      (measurable_pi_apply ij)
  have hG : Measurable G :=
    Real.measurable_log.comp ((continuous_norm.comp (continuous_eval _)).measurable.comp hN)
  have hset : {u : Fin k × Fin n → ℂ | ∀ i, h'.norm (fun j => u (i, j)) < 1} =
      Cj ⁻¹' {u | ∀ i, h.norm (fun j => u (i, j)) < 1} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hCj, hc']
    rfl
  have hpt : ∀ u : Fin k × Fin n → ℂ,
      Real.log ‖eval (fun ij => ((h'.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij)
        (f.map (ComplexEmbedding.conjugate σ))‖ = G (Cj u) := by
    intro u
    have hNs : N (Cj u) = star fun ij => ((h'.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij := by
      funext ij
      have h1 : h'.norm (fun j => u (ij.1, j)) = h.norm (fun j => star (u (ij.1, j))) :=
        hc' _
      simp only [N, hCj, Pi.star_apply]
      rw [← h1, star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal]
    simp only [G, hNs, eval_map_conjugate, Complex.norm_conj]
  unfold mahler sphereMean
  simp only [MeasureTheory.average, Measure.restrict_apply_univ]
  show ∫ u, Real.log ‖eval (fun ij => ((h'.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij)
        (f.map (ComplexEmbedding.conjugate σ))‖
      ∂cond volume {u : Fin k × Fin n → ℂ | ∀ i, h'.norm (fun j => u (i, j)) < 1} =
    ∫ u, G u ∂cond volume {u : Fin k × Fin n → ℂ | ∀ i, h.norm (fun j => u (i, j)) < 1}
  simp_rw [hpt, hset]
  exact integral_cond_linearEquiv Cj _ G hG
end GroundTheory.Heights₂.Heights.ObjectsHeight
