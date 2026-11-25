-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_meanShift_mul_d1c5c8b18f4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:40.148397+00:00
-- url     : https://prove2.me/submissions/737caf38-7a7f-4af9-820a-f523e55066b8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_meanShift_mul_of_ext_0ca9688a2a35

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ChowHeightCycleEq
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChowHeightCycleEq
theorem _root_.solution (hA : ChowHeightMul.Statement) {K : Type} [Field K] [NumberField K]
    (σ : K →+* ℂ) (hσ : ComplexEmbedding.IsReal σ)
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (f g : MvPolynomial (Fin (e + 1) × Fin n) K) (hf : f ≠ 0) (hg : g ≠ 0) :
    meanShift S σ (f * g) = meanShift S σ f + meanShift S σ g := by
  set p : Polynomial K := Polynomial.X ^ 2 + Polynomial.C 1 with hp
  have hroot : ∀ x : K, ¬ p.IsRoot x := by
    intro x hx
    have h1 : σ x ^ 2 + 1 = 0 := by
      have := congrArg σ hx
      simpa [hp] using this
    have him : (σ x).im = 0 := by
      have h2 := RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp hσ) x
      rw [ComplexEmbedding.conjugate_coe_eq] at h2
      exact Complex.conj_eq_iff_im.mp h2
    have h3 := congrArg Complex.re h1
    simp [sq, him] at h3
    nlinarith [mul_self_nonneg (σ x).re]
  have hdeg : p.natDegree = 2 := by
    rw [hp]; compute_degree!
  have hirr : Irreducible p :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) hroot
  have : Fact (Irreducible p) := ⟨hirr⟩
  have hmon : p.Monic := Polynomial.monic_X_pow_add_C 1 (by norm_num)
  have : Module.Finite K (AdjoinRoot p) := hmon.finite_adjoinRoot
  have : NumberField (AdjoinRoot p) := NumberField.of_module_finite K (AdjoinRoot p)
  have heval : p.eval₂ σ Complex.I = 0 := by simp [hp]
  let τ : AdjoinRoot p →+* ℂ := AdjoinRoot.lift σ Complex.I heval
  have hτj : τ.comp (AdjoinRoot.of p) = σ := by
    ext x
    exact AdjoinRoot.lift_of heval
  have hτ : ¬ ComplexEmbedding.IsReal τ := by
    intro h
    have h2 := RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp h) (AdjoinRoot.root p)
    rw [ComplexEmbedding.conjugate_coe_eq] at h2
    have h3 : τ (AdjoinRoot.root p) = Complex.I := AdjoinRoot.lift_root heval
    rw [h3, Complex.conj_I] at h2
    have h4 := congrArg Complex.im h2
    simp at h4
    norm_num at h4
  exact meanShift_mul_of_ext hA (AdjoinRoot.of p) τ hτ σ hσ hτj S hS f g hf hg
end GroundTheory.Heights₂.Heights.ChowHeightCycleEq
