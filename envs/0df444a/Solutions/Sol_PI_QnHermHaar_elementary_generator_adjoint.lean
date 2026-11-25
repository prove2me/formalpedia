-- Prove2me | solution 1 for PI.QnHermHaar.elementary_generator_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:38:52.499827+00:00
-- url     : https://prove2.me/submissions/e327ffad-8455-4c32-9d93-bf0867e0c81c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_rdV_neg
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_supp_single
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_supp_hpart1
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_supp_hpart2
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_inU_hpart1
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_inU_hpart2
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_lie_of
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_hpart1_conj
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_hpart2_conj
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_ec_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
open HermitianAdjointLemmas
namespace PI.QnHermHaar
theorem _root_.solution : EabAdjFrom := by
  intro hRd _hP hT hI k r i μ hμ a b f₁ f₂ h₁ h₂
  set Z : Mx k r := Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) with hZ
  have hX1 : inLieLev k r i (hpart1 (Hpk k r) Z) :=
    lie_of (inU_hpart1 Z) (supp_hpart1 (supp_single i a b))
  have hX2 : inLieLev k r i (hpart2 (Hpk k r) Z) :=
    lie_of (inU_hpart2 Z) (supp_hpart2 (supp_single i a b))
  set Ψ : (Mx k r → ℂ) → Mx k r → ℂ := fun f g =>
    ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EH k r (posL k r i c) (posL k r i d) f g with hΨ
  have hE : ∀ f g, EH k r (posL k r i a) (posL k r i b) f g =
      RdV (hpart1 (Hpk k r) Z) f g + Complex.I * RdV (hpart2 (Hpk k r) Z) f g := fun f g => rfl
  have hPsi : ∀ f, SmoothLev k r i Set.univ f → ∀ g ∈ Glev k r i,
      Ψ f g = -RdV (hpart1 (Hpk k r) Z) f g + Complex.I * RdV (hpart2 (Hpk k r) Z) f g := by
    intro f hf g hg
    rw [hΨ]
    dsimp only
    rw [← ec_expand hf hg a b, hpart1_conj, hpart2_conj, rdV_neg, smul_eq_mul]
  have hR1 : ∀ f, SmoothLev k r i Set.univ f → ∀ g ∈ Glev k r i,
      RdV (hpart1 (Hpk k r) Z) f g = (EH k r (posL k r i a) (posL k r i b) f g - Ψ f g) / 2 := by
    intro f hf g hg
    rw [hE, hPsi f hf g hg]
    ring
  have hR2 : ∀ f, SmoothLev k r i Set.univ f → ∀ g ∈ Glev k r i,
      RdV (hpart2 (Hpk k r) Z) f g =
        (EH k r (posL k r i a) (posL k r i b) f g + Ψ f g) / (2 * Complex.I) := by
    intro f hf g hg
    rw [hE, hPsi f hf g hg]
    field_simp
    ring
  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ Glev k r i := by
    rw [ae_iff]
    exact hμ.conc

  have iA : Integrable (fun x : Mt k r =>
      EH k r (posL k r i a) (posL k r i b) f₁ (Matrix.of x) * star (f₂ (Matrix.of x))) μ :=
    hI k r i μ hμ _ _ (hT k r i a b f₁ h₁) h₂
  have iB : Integrable (fun x : Mt k r => Ψ f₁ (Matrix.of x) * star (f₂ (Matrix.of x))) μ := by
    have e : (fun x : Mt k r => Ψ f₁ (Matrix.of x) * star (f₂ (Matrix.of x))) = fun x =>
        ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) *
          (EH k r (posL k r i c) (posL k r i d) f₁ (Matrix.of x) * star (f₂ (Matrix.of x))) := by
      funext x
      simp only [hΨ, Finset.sum_mul, smul_eq_mul, mul_assoc]
    rw [e]
    exact integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ =>
      (hI k r i μ hμ _ _ (hT k r i c d f₁ h₁) h₂).const_mul _
  have iC : Integrable (fun x : Mt k r =>
      f₁ (Matrix.of x) * star (EH k r (posL k r i a) (posL k r i b) f₂ (Matrix.of x))) μ :=
    hI k r i μ hμ _ _ h₁ (hT k r i a b f₂ h₂)
  have iD : Integrable (fun x : Mt k r => f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x))) μ := by
    have e : (fun x : Mt k r => f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x))) = fun x =>
        ∑ c, ∑ d, star (Hm k r i c b * Hm k r i a d) *
          (f₁ (Matrix.of x) * star (EH k r (posL k r i c) (posL k r i d) f₂ (Matrix.of x))) := by
      funext x
      simp only [hΨ, star_sum, Finset.mul_sum, smul_eq_mul, star_mul']
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      ring
    rw [e]
    exact integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ =>
      (hI k r i μ hμ _ _ h₁ (hT k r i c d f₂ h₂)).const_mul _

  have s1 := hRd k r i μ hμ _ f₁ f₂ hX1 h₁.1 h₂.1 h₁.2 h₂.2
  have s2 := hRd k r i μ hμ _ f₁ f₂ hX2 h₁.1 h₂.1 h₁.2 h₂.2
  have l1 : (∫ x : Mt k r, RdV (hpart1 (Hpk k r) Z) f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) =
      (1 / 2 : ℂ) * ((∫ x : Mt k r, EH k r (posL k r i a) (posL k r i b) f₁ (Matrix.of x) *
        star (f₂ (Matrix.of x)) ∂μ) - ∫ x : Mt k r, Ψ f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) := by
    rw [← integral_sub iA iB, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hR1 f₁ h₁.1 _ hx]
    ring
  have r1 : (∫ x : Mt k r, f₁ (Matrix.of x) * star (RdV (hpart1 (Hpk k r) Z) f₂ (Matrix.of x)) ∂μ) =
      (1 / 2 : ℂ) * ((∫ x : Mt k r, f₁ (Matrix.of x) *
        star (EH k r (posL k r i a) (posL k r i b) f₂ (Matrix.of x)) ∂μ) -
          ∫ x : Mt k r, f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x)) ∂μ) := by
    rw [← integral_sub iC iD, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hR1 f₂ h₂.1 _ hx, star_div₀, star_sub, star_ofNat]
    ring
  have l2 : (∫ x : Mt k r, RdV (hpart2 (Hpk k r) Z) f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) =
      (1 / (2 * Complex.I)) * ((∫ x : Mt k r, EH k r (posL k r i a) (posL k r i b) f₁ (Matrix.of x) *
        star (f₂ (Matrix.of x)) ∂μ) + ∫ x : Mt k r, Ψ f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) := by
    rw [← integral_add iA iB, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hR2 f₁ h₁.1 _ hx]
    ring
  have r2 : (∫ x : Mt k r, f₁ (Matrix.of x) * star (RdV (hpart2 (Hpk k r) Z) f₂ (Matrix.of x)) ∂μ) =
      -(1 / (2 * Complex.I)) * ((∫ x : Mt k r, f₁ (Matrix.of x) *
        star (EH k r (posL k r i a) (posL k r i b) f₂ (Matrix.of x)) ∂μ) +
          ∫ x : Mt k r, f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x)) ∂μ) := by
    rw [← integral_add iC iD, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hR2 f₂ h₂.1 _ hx, star_div₀, star_add, star_mul', star_ofNat, Complex.star_def, Complex.conj_I]
    field_simp
  rw [l1, r1] at s1
  rw [l2, r2] at s2
  show (∫ x : Mt k r, EH k r (posL k r i a) (posL k r i b) f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) =
    ∫ x : Mt k r, f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x)) ∂μ
  set A := ∫ x : Mt k r, EH k r (posL k r i a) (posL k r i b) f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ
  set B := ∫ x : Mt k r, Ψ f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ
  set C := ∫ x : Mt k r, f₁ (Matrix.of x) * star (EH k r (posL k r i a) (posL k r i b) f₂ (Matrix.of x)) ∂μ
  set D := ∫ x : Mt k r, f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x)) ∂μ
  have hk : (1 / (2 * Complex.I) : ℂ) ≠ 0 := by simp
  have e2 : A + B = C + D := mul_left_cancel₀ hk (by rw [s2]; ring)
  linear_combination s1 + (1 / 2 : ℂ) * e2
end PI.QnHermHaar
