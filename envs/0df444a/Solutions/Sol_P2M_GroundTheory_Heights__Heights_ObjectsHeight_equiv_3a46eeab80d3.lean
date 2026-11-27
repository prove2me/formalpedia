-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_equiv_3a46eeab80d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:07:39.180397+00:00
-- url     : https://prove2.me/submissions/1dc3342d-45c0-4278-8c54-32971d1db5e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_norm_fe0404d8d94b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_dualNorm_fa5369e88d9b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_fsLog_1e3034da99c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_exists_eq_ofPointMatrix_f9a576162836
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_std_eq_ofPointMatrix_one_d852079b1f83
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_sphereMean_eq_integral_c09b214a98e7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_mahler_eq_chowMean_15919a81f341
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_gaussNorm_eq_coeffGaussNorm_6e05ff990d93
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_finsum_log_gaussNorm_2b096fa7246f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_finGaussLog_eq_6c42ce4ca209
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_chowHt_eq_chowHeight_9bf18eb67ddd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_chowHt_eq_chowHt_places_1244538cd039

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
theorem _root_.solution :
    (∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S),
      (∀ u, (ofPointMatrix S hS).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) ∧
      (∀ y, (ofPointMatrix S hS).dualNorm y = (IndefiniteRowSideFullHecke.ArithBezout.pointMetric S hS).ρ y) ∧
      (∀ u y, fsLog (ofPointMatrix S hS) u y =
        IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u (fun p => y p.2))) ∧
    (∀ (n : ℕ) (h : HermNorm n), ∃ (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S),
      h = ofPointMatrix S hS) ∧
    (∀ n : ℕ, HermNorm.std n = ofPointMatrix 1 isUnit_one) ∧
    (∀ (n k : ℕ) (S : Matrix (Fin n) (Fin n) ℂ), IsUnit S → ∀ h : HermNorm n,
      (∀ u, h.norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) →
        (∀ g : (Fin k × Fin n → ℂ) → ℝ, Measurable g →
          sphereMean h k g = ∫ u, g u ∂IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S k) ∧
        ∀ f : MvPolynomial (Fin k × Fin n) ℂ, mahler h k f = IndefiniteRowSideFullHecke.ArithBezout.chowMean S k f) ∧
    (∀ (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (ι : Type) (f : MvPolynomial ι K),
      gaussNorm v f = ReciprocityTheory.ChartRestriction.G.Geo.coeffGaussNorm (HeightOneSpectrum.adicAbv K v) f) ∧
    (∀ (K : Type) [Field K] [NumberField K] (ι : Type) (f : MvPolynomial ι K),
      ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f) =
        ∑ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K),
          Real.log (ReciprocityTheory.ChartRestriction.G.Geo.coeffGaussNorm v.1 f)) ∧
    (∀ (ι : Type) (f : MvPolynomial ι ℚ), IndefiniteRowSideFullHecke.ArithBezout.finGaussLog f =
      ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), Real.log (gaussNorm v f)) ∧
    (∀ (n e δ : ℕ) (H : ArchData ℚ n) (S : Matrix (Fin n) (Fin n) ℂ), IsUnit S →
      (∀ σ u, (H.normAt σ).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) →
        ∀ f : MvPolynomial (Fin (e + 1) × Fin n) ℚ,
          chowHt H (e + 1) δ f = IndefiniteRowSideFullHecke.ArithBezout.chowHeight S f δ) ∧
    (∀ (K : Type) [Field K] [NumberField K] (n e δ : ℕ) (H : ArchData K n)
      (S : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ w, IsUnit (S w)) →
      (∀ w u, (H.normAt w.embedding).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm (S w) u) →
        ∀ f : MvPolynomial (Fin (e + 1) × Fin n) K,
          chowHt H (e + 1) δ f =
            ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1)) f δ) :=
  ⟨fun _ S hS => ⟨ofPointMatrix_norm S hS, ofPointMatrix_dualNorm S hS, ofPointMatrix_fsLog S hS⟩,
    fun _ h => exists_eq_ofPointMatrix h,
    fun _ => std_eq_ofPointMatrix_one,
    fun _ _ S hS h hh => ⟨fun g hg => sphereMean_eq_integral S hS h hh g hg,
      fun f => mahler_eq_chowMean S hS h hh f⟩,
    fun _ _ _ v _ f => gaussNorm_eq_coeffGaussNorm v f,
    fun _ _ _ _ f => finsum_log_gaussNorm f,
    fun _ f => finGaussLog_eq f,
    fun _ _ _ H S hS hH f => chowHt_eq_chowHeight H S hS hH f,
    fun _ _ _ _ _ _ H S hS hH f => chowHt_eq_chowHt_places H S hS hH f⟩
end GroundTheory.Heights₂.Heights.ObjectsHeight
