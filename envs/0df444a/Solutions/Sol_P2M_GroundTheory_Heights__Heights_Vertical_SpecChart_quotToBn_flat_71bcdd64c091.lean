-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_quotToBn_flat_71bcdd64c091
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:22.535039+00:00
-- url     : https://prove2.me/submissions/93244990-0a0b-42ec-8002-241d3791b2d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartBack
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart__loc_algebraMap_8a01afb26e26
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Gloc__loc_8a86d412b78c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart__loc_Gloc_d8a0f962d579
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___C_e65327d6784a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_baseToBn_toBase_2f2e4d6deddf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {K : Type} [Field K] [NumberField K] {n e : ℕ} {I : Ideal (MvPolynomial (Fin n) K)} {j : Fin n}
  {v : HeightOneSpectrum (𝓞 K)} {W : Ideal (MvPolynomial (Fin n) (𝓞 K))}
variable [(Q e I j W).IsPrime]
variable {𝔫 : Ideal (SecB e I v)} [𝔫.IsPrime]
namespace GroundTheory.Heights₂.Heights.Vertical.SpecChart
theorem _root_.solution (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : RingHom.Flat (R := MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (S := Localization.AtPrime 𝔫) (quotToBn e 𝔫) := by
  have h : quotToBn e 𝔫 = (Φloc hj hσ hG h𝔫).comp
      ((algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))).comp
        ((C : Base I j →+* Poly e I j).comp
          (algebraMap (MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (Base I j)))) := by
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun g => ?_
    change quotToBn e 𝔫 (Ideal.Quotient.mk _ g) =
      Φloc hj hσ hG h𝔫 (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (C (toBase I j g)))
    rw [quotToBn_mk, Φloc_algebraMap, Φ_C, baseToBn_toBase]
  have hbij : Function.Bijective (Φloc hj hσ hG h𝔫) :=
    Function.bijective_iff_has_inverse.mpr ⟨Gloc hσ hG,
      fun x => RingHom.congr_fun (Gloc_Φloc hj hσ hG h𝔫) x,
      fun y => RingHom.congr_fun (Φloc_Gloc hj hσ hG h𝔫) y⟩
  have h1 : (algebraMap (MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (Base I j)).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (Base I j) (Submonoid.powers (Ideal.Quotient.mk (integralModel I) (X j))))
  have h2 : (C : Base I j →+* Poly e I j).Flat := by
    rw [← MvPolynomial.algebraMap_eq]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have h3 : RingHom.Flat (R := Poly e I j) (S := Localization.AtPrime (Q e I j W))
      (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))) :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization.AtPrime (Q e I j W)) (Q e I j W).primeCompl)
  rw [h]
  exact RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.comp h1 h2) h3) (RingHom.Flat.of_bijective hbij)
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
