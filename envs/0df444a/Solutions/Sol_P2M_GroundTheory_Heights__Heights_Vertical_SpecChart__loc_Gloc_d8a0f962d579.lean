-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart__loc_Gloc_d8a0f962d579
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:49:51.667102+00:00
-- url     : https://prove2.me/submissions/aec7576e-477f-4628-9f8d-37b83254409a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartBack
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart__loc_algebraMap_8a01afb26e26
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_____bd9155de4351
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___cx_89ebc424d343


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
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : (Φloc hj hσ hG h𝔫).comp (Gloc hσ hG) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext 𝔫.primeCompl
  have hρ : (Φloc hj hσ hG h𝔫).comp (ρ hσ) =
      (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)).comp (algebraMap (ParDVR e n v) (SecB e I v)) := by
    apply IsLocalization.ringHom_ext (parPrime e n v).primeCompl
    refine RingHom.ext fun s => ?_
    simp only [RingHom.comp_apply, ρ_algebraMap, Φloc_algebraMap]
    rw [← RingHom.comp_apply (Φ hj), Φ_σ]
    rfl
  have h : (Φloc hj hσ hG h𝔫).comp (G hσ) = algebraMap (SecB e I v) (Localization.AtPrime 𝔫) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      have := RingHom.congr_fun hρ r
      simp only [RingHom.comp_apply] at this ⊢
      rw [G, Ideal.Quotient.lift_mk, G', eval₂Hom_C, this, ← Ideal.Quotient.mk_algebraMap,
        MvPolynomial.algebraMap_eq]
    · intro l
      simp only [RingHom.comp_apply]
      rw [G, Ideal.Quotient.lift_mk, G', eval₂Hom_X', Φloc_algebraMap, Φ_cx]
      simp [toSecB]
  refine RingHom.ext fun b => ?_
  simp only [RingHom.comp_apply, Gloc_algebraMap, RingHom.id_apply]
  exact RingHom.congr_fun h b
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
