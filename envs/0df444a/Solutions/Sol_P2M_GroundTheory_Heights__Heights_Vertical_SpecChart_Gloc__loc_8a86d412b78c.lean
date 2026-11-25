-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Gloc__loc_8a86d412b78c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:33:28.416487+00:00
-- url     : https://prove2.me/submissions/48d66d6c-a7b0-4f5c-afdd-9f33b083ef28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartBack
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart__loc_algebraMap_8a01afb26e26

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
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : (Gloc hσ hG).comp (Φloc hj hσ hG h𝔫) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Q e I j W).primeCompl
  refine RingHom.ext fun c => ?_
  simp only [RingHom.comp_apply, Φloc_algebraMap, RingHom.id_apply]
  rw [← RingHom.comp_apply, Gloc_Φ]
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
