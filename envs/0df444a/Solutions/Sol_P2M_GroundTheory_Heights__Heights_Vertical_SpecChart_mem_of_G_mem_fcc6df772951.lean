-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_G_mem_fcc6df772951
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:09.266095+00:00
-- url     : https://prove2.me/submissions/60cae47b-da63-4d5d-9f4b-49ce887925c3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartBack

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
namespace GroundTheory.Heights₂.Heights.Vertical.SpecChart
theorem _root_.solution (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    {𝔫 : Ideal (SecB e I v)} [𝔫.IsMaximal] (h𝔫 : W.map (toSecB e I v) = 𝔫) {b : SecB e I v}
    (hb : G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))) : b ∈ 𝔫 := by
  have h : 𝔫 = (IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))).comap (G hσ) :=
    Ideal.IsMaximal.eq_of_le ‹_› (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
      (fun _ hb => G_mem hσ h𝔫 hb)
  rw [h]
  exact hb
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
