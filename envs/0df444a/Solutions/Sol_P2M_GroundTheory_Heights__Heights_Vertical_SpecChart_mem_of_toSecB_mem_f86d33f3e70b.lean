-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_toSecB_mem_f86d33f3e70b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:41:18.653227+00:00
-- url     : https://prove2.me/submissions/11d8ffc4-aff6-4de4-b2f2-2194c888bd86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartBack
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_C_toBase_mem_Q_c9a4c04bd9fa


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
theorem _root_.solution [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    {𝔫 : Ideal (SecB e I v)} (h𝔫 : W.map (toSecB e I v) = 𝔫) {g : MvPolynomial (Fin n) (𝓞 K)}
    (hg : toSecB e I v g ∈ 𝔫) : g ∈ W := by
  have h := G_mem hσ h𝔫 hg
  rw [G_toSecB, IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Q e I j W)] at h
  exact mem_of_C_toBase_mem_Q e j hPW hXj h
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
