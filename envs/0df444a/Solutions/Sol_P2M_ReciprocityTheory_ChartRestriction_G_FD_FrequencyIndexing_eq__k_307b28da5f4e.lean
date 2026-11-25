-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing_eq__k_307b28da5f4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:17:52.669876+00:00
-- url     : https://prove2.me/submissions/2425f07a-0d8c-414e-accc-9e894ec799e8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeFourierExpansion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FrequencyIndexing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing_pairing
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing__k_spec_f7cb7fb69995

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (ω : Module.Basis (Fin n) ℝ (ι → ℝ))
namespace ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
theorem _root_.solution (ν : ι → ℝ) (k : Fin n → ℤ) (hk : ∀ j, 2 * ∑ τ, ν τ * ω j τ = k j) : ν = νk ω k := by
  funext τ
  have h1 := pairing ω ν k hk (Pi.single τ 1)
  have h2 := pairing ω (νk ω k) k (νk_spec ω k) (Pi.single τ 1)
  have e : ∀ μ : ι → ℝ, ∑ σ, μ σ * (Pi.single τ (1 : ℝ) : ι → ℝ) σ = μ τ := by
    intro μ
    simp [Pi.single_apply]
  rw [e] at h1 h2
  rw [h1, h2]
end ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
