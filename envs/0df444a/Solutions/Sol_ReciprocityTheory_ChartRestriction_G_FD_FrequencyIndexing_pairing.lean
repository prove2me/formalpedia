-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing.pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:52.277456+00:00
-- url     : https://prove2.me/submissions/2d82bff4-df07-446e-9564-6c01a55d9180

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeFourierExpansion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FrequencyIndexing

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
theorem _root_.solution (ν : ι → ℝ) (k : Fin n → ℤ) (hk : ∀ j, 2 * ∑ τ, ν τ * ω j τ = k j) (v : ι → ℝ) :
    ∑ τ, ν τ * v τ = (∑ j, (k j : ℝ) * ω.repr v j) / 2 := by
  have hv : v = ∑ j, ω.repr v j • ω j := (ω.sum_repr v).symm
  have h1 : ∀ j, (k j : ℝ) * ω.repr v j / 2 = ∑ τ, ν τ * (ω.repr v j * ω j τ) := by
    intro j
    rw [← hk j, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    exact Finset.sum_congr rfl (fun τ _ => by ring)
  rw [Finset.sum_div]
  simp_rw [h1]
  rw [Finset.sum_comm]
  conv_lhs => rw [hv]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
end ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
