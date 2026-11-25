-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing__k_spec_f7cb7fb69995
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:02:49.140182+00:00
-- url     : https://prove2.me/submissions/76baf47d-bbe5-4a7d-a763-3a7ef2cf36b4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeFourierExpansion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FrequencyIndexing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing_repr_sum_single

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
theorem _root_.solution (k : Fin n → ℤ) (i : Fin n) : 2 * ∑ τ, νk ω k τ * ω i τ = k i := by
  have h : ∀ τ, νk ω k τ * ω i τ =
      (∑ j, (k j : ℝ) * (ω i τ * ω.repr (Pi.single τ 1) j)) / 2 := by
    intro τ
    simp only [νk]
    rw [div_mul_eq_mul_div, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp_rw [h]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, repr_sum_single, Module.Basis.repr_self, Finsupp.single_apply]
  simp
  ring
end ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
