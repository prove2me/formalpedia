-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing.repr_sum_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:56.885889+00:00
-- url     : https://prove2.me/submissions/7c48f402-3431-4873-8b68-0eb22be7c5e0

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
theorem _root_.solution (v : ι → ℝ) (j : Fin n) :
    ∑ τ, v τ * ω.repr (Pi.single τ 1) j = ω.repr v j := by
  have hv : v = ∑ τ, v τ • (Pi.single τ (1 : ℝ) : ι → ℝ) := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  rw [map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
end ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
