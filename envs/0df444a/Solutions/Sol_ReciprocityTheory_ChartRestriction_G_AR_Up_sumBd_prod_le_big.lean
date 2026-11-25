-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_prod_le_big
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:34.053438+00:00
-- url     : https://prove2.me/submissions/f6d4f9eb-86fc-4f4e-8b04-64d4447c7add

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution {f : ℕ} (w : Fin f → ℝ) (h0 : ∀ k, 0 ≤ w k) (h1 : ∀ k, w k ≤ 1) (k0 : Fin f)
    {b : ℝ} (hb : w k0 ≤ b) : ∏ k, w k ≤ b := by
  rw [← Finset.mul_prod_erase Finset.univ w (Finset.mem_univ k0)]
  have h2 : ∏ k ∈ Finset.univ.erase k0, w k ≤ 1 := Finset.prod_le_one (fun k _ => h0 k) (fun k _ => h1 k)
  have h3 : 0 ≤ ∏ k ∈ Finset.univ.erase k0, w k := Finset.prod_nonneg fun k _ => h0 k
  nlinarith [h0 k0]
end ReciprocityTheory.ChartRestriction.G.AR.Up
