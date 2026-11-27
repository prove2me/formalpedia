-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_inv_natCast_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:42.342928+00:00
-- url     : https://prove2.me/submissions/ed9bf2a0-d553-4602-851a-f37a5c65e6bf

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_v_natCast_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hvp : v (p : C) = 1) {n : ℕ}
    (hn : ¬ p ∣ n) : ((n : C))⁻¹ ∈ ptIntSub v := by
  have hv : v (n : C) = 0 := pt_v_natCast_eq_zero hp hvp hn
  have hne : (n : C) ≠ 0 := by
    intro h
    rw [h, v.map_zero] at hv
    exact absurd hv WithTop.top_ne_zero
  show (0 : WithTop ℝ) ≤ v ((n : C)⁻¹)
  have h1 := v.map_mul (n : C) ((n : C)⁻¹)
  rw [mul_inv_cancel₀ hne, v.map_one, hv, zero_add] at h1
  rw [← h1]
end ReciprocityTheory.ChartRestriction.G.Sh
