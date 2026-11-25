-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_v_natCast_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:36:34.966411+00:00
-- url     : https://prove2.me/submissions/42b7ceb0-237e-413d-90ad-d603dac01573

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_v_natCast_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_v_intCast_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_symm


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
    (hn : ¬ p ∣ n) : v (n : C) = 0 := by
  have h0 : (0 : WithTop ℝ) ≤ v (n : C) := pt_v_natCast_nonneg n
  refine (h0.lt_or_eq.resolve_left fun hlt => ?_).symm
  have hcop : Nat.Coprime n p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn)
  have hz : ((1 : ℤ) : C) = ((n * Nat.gcdA n p + p * Nat.gcdB n p : ℤ) : C) := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one, Nat.cast_one]
  push_cast at hz
  have h1 : v (1 : C) = 0 := v.map_one
  rw [hz] at h1
  have hmin := v.map_add ((n : C) * (Nat.gcdA n p : C)) ((p : C) * (Nat.gcdB n p : C))
  rw [h1, v.map_mul, v.map_mul, hvp] at hmin
  have ha : (0 : WithTop ℝ) < v (n : C) + v (Nat.gcdA n p : C) :=
    add_pos_of_pos_of_nonneg hlt (pt_v_intCast_nonneg _)
  have hb : (0 : WithTop ℝ) < 1 + v (Nat.gcdB n p : C) :=
    add_pos_of_pos_of_nonneg zero_lt_one (pt_v_intCast_nonneg _)
  exact absurd hmin (not_le.mpr (lt_min ha hb))
end ReciprocityTheory.ChartRestriction.G.Sh
