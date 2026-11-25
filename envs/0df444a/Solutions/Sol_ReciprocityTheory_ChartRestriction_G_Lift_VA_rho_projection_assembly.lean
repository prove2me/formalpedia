-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lift.VA.rho_projection_assembly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:16:53.825463+00:00
-- url     : https://prove2.me/submissions/fb732579-f9ce-4f38-af5a-86f1d3f0c8fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_LiftSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_LargeSmall
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_RhoProjectionAssembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lift ReciprocityTheory.ChartRestriction.G.Lift.VA
open WithZero
namespace ReciprocityTheory.ChartRestriction.G.Lift.VA
theorem _root_.solution : Assembly := by
  intro Ω _ ι _ v h1 hN n
  classical
  choose π hπ using h1
  have hπ0 : ∀ i, π i ≠ 0 := by
    intro i h
    have := hπ i
    rw [h, map_zero] at this
    exact exp_ne_zero this.symm
  set t : ι → Ω := fun i => π i ^ n i with ht
  have ht0 : ∀ i k, 0 < v k (t i) := fun i k =>
    zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr (zpow_ne_zero _ (hπ0 i)))
  have hε : ∀ i k, exp (n k) * (v k (t i))⁻¹ ≠ 0 := fun i k =>
    mul_ne_zero exp_ne_zero (inv_ne_zero (ht0 i k).ne')
  choose z hz1 hz2 using fun i => hN i (fun k => exp (n k) * (v k (t i))⁻¹) (hε i)
  refine ⟨∑ i, z i * t i, fun k => ?_⟩
  have hmain : v k (z k * t k) = exp (n k) := by
    rw [map_mul, hz1 k, one_mul, ht]
    simp only
    rw [map_zpow₀, hπ k, ← exp_zsmul, smul_eq_mul, mul_one]
  have hrest : v k (∑ i ∈ Finset.univ.erase k, z i * t i) < exp (n k) := by
    refine Valuation.map_sum_lt _ exp_ne_zero (fun i hi => ?_)
    have hik : k ≠ i := fun h => (Finset.mem_erase.mp hi).1 h.symm
    rw [map_mul]
    exact (lt_mul_inv_iff₀ (ht0 i k)).mp (hz2 i k hik)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), Valuation.map_add_eq_of_lt_left _ (hmain ▸ hrest), hmain]
end ReciprocityTheory.ChartRestriction.G.Lift.VA
