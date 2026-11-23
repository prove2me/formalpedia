-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_zero_of_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:10.08699+00:00
-- url     : https://prove2.me/submissions/90c681e5-2ff2-4950-8956-abe907c7cb4b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {σ : Type} [Fintype σ] (w : σ → ℕ) (f : MvPowerSeries σ k)
    (h : subst ((fun s => (2 : k) ^ w s) • (X : σ → MvPowerSeries σ k)) f = (2 : k) • f) (n : σ →₀ ℕ)
    (hn : (∑ s, w s * n s) ≠ 1) : coeff n f = 0 := by
  have h2 := congrArg (coeff n) h
  rw [← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale,
    Finsupp.prod_fintype _ _ (fun s => by simp), map_smul, smul_eq_mul] at h2
  simp only [← pow_mul, Finset.prod_pow_eq_pow_sum] at h2
  have hr : ((2 : ℚ) ^ (∑ s, w s * n s) - 2) ≠ 0 := by
    intro h0
    apply hn
    have h3 : (2 : ℕ) ^ (∑ s, w s * n s) = 2 := by exact_mod_cast sub_eq_zero.1 h0
    exact Nat.pow_right_injective (le_refl 2) (h3.trans (pow_one 2).symm)
  have hk : algebraMap ℚ k ((2 : ℚ) ^ (∑ s, w s * n s) - 2) * coeff n f = 0 := by
    rw [map_sub, map_pow, map_ofNat]
    linear_combination h2
  calc coeff n f
      = algebraMap ℚ k (((2 : ℚ) ^ (∑ s, w s * n s) - 2)⁻¹ * ((2 : ℚ) ^ (∑ s, w s * n s) - 2))
          * coeff n f := by rw [inv_mul_cancel₀ hr, map_one, one_mul]
    _ = 0 := by rw [map_mul, mul_assoc, hk, mul_zero]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
