-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.exp_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:42.277818+00:00
-- url     : https://prove2.me/submissions/4774128e-3dd6-4893-9a37-fcc10611049b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}
variable [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
theorem _root_.solution (t : k) (q : PS k 1 d) (hq0 : constantCoeff q = 0) (N : ℕ) :
    ∃ Y : PS k 1 d, FB.expS k (t • q) =
      ∑ n ∈ Finset.range (N + 1), C (algebraMap ℚ k (1 / (n.factorial : ℚ)) * t ^ n) * q ^ n +
        q ^ (N + 1) * Y := by
  classical
  have hdvd : (PowerSeries.X : PowerSeries k) ^ (N + 1) ∣
      PowerSeries.exp k - ∑ n ∈ Finset.range (N + 1),
        algebraMap ℚ k (1 / (n.factorial : ℚ)) • (PowerSeries.X : PowerSeries k) ^ n := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    have hm' : m ∈ Finset.range (N + 1) := Finset.mem_range.mpr hm
    first
    | (simp only [map_sub, map_sum, map_smul, PowerSeries.coeff_exp, PowerSeries.coeff_X_pow, smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, hm', if_true, sub_self]; done)
    | (simp [PowerSeries.coeff_exp, PowerSeries.coeff_X_pow, hm']; done)
  obtain ⟨R, hR⟩ := hdvd
  have hexp : PowerSeries.exp k = (∑ n ∈ Finset.range (N + 1),
      algebraMap ℚ k (1 / (n.factorial : ℚ)) • (PowerSeries.X : PowerSeries k) ^ n) +
        PowerSeries.X ^ (N + 1) * R := by
    rw [← hR]
    ring
  have hc : constantCoeff (t • q) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, hq0, mul_zero]
  have hs : PowerSeries.HasSubst (t • q) := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero hc
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' hc
    | (show IsNilpotent _; rw [hc]; exact IsNilpotent.zero)
  have key : ∀ f : PowerSeries k, PowerSeries.subst (t • q) f = PowerSeries.substAlgHom hs f := by
    intro f
    first
    | rw [PowerSeries.coe_substAlgHom]
    | rfl
  have hX : PowerSeries.substAlgHom hs (PowerSeries.X : PowerSeries k) = t • q := by
    first
    | exact PowerSeries.substAlgHom_X hs
    | (rw [← key]; exact PowerSeries.subst_X hs)
  refine ⟨C (t ^ (N + 1)) * PowerSeries.subst (t • q) R, ?_⟩
  unfold FB.expS
  rw [hexp]
  simp only [key, map_add, map_sum, map_mul, map_pow, map_smul, hX]
  simp only [smul_pow, smul_smul, MvPowerSeries.smul_eq_C_mul, map_mul, map_pow]
  congr 1
  all_goals first
    | rfl
    | ring1
    | (refine Finset.sum_congr rfl fun n _ => ?_; ring1)
end ReciprocityTheory.ChartRestriction.G.TB.GE
