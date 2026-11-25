-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:17.037458+00:00
-- url     : https://prove2.me/submissions/5fce6f18-fb1d-46b2-93d8-aff41ac4268e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_coeff_prim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_degree_eq_sum

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
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [Fintype τ] [DecidableEq τ]
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution (ω : τ → MvPowerSeries τ k)
    (hω : ∀ a c, pderiv k c (ω a) = pderiv k a (ω c)) (v : τ) : pderiv k v (prim ω) = ω v := by
  ext m
  rw [coeff_pderiv, coeff_prim]
  set n := m + Finsupp.single v 1 with hn
  have key : ∀ w, (if n w = 0 then 0 else coeff (n - Finsupp.single w 1) (ω w)) * ((m v : k) + 1)
      = (n w : k) * coeff m (ω v) := by
    intro w
    by_cases hw : w = v
    · subst hw
      have h1 : n w = m w + 1 := by simp [hn]
      have h2 : n - Finsupp.single w 1 = m := by rw [hn]; exact add_tsub_cancel_right _ _
      rw [if_neg (by omega), h2, h1]
      push_cast
      ring
    · have h1 : n w = m w := by simp [hn, Finsupp.single_apply, hw, Ne.symm hw]
      by_cases hm : m w = 0
      · rw [if_pos (by rw [h1, hm]), h1, hm]
        simp
      · rw [if_neg (by rw [h1]; exact hm), h1]
        have hle : Finsupp.single w 1 ≤ m := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hm)
        have hc := congrArg (coeff (m - Finsupp.single w 1)) (hω w v)
        rw [coeff_pderiv, coeff_pderiv] at hc
        have e1 : m - Finsupp.single w 1 + Finsupp.single v 1 = n - Finsupp.single w 1 := by
          rw [hn]; exact tsub_add_eq_add_tsub hle
        have e2 : m - Finsupp.single w 1 + Finsupp.single w 1 = m := tsub_add_cancel_of_le hle
        have e3 : (m - Finsupp.single w 1 : τ →₀ ℕ) v = m v := by
          simp [Finsupp.single_apply, hw, Ne.symm hw]
        have e4' : (m - Finsupp.single w 1 : τ →₀ ℕ) w + 1 = m w := by
          rw [Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
        have e4 : ((m - Finsupp.single w 1 : τ →₀ ℕ) w : k) + 1 = (m w : k) := by
          rw [← e4', Nat.cast_add, Nat.cast_one]
        rw [e1, e2, e3, e4] at hc
        rw [hc]
        ring
  have hsum : (∑ w, if n w = 0 then 0 else coeff (n - Finsupp.single w 1) (ω w)) * ((m v : k) + 1)
      = (n.degree : k) * coeff m (ω v) := by
    rw [Finset.sum_mul, Finset.sum_congr rfl (fun w _ => key w), ← Finset.sum_mul, degree_eq_sum,
      Nat.cast_sum]
  have hnv : n v = m v + 1 := by simp [hn]
  have hD : (n.degree : ℚ) ≠ 0 := by
    have : n v ≤ n.degree := by
      rw [degree_eq_sum]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    exact_mod_cast (show n.degree ≠ 0 by omega)
  rw [mul_assoc, hsum, ← mul_assoc, ← map_natCast (algebraMap ℚ k) n.degree, ← map_mul,
    inv_mul_cancel₀ hD, map_one, one_mul]
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
