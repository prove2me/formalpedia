-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.Canon.pderiv_primT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:31:01.553435+00:00
-- url     : https://prove2.me/submissions/d28802b9-b26d-4122-bc73-ac9678944925

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.LocalProperties.Reduced
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.Canon
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [DecidableEq τ]
namespace ReciprocityTheory.ChartRestriction.G.TB.Canon
theorem _root_.solution (T : Finset τ) (ω : τ → MvPowerSeries τ k)
    (hω : ∀ a ∈ T, ∀ c ∈ T, pderiv k c (ω a) = pderiv k a (ω c)) (v : τ) (hv : v ∈ T) : pderiv k v (primT T ω) = ω v := by
  ext n
  rw [MvPowerSeries.coeff_pderiv]
  have hS : (∑ w ∈ T, (n + Finsupp.single v 1 : τ →₀ ℕ) w) = (∑ w ∈ T, n w) + 1 := by
    simp [Finset.sum_add_distrib, Finsupp.single_apply, hv]
  have hterm : ∀ w ∈ T, (if (n + Finsupp.single v 1 : τ →₀ ℕ) w = 0 then 0 else
      coeff (n + Finsupp.single v 1 - Finsupp.single w 1) (ω w)) * ((n v : k) + 1) =
      ((n w : k) + if w = v then 1 else 0) * coeff n (ω v) := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv
      have h1 : (n + Finsupp.single w 1 : τ →₀ ℕ) w ≠ 0 := by simp
      rw [if_neg h1, add_tsub_cancel_right, if_pos rfl]
      ring
    · have hvw : v ≠ w := Ne.symm hwv
      by_cases hn : n w = 0
      · have h0 : (n + Finsupp.single v 1 : τ →₀ ℕ) w = 0 := by
          rw [Finsupp.add_apply, Finsupp.single_apply, if_neg hvw, hn, add_zero]
        rw [if_pos h0, if_neg hwv, hn]
        simp
      · obtain ⟨p, rfl⟩ : ∃ p : τ →₀ ℕ, n = p + Finsupp.single w 1 := by
          refine ⟨n - Finsupp.single w 1, ?_⟩
          ext x
          by_cases hx : x = w
          · subst hx
            rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
            omega
          · rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hx)]
            simp
        have h1 : (p + Finsupp.single w 1 + Finsupp.single v 1 : τ →₀ ℕ) w ≠ 0 := by
          simp [Finsupp.single_apply, hvw]
        have h2 : p + Finsupp.single w 1 + Finsupp.single v 1 - Finsupp.single w 1 =
            p + Finsupp.single v 1 := by
          rw [add_right_comm, add_tsub_cancel_right]
        have h3 : (p + Finsupp.single w 1 : τ →₀ ℕ) v = p v := by
          rw [Finsupp.add_apply, Finsupp.single_apply, if_neg hwv, add_zero]
        have h4 : (p + Finsupp.single w 1 : τ →₀ ℕ) w = p w + 1 := by
          rw [Finsupp.add_apply, Finsupp.single_eq_same]
        rw [if_neg h1, h2, h3, h4, if_neg hwv, ← MvPowerSeries.coeff_pderiv, hω w hw v hv,
          MvPowerSeries.coeff_pderiv]
        push_cast
        ring
  show (algebraMap ℚ k (((∑ w ∈ T, (n + Finsupp.single v 1 : τ →₀ ℕ) w : ℕ) : ℚ)⁻¹) *
      ∑ w ∈ T, (if (n + Finsupp.single v 1 : τ →₀ ℕ) w = 0 then 0 else
        coeff (n + Finsupp.single v 1 - Finsupp.single w 1) (ω w))) * ((n v : k) + 1) = coeff n (ω v)
  rw [mul_assoc, Finset.sum_mul, Finset.sum_congr rfl hterm, ← Finset.sum_mul, Finset.sum_add_distrib, hS]
  simp only [Finset.sum_ite_eq', hv, if_true, ite_true]
  have hc : (∑ w ∈ T, (n w : k)) + 1 = algebraMap ℚ k (((∑ w ∈ T, n w) + 1 : ℕ) : ℚ) := by simp
  rw [hc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (by positivity), map_one, one_mul]
end ReciprocityTheory.ChartRestriction.G.TB.Canon
