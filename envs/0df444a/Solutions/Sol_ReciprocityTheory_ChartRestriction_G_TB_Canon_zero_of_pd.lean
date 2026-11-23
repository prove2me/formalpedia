-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.Canon.zero_of_pd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:31.779129+00:00
-- url     : https://prove2.me/submissions/239ac403-3457-45dc-949c-0099a983d0db

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.LocalProperties.Reduced
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_coeff_kill

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
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
variable [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.Canon
theorem _root_.solution (j : Fin n) {f : PS k n d} (h : ∀ b, pderiv k (j, b) f = 0) (h0 : sb (Function.update gen j 0) f = 0) :
    f = 0 := by
  ext m
  rw [map_zero]
  by_cases hm : ∀ b, m (j, b) = 0
  · have := congrArg (coeff m) h0
    rw [coeff_kill, if_pos hm, map_zero] at this
    exact this
  · push_neg at hm
    obtain ⟨b, hb⟩ := hm
    obtain ⟨m', rfl⟩ : ∃ m' : Fin n × Fin d →₀ ℕ, m = m' + Finsupp.single (j, b) 1 := by
      refine ⟨m - Finsupp.single (j, b) 1, ?_⟩
      ext x
      by_cases hx : x = (j, b)
      · subst hx
        rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      · rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hx)]
        simp
    have hc := congrArg (coeff m') (h b)
    rw [MvPowerSeries.coeff_pderiv, map_zero] at hc
    have hu : IsUnit ((m' (j, b) : k) + 1) := by
      have e : ((m' (j, b) : k) + 1) = algebraMap ℚ k ((m' (j, b) : ℚ) + 1) := by simp
      rw [e]
      exact (isUnit_iff_ne_zero.mpr (by positivity)).map (algebraMap ℚ k)
    exact hu.mul_left_eq_zero.mp hc
end ReciprocityTheory.ChartRestriction.G.TB.Canon
