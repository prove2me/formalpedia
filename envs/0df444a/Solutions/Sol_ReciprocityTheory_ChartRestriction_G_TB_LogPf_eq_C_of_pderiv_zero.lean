-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.eq_C_of_pderiv_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:56:57.660572+00:00
-- url     : https://prove2.me/submissions/58e652c9-965b-4fee-be62-f4df43484d4f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain

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
open MvPowerSeries Formalism.FG.SolveVAux
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {σ τ : Type}
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution [Algebra ℚ k] {g : MvPowerSeries τ k} (h : ∀ v, pderiv k v g = 0) :
    g = C (constantCoeff g) := by
  classical
  ext n
  rw [MvPowerSeries.coeff_C]
  split_ifs with hn
  · subst hn
    simp
  · obtain ⟨v, hv⟩ : ∃ v, n v ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hn (Finsupp.ext fun i => by simpa using hcon i)
    set m := n - Finsupp.single v 1 with hm
    have hnm : n = m + Finsupp.single v 1 :=
      (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hv))).symm
    have h0 := congrArg (MvPowerSeries.coeff m) (h v)
    rw [MvPowerSeries.coeff_pderiv, ← hnm, map_zero] at h0
    have hu : IsUnit ((m v : k) + 1) := by
      have e : ((m v : k) + 1) = algebraMap ℚ k ((m v : ℚ) + 1) := by simp
      rw [e]
      exact (IsUnit.mk0 _ (by positivity)).map _
    exact (hu.mul_left_eq_zero).mp h0
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
