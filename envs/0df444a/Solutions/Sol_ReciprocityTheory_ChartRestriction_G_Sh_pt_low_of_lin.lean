-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_low_of_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:29:05.471807+00:00
-- url     : https://prove2.me/submissions/7c3b046c-e192-431e-8575-49fac7e30a45

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
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
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution {σ : Type*} [Fintype σ] {Φ : MvPowerSeries σ C}
    (h0 : constantCoeff Φ = 0) (m : σ → C)
    (hm : ∀ s, coeff (Finsupp.single s 1) Φ = m s) :
    ∀ α : σ →₀ ℕ, α.degree ≤ 1 → coeff α (Φ - ∑ a, m a • X a) = 0 := by
  intro α hα
  rw [map_sub, map_sum]
  simp only [map_smul, smul_eq_mul]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hα with h | h
  · obtain rfl := (Finsupp.degree_eq_zero_iff α).mp h
    simp [MvPowerSeries.coeff_X, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    refine Finset.sum_eq_zero fun a _ => if_neg ?_
    exact fun e => (Finsupp.single_ne_zero.mpr one_ne_zero) e.symm
  · have hne : α ≠ 0 := by
      rintro rfl
      simp at h
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hne
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hs
    have hle : Finsupp.single s 1 ≤ α := by
      rw [Finsupp.le_def]
      intro i
      by_cases hi : i = s
      · subst hi
        simp only [Finsupp.single_eq_same]
        omega
      · simp [Finsupp.single_apply, Ne.symm hi]
    have hadd := add_tsub_cancel_of_le hle
    have hd := congrArg Finsupp.degree hadd
    rw [map_add, Finsupp.degree_single, h] at hd
    have h0' : α - Finsupp.single s 1 = 0 := (Finsupp.degree_eq_zero_iff _).mp (by omega)
    rw [← hadd, h0', add_zero]
    simp [MvPowerSeries.coeff_X, hm, Finsupp.single_left_inj one_ne_zero]
end ReciprocityTheory.ChartRestriction.G.Sh
