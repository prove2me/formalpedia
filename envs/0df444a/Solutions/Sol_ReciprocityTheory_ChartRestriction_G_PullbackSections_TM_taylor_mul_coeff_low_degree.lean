-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TM.taylor_mul_coeff_low_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:41:30.816662+00:00
-- url     : https://prove2.me/submissions/1b7d34ac-68bf-40b9-b050-731e28a4b018

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_tay_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_tay_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_mD_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_deriv_analytic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_pderiv_tay
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_deriv_mul_ev

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
theorem _root_.solution (N : ℕ) : ∀ (f h : (Fin g → ℂ) → ℂ), ContDiffAt ℂ ω f 0 → ContDiffAt ℂ ω h 0 →
    ∀ n : Fin 1 × Fin g →₀ ℕ, n.degree < N → coeff n (tay (f * h) 0) = coeff n (tay f 0 * tay h 0) := by
  induction N with
  | zero =>
    intro f h _ _ n hn
    exact absurd hn (Nat.not_lt_zero _)
  | succ N ih =>
    intro f h hf hh n hn
    by_cases h0 : n = 0
    · subst h0
      simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
      simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      show mD (f * h) 0 (dirs 0 + 0) / fct 0 = (mD f 0 (dirs 0 + 0) / fct 0) * (mD h 0 (dirs 0 + 0) / fct 0)
      simp [dirs, fct, mD_zero]
    · obtain ⟨x, hx⟩ : ∃ x, n x ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact h0 (Finsupp.ext hc)
      obtain ⟨i, j⟩ := x
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      obtain ⟨m, hm⟩ : ∃ m, m = n - Finsupp.single ((0 : Fin 1), j) 1 := ⟨_, rfl⟩
      have hnm : n = m + Finsupp.single ((0 : Fin 1), j) 1 := by
        rw [hm]
        exact (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hx))).symm
      have hmdeg : m.degree < N := by
        have h1 : n.degree = m.degree + 1 := by
          rw [hnm, map_add, Finsupp.degree_single]
        omega
      have key : ∀ F : MvPowerSeries (Fin 1 × Fin g) ℂ,
          coeff m (pderiv ℂ ((0 : Fin 1), j) F) = coeff n F * ((m ((0 : Fin 1), j) : ℂ) + 1) := fun F => by
        rw [MvPowerSeries.coeff_pderiv, ← hnm]
      have hc : ((m ((0 : Fin 1), j) : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
      apply mul_right_cancel₀ hc
      rw [← key, ← key]
      have hfh : ContDiffAt ℂ ω (f * h) 0 := hf.mul hh
      have hf' := deriv_analytic hf (Pi.single j 1)
      have hh' := deriv_analytic hh (Pi.single j 1)
      rw [pderiv_tay hfh, tay_local (deriv_mul_ev hf hh (Pi.single j 1)), tay_add (f := (fun y => fderiv ℂ f y (Pi.single j 1)) * h)
        (h := f * fun y => fderiv ℂ h y (Pi.single j 1)) (hf'.mul hh) (hf.mul hh'),
        map_add, Derivation.leibniz, pderiv_tay hf, pderiv_tay hh, ih _ _ hf' hh m hmdeg,
        ih _ _ hf hh' m hmdeg, smul_eq_mul, smul_eq_mul, map_add, mul_comm (tay h 0)]
      ring
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
