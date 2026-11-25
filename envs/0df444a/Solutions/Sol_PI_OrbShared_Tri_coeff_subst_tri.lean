-- Prove2me | solution 1 for PI.OrbShared.Tri.coeff_subst_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:21:03.962506+00:00
-- url     : https://prove2.me/submissions/a910fb83-ae42-47b8-bb95-8d0d446a37dc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_SolvableEquivalenceOfBaseChange
import Theorems.Thm_PI_OrbShared_Tri_IsTri_hasSubst
import Theorems.Thm_PI_OrbShared_Tri_coeff_P_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.OrbShared PI.OrbShared.Tri
open MvPowerSeries Finsupp
variable {K : Type*} [Field K] {σ : Type*} [Finite σ]
variable {c : K} {a : σ → MvPowerSeries σ K}
namespace PI.OrbShared.Tri
theorem _root_.solution (ha : IsTri c a) (F : MvPowerSeries σ K) (e : σ →₀ ℕ) :
    coeff e (subst a F) = c ^ e.degree * coeff e F +
      ∑ᶠ d, if d.degree < e.degree then coeff d F * coeff e (P a d) else 0 := by
  rw [coeff_subst ha.hasSubst]
  have hterm : ∀ d : σ →₀ ℕ, coeff d F • coeff e (d.prod fun s e => (a s) ^ e) =
      (if d = e then c ^ e.degree * coeff e F else 0) +
        (if d.degree < e.degree then coeff d F * coeff e (P a d) else 0) := by
    intro d
    change coeff d F * coeff e (P a d) = _
    rcases lt_trichotomy d.degree e.degree with hlt | heq | hgt
    · have hne : d ≠ e := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
      rw [if_neg hne, if_pos hlt, zero_add]
    · rw [if_neg (show ¬ d.degree < e.degree by rw [heq]; exact lt_irrefl _), add_zero,
        coeff_P_of_le ha d e heq.ge]
      by_cases hde : d = e
      · subst hde; simp [mul_comm]
      · rw [if_neg hde, if_neg (Ne.symm hde), mul_zero]
    · have hne : d ≠ e := fun h => by rw [h] at hgt; exact lt_irrefl _ hgt
      rw [if_neg hne, if_neg (not_lt.mpr hgt.le), coeff_P_of_le ha d e hgt.le, if_neg (Ne.symm hne)]
      simp
  simp_rw [hterm]
  rw [finsum_add_distrib]
  · rw [finsum_eq_single _ e (fun d hd => if_neg hd), if_pos rfl]
  · apply Set.Finite.subset (Set.finite_singleton e)
    intro d hd
    by_contra h
    exact hd (if_neg h)
  · apply Set.Finite.subset (Finsupp.finite_of_degree_lt e.degree)
    intro d hd
    by_contra h
    exact hd (if_neg h)
end PI.OrbShared.Tri
