-- Prove2me | solution 1 for PI.OrbShared.Tri.subst_sol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:26:44.233326+00:00
-- url     : https://prove2.me/submissions/5733f9f2-aa3d-47ec-836f-c8149573c407

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_SolvableEquivalenceOfBaseChange
import Theorems.Thm_PI_OrbShared_Tri_coeff_subst_tri
import Theorems.Thm_PI_OrbShared_Tri_triangular_solution_stable

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
theorem _root_.solution (hc : c ≠ 0) (ha : IsTri c a) (G : MvPowerSeries σ K) : subst a (sol c a G) = G := by
  ext m
  rw [coeff_subst_tri ha]
  have hsol : ∀ d : σ →₀ ℕ, coeff d (sol c a G) = solvable_equivalence_of_base_change c a G (d.degree + 1) d := fun d => rfl
  have hS : (∑ᶠ d, if d.degree < m.degree then coeff d (sol c a G) * coeff m (P a d) else 0) =
      ∑ᶠ d, if d.degree < m.degree then solvable_equivalence_of_base_change c a G m.degree d * coeff m (P a d) else 0 := by
    apply finsum_congr
    intro d
    split_ifs with hd
    · rw [hsol, triangular_solution_stable G m.degree d hd]
    · rfl
  rw [hS, hsol, solvable_equivalence_of_base_change.eq_2]
  beta_reduce
  rw [if_pos rfl, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hc), one_mul, sub_add_cancel]
end PI.OrbShared.Tri
