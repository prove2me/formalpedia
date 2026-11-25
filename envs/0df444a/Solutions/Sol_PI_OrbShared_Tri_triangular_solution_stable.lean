-- Prove2me | solution 1 for PI.OrbShared.Tri.triangular_solution_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:01:56.832145+00:00
-- url     : https://prove2.me/submissions/fd3bdc2e-8a78-4498-a070-a223dfe2e2a2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_SolvableEquivalenceOfBaseChange

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
theorem _root_.solution (G : MvPowerSeries σ K) :
    ∀ k (m : σ →₀ ℕ), m.degree < k → solvable_equivalence_of_base_change c a G k m = solvable_equivalence_of_base_change c a G (m.degree + 1) m := by
  intro k
  induction k with
  | zero => intro m hm; exact absurd hm (Nat.not_lt_zero _)
  | succ k ih =>
    intro m hm
    by_cases hk : m.degree = k
    · rw [hk]
    · have hlt : m.degree < k := by omega
      show (if m.degree = k then _ else solvable_equivalence_of_base_change c a G k m) = _
      rw [if_neg hk, ih m hlt]
end PI.OrbShared.Tri
