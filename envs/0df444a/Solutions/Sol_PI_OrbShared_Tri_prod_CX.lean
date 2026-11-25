-- Prove2me | solution 1 for PI.OrbShared.Tri.prod_CX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:01:52.565614+00:00
-- url     : https://prove2.me/submissions/30cd74fd-493c-4c72-a47d-897b675d638d

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
theorem _root_.solution (d : σ →₀ ℕ) :
    (d.prod fun s e => (C c * X s : MvPowerSeries σ K) ^ e) = monomial d (c ^ d.degree) := by
  classical
  have key : ∀ S : Finset σ, (∏ s ∈ S, (C c * X s : MvPowerSeries σ K) ^ d s) =
      monomial (∑ s ∈ S, single s (d s)) (c ^ (∑ s ∈ S, d s)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
      rw [Finset.prod_insert hj, ih, Finset.sum_insert hj, Finset.sum_insert hj, mul_pow, X_pow_eq,
        ← map_pow, ← monomial_zero_eq_C_apply, monomial_mul_monomial, monomial_mul_monomial, zero_add,
        mul_one, pow_add]
  have hs : (∑ s ∈ d.support, single s (d s)) = d := Finsupp.sum_single d
  rw [Finsupp.prod, key, hs]
  rfl
end PI.OrbShared.Tri
