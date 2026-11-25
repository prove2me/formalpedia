-- Prove2me | solution 1 for PI.OrbShared.Tri.ord_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:02:33.116332+00:00
-- url     : https://prove2.me/submissions/20b6871f-7772-4c7c-9cbb-c9c9febdfcc4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_SolvableEquivalenceOfBaseChange
import Theorems.Thm_PI_OrbShared_Tri_ord_mul
import Theorems.Thm_PI_OrbShared_Tri_ord_add
import Theorems.Thm_PI_OrbShared_Tri_ord_pow

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
theorem _root_.solution {x y : MvPowerSeries σ K} (hx : 1 ≤ x.order) (hy : 1 ≤ y.order)
    (hxy : ((2 : ℕ) : ℕ∞) ≤ (y - x).order) (n : ℕ) : ((n + 1 : ℕ) : ℕ∞) ≤ (y ^ n - x ^ n).order := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show y ^ (n + 1) - x ^ (n + 1) = y ^ n * (y - x) + (y ^ n - x ^ n) * x by ring]
    apply ord_add
    · have := ord_mul (ord_pow hy n) hxy
      exact le_trans (by norm_cast) this
    · have := ord_mul ih (n := 1) (by simpa using hx)
      exact le_trans (by norm_cast) this
end PI.OrbShared.Tri
