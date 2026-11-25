-- Prove2me | solution 1 for PI.OrbShared.Tri.vanish_of_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:21.206802+00:00
-- url     : https://prove2.me/submissions/1602fc9e-c6b4-4663-9d7a-577928d9e213

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_SolvableEquivalenceOfBaseChange
import Theorems.Thm_PI_OrbShared_Tri_coeff_subst_tri

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
theorem _root_.solution (hc : c ≠ 0) (ha : IsTri c a) (F : MvPowerSeries σ K) (n : ℕ)
    (h : ∀ m : σ →₀ ℕ, m.degree < n → coeff m (subst a F) = 0) :
    ∀ m : σ →₀ ℕ, m.degree < n → coeff m F = 0 := by
  have key : ∀ k, ∀ m : σ →₀ ℕ, m.degree = k → k < n → coeff m F = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro m hm hk
      have h1 := h m (hm ▸ hk)
      rw [coeff_subst_tri ha] at h1
      have h2 : (∑ᶠ d, if d.degree < m.degree then coeff d F * coeff m (P a d) else 0) = 0 := by
        apply finsum_eq_zero_of_forall_eq_zero
        intro d
        split_ifs with hd
        · rw [ih d.degree (hm ▸ hd) d rfl (lt_trans (hm ▸ hd) hk), zero_mul]
        · rfl
      rw [h2, add_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hc)
  exact fun m hm => key _ m rfl hm
end PI.OrbShared.Tri
