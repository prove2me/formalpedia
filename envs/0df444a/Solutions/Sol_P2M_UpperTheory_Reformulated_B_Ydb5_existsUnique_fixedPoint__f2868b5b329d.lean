-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Ydb5_existsUnique_fixedPoint__f2868b5b329d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:00:26.645586+00:00
-- url     : https://prove2.me/submissions/b71f2a33-e96d-4340-8f9a-efc85f9d299d

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsUniqueFixedPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPowerSeries in
private theorem UpperTheory.Reformulated.B.Ydb5.le_order_iff {σ R : Type*} [CommRing R]
    (f g : MvPowerSeries σ R) (n : ℕ) :
    (n : ℕ∞) ≤ (f - g).order ↔ ∀ d : σ →₀ ℕ, d.degree < n → coeff d f = coeff d g := by
  constructor
  · intro h d hd
    have h0 : coeff d (f - g) = 0 :=
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
    rwa [map_sub, sub_eq_zero] at h0
  · intro h
    refine nat_le_order fun d hd => ?_
    rw [map_sub, h d hd, sub_self]
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Ydb5.existsUnique_fixedPoint
theorem _root_.solution.{u_1, u_2} :
    ∀ {σ : Type u_1} {R : Type u_2} [inst : CommRing R] (Φ : MvPowerSeries σ R → MvPowerSeries σ R),
      (∀ (f g : MvPowerSeries σ R) (n : ℕ), (↑n : ℕ∞) ≤ (f - g).order → (↑(n + (1 : ℕ)) : ℕ∞) ≤ (Φ f - Φ g).order) →
        ∃! f : MvPowerSeries σ R, Φ f = f := by
  intro σ R _ Φ h
  simp only [UpperTheory.Reformulated.B.Ydb5.le_order_iff] at h
  have step : ∀ (k : ℕ) (g : MvPowerSeries σ R) (d : σ →₀ ℕ), d.degree < k →
      MvPowerSeries.coeff d (Φ^[k] g) = MvPowerSeries.coeff d (Φ^[k] 0) := by
    intro k g
    induction k with
    | zero => intro d hd; exact absurd hd (Nat.not_lt_zero _)
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact h _ _ k ih
  let f : MvPowerSeries σ R := fun d => MvPowerSeries.coeff d (Φ^[d.degree + 1] 0)
  have hf : ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d f = MvPowerSeries.coeff d (Φ^[d.degree + 1] 0) := fun _ => rfl
  have approx : ∀ (k : ℕ) (d : σ →₀ ℕ), d.degree < k →
      MvPowerSeries.coeff d f = MvPowerSeries.coeff d (Φ^[k] 0) := by
    intro k d hd
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hd)
    rw [hf, Function.iterate_add_apply Φ (Nat.succ _) m]
    exact (step _ _ d (Nat.lt_succ_self _)).symm
  refine ⟨f, ?_, ?_⟩
  · ext d
    rw [h f _ d.degree (approx _) d (Nat.lt_succ_self _), hf, Function.iterate_succ_apply']
  · intro g hg
    ext d
    rw [hf, ← step _ g d (Nat.lt_succ_self _), Function.iterate_fixed hg]
end UpperTheory.Reformulated.B.Ydb5.existsUnique_fixedPoint
