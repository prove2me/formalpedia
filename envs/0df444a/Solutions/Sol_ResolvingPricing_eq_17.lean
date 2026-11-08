-- Prove2me | solution 1 for ResolvingPricing.eq_17
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:01:55.612682+00:00
-- url     : https://prove2.me/submissions/a52733db-ce2a-4421-adc1-2d3f20fb7d80

import Mathlib
import Definitions.Def_ResolvingPricing_Run

open MeasureTheory

namespace Aux_ResolvingPricing_eq_17

lemma main (T : ℕ) (Δ ξδ : ℕ → ℝ) : ∀ k s : ℕ, s + k = T + 1 → 2 ≤ s →
    ∑ τ ∈ Finset.Icc s T, (Δ τ - ResolvingPricing.harm T Δ τ + ResolvingPricing.harm T ξδ τ - ξδ τ)
      - ((s : ℝ) - 1) * (ResolvingPricing.harm T Δ (s - 1) - ResolvingPricing.harm T ξδ (s - 1))
      = 0 := by
  intro k
  induction k with
  | zero =>
    intro s hs _
    have hsT : s = T + 1 := by omega
    subst hsT
    have e : Finset.Icc (T + 1) T = ∅ := Finset.Icc_eq_empty (by omega)
    rw [e, Finset.sum_empty, Nat.add_sub_cancel]
    unfold ResolvingPricing.harm
    rw [Finset.Ioc_self, Finset.sum_empty, Finset.sum_empty]
    ring
  | succ k ih =>
    intro s hs h2
    have IH := ih (s + 1) (by omega) (by omega)
    have hsT : s ≤ T := by omega
    have hI : ∀ f : ℕ → ℝ, ∑ τ ∈ Finset.Icc s T, f τ = f s + ∑ τ ∈ Finset.Ioc s T, f τ := by
      intro f; rw [Finset.Icc_eq_cons_Ioc hsT, Finset.sum_cons]
    have hH : ∀ a : ℕ → ℝ, ResolvingPricing.harm T a (s - 1)
        = a s / ((s : ℝ) - 1) + ResolvingPricing.harm T a s := by
      intro a
      unfold ResolvingPricing.harm
      have : Finset.Ioc (s - 1) T = Finset.Icc s T := by
        rw [← Finset.Icc_add_one_left_eq_Ioc, Nat.sub_add_cancel (by omega)]
      rw [this, hI]
    rw [Nat.add_sub_cancel, Finset.Icc_add_one_left_eq_Ioc] at IH
    rw [hI, hH, hH]
    push_cast at IH
    have hs1 : (s : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ s := by exact_mod_cast h2
      intro h; linarith
    have e1 : ((s : ℝ) - 1) * (Δ s / ((s : ℝ) - 1)) = Δ s := by field_simp
    have e2 : ((s : ℝ) - 1) * (ξδ s / ((s : ℝ) - 1)) = ξδ s := by field_simp
    linarith

end Aux_ResolvingPricing_eq_17

open ResolvingPricing in
theorem solution (T s : ℕ) (hs : 2 ≤ s) (hsT : s ≤ T + 1) (Δ ξδ : ℕ → ℝ) :
    ∑ τ ∈ Finset.Icc s T, (Δ τ - harm T Δ τ + harm T ξδ τ - ξδ τ)
      - ((s : ℝ) - 1) * (harm T Δ (s - 1) - harm T ξδ (s - 1)) = 0 :=
  Aux_ResolvingPricing_eq_17.main T Δ ξδ (T + 1 - s) s (by omega) hs
