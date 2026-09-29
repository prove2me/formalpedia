-- Prove2me | solution 1 for Supermodularity.MDP.value_increasing_of_stochastically_increasing
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:41:05.656132+00:00
-- url     : https://prove2.me/submissions/f971e977-a1ea-47d7-92a7-c224b6744b6e

import Mathlib
import Definitions.Def_Supermodularity_MDP_StochasticallyIncreasingOn

open MeasureTheory

namespace Supermodularity.MDP

/-- The Dirac family `t ↦ δ_t` is stochastically increasing on any set. -/
theorem aux_visi_dirac_si (D : Set (Fin 1 → ℝ)) :
    StochasticallyIncreasingOn D (fun t : Fin 1 → ℝ => Measure.dirac t) := by
  intro S hS a _ b _ hab
  simp only [Measure.dirac_apply]
  by_cases ha : a ∈ S
  · have hb : b ∈ S := hS hab ha
    simp [Set.indicator_of_mem ha, Set.indicator_of_mem hb]
  · by_cases hb : b ∈ S
    · simp [Set.indicator_of_notMem ha, Set.indicator_of_mem hb]
    · simp [Set.indicator_of_notMem ha, Set.indicator_of_notMem hb]

end Supermodularity.MDP

open Supermodularity.MDP

theorem solution : ¬ (∀ {n m : ℕ} (k : ℕ)
    (T : ℕ → Set (Fin m → ℝ)) (X : ℕ → (Fin m → ℝ) → Finset (Fin n → ℝ))
    (S : ℕ → Set ((Fin n → ℝ) × (Fin m → ℝ)))
    (hS : ∀ i, S i = {p : (Fin n → ℝ) × (Fin m → ℝ) | p.2 ∈ T i ∧ p.1 ∈ X i p.2})
    (r : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (μ : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → Measure (Fin m → ℝ))
    (hμprob : ∀ i x t, IsProbabilityMeasure (μ i x t))
    (f : ℕ → (Fin m → ℝ) → ℝ) (g : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hgk : ∀ x t, g k x t = r k x t)
    (hg : ∀ i, 1 ≤ i → i < k → ∀ x t, (x, t) ∈ S i →
      g i x t = r i x t + (1 / (1 + β)) * ∫ w, f (i + 1) w ∂ (μ i x t))
    (hfint : ∀ i, 1 ≤ i → i < k → ∀ x t, (x, t) ∈ S i → Integrable (f (i + 1)) (μ i x t))
    (hf : ∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i,
      IsGreatest ((fun x => g i x t) '' (X i t : Set (Fin n → ℝ))) (f i t))
    (hXne : ∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i, (X i t).Nonempty)
    (hXsub : ∀ i, 1 ≤ i → i ≤ k → ∀ ⦃t' t'' : Fin m → ℝ⦄, t' ∈ T i → t'' ∈ T i → t' ≤ t'' →
      X i t' ⊆ X i t'')
    (hrmono : ∀ i, 1 ≤ i → i ≤ k → ∀ x, MonotoneOn (fun t => r i x t) {t | (x, t) ∈ S i})
    (hFmono : ∀ i, 1 ≤ i → i ≤ k → ∀ x,
      Supermodularity.MDP.StochasticallyIncreasingOn {t | (x, t) ∈ S i} (μ i x)),
    ∀ i, 1 ≤ i → i ≤ k → MonotoneOn (f i) (T i)) := by
  intro H
  -- Counterexample: `n = 0`, `m = 1`, `k = 2`, `T 1 = {0, 1}`, `T 2 = {0}`, `X = {0}`,
  -- `r = 0`, `β = 0`, `μ i x t = δ_t`, `f i w = -(w 0)`.
  let T : ℕ → Set (Fin 1 → ℝ) := fun i => if i = 2 then {0} else {0, 1}
  let X : ℕ → (Fin 1 → ℝ) → Finset (Fin 0 → ℝ) := fun _ _ => {0}
  let S : ℕ → Set ((Fin 0 → ℝ) × (Fin 1 → ℝ)) :=
    fun i => {p | p.2 ∈ T i ∧ p.1 ∈ X i p.2}
  let r : ℕ → (Fin 0 → ℝ) → (Fin 1 → ℝ) → ℝ := fun _ _ _ => 0
  let μ : ℕ → (Fin 0 → ℝ) → (Fin 1 → ℝ) → Measure (Fin 1 → ℝ) :=
    fun _ _ t => Measure.dirac t
  let f : ℕ → (Fin 1 → ℝ) → ℝ := fun _ w => -(w 0)
  let g : ℕ → (Fin 0 → ℝ) → (Fin 1 → ℝ) → ℝ := fun i _ t => if i = 2 then 0 else -(t 0)
  have key := H (n := 0) (m := 1) 2 T X S (fun _ => rfl) r 0 le_rfl zero_le_one μ
    (fun _ _ _ => by simp only [μ]; infer_instance) f g
    ?hgk ?hg ?hfint ?hf ?hXne ?hXsub ?hrmono ?hFmono
  · have hmono := key 1 le_rfl (by norm_num)
    have h0 : (0 : Fin 1 → ℝ) ∈ T 1 := by simp [T]
    have h1 : (1 : Fin 1 → ℝ) ∈ T 1 := by simp [T]
    have := hmono h0 h1 zero_le_one
    simp [f] at this
    norm_num at this
  case hgk =>
    intro x t
    simp [g, r]
  case hg =>
    intro i hi1 hi2 x t _
    have hi : i = 1 := by omega
    subst hi
    simp [g, r, μ, f, integral_dirac]
  case hfint =>
    intro i _ _ x t _
    exact integrable_dirac (by simp [enorm_lt_top])
  case hf =>
    intro i hi1 hi2 t ht
    have himg : (fun x => g i x t) '' (X i t : Set (Fin 0 → ℝ)) = {g i 0 t} := by
      simp [X]
    rw [himg]
    have : f i t = g i 0 t := by
      by_cases h2 : i = 2
      · subst h2
        have ht0 : t = 0 := by simpa [T] using ht
        subst ht0
        simp [f, g]
      · simp [f, g, h2]
    rw [this]
    exact isGreatest_singleton
  case hXne =>
    intro i _ _ t _
    simp [X]
  case hXsub =>
    intro i _ _ t' t'' _ _ _
    simp [X]
  case hrmono =>
    intro i _ _ x a _ b _ _
    simp [r]
  case hFmono =>
    intro i _ _ x
    exact aux_visi_dirac_si _
