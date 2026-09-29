-- Prove2me | solution 1 for Supermodularity.MDP.optimal_return_supermodular_and_decision_increasing
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:13:55.839444+00:00
-- url     : https://prove2.me/submissions/cc3723ea-74b4-4cfa-960a-290d57841574

import Mathlib
import Definitions.Def_Supermodularity_MDP_StochasticallyIncreasingOn
import Definitions.Def_Supermodularity_MDP_StochasticallySupermodularOn
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

open MeasureTheory

namespace Supermodularity.MDP

/-- The diagonal point `(min t₀ t₁, min t₀ t₁)`. -/
def aux_orsd_p (t : Fin 2 → ℝ) : Fin 2 → ℝ := fun _ => min (t 0) (t 1)

theorem aux_orsd_p_mono {t t' : Fin 2 → ℝ} (h : t ≤ t') : aux_orsd_p t ≤ aux_orsd_p t' := by
  intro j
  simp only [aux_orsd_p]
  exact min_le_min (h 0) (h 1)

theorem aux_orsd_ind_mono {U : Set (Fin 2 → ℝ)} (hU : IsUpperSet U) {a b : Fin 2 → ℝ}
    (h : a ≤ b) : (Measure.dirac a U).toReal ≤ (Measure.dirac b U).toReal := by
  simp only [Measure.dirac_apply]
  by_cases ha : a ∈ U
  · have hb : b ∈ U := hU h ha
    simp [Set.indicator_of_mem ha, Set.indicator_of_mem hb]
  · by_cases hb : b ∈ U
    · simp [Set.indicator_of_notMem ha, Set.indicator_of_mem hb]
    · simp [Set.indicator_of_notMem ha, Set.indicator_of_notMem hb]

theorem aux_orsd_super {U : Set (Fin 2 → ℝ)} (hU : IsUpperSet U) (x y : Fin 2 → ℝ) :
    (Measure.dirac (aux_orsd_p x) U).toReal + (Measure.dirac (aux_orsd_p y) U).toReal ≤
      (Measure.dirac (aux_orsd_p (x ⊔ y)) U).toReal +
        (Measure.dirac (aux_orsd_p (x ⊓ y)) U).toReal := by
  rcases le_total (min (x 0) (x 1)) (min (y 0) (y 1)) with h | h
  · have e : aux_orsd_p (x ⊓ y) = aux_orsd_p x := by
      funext j
      simp only [aux_orsd_p, Pi.inf_apply]
      rw [min_min_min_comm, min_eq_left h]
    have hle : aux_orsd_p y ≤ aux_orsd_p (x ⊔ y) := aux_orsd_p_mono le_sup_right
    rw [e]
    linarith [aux_orsd_ind_mono hU hle]
  · have e : aux_orsd_p (x ⊓ y) = aux_orsd_p y := by
      funext j
      simp only [aux_orsd_p, Pi.inf_apply]
      rw [min_min_min_comm, min_eq_right h]
    have hle : aux_orsd_p x ≤ aux_orsd_p (x ⊔ y) := aux_orsd_p_mono le_sup_left
    rw [e]
    linarith [aux_orsd_ind_mono hU hle]

end Supermodularity.MDP

open Supermodularity.MDP

theorem solution : ¬ (∀ {n m : ℕ} (k : ℕ)
    (T : ℕ → Set (Fin m → ℝ)) (X : ℕ → (Fin m → ℝ) → Finset (Fin n → ℝ))
    (S : ℕ → Set ((Fin n → ℝ) × (Fin m → ℝ)))
    (hS : ∀ i, S i = {p : (Fin n → ℝ) × (Fin m → ℝ) | p.2 ∈ T i ∧ p.1 ∈ X i p.2})
    (hSlattice : ∀ i, IsSublattice (S i))
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
    (hrsuper : ∀ i, 1 ≤ i → i ≤ k →
      Supermodularity.Monotonicity.SupermodularOn
        (fun p : (Fin n → ℝ) × (Fin m → ℝ) => r i p.1 p.2) (S i))
    (hFmono : ∀ i, 1 ≤ i → i ≤ k → ∀ x,
      Supermodularity.MDP.StochasticallyIncreasingOn {t | (x, t) ∈ S i} (μ i x))
    (hFsuper : ∀ i, 1 ≤ i → i ≤ k →
      Supermodularity.MDP.StochasticallySupermodularOn (S i)
        (fun p : (Fin n → ℝ) × (Fin m → ℝ) => μ i p.1 p.2)),
    (∀ i, 1 ≤ i → i ≤ k →
      Supermodularity.Monotonicity.SupermodularOn
        (fun p : (Fin n → ℝ) × (Fin m → ℝ) => g i p.1 p.2) (S i)) ∧
    (∀ i, 1 ≤ i → i ≤ k → Supermodularity.Monotonicity.SupermodularOn (f i) (T i)) ∧
    (∀ i, 1 ≤ i → i ≤ k → ∀ ⦃t t' : Fin m → ℝ⦄, t ∈ T i → t' ∈ T i → t ≤ t' →
      Supermodularity.Lattices.InducedSetOrder
        {x : Fin n → ℝ | x ∈ X i t ∧ ∀ y ∈ X i t, g i y t ≤ g i x t}
        {x : Fin n → ℝ | x ∈ X i t' ∧ ∀ y ∈ X i t', g i y t' ≤ g i x t'}) ∧
    (∃ xg xl : ℕ → (Fin m → ℝ) → (Fin n → ℝ),
      (∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i,
        IsGreatest {x : Fin n → ℝ | x ∈ X i t ∧ ∀ y ∈ X i t, g i y t ≤ g i x t} (xg i t)) ∧
      (∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i,
        IsLeast {x : Fin n → ℝ | x ∈ X i t ∧ ∀ y ∈ X i t, g i y t ≤ g i x t} (xl i t)) ∧
      (∀ i, 1 ≤ i → i ≤ k → MonotoneOn (xg i) (T i)) ∧
      (∀ i, 1 ≤ i → i ≤ k → MonotoneOn (xl i) (T i)))) := by
  intro H
  -- Counterexample: `n = 0`, `m = 2`, `k = 2`, `T 1 = univ`, `T 2 = ∅`, `X = {0}`, `r = 0`,
  -- `β = 0`, `μ i x t = δ_(min t₀ t₁, min t₀ t₁)`, `f 2 w = -w₀`, `f 1 t = -min t₀ t₁`.
  let T : ℕ → Set (Fin 2 → ℝ) := fun i => if i = 1 then Set.univ else ∅
  let X : ℕ → (Fin 2 → ℝ) → Finset (Fin 0 → ℝ) := fun _ _ => {0}
  let S : ℕ → Set ((Fin 0 → ℝ) × (Fin 2 → ℝ)) :=
    fun i => {p | p.2 ∈ T i ∧ p.1 ∈ X i p.2}
  let r : ℕ → (Fin 0 → ℝ) → (Fin 2 → ℝ) → ℝ := fun _ _ _ => 0
  let μ : ℕ → (Fin 0 → ℝ) → (Fin 2 → ℝ) → Measure (Fin 2 → ℝ) :=
    fun _ _ t => Measure.dirac (aux_orsd_p t)
  let f : ℕ → (Fin 2 → ℝ) → ℝ := fun i w => if i = 1 then -(min (w 0) (w 1)) else -(w 0)
  let g : ℕ → (Fin 0 → ℝ) → (Fin 2 → ℝ) → ℝ :=
    fun i _ t => if i = 1 then -(min (t 0) (t 1)) else 0
  have key := H (n := 0) (m := 2) 2 T X S (fun _ => rfl) ?hSl r 0 le_rfl zero_le_one μ
    (fun _ _ _ => by simp only [μ]; infer_instance) f g
    ?hgk ?hg ?hfint ?hf ?hXne ?hXsub ?hrmono ?hrsuper ?hFmono ?hFsuper
  · have hsup := key.2.1 1 le_rfl (by norm_num)
    have hx : (![1, 0] : Fin 2 → ℝ) ∈ T 1 := by simp [T]
    have hy : (![0, 1] : Fin 2 → ℝ) ∈ T 1 := by simp [T]
    have := hsup hx hy
    simp [f] at this
    norm_num at this
  case hSl =>
    intro i
    by_cases h1 : i = 1
    · have : S i = Set.univ := by
        ext p
        simp [S, T, X, h1]
        exact Subsingleton.elim _ _
      rw [this]
      exact isSublattice_univ
    · have : S i = ∅ := by
        ext p
        simp [S, T, h1]
      rw [this]
      exact isSublattice_empty
  case hgk =>
    intro x t
    simp [g, r]
  case hg =>
    intro i hi1 hi2 x t _
    have hi : i = 1 := by omega
    subst hi
    simp [g, r, μ, f, integral_dirac, aux_orsd_p]
  case hfint =>
    intro i _ _ x t _
    exact integrable_dirac (by simp [enorm_lt_top])
  case hf =>
    intro i hi1 hi2 t ht
    have h1 : i = 1 := by
      by_contra h1
      simp [T, h1] at ht
    subst h1
    have himg : (fun x => g 1 x t) '' (X 1 t : Set (Fin 0 → ℝ)) = {g 1 0 t} := by
      simp [X]
    rw [himg]
    have : f 1 t = g 1 0 t := by simp [f, g]
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
  case hrsuper =>
    intro i _ _ a _ b _
    simp [r]
  case hFmono =>
    intro i _ _ x U hU a _ b _ hab
    exact aux_orsd_ind_mono hU (aux_orsd_p_mono hab)
  case hFsuper =>
    intro i _ _ U hU a _ b _
    exact aux_orsd_super hU a.2 b.2
