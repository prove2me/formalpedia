-- Prove2me | solution 1 for bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T20:04:34.514042+00:00
-- url     : https://prove2.me/submissions/d96236fe-dc5a-4196-ace2-62a6cfe0985e

import Theorems.Thm_bernoulli_event_intersection_probability_from_lower_bounds
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

private lemma bernoulliObservationWeight_sum_eq_one
    {n₁ n₂ : ℕ} {p : ℝ} :
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega) = 1 := by
  classical
  let α := Fin n₁ × Fin n₂
  let N := Fintype.card α
  have hsum_powerset :
      (∑ Omega : Finset α,
          p ^ Omega.card * (1 - p) ^ (N - Omega.card)) =
        ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := by
    rw [← Finset.powerset_univ]
    rw [Finset.sum_powerset]
    apply Finset.sum_congr rfl
    intro k hk
    have hcard :
        (Finset.univ : Finset α).card = N := by
      simp [N]
    have h :=
      Finset.sum_powersetCard k (Finset.univ : Finset α)
        (fun j : ℕ => p ^ j * (1 - p) ^ (N - j))
    simpa [hcard, mul_assoc, mul_left_comm, mul_comm] using h
  calc
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega)
        = ∑ Omega : Finset α,
            p ^ Omega.card * (1 - p) ^ (N - Omega.card) := by
          simp [α, N, bernoulliObservationWeight]
    _ = ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := hsum_powerset
    _ = ∑ k ∈ Finset.range (N + 1),
          p ^ k * (1 - p) ^ (N - k) * (Nat.choose N k : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = (p + (1 - p)) ^ N := by
          rw [add_pow]
    _ = 1 := by
          ring

private lemma bernoulliEventProb_true
    {n₁ n₂ : ℕ} (p : ℝ) :
    bernoulliEventProb p (fun _ : Finset (Fin n₁ × Fin n₂) => True) = 1 := by
  unfold bernoulliEventProb
  simpa using (bernoulliObservationWeight_sum_eq_one (n₁ := n₁) (n₂ := n₂) (p := p))

private theorem finite_pair_intersection_aux
    {n₁ n₂ : ℕ} (p c failureScale : ℝ)
    (Event :
      ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) →
        Finset (Fin n₁ × Fin n₂) → Prop)
    (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (hPoint :
      ∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
        bernoulliEventProb p (Event pair) ≥ 1 - c * failureScale) :
    ∀ s : Finset ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)),
      bernoulliEventProb p
          (fun Omega =>
            ∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
              pair ∈ s → Event pair Omega) ≥
        1 - (((s.card : ℝ) * c) * failureScale) := by
  intro s
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [bernoulliEventProb_true]
  | insert a s ha ih =>
      have hA :
          bernoulliEventProb p (Event a) ≥ 1 - c * failureScale :=
        hPoint a
      have hB :
          bernoulliEventProb p
              (fun Omega =>
                ∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
                  pair ∈ s → Event pair Omega) ≥
            1 - ((s.card : ℝ) * c) * failureScale :=
        ih
      have hInter :=
        bernoulli_event_intersection_probability_from_lower_bounds
          p c ((s.card : ℝ) * c) failureScale
          (Event a)
          (fun Omega =>
            ∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
              pair ∈ s → Event pair Omega)
          hp hp_one hA hB
      have hcard : (insert a s).card = s.card + 1 := by
        simp [ha]
      have hconst :
          (c + (s.card : ℝ) * c) * failureScale =
            (((insert a s).card : ℝ) * c) * failureScale := by
        rw [hcard, Nat.cast_add, Nat.cast_one]
        ring
      have hevent :
          (fun Omega : Finset (Fin n₁ × Fin n₂) =>
              Event a Omega ∧
                (∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
                  pair ∈ s → Event pair Omega)) =
            (fun Omega =>
              ∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
                pair ∈ insert a s → Event pair Omega) := by
        funext Omega
        apply propext
        constructor
        · intro h pair hpair
          rcases h with ⟨haEvent, hsEvent⟩
          by_cases hpa : pair = a
          · simpa [hpa] using haEvent
          · exact hsEvent pair (by simpa [Finset.mem_insert, hpa] using hpair)
        · intro h
          constructor
          · exact h a (by simp)
          · intro pair hpair
            exact h pair (by simp [hpair])
      simpa [hevent, hconst] using hInter

theorem solution
    (Cpoint cpoint : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∀ (p scale failureScale : ℝ), 0 ≤ p → p ≤ 1 →
      ∀ (n₁ n₂ : ℕ),
        ∀ Coeff : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) →
          Finset (Fin n₁ × Fin n₂) → ℝ,
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          bernoulliEventProb p
              (fun Omega => |Coeff w1 w2 Omega| ≤ Cpoint * scale) ≥
            1 - cpoint * failureScale) →
        bernoulliEventProb p
            (fun Omega =>
              ∀ w1 w2 : Fin n₁ × Fin n₂,
                |Coeff w1 w2 Omega| ≤ Cpoint * scale) ≥
          1 -
            (((Fintype.card
              ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) *
              cpoint) * failureScale) := by
  intro _hCpoint _hcpoint p scale failureScale hp hp_one n₁ n₂ Coeff hPoint
  have h :=
    finite_pair_intersection_aux p cpoint failureScale
      (fun pair Omega => |Coeff pair.1 pair.2 Omega| ≤ Cpoint * scale)
      hp hp_one
      (by
        intro pair
        exact hPoint pair.1 pair.2)
      (Finset.univ :
        Finset ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)))
  simpa [Prod.forall] using h
