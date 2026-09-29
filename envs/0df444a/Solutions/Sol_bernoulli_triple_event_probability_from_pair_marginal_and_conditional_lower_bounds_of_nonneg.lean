-- Prove2me | solution 1 for bernoulli_triple_event_probability_from_pair_marginal_and_conditional_lower_bounds_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:28:34.184779+00:00
-- url     : https://prove2.me/submissions/a75ebd45-6c54-4faa-bda7-08a36733cc26

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

private lemma bernoulliObservationWeight_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp _)
    (pow_nonneg (sub_nonneg.mpr hp_one) _)

private lemma sum_bernoulliObservationWeight_eq_one
    {n₁ n₂ : ℕ} {p : ℝ} (_hp : 0 ≤ p) (_hp_one : p ≤ 1) :
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

private lemma bernoulliEventProb_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ bernoulliEventProb p Event := by
  unfold bernoulliEventProb
  apply Finset.sum_nonneg
  intro Omega _
  by_cases hEvent : Event Omega
  · simp [hEvent, bernoulliObservationWeight_nonneg hp hp_one Omega]
  · simp [hEvent]

private lemma bernoulliEventProb_le_one
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliEventProb p Event ≤ 1 := by
  have hle :
      bernoulliEventProb p Event ≤
        ∑ Omega : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Omega := by
    unfold bernoulliEventProb
    apply Finset.sum_le_sum
    intro Omega _
    by_cases hEvent : Event Omega
    · simp [hEvent]
    · simp [hEvent, bernoulliObservationWeight_nonneg hp hp_one Omega]
  simpa [sum_bernoulliObservationWeight_eq_one hp hp_one] using hle

private lemma bernoulliPairEventProb_as_conditional_sum
    {n₁ n₂ : ℕ} (p : ℝ)
    (EventPair :
      Finset (Fin n₁ × Fin n₂) → Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliPairEventProb p EventPair =
      ∑ Omega2 : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega2 *
          bernoulliEventProb p (fun Omega1 => EventPair Omega1 Omega2) := by
  unfold bernoulliPairEventProb bernoulliEventProb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Omega2 _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Omega1 _
  by_cases hEvent : EventPair Omega1 Omega2
  · simp [hEvent]
    ring
  · simp [hEvent]

private lemma bernoulliPairEventProb_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (EventPair :
      Finset (Fin n₁ × Fin n₂) → Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ bernoulliPairEventProb p EventPair := by
  rw [bernoulliPairEventProb_as_conditional_sum]
  apply Finset.sum_nonneg
  intro Omega2 _
  exact mul_nonneg
    (bernoulliObservationWeight_nonneg hp hp_one Omega2)
    (bernoulliEventProb_nonneg hp hp_one _)

private lemma bernoulliPairEventProb_le_one
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (EventPair :
      Finset (Fin n₁ × Fin n₂) → Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliPairEventProb p EventPair ≤ 1 := by
  rw [bernoulliPairEventProb_as_conditional_sum]
  have hle :
      (∑ Omega2 : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega2 *
          bernoulliEventProb p (fun Omega1 => EventPair Omega1 Omega2)) ≤
      ∑ Omega2 : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega2 * 1 := by
    apply Finset.sum_le_sum
    intro Omega2 _
    exact mul_le_mul_of_nonneg_left
      (bernoulliEventProb_le_one hp hp_one _)
      (bernoulliObservationWeight_nonneg hp hp_one Omega2)
  have hsum :
      (∑ Omega2 : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega2 * 1) = 1 := by
    simpa using sum_bernoulliObservationWeight_eq_one (n₁ := n₁) (n₂ := n₂) hp hp_one
  exact le_trans hle (le_of_eq hsum)

private lemma bernoulliTripleEventProb_as_conditional_sum
    {n₁ n₂ : ℕ} (p : ℝ)
    (EventTriple :
      Finset (Fin n₁ × Fin n₂) →
      Finset (Fin n₁ × Fin n₂) →
      Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliTripleEventProb p EventTriple =
      ∑ Omega2 : Finset (Fin n₁ × Fin n₂),
        ∑ Omega3 : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Omega2 *
            bernoulliObservationWeight p Omega3 *
              bernoulliEventProb p
                (fun Omega1 => EventTriple Omega1 Omega2 Omega3) := by
  unfold bernoulliTripleEventProb bernoulliEventProb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Omega2 _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Omega3 _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Omega1 _
  by_cases hEvent : EventTriple Omega1 Omega2 Omega3
  · simp [hEvent]
    ring
  · simp [hEvent]

theorem solution
    {n₁ n₂ : ℕ} (p cPair cCond scale : ℝ)
    (EventPair :
      Finset (Fin n₁ × Fin n₂) → Finset (Fin n₁ × Fin n₂) → Prop)
    (EventTriple :
      Finset (Fin n₁ × Fin n₂) →
      Finset (Fin n₁ × Fin n₂) →
      Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    0 ≤ cCond * scale →
    bernoulliPairEventProb p EventPair ≥ 1 - cPair * scale →
    (∀ Omega2 Omega3,
      EventPair Omega2 Omega3 →
        bernoulliEventProb p (fun Omega1 => EventTriple Omega1 Omega2 Omega3) ≥
          1 - cCond * scale) →
    bernoulliTripleEventProb p EventTriple ≥ 1 - (cCond + cPair) * scale := by
  intro hp hp_one hCondFailureNonneg hPair hCond
  let pairProb : ℝ := bernoulliPairEventProb p EventPair
  let condFailure : ℝ := cCond * scale
  let pairFailure : ℝ := cPair * scale
  have hpair_le_one : pairProb ≤ 1 := by
    exact bernoulliPairEventProb_le_one hp hp_one EventPair
  have hpairFailureNonneg : 0 ≤ pairFailure := by
    have hle_one : 1 - pairFailure ≤ 1 := le_trans hPair hpair_le_one
    linarith
  have htriple_lower :
      bernoulliTripleEventProb p EventTriple ≥
        pairProb * (1 - condFailure) := by
    rw [bernoulliTripleEventProb_as_conditional_sum]
    have hsum_lower :
        (∑ Omega2 : Finset (Fin n₁ × Fin n₂),
          ∑ Omega3 : Finset (Fin n₁ × Fin n₂),
            (if EventPair Omega2 Omega3 then
              bernoulliObservationWeight p Omega2 *
                bernoulliObservationWeight p Omega3 *
                  (1 - condFailure)
            else 0)) ≤
          ∑ Omega2 : Finset (Fin n₁ × Fin n₂),
            ∑ Omega3 : Finset (Fin n₁ × Fin n₂),
              bernoulliObservationWeight p Omega2 *
                bernoulliObservationWeight p Omega3 *
                  bernoulliEventProb p
                    (fun Omega1 => EventTriple Omega1 Omega2 Omega3) := by
      apply Finset.sum_le_sum
      intro Omega2 _
      apply Finset.sum_le_sum
      intro Omega3 _
      by_cases hP : EventPair Omega2 Omega3
      · have hw2 := bernoulliObservationWeight_nonneg hp hp_one Omega2
        have hw3 := bernoulliObservationWeight_nonneg hp hp_one Omega3
        have hw23 : 0 ≤
            bernoulliObservationWeight p Omega2 *
              bernoulliObservationWeight p Omega3 :=
          mul_nonneg hw2 hw3
        have hc :
            1 - condFailure ≤
              bernoulliEventProb p
                (fun Omega1 => EventTriple Omega1 Omega2 Omega3) := by
          simpa [condFailure] using hCond Omega2 Omega3 hP
        simp [hP]
        exact mul_le_mul_of_nonneg_left hc hw23
      · have hw2 := bernoulliObservationWeight_nonneg hp hp_one Omega2
        have hw3 := bernoulliObservationWeight_nonneg hp hp_one Omega3
        have hprob :
            0 ≤ bernoulliEventProb p
              (fun Omega1 => EventTriple Omega1 Omega2 Omega3) :=
          bernoulliEventProb_nonneg hp hp_one _
        simp [hP]
        exact mul_nonneg (mul_nonneg hw2 hw3) hprob
    have hsum_eq :
        (∑ Omega2 : Finset (Fin n₁ × Fin n₂),
          ∑ Omega3 : Finset (Fin n₁ × Fin n₂),
            (if EventPair Omega2 Omega3 then
              bernoulliObservationWeight p Omega2 *
                bernoulliObservationWeight p Omega3 *
                  (1 - condFailure)
            else 0)) =
          pairProb * (1 - condFailure) := by
      unfold pairProb bernoulliPairEventProb
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro Omega2 _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro Omega3 _
      by_cases hP : EventPair Omega2 Omega3
      · simp [hP]
      · simp [hP]
    simpa [hsum_eq] using hsum_lower
  have hscalar :
      pairProb * (1 - condFailure) ≥
        1 - (cCond + cPair) * scale := by
    have htarget :
        1 - (cCond + cPair) * scale =
          1 - condFailure - pairFailure := by
      simp [condFailure, pairFailure]
      ring
    rw [htarget]
    by_cases hfactor : 0 ≤ 1 - condFailure
    · have hprod_lower :
          (1 - pairFailure) * (1 - condFailure) ≤
            pairProb * (1 - condFailure) := by
        exact mul_le_mul_of_nonneg_right hPair hfactor
      have hcross :
          1 - condFailure - pairFailure ≤
            (1 - pairFailure) * (1 - condFailure) := by
        nlinarith [hCondFailureNonneg, hpairFailureNonneg]
      exact le_trans hcross hprod_lower
    · have hfactor_nonpos : 1 - condFailure ≤ 0 := le_of_lt (lt_of_not_ge hfactor)
      have hprod_ge_factor :
          1 - condFailure ≤ pairProb * (1 - condFailure) := by
        have hmul :=
          mul_le_mul_of_nonpos_right hpair_le_one hfactor_nonpos
        simpa using hmul
      have htarget_le_factor :
          1 - condFailure - pairFailure ≤ 1 - condFailure := by
        linarith
      exact le_trans htarget_le_factor hprod_ge_factor
  exact le_trans hscalar htriple_lower
