-- Prove2me | solution 1 for bernoulli_powerset_expectation_quadruple
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T22:13:43.883404+00:00
-- url     : https://prove2.me/submissions/0ef457ec-f72d-46ac-b706-2b2824666368

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

/-- Single-sum linearity of the Bernoulli powerset expectation: the expectation
of a finite sum (over any index type) of statistics pushes through the sum. -/
private theorem bexp_sum_pushthrough {n₁ n₂ : ℕ} {ι : Type*} [Fintype ι] (p : ℝ)
    (F : ι → Finset (Fin n₁ × Fin n₂) → ℝ) :
    bernoulliExpectation p (fun Omega => ∑ i : ι, F i Omega) =
      ∑ i : ι, bernoulliExpectation p (fun Omega => F i Omega) := by
  classical
  unfold bernoulliExpectation
  have hdist : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      bernoulliObservationWeight p Omega * (∑ i : ι, F i Omega) =
        ∑ i : ι, bernoulliObservationWeight p Omega * F i Omega := by
    intro Omega; rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun Omega _ => hdist Omega), Finset.sum_comm]

/-- `bernoulli_powerset_expectation_quadruple`.

**Quadruple linearity** of the Bernoulli powerset expectation: the expectation of
a fourfold coordinate sum of functions of four inclusion indicators pushes through
all four sums term-by-term. Proved by applying the single-sum push-through lemma
(distribute the weight, swap order so `∑_Ω` lands innermost) four times in
succession. This is the form used to expand the **fourth moment** of a statistic
linear in the inclusion indicators into a fourfold sum of coordinate
expectations, the first step of the Rosenthal/Latała even-moment expansion
(Boucheron–Lugosi–Massart, *Concentration Inequalities*, OUP 2013, Ch. 15). -/
theorem solution {n₁ n₂ : ℕ} (p : ℝ)
    (G : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) →
      ℝ → ℝ → ℝ → ℝ → ℝ) :
    bernoulliExpectation p
        (fun Omega => ∑ a : Fin n₁ × Fin n₂, ∑ b : Fin n₁ × Fin n₂,
          ∑ c : Fin n₁ × Fin n₂, ∑ d : Fin n₁ × Fin n₂,
          G a b c d (if a ∈ Omega then 1 else 0) (if b ∈ Omega then 1 else 0)
            (if c ∈ Omega then 1 else 0) (if d ∈ Omega then 1 else 0)) =
      ∑ a : Fin n₁ × Fin n₂, ∑ b : Fin n₁ × Fin n₂,
        ∑ c : Fin n₁ × Fin n₂, ∑ d : Fin n₁ × Fin n₂,
        bernoulliExpectation p
          (fun Omega => G a b c d (if a ∈ Omega then 1 else 0) (if b ∈ Omega then 1 else 0)
            (if c ∈ Omega then 1 else 0) (if d ∈ Omega then 1 else 0)) := by
  classical
  rw [bexp_sum_pushthrough p
    (fun a Omega => ∑ b : Fin n₁ × Fin n₂, ∑ c : Fin n₁ × Fin n₂, ∑ d : Fin n₁ × Fin n₂,
      G a b c d (if a ∈ Omega then 1 else 0) (if b ∈ Omega then 1 else 0)
        (if c ∈ Omega then 1 else 0) (if d ∈ Omega then 1 else 0))]
  apply Finset.sum_congr rfl; intro a _
  rw [bexp_sum_pushthrough p
    (fun b Omega => ∑ c : Fin n₁ × Fin n₂, ∑ d : Fin n₁ × Fin n₂,
      G a b c d (if a ∈ Omega then 1 else 0) (if b ∈ Omega then 1 else 0)
        (if c ∈ Omega then 1 else 0) (if d ∈ Omega then 1 else 0))]
  apply Finset.sum_congr rfl; intro b _
  rw [bexp_sum_pushthrough p
    (fun c Omega => ∑ d : Fin n₁ × Fin n₂,
      G a b c d (if a ∈ Omega then 1 else 0) (if b ∈ Omega then 1 else 0)
        (if c ∈ Omega then 1 else 0) (if d ∈ Omega then 1 else 0))]
  apply Finset.sum_congr rfl; intro c _
  rw [bexp_sum_pushthrough p
    (fun d Omega =>
      G a b c d (if a ∈ Omega then 1 else 0) (if b ∈ Omega then 1 else 0)
        (if c ∈ Omega then 1 else 0) (if d ∈ Omega then 1 else 0))]
