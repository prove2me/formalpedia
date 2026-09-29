-- Prove2me | solution 1 for centered_sampling_jensen_independent_copy_moment_bound_of_sample_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T23:02:17.507323+00:00
-- url     : https://prove2.me/submissions/3bdc8b7c-bc87-48d5-9c38-68113c8bb822

import Theorems.Thm_centered_sampling_jensen_pointwise_independent_copy_bound_of_sample_ratio
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

/-!
Source: Candes-Recht, "Exact Matrix Completion via Convex Optimization",
Section 6.1, PDF p. 24 in the local copy.  The paragraph beginning "Since the
function `f(S)=||S||^q` is convex, Jensen's inequality gives..." derives
`E ||S||^q <= E ||S - S'||^q`, where `S'` is an independent copy of the
centered sampled matrix.

Reduction: the child theorem is the pointwise-in-`Omega` Jensen inequality.
The present parent theorem integrates that pointwise inequality over `Omega`.
The sample-ratio hypotheses give `p in [0,1]`, so all Bernoulli weights are
nonnegative and the finite sum is monotone.
-/

private lemma bernoulliObservationWeight_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp _)
    (pow_nonneg (sub_nonneg.mpr hp_one) _)

theorem solution :
    ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
      bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            spectralNorm
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
        bernoulliPairExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega Omega' =>
            spectralNorm
              (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X -
                centeredSamplingFluctuation Omega'
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) := by
  intro n₁ n₂ m q X hn₁ hn₂ hm hq
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hp, hp_one⟩
  have hPointwise :=
    centered_sampling_jensen_pointwise_independent_copy_bound_of_sample_ratio
      n₁ n₂ m q X hn₁ hn₂ hm hq
  change
    bernoulliExpectation p
        (fun Omega =>
          spectralNorm (centeredSamplingFluctuation Omega p X) ^ q) ≤
      bernoulliPairExpectation p
        (fun Omega Omega' =>
          spectralNorm
            (centeredSamplingFluctuation Omega p X -
              centeredSamplingFluctuation Omega' p X) ^ q)
  unfold bernoulliExpectation bernoulliPairExpectation
  apply Finset.sum_le_sum
  intro Omega _hOmega
  have hweight_nonneg : 0 ≤ bernoulliObservationWeight p Omega :=
    bernoulliObservationWeight_nonneg hp hp_one Omega
  have hOmegaPointwise :
      spectralNorm (centeredSamplingFluctuation Omega p X) ^ q ≤
        ∑ Omega' : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Omega' *
            spectralNorm
              (centeredSamplingFluctuation Omega p X -
                centeredSamplingFluctuation Omega' p X) ^ q := by
    simpa [p, bernoulliExpectation] using hPointwise Omega
  calc
    bernoulliObservationWeight p Omega *
        spectralNorm (centeredSamplingFluctuation Omega p X) ^ q
        ≤ bernoulliObservationWeight p Omega *
          (∑ Omega' : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Omega' *
              spectralNorm
                (centeredSamplingFluctuation Omega p X -
                  centeredSamplingFluctuation Omega' p X) ^ q) := by
          exact mul_le_mul_of_nonneg_left hOmegaPointwise hweight_nonneg
    _ =
        ∑ Omega' : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Omega *
            bernoulliObservationWeight p Omega' *
              spectralNorm
                (centeredSamplingFluctuation Omega p X -
                  centeredSamplingFluctuation Omega' p X) ^ q := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro Omega' _hOmega'
          ring
