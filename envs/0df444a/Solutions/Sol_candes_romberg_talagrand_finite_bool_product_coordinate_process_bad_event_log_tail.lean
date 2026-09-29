-- Prove2me | solution 1 for candes_romberg_talagrand_finite_bool_product_coordinate_process_bad_event_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T03:21:31.085808+00:00
-- url     : https://prove2.me/submissions/7af93d65-18d3-4cbb-81d9-df7a81b6086b

import Theorems.Thm_ledoux_talagrand_finite_bool_product_coordinate_process_good_event_log_tail
import Mathlib.Tactic

open MatrixCompletion
open MeasureTheory
open scoped Classical BigOperators

/-!
Source: formal complement bridge from the Ledoux--Talagrand good-event theorem
to the Candès--Romberg bad-event statement.  The analytic input is
Ledoux, *The Concentration of Measure Phenomenon*, Section 7, Corollary 7.8,
as used in Candès--Romberg, PDF p. 11, Section 3, Theorem 3.2/equation (3.9),
and cited by Candès--Recht, Appendix 9.1, PDF p. 46, Theorem 9.1 and
equations (9.1)--(9.2).  This sketch only uses the formal identity
`μ(Gᶜ) = 1 - μ(G)` for a probability measure.
-/

theorem solution :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ : ℕ) (p : NNReal) (hp : p ≤ 1)
        (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂, |coeff a i j| ≤ B) →
        (∀ a : ι,
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            (p : ℝ) * (1 - (p : ℝ)) * (coeff a i j) ^ 2 ≤ sigmaSq) →
        let boolProcess : ι → ((Fin n₁ × Fin n₂) → Bool) → ℝ :=
          fun a ω =>
            ∑ i : Fin n₁, ∑ j : Fin n₂,
              ((cond (ω (i, j)) (1 : ℝ) 0 - (p : ℝ)) * coeff a i j)
        let boolZ : ((Fin n₁ × Fin n₂) → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => boolProcess a ω)
        let boolZbar : ((Fin n₁ × Fin n₂) → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |boolProcess a ω|)
        (bernMeasure (n1 := n₁) (n2 := n₂) p hp).real
            {ω | ¬ |boolZ ω -
                  (∫ ω, boolZ ω ∂(bernMeasure (n1 := n₁) (n2 := n₂) p hp))| ≤ t} ≤
          3 * Real.exp
            (-(t / (K * B)) *
              Real.log
                (1 + (B * t) /
                  (sigmaSq + B *
                    (∫ ω, boolZbar ω ∂(bernMeasure (n1 := n₁) (n2 := n₂) p hp))))) := by
  rcases ledoux_talagrand_finite_bool_product_coordinate_process_good_event_log_tail with
    ⟨K, hK, hGoodTail⟩
  refine ⟨K, hK, ?_⟩
  intro n₁ n₂ p hp ι _instFintype _instNonempty coeff B sigmaSq t
    hB hsigma ht hbound hvar
  let boolProcess : ι → ((Fin n₁ × Fin n₂) → Bool) → ℝ :=
    fun a ω =>
      ∑ i : Fin n₁, ∑ j : Fin n₂,
        ((cond (ω (i, j)) (1 : ℝ) 0 - (p : ℝ)) * coeff a i j)
  let boolZ : ((Fin n₁ × Fin n₂) → Bool) → ℝ :=
    fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => boolProcess a ω)
  let boolZbar : ((Fin n₁ × Fin n₂) → Bool) → ℝ :=
    fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |boolProcess a ω|)
  let μ := bernMeasure (n1 := n₁) (n2 := n₂) p hp
  let failure : ℝ :=
    3 * Real.exp
      (-(t / (K * B)) *
        Real.log
          (1 + (B * t) /
            (sigmaSq + B * (∫ ω, boolZbar ω ∂μ))))
  let Good : Set ((Fin n₁ × Fin n₂) → Bool) :=
    {ω | |boolZ ω - (∫ ω, boolZ ω ∂μ)| ≤ t}
  have hGood : μ.real Good ≥ 1 - failure := by
    simpa [boolProcess, boolZ, boolZbar, μ, failure, Good] using
      hGoodTail n₁ n₂ p hp ι coeff B sigmaSq t
        hB hsigma ht hbound hvar
  have hGoodMeas : MeasurableSet Good :=
    MeasurableSet.of_discrete
  have hcompl : μ.real Goodᶜ = 1 - μ.real Good := by
    exact probReal_compl_eq_one_sub (μ := μ) hGoodMeas
  have hbad : μ.real Goodᶜ ≤ failure := by
    rw [hcompl]
    linarith
  change μ.real Goodᶜ ≤ failure
  exact hbad
