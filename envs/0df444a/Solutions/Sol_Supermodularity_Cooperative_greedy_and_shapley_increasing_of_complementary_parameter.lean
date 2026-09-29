-- Prove2me | solution 1 for Supermodularity.Cooperative.greedy_and_shapley_increasing_of_complementary_parameter
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T12:56:40.968952+00:00
-- url     : https://prove2.me/submissions/ca203ad5-dd43-437d-8148-865528b48e3a

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_GreedyPayoff
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn

set_option autoImplicit false

open Supermodularity.Cooperative in
lemma smc_marginal_mono {n : ℕ} {T : Type*} [PartialOrder T] (f : T → Finset (Fin n) → ℝ)
    (hcomp : Supermodularity.Monotonicity.IncreasingDifferencesOn
      (fun (S : Finset (Fin n)) (t : T) => f t S) Set.univ)
    {t' t'' : T} (ht : t' ≤ t'') {A B : Finset (Fin n)} (hAB : A ⊆ B) :
    f t' B - f t' A ≤ f t'' B - f t'' A := by
  rcases ht.lt_or_eq with h | h
  · have := hcomp h (a := A) (b := B) (by simp) (by simp) hAB
    simp only at this
    linarith
  · subst h; exact le_refl _

open Supermodularity.Cooperative in
theorem solution
    {n : ℕ} {T : Type*} [PartialOrder T] (f : T → Finset (Fin n) → ℝ)
    (hcomp : Supermodularity.Monotonicity.IncreasingDifferencesOn
      (fun (S : Finset (Fin n)) (t : T) => f t S) Set.univ) :
    (∀ σ : Equiv.Perm (Fin n), Monotone (fun t : T => GreedyPayoff σ (f t))) ∧
    Monotone (fun t : T => ShapleyValue (f t)) := by
  refine ⟨fun σ t' t'' ht i => ?_, fun t' t'' ht i => ?_⟩
  · simp only [GreedyPayoff]
    apply smc_marginal_mono f hcomp ht
    intro k hk
    simp only [InitialCoalition, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    omega
  · simp only [ShapleyValue]
    apply Finset.sum_le_sum
    intro S _
    apply mul_le_mul_of_nonneg_left
    · exact smc_marginal_mono f hcomp ht (Finset.subset_insert i S)
    · positivity
