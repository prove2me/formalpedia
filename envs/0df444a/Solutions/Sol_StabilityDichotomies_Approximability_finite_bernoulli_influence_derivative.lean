-- Prove2me | solution 1 for StabilityDichotomies.Approximability.finite_bernoulli_influence_derivative
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:15:52.663205+00:00
-- url     : https://prove2.me/submissions/ebe63a73-bed3-492b-af48-bca0bd836ea0

import Mathlib
noncomputable section
open scoped Classical BigOperators

private def bernWeight {ι : Type} [Fintype ι] (t : ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, if x i then t else 1 - t

private def bernExcept {ι : Type} [Fintype ι] (t : ℝ) (x : ι → Bool) (i : ι) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, if x j then t else 1 - t

private theorem bernoulli_expectation_derivative_expanded {ι : Type} [Fintype ι]
    (h : (ι → Bool) → ℝ) (t : ℝ) :
    HasDerivAt (fun p => ∑ x : ι → Bool, h x * bernWeight p x)
      (∑ x : ι → Bool, h x * ∑ i : ι,
        bernExcept t x i * (if x i then (1 : ℝ) else -1)) t := by
  apply HasDerivAt.fun_sum
  intro x hx
  apply HasDerivAt.const_mul
  unfold bernWeight bernExcept
  apply HasDerivAt.fun_finsetProd
  intro i hi
  cases hxi : x i
  · change HasDerivAt (fun p : ℝ => 1 - p) (-1) t
    exact (hasDerivAt_id t).const_sub 1
  · change HasDerivAt (fun p : ℝ => p) 1 t
    exact hasDerivAt_id t

private def flipAt {ι : Type} (i : ι) (x : ι → Bool) : ι → Bool :=
  Function.update x i (!x i)

private theorem flipAt_involutive {ι : Type} (i : ι) : Function.Involutive (flipAt i) := by
  intro x
  funext j
  by_cases h : j = i
  · subst j
    simp [flipAt]
  · simp [flipAt, Function.update, h]

private theorem bernExcept_flip {ι : Type} [Fintype ι]
    (t : ℝ) (x : ι → Bool) (i : ι) : bernExcept t (flipAt i x) i = bernExcept t x i := by
  unfold bernExcept
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [flipAt, Function.update, hji]

private theorem update_flip {ι : Type} (i : ι) (x : ι → Bool) (b : Bool) :
    Function.update (flipAt i x) i b = Function.update x i b := by
  funext j
  by_cases h : j = i
  · subst j; simp [flipAt]
  · simp [flipAt, Function.update, h]

private theorem bernWeight_split {ι : Type} [Fintype ι]
    (t : ℝ) (x : ι → Bool) (i : ι) :
    bernWeight t x = bernExcept t x i * (if x i then t else 1 - t) := by
  unfold bernWeight bernExcept
  exact (Finset.prod_erase_mul Finset.univ (fun j => if x j then t else 1 - t)
    (Finset.mem_univ i)).symm

private theorem paired_influence_identity {ι : Type} [Fintype ι]
    (h : (ι → Bool) → ℝ) (t : ℝ) (i : ι) (x : ι → Bool) :
    let G : (ι → Bool) → ℝ := fun y => h y * bernExcept t y i * (if y i then (1 : ℝ) else -1)
    let H : (ι → Bool) → ℝ := fun y => bernWeight t y *
      (h (Function.update y i true) - h (Function.update y i false))
    G x + G (flipAt i x) = H x + H (flipAt i x) := by
  dsimp only
  rw [bernWeight_split t x i, bernWeight_split t (flipAt i x) i, bernExcept_flip]
  rw [update_flip, update_flip]
  cases hx : x i with
  | false =>
    have h0 : Function.update x i false = x := Function.update_eq_self_iff.mpr hx.symm
    have h1 : flipAt i x = Function.update x i true := by simp [flipAt, hx]
    rw [h0, h1]
    simp [hx]
    ring
  | true =>
    have h1 : Function.update x i true = x := Function.update_eq_self_iff.mpr hx.symm
    have h0 : flipAt i x = Function.update x i false := by simp [flipAt, hx]
    rw [h1, h0]
    simp [hx]
    ring

private theorem influence_sum_identity {ι : Type} [Fintype ι]
    (h : (ι → Bool) → ℝ) (t : ℝ) (i : ι) :
    (∑ x : ι → Bool, h x * bernExcept t x i * (if x i then (1 : ℝ) else -1)) =
      ∑ x : ι → Bool, bernWeight t x *
        (h (Function.update x i true) - h (Function.update x i false)) := by
  let G : (ι → Bool) → ℝ := fun y => h y * bernExcept t y i * (if y i then 1 else -1)
  let H : (ι → Bool) → ℝ := fun y => bernWeight t y *
    (h (Function.update y i true) - h (Function.update y i false))
  let E : (ι → Bool) ≃ (ι → Bool) := ⟨flipAt i, flipAt i, flipAt_involutive i, flipAt_involutive i⟩
  have hg : (∑ x, G (flipAt i x)) = ∑ x, G x := E.sum_comp G
  have hh : (∑ x, H (flipAt i x)) = ∑ x, H x := E.sum_comp H
  have hp : (∑ x, (G x + G (flipAt i x))) = ∑ x, (H x + H (flipAt i x)) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact paired_influence_identity h t i x
  simp only [Finset.sum_add_distrib] at hp
  rw [hg, hh] at hp
  change (∑ x, G x) = ∑ x, H x
  linarith

private theorem bernoulli_expectation_derivative_influences {ι : Type} [Fintype ι]
    (h : (ι → Bool) → ℝ) (t : ℝ) :
    HasDerivAt (fun p => ∑ x : ι → Bool, h x * bernWeight p x)
      (∑ i : ι, ∑ x : ι → Bool, bernWeight t x *
        (h (Function.update x i true) - h (Function.update x i false))) t := by
  apply (bernoulli_expectation_derivative_expanded h t).congr_deriv
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact influence_sum_identity h t i

theorem solution {ι : Type} [Fintype ι]
    (h : (ι → Bool) → ℝ) (t : ℝ) :
    HasDerivAt (fun p => ∑ x : ι → Bool, h x * ∏ i : ι, (if x i then p else 1 - p))
      (∑ i : ι, ∑ x : ι → Bool, (∏ j : ι, (if x j then t else 1 - t)) *
        (h (Function.update x i true) - h (Function.update x i false))) t := by
  simpa only [bernWeight] using bernoulli_expectation_derivative_influences h t
