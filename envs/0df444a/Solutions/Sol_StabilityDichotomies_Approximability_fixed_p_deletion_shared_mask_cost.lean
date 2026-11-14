-- Prove2me | solution 1 for StabilityDichotomies.Approximability.fixed_p_deletion_shared_mask_cost
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:10:24.926221+00:00
-- url     : https://prove2.me/submissions/7ada0d09-3ae5-419e-8677-db0503d8f35b

import Mathlib
noncomputable section
open scoped Classical BigOperators

private def weight {ι : Type} [Fintype ι] (p : ℝ) (x : ι → Bool) : ℝ :=
  ∏ j, if x j then p else 1-p
private def weightExcept {ι : Type} [Fintype ι] (p : ℝ) (x : ι → Bool) (i : ι) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, if x j then p else 1-p
private def flipAt {ι : Type} (i : ι) (x : ι → Bool) : ι → Bool := Function.update x i (!x i)

private theorem flipAt_involutive {ι : Type} (i : ι) : Function.Involutive (flipAt i) := by
  intro x
  funext j
  by_cases h : j = i
  · subst j; simp [flipAt]
  · simp [flipAt, Function.update, h]

private theorem weightExcept_flip {ι : Type} [Fintype ι] (p : ℝ) (x : ι → Bool) (i : ι) :
    weightExcept p (flipAt i x) i = weightExcept p x i := by
  unfold weightExcept
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

private theorem weight_split {ι : Type} [Fintype ι] (p : ℝ) (x : ι → Bool) (i : ι) :
    weight p x = weightExcept p x i * (if x i then p else 1-p) := by
  unfold weight weightExcept
  exact (Finset.prod_erase_mul Finset.univ (fun j => if x j then p else 1-p)
    (Finset.mem_univ i)).symm

private theorem coordinate_pair_identity {ι : Type} [Fintype ι]
    (d : (ι → Bool) → (ι → Bool) → ℝ) (p : ℝ) (i : ι) (x : ι → Bool) :
    let Δ : (ι → Bool) → ℝ := fun y => d (Function.update y i true) (Function.update y i false)
    let L : (ι → Bool) → ℝ := fun y => weight p y * (if y i then Δ y else 0)
    let R : (ι → Bool) → ℝ := fun y => p * weight p y * Δ y
    L x + L (flipAt i x) = R x + R (flipAt i x) := by
  dsimp only
  rw [weight_split p x i, weight_split p (flipAt i x) i, weightExcept_flip]
  simp only [update_flip]
  cases hx : x i <;> simp [flipAt, hx] <;> ring

private theorem coordinate_activation_identity {ι : Type} [Fintype ι]
    (d : (ι → Bool) → (ι → Bool) → ℝ) (p : ℝ) (i : ι) :
    (∑ x : ι → Bool, weight p x *
      (if x i then d (Function.update x i true) (Function.update x i false) else 0)) =
    p * ∑ x : ι → Bool, weight p x *
      d (Function.update x i true) (Function.update x i false) := by
  let Δ : (ι → Bool) → ℝ := fun y => d (Function.update y i true) (Function.update y i false)
  let L : (ι → Bool) → ℝ := fun y => weight p y * (if y i then Δ y else 0)
  let R : (ι → Bool) → ℝ := fun y => p * weight p y * Δ y
  let E : (ι → Bool) ≃ (ι → Bool) := ⟨flipAt i, flipAt i, flipAt_involutive i, flipAt_involutive i⟩
  have hL : (∑ x, L (flipAt i x)) = ∑ x, L x := E.sum_comp L
  have hR : (∑ x, R (flipAt i x)) = ∑ x, R x := E.sum_comp R
  have hp : (∑ x, (L x + L (flipAt i x))) = ∑ x, (R x + R (flipAt i x)) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact coordinate_pair_identity d p i x
  simp only [Finset.sum_add_distrib] at hp
  rw [hL,hR] at hp
  change (∑ x, L x) = p * ∑ x, weight p x * Δ x
  simp only [Finset.mul_sum] at *
  dsimp only [R] at hp
  simp only [mul_assoc] at hp
  linarith

private theorem fixed_p_deletion_shared_mask_cost {ι V : Type} [Fintype ι] [Fintype V]
    (out : (ι → Bool) → V → Bool) (p : ℝ) (i : ι) :
    (∑ x : ι → Bool, weight p x *
      (hammingDist (out x) (out (Function.update x i false)) : ℝ)) =
    p * ∑ x : ι → Bool, weight p x *
      (hammingDist (out (Function.update x i true)) (out (Function.update x i false)) : ℝ) := by
  have he (x : ι → Bool) :
      (hammingDist (out x) (out (Function.update x i false)) : ℝ) =
      if x i then (hammingDist (out (Function.update x i true))
        (out (Function.update x i false)) : ℝ) else 0 := by
    cases hx : x i with
    | false =>
      have hself : Function.update x i false = x := Function.update_eq_self_iff.mpr hx.symm
      simp [hx, hself]
    | true =>
      have hself : Function.update x i true = x := Function.update_eq_self_iff.mpr hx.symm
      simp [hx, hself]
  simp_rw [he]
  exact coordinate_activation_identity (fun a b => (hammingDist (out a) (out b) : ℝ)) p i


theorem solution {ι V : Type} [Fintype ι] [Fintype V]
    (out : (ι → Bool) → V → Bool) (p : ℝ) (i : ι) :
    (∑ x : ι → Bool, (∏ j : ι, if x j then p else 1-p) *
      (hammingDist (out x) (out (Function.update x i false)) : ℝ)) =
    p * ∑ x : ι → Bool, (∏ j : ι, if x j then p else 1-p) *
      (hammingDist (out (Function.update x i true)) (out (Function.update x i false)) : ℝ) := by
  simpa only [weight] using fixed_p_deletion_shared_mask_cost out p i
