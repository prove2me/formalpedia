-- Prove2me | solution 1 for OptInapprox.LevelOne.level_one_le_l1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:57:07.114232+00:00
-- url     : https://prove2.me/submissions/67197f1c-a06a-4224-8f5a-65e8ccf9cb1f

import Mathlib
import Definitions.Def_OptInapprox_LevelOne_Cube

set_option autoImplicit false

open OptInapprox.LevelOne OptInapprox.MaxCut

lemma pm_not (b : Bool) : pm (!b) = - pm b := by cases b <;> simp [pm]

lemma pm_mul_self (b : Bool) : pm b * pm b = 1 := by cases b <;> simp [pm]

lemma sum_pm_mul {n : ℕ} (i j : Fin n) :
    ∑ x : Fin n → Bool, pm (x i) * pm (x j) = if i = j then (2 : ℝ) ^ n else 0 := by
  by_cases hij : i = j
  · subst hij
    simp [pm_mul_self, Finset.card_univ, Fintype.card_fun]
  · rw [if_neg hij]
    refine Finset.sum_involution (fun x _ => Function.update x i (!x i)) ?_ ?_ ?_ ?_
    · intro x _
      have h1 : Function.update x i (!x i) j = x j := Function.update_of_ne (Ne.symm hij) _ _
      simp only [Function.update_self, h1, pm_not]
      ring
    · intro x _ _ h
      have := congrFun h i
      simp at this
    · intro x _; exact Finset.mem_univ _
    · intro x _
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Function.update_of_ne hk]

lemma cubeE_add {n : ℕ} (g h : (Fin n → Bool) → ℝ) :
    cubeE (fun x => g x + h x) = cubeE g + cubeE h := by
  unfold cubeE; rw [Finset.sum_add_distrib]; ring

lemma cubeE_const_mul {n : ℕ} (c : ℝ) (g : (Fin n → Bool) → ℝ) :
    cubeE (fun x => c * g x) = c * cubeE g := by
  unfold cubeE; rw [← Finset.mul_sum]; ring

lemma cubeE_sum {n : ℕ} {ι : Type*} (s : Finset ι) (g : ι → (Fin n → Bool) → ℝ) :
    cubeE (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, cubeE (g i) := by
  unfold cubeE; rw [Finset.sum_comm, Finset.mul_sum]

lemma cubeE_nonneg {n : ℕ} (g : (Fin n → Bool) → ℝ) (h : ∀ x, 0 ≤ g x) : 0 ≤ cubeE g := by
  unfold cubeE
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun x _ => h x))

lemma cubeE_mono {n : ℕ} (g h : (Fin n → Bool) → ℝ) (hgh : ∀ x, g x ≤ h x) : cubeE g ≤ cubeE h := by
  unfold cubeE
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => hgh x)) (by positivity)

lemma cubeE_pm_mul {n : ℕ} (i j : Fin n) :
    cubeE (fun x => pm (x i) * pm (x j)) = if i = j then 1 else 0 := by
  unfold cubeE
  rw [sum_pm_mul]
  split_ifs
  · exact inv_mul_cancel₀ (by positivity)
  · simp

lemma cubeE_sq_lin {n : ℕ} (a : Fin n → ℝ) :
    cubeE (fun x => (∑ i, a i * pm (x i)) ^ 2) = ∑ i, a i ^ 2 := by
  have h1 : ∀ x : Fin n → Bool, (∑ i, a i * pm (x i)) ^ 2 =
      ∑ i, ∑ j, (a i * a j) * (pm (x i) * pm (x j)) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  simp_rw [h1]
  rw [cubeE_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [cubeE_sum]
  simp_rw [cubeE_const_mul, cubeE_pm_mul]
  simp [sq]

lemma cubeE_mul_lin {n : ℕ} (f : (Fin n → Bool) → ℝ) (a : Fin n → ℝ) :
    cubeE (fun x => f x * ∑ i, a i * pm (x i)) = ∑ i, a i * cubeE (fun x => f x * pm (x i)) := by
  have h1 : ∀ x : Fin n → Bool, f x * ∑ i, a i * pm (x i) = ∑ i, a i * (f x * pm (x i)) := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  simp_rw [h1]
  rw [cubeE_sum]
  simp_rw [cubeE_const_mul]

theorem solution {n : ℕ} (f : (Fin n → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    levelOneWeight f = l2Norm (linPart f) ^ 2 ∧
    l2Norm (linPart f) ^ 2 = OptInapprox.MaxCut.cubeE (fun x => f x * linPart f x) ∧
    OptInapprox.MaxCut.cubeE (fun x => f x * linPart f x) ≤ supNorm f * l1Norm (linPart f) ∧
    supNorm f * l1Norm (linPart f) ≤ l1Norm (linPart f) := by
  have hchi : ∀ i : Fin n, ∀ x : Fin n → Bool, chi {i} x = pm (x i) := by
    intro i x; simp [chi]
  have hfou : ∀ i : Fin n, OptInapprox.MaxCut.fourier f {i} = cubeE (fun x => f x * pm (x i)) := by
    intro i; unfold OptInapprox.MaxCut.fourier; simp_rw [hchi]
  have hlin : ∀ x, linPart f x = ∑ i, OptInapprox.MaxCut.fourier f {i} * pm (x i) := fun x => rfl
  have hE2 : cubeE (fun x => linPart f x ^ 2) = ∑ i, OptInapprox.MaxCut.fourier f {i} ^ 2 := by
    simp_rw [hlin]; exact cubeE_sq_lin _
  have hEf : cubeE (fun x => f x * linPart f x) = ∑ i, OptInapprox.MaxCut.fourier f {i} ^ 2 := by
    simp_rw [hlin]
    rw [cubeE_mul_lin]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hfou]; ring
  have hsq : l2Norm (linPart f) ^ 2 = ∑ i, OptInapprox.MaxCut.fourier f {i} ^ 2 := by
    unfold l2Norm
    rw [Real.sq_sqrt, hE2]
    exact cubeE_nonneg _ (fun x => sq_nonneg _)
  have hl1 : 0 ≤ l1Norm (linPart f) := cubeE_nonneg _ (fun x => abs_nonneg _)
  have hsup : supNorm f ≤ 1 := by
    unfold supNorm
    exact ciSup_le hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsq]; rfl
  · rw [hsq, hEf]
  · have : ∀ x, f x * linPart f x ≤ supNorm f * |linPart f x| := by
      intro x
      have h1 : |f x| ≤ supNorm f := le_ciSup (Finite.bddAbove_range (fun x => |f x|)) x
      calc f x * linPart f x ≤ |f x * linPart f x| := le_abs_self _
        _ = |f x| * |linPart f x| := abs_mul _ _
        _ ≤ supNorm f * |linPart f x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    calc cubeE (fun x => f x * linPart f x) ≤ cubeE (fun x => supNorm f * |linPart f x|) :=
          cubeE_mono _ _ this
      _ = supNorm f * l1Norm (linPart f) := cubeE_const_mul _ _
  · nlinarith
