-- Prove2me | solution 1 for UnderstandingML.rademacher_linearEvalSet_le
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T16:21:16.242988+00:00
-- url     : https://prove2.me/submissions/5669e18f-d4ec-4ae9-9056-ab2274880d21

import Definitions.Def_UnderstandingML_Rademacher
import Mathlib.Algebra.Order.Chebyshev

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML.LinearAux

variable {m : ℕ}

lemma signVec_sq (σ : Fin m → Bool) (i : Fin m) : signVec σ i * signVec σ i = 1 := by
  unfold signVec; cases σ i <;> simp

/-- `E_σ[σᵢ σⱼ] = 𝟙[i = j]`, written as a sum over the `2^m` sign vectors. -/
lemma sum_signVec_mul (i j : Fin m) :
    ∑ σ : Fin m → Bool, signVec σ i * signVec σ j = if i = j then (2 : ℝ) ^ m else 0 := by
  classical
  split_ifs with hij
  · subst hij
    simp [signVec_sq, Finset.card_univ, Fintype.card_bool, Fintype.card_fin]
  · let flip : (Fin m → Bool) → (Fin m → Bool) := fun σ ↦ Function.update σ i (!σ i)
    have hinv : Function.Involutive flip := by
      intro σ; funext k
      by_cases hk : k = i
      · subst hk; simp [flip]
      · simp [flip, Function.update_of_ne hk]
    have h1 : ∀ σ, signVec (flip σ) i * signVec (flip σ) j = -(signVec σ i * signVec σ j) := by
      intro σ
      have hj : j ≠ i := fun h ↦ hij h.symm
      simp only [signVec, flip, Function.update_self, Function.update_of_ne hj]
      cases σ i <;> cases σ j <;> simp
    have h2 : ∑ σ : Fin m → Bool, signVec σ i * signVec σ j =
        ∑ σ : Fin m → Bool, signVec (flip σ) i * signVec (flip σ) j :=
      (Fintype.sum_equiv (hinv.toPerm _) _ _ (fun _ ↦ rfl)).symm
    simp only [h1, Finset.sum_neg_distrib] at h2
    linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `∑_σ ‖∑ᵢ σᵢ xᵢ‖² = 2^m ∑ᵢ ‖xᵢ‖²`. -/
lemma sum_norm_sq (x : Fin m → E) :
    ∑ σ : Fin m → Bool, ‖∑ i, signVec σ i • x i‖ ^ 2 = 2 ^ m * ∑ i, ‖x i‖ ^ 2 := by
  classical
  have : ∀ σ : Fin m → Bool, ‖∑ i, signVec σ i • x i‖ ^ 2 =
      ∑ i, ∑ j, signVec σ i * signVec σ j * ⟪x i, x j⟫_ℝ := by
    intro σ
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [inner_sum]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  rw [Finset.sum_congr rfl (fun σ _ ↦ this σ), Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_signVec_mul]
  simp

end UnderstandingML.LinearAux

open UnderstandingML UnderstandingML.LinearAux in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (B : ℝ) (hB : 0 ≤ B) (x : Fin m → E) :
    rademacher (linearEvalSet B x) ≤ B * (⨆ i, ‖x i‖) / Real.sqrt m := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [rademacher]
  set M := ⨆ i, ‖x i‖ with hM
  have hMi : ∀ i, ‖x i‖ ≤ M := fun i ↦
    le_ciSup (f := fun i ↦ ‖x i‖) (Set.finite_range _).bddAbove i
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMi ⟨0, hm⟩)
  have hne : Nonempty (linearEvalSet B x) := ⟨⟨fun i ↦ ⟪(0 : E), x i⟫_ℝ, 0, by simpa using hB, rfl⟩⟩
  set v : (Fin m → Bool) → E := fun σ ↦ ∑ i, signVec σ i • x i with hv
  -- the supremum for a fixed sign vector
  have hsup : ∀ σ : Fin m → Bool,
      (⨆ a : linearEvalSet B x, ∑ i, signVec σ i * (a : Fin m → ℝ) i) ≤ B * ‖v σ‖ := by
    intro σ
    refine ciSup_le (fun a ↦ ?_)
    obtain ⟨_, w, hw, rfl⟩ := a
    have : ∑ i, signVec σ i * ⟪w, x i⟫_ℝ = ⟪w, v σ⟫_ℝ := by
      rw [hv, inner_sum]
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      rw [real_inner_smul_right]
    simp only
    rw [this]
    calc ⟪w, v σ⟫_ℝ ≤ ‖w‖ * ‖v σ‖ := real_inner_le_norm _ _
      _ ≤ B * ‖v σ‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
  -- Cauchy–Schwarz over the sign vectors
  have hcard : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m := by
    simp [Finset.card_univ, Fintype.card_bool, Fintype.card_fin]
  have hCS : (∑ σ : Fin m → Bool, ‖v σ‖) ^ 2 ≤ 2 ^ m * ∑ σ : Fin m → Bool, ‖v σ‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m → Bool)))
      (f := fun σ ↦ ‖v σ‖)
    simpa [hcard] using this
  rw [sum_norm_sq] at hCS
  have hsumx : ∑ i, ‖x i‖ ^ 2 ≤ m * M ^ 2 := by
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin m, M ^ 2 :=
          Finset.sum_le_sum (fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hMi i) 2)
      _ = m * M ^ 2 := by simp
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hsq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm'.le
  have hsqpos : 0 < Real.sqrt m := Real.sqrt_pos.2 hm'
  have hnorm : ∑ σ : Fin m → Bool, ‖v σ‖ ≤ 2 ^ m * (M * Real.sqrt m) := by
    have h2 : (∑ σ : Fin m → Bool, ‖v σ‖) ^ 2 ≤ (2 ^ m * (M * Real.sqrt m)) ^ 2 := by
      calc _ ≤ 2 ^ m * (2 ^ m * ∑ i, ‖x i‖ ^ 2) := hCS
        _ ≤ 2 ^ m * (2 ^ m * (m * M ^ 2)) := by gcongr
        _ = (2 ^ m * (M * Real.sqrt m)) ^ 2 := by
          rw [mul_pow, mul_pow, sq (Real.sqrt _), hsq]; ring
    exact (abs_le_of_sq_le_sq' h2 (by positivity)).2
  unfold rademacher
  calc 1 / (m : ℝ) * (1 / 2 ^ m * ∑ σ : Fin m → Bool,
        ⨆ a : linearEvalSet B x, ∑ i, signVec σ i * (a : Fin m → ℝ) i)
      ≤ 1 / (m : ℝ) * (1 / 2 ^ m * ∑ σ : Fin m → Bool, B * ‖v σ‖) := by
        gcongr with σ; exact hsup σ
    _ = 1 / (m : ℝ) * (1 / 2 ^ m * (B * ∑ σ : Fin m → Bool, ‖v σ‖)) := by
        rw [← Finset.mul_sum]
    _ ≤ 1 / (m : ℝ) * (1 / 2 ^ m * (B * (2 ^ m * (M * Real.sqrt m)))) := by gcongr
    _ = B * M / Real.sqrt m := by
        rw [eq_div_iff hsqpos.ne']
        field_simp
        linear_combination (B * M) * hsq
