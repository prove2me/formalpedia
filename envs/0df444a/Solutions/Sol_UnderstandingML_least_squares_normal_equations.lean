-- Prove2me | solution 1 for UnderstandingML.least_squares_normal_equations
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T14:54:00.95175+00:00
-- url     : https://prove2.me/submissions/db8acc1b-ce93-48f2-874e-39db89fd9e2f

import Definitions.Def_UnderstandingML_Linear

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML.LeastSquaresProof

variable {d m : ℕ}

lemma gram_apply (x : Fin m → Vec d) (w : Vec d) :
    gram x w = ∑ i, ⟪x i, w⟫_ℝ • x i := by
  simp [gram, LinearMap.sum_apply]

lemma inner_gram (x : Fin m → Vec d) (v w : Vec d) :
    ⟪v, gram x w⟫_ℝ = ∑ i, ⟪x i, v⟫_ℝ * ⟪x i, w⟫_ℝ := by
  rw [gram_apply, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, real_inner_comm (x i) v]
  ring

lemma gram_isSymmetric (x : Fin m → Vec d) : (gram x).IsSymmetric := by
  intro u v
  rw [real_inner_comm, inner_gram, inner_gram]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma inner_lsTarget (x : Fin m → Vec d) (y : Fin m → ℝ) (v : Vec d) :
    ⟪v, lsTarget x y⟫_ℝ = ∑ i, y i * ⟪x i, v⟫_ℝ := by
  rw [lsTarget, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, real_inner_comm]

/-- The objective `f(w) = ∑ᵢ (⟨w, xᵢ⟩ − yᵢ)²`. -/
noncomputable def obj (x : Fin m → Vec d) (y : Fin m → ℝ) (w : Vec d) : ℝ :=
  ∑ i, (⟪w, x i⟫_ℝ - y i) ^ 2

lemma obj_add (x : Fin m → Vec d) (y : Fin m → ℝ) (w v : Vec d) :
    obj x y (w + v) = obj x y w + 2 * ⟪v, gram x w - lsTarget x y⟫_ℝ +
      ∑ i, ⟪x i, v⟫_ℝ ^ 2 := by
  rw [inner_sub_right, inner_gram, inner_lsTarget, obj, obj]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_add_left, real_inner_comm (x i) v, real_inner_comm (x i) w]
  ring

lemma empRisk_eq (x : Fin m → Vec d) (y : Fin m → ℝ) (w : Vec d) :
    empRisk squaredLoss (fun i ↦ (x i, y i)) (affine w 0) = obj x y w / m := by
  simp [empRisk, squaredLoss, affine, obj]

lemma exists_solution (x : Fin m → Vec d) (y : Fin m → ℝ) :
    ∃ w : Vec d, gram x w = lsTarget x y := by
  have hker : lsTarget x y ∈ (LinearMap.ker (gram x))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    have h0 : ⟪v, gram x v⟫_ℝ = 0 := by rw [hv, inner_zero_right]
    rw [inner_gram] at h0
    have hz : ∀ i, ⟪x i, v⟫_ℝ = 0 := by
      intro i
      have hsq : ∑ j, ⟪x j, v⟫_ℝ ^ 2 = 0 := by
        rw [← h0]; exact Finset.sum_congr rfl fun j _ => sq _
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (⟪x j, v⟫_ℝ))).1 hsq i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    rw [inner_lsTarget]
    simp [hz]
  rw [← (gram_isSymmetric x).orthogonal_range, Submodule.orthogonal_orthogonal] at hker
  exact hker

lemma solution_iff_min (x : Fin m → Vec d) (y : Fin m → ℝ) (w : Vec d) :
    gram x w = lsTarget x y ↔ ∀ w' : Vec d, obj x y w ≤ obj x y w' := by
  constructor
  · intro h w'
    have := obj_add x y w (w' - w)
    rw [add_sub_cancel, h, sub_self, inner_zero_right] at this
    rw [this]
    have : 0 ≤ ∑ i, ⟪x i, w' - w⟫_ℝ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  · intro h
    set g := gram x w - lsTarget x y with hg
    set Q := ∑ i, ⟪x i, g⟫_ℝ ^ 2 with hQ
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
    have key : ∀ s : ℝ, 0 < s → 2 * ‖g‖ ^ 2 ≤ s * Q := by
      intro s hs
      have h1 := h (w + (-s) • g)
      rw [obj_add, inner_smul_left] at h1
      simp only [RCLike.conj_to_real, inner_smul_right] at h1
      rw [← hg, real_inner_self_eq_norm_sq] at h1
      have h2 : ∑ i, (-s * ⟪x i, g⟫_ℝ) ^ 2 = s ^ 2 * Q := by
        rw [hQ, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [h2] at h1
      nlinarith
    have hg0 : ‖g‖ ^ 2 = 0 := by
      by_contra hne
      have hpos : 0 < ‖g‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
      have := key (‖g‖ ^ 2 / (Q + 1)) (by positivity)
      have h3 : ‖g‖ ^ 2 / (Q + 1) * Q < ‖g‖ ^ 2 := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith
      linarith
    have : g = 0 := by simpa using hg0
    exact sub_eq_zero.1 this

end UnderstandingML.LeastSquaresProof

open UnderstandingML UnderstandingML.LeastSquaresProof in
theorem solution {d m : ℕ} (x : Fin m → Vec d) (y : Fin m → ℝ) :
    (∃ w : Vec d, gram x w = lsTarget x y) ∧
    ∀ w : Vec d, gram x w = lsTarget x y ↔
      IsERM squaredLoss (homLinear d) (fun i ↦ (x i, y i)) (affine w 0) := by
  refine ⟨exists_solution x y, fun w => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · constructor
    · intro _
      refine ⟨⟨w, rfl⟩, fun h' _ => ?_⟩
      simp [empRisk]
    · intro _
      simp [gram, lsTarget]
  rw [solution_iff_min]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · intro h
    refine ⟨⟨w, rfl⟩, ?_⟩
    rintro _ ⟨w', rfl⟩
    rw [empRisk_eq, empRisk_eq]
    exact div_le_div_of_nonneg_right (h w') hm'.le
  · rintro ⟨-, h⟩ w'
    have := h (affine w' 0) ⟨w', rfl⟩
    rw [empRisk_eq, empRisk_eq] at this
    exact (div_le_div_iff_of_pos_right hm').1 this
