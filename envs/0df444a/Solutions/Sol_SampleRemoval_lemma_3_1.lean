-- Prove2me | solution 1 for SampleRemoval.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:34:45.517216+00:00
-- url     : https://prove2.me/submissions/a8a1d6fc-ae6b-48d2-b234-215507fce5c2

import Mathlib
import Definitions.Def_SampleRemoval_gram
import Definitions.Def_SampleRemoval_ols
import Theorems.Thm_SampleRemoval_normal_equations

section
set_option autoImplicit false

open Matrix

namespace SampleRemoval
namespace Dev
namespace Lemma31

theorem sum_update {n : ℕ} {N : Type*} [AddCommMonoid N] [Module ℝ N] (w : Fin n → ℝ)
    (t : Fin n) (a : ℝ) (F : Fin n → N) :
    ∑ i, Function.update w t a i • F i = a • F t + ∑ i ∈ Finset.univ.erase t, w i • F i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem moment_update {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (w : Fin n → ℝ)
    (t : Fin n) (a : ℝ) :
    moment x y (Function.update w t a) =
      (a * y t) • x t + ∑ i ∈ Finset.univ.erase t, (w i * y i) • x i := by
  unfold moment
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem vv_mulVec {d : ℕ} (a v : Fin d → ℝ) :
    vecMulVec a a *ᵥ v = (a ⬝ᵥ v) • a := by
  ext j
  simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem residual_sum {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (w : Fin n → ℝ)
    (b : Fin d → ℝ) :
    ∑ i, (w i * (y i - x i ⬝ᵥ b)) • x i = moment x y w - gram x w *ᵥ b := by
  ext j
  simp only [moment, gram, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
    Matrix.mulVec, dotProduct, Matrix.sum_apply]
  simp only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm (f := fun k c => w c * (x c j * x c k) * b k), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem main {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) (t : Fin n)
    (hG₀ : (∑ i ∈ Finset.univ.erase t, w i • Matrix.vecMulVec (x i) (x i)).PosDef) :
    let G₀ : Matrix (Fin d) (Fin d) ℝ := ∑ i ∈ Finset.univ.erase t, w i • Matrix.vecMulVec (x i) (x i)
    let β₀ : Fin d → ℝ := ols x y (Function.update w t 0)
    let η : ℝ := x t ⬝ᵥ (G₀⁻¹ *ᵥ x t)
    0 ≤ η ∧
      (∀ a ∈ Set.Icc (0 : ℝ) 1, ols x y (Function.update w t a) =
        β₀ + (a / (1 + a * η) * (y t - x t ⬝ᵥ β₀)) • (G₀⁻¹ *ᵥ x t)) ∧
      ∀ e : Fin d → ℝ,
        MonotoneOn (fun a : ℝ => e ⬝ᵥ ols x y (Function.update w t a)) (Set.Icc 0 1) ∨
          AntitoneOn (fun a : ℝ => e ⬝ᵥ ols x y (Function.update w t a)) (Set.Icc 0 1) := by
  intro G₀ β₀ η
  set g₀ : Fin d → ℝ := ∑ i ∈ Finset.univ.erase t, (w i * y i) • x i with hg₀
  have hdet : IsUnit G₀.det := (Matrix.isUnit_iff_isUnit_det _).mp hG₀.isUnit
  have hgram : ∀ a, gram x (Function.update w t a) = a • vecMulVec (x t) (x t) + G₀ := by
    intro a
    unfold gram
    exact sum_update w t a (fun i => vecMulVec (x i) (x i))
  have hmom : ∀ a, moment x y (Function.update w t a) = (a * y t) • x t + g₀ :=
    fun a => moment_update x y w t a
  have hβ₀ : β₀ = G₀⁻¹ *ᵥ g₀ := by
    simp only [β₀, ols, hgram, hmom, zero_smul, zero_add, zero_mul]
  have hG₀β₀ : G₀ *ᵥ β₀ = g₀ := by
    rw [hβ₀, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hGu : G₀ *ᵥ (G₀⁻¹ *ᵥ x t) = x t := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hη : 0 ≤ η := by
    have := hG₀.inv.posSemidef.dotProduct_mulVec_nonneg (x t)
    simp only [star_trivial] at this
    exact this
  -- positive definiteness of G(a)
  have hPD : ∀ a ∈ Set.Icc (0 : ℝ) 1, (gram x (Function.update w t a)).PosDef := by
    intro a ha
    rw [hgram]
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · have h1 : (a • vecMulVec (x t) (x t)).IsHermitian := by
        ext i j
        simp [Matrix.conjTranspose_apply, vecMulVec_apply, mul_comm]
      exact h1.add hG₀.isHermitian
    · intro v hv
      have := hG₀.dotProduct_mulVec_pos hv
      rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, vv_mulVec, dotProduct_smul,
        dotProduct_smul]
      simp only [star_trivial, smul_eq_mul] at this ⊢
      have h2 : 0 ≤ a * ((x t ⬝ᵥ v) * (v ⬝ᵥ x t)) := by
        rw [dotProduct_comm v (x t)]
        exact mul_nonneg ha.1 (mul_self_nonneg _)
      linarith
  have hpos : ∀ a ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + a * η := fun a ha => by
    have := mul_nonneg ha.1 hη
    linarith
  have hformula : ∀ a ∈ Set.Icc (0 : ℝ) 1, ols x y (Function.update w t a) =
      β₀ + (a / (1 + a * η) * (y t - x t ⬝ᵥ β₀)) • (G₀⁻¹ *ᵥ x t) := by
    intro a ha
    have hne : (1 + a * η) ≠ 0 := (hpos a ha).ne'
    have hw' : ∀ i, Function.update w t a i ∈ Set.Icc (0 : ℝ) 1 := by
      intro i
      by_cases hi : i = t
      · subst hi; simpa using ha
      · rw [Function.update_of_ne hi]; exact hw i
    symm
    have key := (normal_equations x y (Function.update w t a) hw' (hPD a ha)
      (β₀ + (a / (1 + a * η) * (y t - x t ⬝ᵥ β₀)) • (G₀⁻¹ *ᵥ x t))).mp
    apply key
    rw [residual_sum, hgram, hmom, sub_eq_zero]
    set u := G₀⁻¹ *ᵥ x t with hu
    set r := y t - x t ⬝ᵥ β₀ with hr
    set c := a / (1 + a * η) with hc
    have hcc : c * (1 + a * η) = a := by rw [hc]; field_simp
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, vv_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
      hG₀β₀, hGu, dotProduct_add, dotProduct_smul, smul_eq_mul]
    have hxu : x t ⬝ᵥ u = η := rfl
    rw [hxu]
    have hrr : y t = r + x t ⬝ᵥ β₀ := by simp [hr]
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (x t j * a) * hrr - (x t j * r) * hcc
  refine ⟨hη, hformula, fun e => ?_⟩
  have hval : ∀ a ∈ Set.Icc (0 : ℝ) 1, e ⬝ᵥ ols x y (Function.update w t a) =
      e ⬝ᵥ β₀ + (a / (1 + a * η)) * ((y t - x t ⬝ᵥ β₀) * (e ⬝ᵥ (G₀⁻¹ *ᵥ x t))) := by
    intro a ha
    rw [hformula a ha, dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  have hc : MonotoneOn (fun a : ℝ => a / (1 + a * η)) (Set.Icc 0 1) := by
    intro a ha b hb hab
    simp only
    rw [div_le_div_iff₀ (hpos a ha) (hpos b hb)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) hη]
  rcases le_total 0 ((y t - x t ⬝ᵥ β₀) * (e ⬝ᵥ (G₀⁻¹ *ᵥ x t))) with hK | hK
  · left
    intro a ha b hb hab
    simp only
    rw [hval a ha, hval b hb]
    have := mul_le_mul_of_nonneg_right (hc ha hb hab) hK
    linarith
  · right
    intro a ha b hb hab
    simp only
    rw [hval a ha, hval b hb]
    have := mul_le_mul_of_nonpos_right (hc ha hb hab) hK
    linarith

end Lemma31
end Dev

theorem chk_lemma_3_1 {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) (t : Fin n)
    (hG₀ : (∑ i ∈ Finset.univ.erase t, w i • Matrix.vecMulVec (x i) (x i)).PosDef) :
    let G₀ : Matrix (Fin d) (Fin d) ℝ := ∑ i ∈ Finset.univ.erase t, w i • Matrix.vecMulVec (x i) (x i)
    let β₀ : Fin d → ℝ := ols x y (Function.update w t 0)
    let η : ℝ := x t ⬝ᵥ (G₀⁻¹ *ᵥ x t)
    0 ≤ η ∧
      (∀ a ∈ Set.Icc (0 : ℝ) 1, ols x y (Function.update w t a) =
        β₀ + (a / (1 + a * η) * (y t - x t ⬝ᵥ β₀)) • (G₀⁻¹ *ᵥ x t)) ∧
      ∀ e : Fin d → ℝ,
        MonotoneOn (fun a : ℝ => e ⬝ᵥ ols x y (Function.update w t a)) (Set.Icc 0 1) ∨
          AntitoneOn (fun a : ℝ => e ⬝ᵥ ols x y (Function.update w t a)) (Set.Icc 0 1) :=
  Dev.Lemma31.main x y w hw t hG₀

end SampleRemoval

end

theorem solution : type_of% @SampleRemoval.chk_lemma_3_1 := @SampleRemoval.chk_lemma_3_1
