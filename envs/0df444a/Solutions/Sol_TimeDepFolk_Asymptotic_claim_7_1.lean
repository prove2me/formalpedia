-- Prove2me | solution 1 for TimeDepFolk.Asymptotic.claim_7_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:18:48.151126+00:00
-- url     : https://prove2.me/submissions/14a3f502-1bd6-4e83-9f67-9eebd02bb360

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TDF71

open TimeDepFolk.Asymptotic Finset Matrix

theorem rowSumNorm_nonneg {m n : Type*} [Fintype n] (M : Matrix m n ℝ) : 0 ≤ rowSumNorm M :=
  Real.iSup_nonneg (f := fun r => ∑ c, |M r c|) fun _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- `|(M v)_r| ≤ ‖M‖_∞ B` when every `|v_c| ≤ B`. -/
theorem abs_mulVec_le {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) (v : n → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hv : ∀ c, |v c| ≤ B) (r : m) : |(M *ᵥ v) r| ≤ rowSumNorm M * B := by
  have h1 : |(M *ᵥ v) r| ≤ (∑ c, |M r c|) * B := by
    simp only [Matrix.mulVec, dotProduct]
    calc |∑ c, M r c * v c| ≤ ∑ c, |M r c * v c| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, |M r c| * B := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hv c) (abs_nonneg _)
      _ = (∑ c, |M r c|) * B := by rw [Finset.sum_mul]
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ hB)
  exact le_ciSup (f := fun r => ∑ c, |M r c|) (Set.finite_range _).bddAbove r

end TDF71

open TimeDepFolk.Asymptotic Finset Matrix

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (hL : L ≤ Fintype.card ι + 1) (x : Fin L → ι → ℝ) (hx : AffineIndependent ℝ x)
    (lam : Fin L → ℝ) (hlam0 : ∀ ℓ, 0 ≤ lam ℓ) (hlam1 : ∑ ℓ, lam ℓ = 1)
    (x0 : ι → ℝ) (hx0 : ∑ ℓ, lam ℓ • x ℓ = x0)
    (η : ℝ) (hη : 0 < η) (hball : Metric.closedBall x0 η ⊆ convexHull ℝ (Set.range x))
    (φ : Fin L) (x' : ι → ℝ) (hx' : x' ∈ Metric.closedBall (x φ) (η / 5))
    (lam' : Fin L → ℝ) (hlam'0 : ∀ ℓ, 0 ≤ lam' ℓ) (hlam'1 : ∑ ℓ, lam' ℓ = 1)
    (hx0' : lam' φ • x' + ∑ ℓ ∈ Finset.univ.erase φ, lam' ℓ • x ℓ = x0) :
    ∀ ℓ, |lam' ℓ - lam ℓ| ≤ η / 5 * L * Rcoef x φ := by
  classical
  set S := {s : Fin L // s ≠ φ}
  -- Step 1: `L = |ι| + 1`
  have htop : affineSpan ℝ (Set.range x) = ⊤ := by
    rw [← interior_convexHull_nonempty_iff_affineSpan_eq_top]
    refine ⟨x0, ?_⟩
    have : Metric.ball x0 η ⊆ interior (convexHull ℝ (Set.range x)) :=
      interior_maximal (Metric.ball_subset_closedBall.trans hball) Metric.isOpen_ball
    exact this (Metric.mem_ball_self hη)
  have hcardS : Fintype.card S = Fintype.card ι := by
    have hL1 : Fintype.card (Fin L) = (L - 1) + 1 := by
      simp only [Fintype.card_fin]; have := φ.pos; omega
    have h1 := hx.finrank_vectorSpan hL1
    rw [← direction_affineSpan, htop, AffineSubspace.direction_top, finrank_top,
      Module.finrank_fintype_fun_eq_card] at h1
    simp only [S, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
    omega
  -- Step 2: the edge matrix and the linear system `X d = v`
  set X := edgeMatrix x φ with hXdef
  set d : S → ℝ := fun s => lam' s.1 - lam s.1 with hd
  set v : ι → ℝ := lam' φ • (x φ - x') with hv
  have hsys : X *ᵥ d = v := by
    have hsum0 : ∑ ℓ, (lam' ℓ - lam ℓ) = 0 := by
      rw [Finset.sum_sub_distrib, hlam1, hlam'1, sub_self]
    have hcomb : ∑ ℓ, (lam' ℓ - lam ℓ) • x ℓ = v := by
      have e1 : ∑ ℓ, lam' ℓ • x ℓ = lam' φ • x φ + ∑ ℓ ∈ Finset.univ.erase φ, lam' ℓ • x ℓ :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ φ)).symm
      simp only [sub_smul, Finset.sum_sub_distrib, e1, hx0, hv, smul_sub]
      rw [← hx0']; abel
    have hcomb' : ∑ ℓ, (lam' ℓ - lam ℓ) • (x ℓ - x φ) = v := by
      simp only [smul_sub, Finset.sum_sub_distrib, hcomb, ← Finset.sum_smul, hsum0, zero_smul,
        sub_zero]
    rw [← hcomb']
    funext i
    simp only [Matrix.mulVec, dotProduct, X, edgeMatrix, Matrix.of_apply, d]
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ φ), sub_self, mul_zero, add_zero]
    rw [Finset.sum_subtype (Finset.univ.erase φ) (p := fun s => s ≠ φ) (by simp)]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  -- Step 3: `X` is injective (edge vectors are linearly independent)
  have hli := (affineIndependent_iff_linearIndependent_vsub ℝ x φ).1 hx
  have hXv : ∀ z : S → ℝ, X *ᵥ z = ∑ s, z s • (x s.1 - x φ) := by
    intro z; funext i
    simp only [Matrix.mulVec, dotProduct, X, edgeMatrix, Matrix.of_apply, Finset.sum_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have hinj : Function.Injective (X *ᵥ ·) := by
    intro z1 z2 h
    simp only at h
    have h0 : ∑ s, (z1 s - z2 s) • (x s.1 -ᵥ x φ) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, vsub_eq_sub]
      rw [← hXv, ← hXv, h, sub_self]
    funext s
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 s)
  -- Step 4: `X Xᵀ` is invertible and `d = Xᵀ (X Xᵀ)⁻¹ v`
  let e : S ≃ ι := Fintype.equivOfCardEq hcardS
  let Y : Matrix ι ι ℝ := Matrix.of fun i k => X i (e.symm k)
  have hY : IsUnit Y := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro z1 z2 h
    have hz : ∀ z : ι → ℝ, Y *ᵥ z = X *ᵥ (fun s => z (e s)) := by
      intro z; funext i
      simp only [Matrix.mulVec, dotProduct, Y, Matrix.of_apply]
      exact (e.symm.sum_comp (fun s => X i s * z (e s))).symm.trans
        (by simp [Equiv.apply_symm_apply]) |>.symm
    have := hinj (by simpa only [hz] using h : X *ᵥ (fun s => z1 (e s)) = X *ᵥ (fun s => z2 (e s)))
    funext k
    have := congrFun this (e.symm k)
    simpa using this
  have hXX : X * Xᵀ = Y * Yᵀ := by
    funext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Y, Matrix.of_apply]
    exact (e.symm.sum_comp (fun s => X i s * X j s)).symm
  have hunit : IsUnit (X * Xᵀ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det, hXX]
    exact hY.mul ((Matrix.isUnit_transpose Y).2 hY)
  have hdu : d = Xᵀ *ᵥ ((X * Xᵀ)⁻¹ *ᵥ v) := by
    apply hinj
    simp only
    rw [hsys, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  -- Step 5: the norm bounds
  have hη5 : 0 ≤ η / 5 := by positivity
  have hvb : ∀ i, |v i| ≤ η / 5 := by
    intro i
    have h1 : |x φ i - x' i| ≤ η / 5 := by
      have hd' : ‖x' - x φ‖ ≤ η / 5 := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.1 hx'
      have := norm_le_pi_norm (x' - x φ) i
      rw [Real.norm_eq_abs, Pi.sub_apply] at this
      rw [abs_sub_comm]; linarith
    have hl1 : lam' φ ≤ 1 := by
      rw [← hlam'1]
      exact Finset.single_le_sum (fun ℓ _ => hlam'0 ℓ) (Finset.mem_univ φ)
    simp only [v, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_of_nonneg (hlam'0 φ)]
    calc lam' φ * |x φ i - x' i| ≤ 1 * (η / 5) :=
          mul_le_mul hl1 h1 (abs_nonneg _) zero_le_one
      _ = η / 5 := one_mul _
  set N2 := rowSumNorm (X * Xᵀ)⁻¹
  have hN2 : 0 ≤ N2 := TDF71.rowSumNorm_nonneg _
  have hwb := TDF71.abs_mulVec_le (X * Xᵀ)⁻¹ v (η / 5) hη5 hvb
  have hdb : ∀ s, |d s| ≤ Rcoef x φ * (η / 5) := by
    intro s
    rw [hdu]
    have := TDF71.abs_mulVec_le Xᵀ _ (N2 * (η / 5)) (by positivity) hwb s
    rw [Rcoef, mul_assoc]
    exact this
  have hR : 0 ≤ Rcoef x φ :=
    mul_nonneg (TDF71.rowSumNorm_nonneg _) (TDF71.rowSumNorm_nonneg _)
  have hL1 : (1 : ℝ) ≤ L := by have := φ.pos; exact_mod_cast this
  intro ℓ
  by_cases hℓ : ℓ = φ
  · subst hℓ
    have hsum0 : ∑ ℓ, (lam' ℓ - lam ℓ) = 0 := by
      rw [Finset.sum_sub_distrib, hlam1, hlam'1, sub_self]
    have hsplit : lam' ℓ - lam ℓ = -∑ s : S, d s := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ)] at hsum0
      rw [Finset.sum_subtype (Finset.univ.erase ℓ) (p := fun s => s ≠ ℓ) (by simp)] at hsum0
      simp only [d]; linarith
    rw [hsplit, abs_neg]
    have hcard : (Fintype.card S : ℝ) ≤ L := by
      have := Fintype.card_subtype_le (fun s : Fin L => s ≠ ℓ)
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    calc |∑ s : S, d s| ≤ ∑ s : S, |d s| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s : S, Rcoef x ℓ * (η / 5) := Finset.sum_le_sum fun s _ => hdb s
      _ = (Fintype.card S : ℝ) * (Rcoef x ℓ * (η / 5)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ ≤ L * (Rcoef x ℓ * (η / 5)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = η / 5 * L * Rcoef x ℓ := by ring
  · have := hdb ⟨ℓ, hℓ⟩
    simp only [d] at this
    calc |lam' ℓ - lam ℓ| ≤ Rcoef x φ * (η / 5) := this
      _ = 1 * (η / 5) * Rcoef x φ := by ring
      _ ≤ L * (η / 5) * Rcoef x φ := by
          apply mul_le_mul_of_nonneg_right _ hR
          exact mul_le_mul_of_nonneg_right hL1 hη5
      _ = η / 5 * L * Rcoef x φ := by ring
