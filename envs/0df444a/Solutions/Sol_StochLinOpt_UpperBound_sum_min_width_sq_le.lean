-- Prove2me | solution 1 for StochLinOpt.UpperBound.sum_min_width_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T06:12:27.074489+00:00
-- url     : https://prove2.me/submissions/fecd6d1e-9b91-42ab-a949-37b00a23848b

import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_analysisQuantities

open Matrix
open StochLinOpt.UpperBound

private theorem rk1p {n : ℕ} (z v : Fin n → ℝ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.vecMulVec z v).det = 1 + v ⬝ᵥ z := by
  rw [Matrix.vecMulVec_eq (Fin 1)]
  exact Matrix.det_one_add_replicateCol_mul_replicateRow z v

/-- The matrix determinant lemma, rank-one update form. -/
private theorem det_update {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (w : Fin n → ℝ) :
    (A + Matrix.vecMulVec w w).det = A.det * (1 + w ⬝ᵥ (A⁻¹ *ᵥ w)) := by
  have h1 : ∀ (B : Matrix (Fin n) (Fin n) ℝ) (v z : Fin n → ℝ),
      B * Matrix.vecMulVec v z = Matrix.vecMulVec (B *ᵥ v) z := by
    intro B v z
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h2 : A *ᵥ (A⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]
  have hz : A * Matrix.vecMulVec (A⁻¹ *ᵥ w) w = Matrix.vecMulVec w w := by
    rw [h1, h2]
  have hfac : A + Matrix.vecMulVec w w = A * (1 + Matrix.vecMulVec (A⁻¹ *ᵥ w) w) := by
    rw [Matrix.mul_add, Matrix.mul_one, hz]
  rw [hfac, Matrix.det_mul, rk1p]

/-- The design matrix `A_t = I + ∑_{τ<t} x_τ x_τᵀ` is positive definite. -/
private theorem dm_pd {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) : (designMatrix x t).PosDef := by
  have hpsd : ∀ v : Fin n → ℝ, (Matrix.vecMulVec v v).PosSemidef := fun v => by
    simpa using Matrix.posSemidef_vecMulVec_self_star v
  have hsumpsd : (∑ τ ∈ Finset.Ico 1 t, Matrix.vecMulVec (x τ) (x τ)).PosSemidef :=
    Matrix.posSemidef_sum _ (fun i _ => hpsd _)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [designMatrix]
    exact Matrix.IsHermitian.add (by simp [Matrix.IsHermitian]) hsumpsd.1
  · intro y hy
    have h1 : (0:ℝ) ≤ star y ⬝ᵥ ((∑ τ ∈ Finset.Ico 1 t, Matrix.vecMulVec (x τ) (x τ)) *ᵥ y) :=
      hsumpsd.dotProduct_mulVec_nonneg y
    have h2 : (0:ℝ) < star y ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) := by
      rw [Matrix.one_mulVec]
      simp only [star_trivial]
      rcases Function.ne_iff.mp hy with ⟨i, hi⟩
      exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
        ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
    rw [designMatrix, Matrix.add_mulVec, dotProduct_add]
    linarith

private theorem dm_det_pos {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) : 0 < (designMatrix x t).det :=
  (dm_pd x t).det_pos

private theorem dm_unit {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) : IsUnit (designMatrix x t).det :=
  isUnit_iff_ne_zero.mpr (dm_det_pos x t).ne'

private theorem dm_rec {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    designMatrix x (t + 1) = designMatrix x t + Matrix.vecMulVec (x t) (x t) := by
  rw [designMatrix, designMatrix, Finset.sum_Ico_succ_top ht]
  abel

/-- `w_t² = x_tᵀ A_t⁻¹ x_t` (the argument of the square root is nonnegative). -/
private theorem width_sq {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) :
    width x t ^ 2 = x t ⬝ᵥ ((designMatrix x t)⁻¹ *ᵥ x t) := by
  have hpd : ((designMatrix x t)⁻¹).PosDef := Matrix.posDef_inv_iff.mpr (dm_pd x t)
  have hnn : (0:ℝ) ≤ x t ⬝ᵥ ((designMatrix x t)⁻¹ *ᵥ x t) := by
    simpa using hpd.posSemidef.dotProduct_mulVec_nonneg (x t)
  rw [width, Real.sq_sqrt hnn]

/-- The determinant of `A_{t+1}` telescopes into the widths. -/
private theorem det_dm_succ {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) :
    (designMatrix x (t + 1)).det = ∏ τ ∈ Finset.Icc 1 t, (1 + width x τ ^ 2) := by
  induction t with
  | zero =>
    simp [designMatrix]
  | succ s ih =>
    rw [dm_rec x (s + 1) (by omega), det_update _ (dm_unit x (s + 1)),
      Finset.prod_Icc_succ_top (by omega : 1 ≤ s + 1), ih, width_sq]

/-- `min(a,1) ≤ 2 log(1+a)` for `a ≥ 0`. -/
private theorem min_le_two_log (a : ℝ) (ha : 0 ≤ a) : min a 1 ≤ 2 * Real.log (1 + a) := by
  have h1a : (0:ℝ) < 1 + a := by linarith
  have hL : 0 ≤ Real.log (1 + a) := Real.log_nonneg (by linarith)
  have hlog : a ≤ (1 + a) * Real.log (1 + a) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / (1 + a) by positivity)
    have hinv : Real.log (1 / (1 + a)) = -Real.log (1 + a) := by rw [one_div, Real.log_inv]
    rw [hinv] at h
    have hmul := mul_le_mul_of_nonneg_right h h1a.le
    have hexp : (1 / (1 + a) - 1) * (1 + a) = -a := by field_simp; ring
    rw [hexp] at hmul
    linarith
  rcases le_or_gt a 1 with hle | hgt
  · rw [min_eq_left hle]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a) hL]
  · rw [min_eq_right hgt.le]
    have h2 : Real.log 2 ≤ Real.log (1 + a) := Real.log_le_log (by norm_num) (by linarith)
    have h3 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith

/-- The trace of the design matrix. -/
private theorem trace_dm {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) :
    (designMatrix x t).trace = (n : ℝ) + ∑ τ ∈ Finset.Ico 1 t, ∑ i, x τ i * x τ i := by
  rw [designMatrix, Matrix.trace_add, Matrix.trace_one, Matrix.trace_sum]
  have hv : ∀ τ : ℕ, (Matrix.vecMulVec (x τ) (x τ)).trace = ∑ i, x τ i * x τ i := by
    intro τ
    rw [Matrix.trace]
    exact Finset.sum_congr rfl fun i _ => by simp [Matrix.vecMulVec_apply]
  rw [Finset.sum_congr rfl fun τ (_ : τ ∈ Finset.Ico 1 t) => hv τ]
  simp [Fintype.card_fin]

theorem solution {n : ℕ} (x : ℕ → Fin n → ℝ)
    (hx : ∀ τ : ℕ, 1 ≤ τ → ∀ i, |x τ i| ≤ 1) (t : ℕ) :
    ∑ τ ∈ Finset.Icc 1 t, min (width x τ ^ 2) 1 ≤ 2 * n * Real.log (t + 1) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    have hz : ∀ τ : ℕ, min (width x τ ^ 2) 1 = 0 := by
      intro τ
      have hw : width x τ = 0 := by simp [width, dotProduct]
      rw [hw]
      norm_num
    rw [Finset.sum_congr rfl fun τ (_ : τ ∈ Finset.Icc 1 t) => hz τ]
    simp
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- widths are nonnegative
  have hwnn : ∀ τ : ℕ, 0 ≤ width x τ ^ 2 := fun τ => sq_nonneg _
  -- step 1: the `min` bound
  have hstep1 : ∑ τ ∈ Finset.Icc 1 t, min (width x τ ^ 2) 1
      ≤ ∑ τ ∈ Finset.Icc 1 t, 2 * Real.log (1 + width x τ ^ 2) :=
    Finset.sum_le_sum fun τ _ => min_le_two_log _ (hwnn τ)
  -- step 2: the sum of logs is the log of the determinant
  have hprodpos : ∀ τ : ℕ, (1 : ℝ) + width x τ ^ 2 ≠ 0 := fun τ => by
    have := hwnn τ; intro h; linarith
  have hlogsum : ∑ τ ∈ Finset.Icc 1 t, 2 * Real.log (1 + width x τ ^ 2)
      = 2 * Real.log ((designMatrix x (t + 1)).det) := by
    rw [det_dm_succ, Real.log_prod (fun τ _ => hprodpos τ), Finset.mul_sum]
  -- step 3: AM–GM on the eigenvalues
  have hPD := dm_pd x (t + 1)
  have hherm : (designMatrix x (t + 1)).IsHermitian := hPD.1
  have hev : ∀ i, 0 < hherm.eigenvalues i := fun i => hPD.eigenvalues_pos i
  have htrev : (designMatrix x (t + 1)).trace = ∑ i, hherm.eigenvalues i := by
    simpa using hherm.trace_eq_sum_eigenvalues
  have hdetev : (designMatrix x (t + 1)).det = ∏ i, hherm.eigenvalues i := by
    simpa using hherm.det_eq_prod_eigenvalues
  have htrpos : (0:ℝ) < (designMatrix x (t + 1)).trace := by
    rw [trace_dm]
    have : (0:ℝ) ≤ ∑ τ ∈ Finset.Ico 1 (t + 1), ∑ i, x τ i * x τ i :=
      Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ => mul_self_nonneg _
    linarith
  have hMpos : 0 < (designMatrix x (t + 1)).trace / (n : ℝ) := div_pos htrpos hnR
  have hLT : Real.log ((designMatrix x (t + 1)).det)
      ≤ (n : ℝ) * Real.log ((designMatrix x (t + 1)).trace / (n : ℝ)) := by
    rw [hdetev, Real.log_prod (fun i _ => (hev i).ne')]
    have hb : ∀ i : Fin n, Real.log (hherm.eigenvalues i)
        ≤ (hherm.eigenvalues i / ((designMatrix x (t + 1)).trace / (n : ℝ)) - 1)
          + Real.log ((designMatrix x (t + 1)).trace / (n : ℝ)) := by
      intro i
      have h := Real.log_le_sub_one_of_pos (div_pos (hev i) hMpos)
      rw [Real.log_div (hev i).ne' hMpos.ne'] at h
      linarith
    refine le_trans (Finset.sum_le_sum fun i _ => hb i) ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_sub_distrib, Finset.sum_const,
      ← Finset.sum_div, ← htrev]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    linarith
  -- step 4: the trace bound
  have hnormbd : ∀ τ ∈ Finset.Ico 1 (t + 1), ∑ i, x τ i * x τ i ≤ (n : ℝ) := by
    intro τ hτ
    have hτ1 : 1 ≤ τ := (Finset.mem_Ico.mp hτ).1
    calc ∑ i, x τ i * x τ i ≤ ∑ _i : Fin n, (1:ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := hx τ hτ1 i
          nlinarith [abs_nonneg (x τ i), sq_abs (x τ i)]
      _ = (n : ℝ) := by simp
  have htrle : (designMatrix x (t + 1)).trace ≤ (n : ℝ) * ((t : ℝ) + 1) := by
    rw [trace_dm]
    have h1 : ∑ τ ∈ Finset.Ico 1 (t + 1), ∑ i, x τ i * x τ i
        ≤ ∑ _τ ∈ Finset.Ico 1 (t + 1), (n : ℝ) := Finset.sum_le_sum hnormbd
    rw [Finset.sum_const, Nat.card_Ico] at h1
    simp only [nsmul_eq_mul] at h1
    have h2 : ((t + 1 - 1 : ℕ) : ℝ) = (t : ℝ) := by simp
    rw [h2] at h1
    linarith
  have hMle : (designMatrix x (t + 1)).trace / (n : ℝ) ≤ (t : ℝ) + 1 := by
    rw [div_le_iff₀ hnR]
    linarith [htrle]
  have hlogle : Real.log ((designMatrix x (t + 1)).trace / (n : ℝ)) ≤ Real.log ((t : ℝ) + 1) :=
    Real.log_le_log hMpos hMle
  have hfin : Real.log ((designMatrix x (t + 1)).det) ≤ (n : ℝ) * Real.log ((t : ℝ) + 1) := by
    refine le_trans hLT ?_
    exact mul_le_mul_of_nonneg_left hlogle hnR.le
  calc ∑ τ ∈ Finset.Icc 1 t, min (width x τ ^ 2) 1
      ≤ ∑ τ ∈ Finset.Icc 1 t, 2 * Real.log (1 + width x τ ^ 2) := hstep1
    _ = 2 * Real.log ((designMatrix x (t + 1)).det) := hlogsum
    _ ≤ 2 * ((n : ℝ) * Real.log ((t : ℝ) + 1)) := by linarith
    _ = 2 * (n : ℝ) * Real.log ((t : ℝ) + 1) := by ring
