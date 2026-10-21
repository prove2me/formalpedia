-- Prove2me | solution 1 for SDPT3.ScaleInv.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T23:26:04.341193+00:00
-- url     : https://prove2.me/submissions/78cfff36-901c-4672-af70-d08c022033b7

import Mathlib
import Definitions.Def_SDPT3_ScaleInv_Setting

namespace SOCScaleProof
open Matrix SDPT3.ScaleInv
end SOCScaleProof

open Matrix SDPT3.ScaleInv
open scoped BigOperators

namespace SOCScaleProof

variable {k : ℕ}

theorem jbar_transpose (k : ℕ) : (Jbar k)ᵀ = Jbar k := by
  simp [Jbar]

theorem jbar_mul_self (k : ℕ) : Jbar k * Jbar k = 1 := by
  rw [Jbar, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hi : i = 0 <;> simp [Matrix.diagonal, Matrix.one_apply, hi]

theorem jbar_mulVec_zero (v : Fin (k + 1) → ℝ) : (Jbar k *ᵥ v) 0 = v 0 := by
  simp [Jbar, Matrix.mulVec_diagonal]

theorem jbar_mulVec_succ (v : Fin (k + 1) → ℝ) (i : Fin k) :
    (Jbar k *ᵥ v) i.succ = -v i.succ := by
  simp [Jbar, Matrix.mulVec_diagonal]

theorem jbar_e1 (k : ℕ) : Jbar k *ᵥ e1 k = e1 k := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact jbar_mulVec_zero _
  · simp [jbar_mulVec_succ, e1]

theorem jbar_eq (k : ℕ) :
    Jbar k = (2 : ℝ) • Matrix.vecMulVec (e1 k) (e1 k) - 1 := by
  ext i j
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> by_cases hij : i = j <;>
    norm_num [Jbar, e1, Matrix.vecMulVec, Matrix.one_apply, Matrix.diagonal,
      Pi.single_apply, hi, hj, hij, eq_comm]

theorem gammaSq_eq_head_sub_tail (v : Fin (k + 1) → ℝ) :
    gammaSq v = (v 0) ^ 2 - ∑ i : Fin k, (v i.succ) ^ 2 := by
  unfold gammaSq dotProduct
  rw [Fin.sum_univ_succ]
  simp only [jbar_mulVec_zero, jbar_mulVec_succ, mul_neg, Finset.sum_neg_distrib,
    pow_two, sub_eq_add_neg]

theorem gammaSq_smul (a : ℝ) (v : Fin (k + 1) → ℝ) :
    gammaSq (a • v) = a ^ 2 * gammaSq v := by
  simp only [gammaSq, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  ring

theorem gammaSq_jbar (v : Fin (k + 1) → ℝ) :
    gammaSq (Jbar k *ᵥ v) = gammaSq v := by
  simp [gammaSq_eq_head_sub_tail, jbar_mulVec_zero, jbar_mulVec_succ]

theorem socInt_jbar {v : Fin (k + 1) → ℝ} (hv : socInt v) :
    socInt (Jbar k *ᵥ v) := by
  exact ⟨by simpa only [jbar_mulVec_zero] using hv.1,
    by simpa only [gammaSq_jbar] using hv.2⟩

theorem socInt_smul {a : ℝ} {v : Fin (k + 1) → ℝ} (ha : 0 < a)
    (hv : socInt v) : socInt (a • v) := by
  exact ⟨mul_pos ha hv.1, by rw [gammaSq_smul]; exact mul_pos (sq_pos_of_pos ha) hv.2⟩

theorem gam_pos {v : Fin (k + 1) → ℝ} (hv : socInt v) : 0 < gam v :=
  Real.sqrt_pos.2 hv.2

theorem gam_sq {v : Fin (k + 1) → ℝ} (hv : socInt v) : (gam v) ^ 2 = gammaSq v :=
  Real.sq_sqrt hv.2.le

theorem soc_inner_pos {u v : Fin (k + 1) → ℝ} (hu : socInt u) (hv : socInt v) :
    0 < u ⬝ᵥ v := by
  have hU : 0 ≤ ∑ i : Fin k, (u i.succ) ^ 2 := Finset.sum_nonneg (by intros; positivity)
  have hV : 0 ≤ ∑ i : Fin k, (v i.succ) ^ 2 := Finset.sum_nonneg (by intros; positivity)
  have hu' := hu.2
  have hv' := hv.2
  rw [gammaSq_eq_head_sub_tail] at hu' hv'
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin k => u i.succ) (fun i : Fin k => v i.succ)
  have hp : 0 < u 0 * v 0 := mul_pos hu.1 hv.1
  have hb : (∑ i : Fin k, (u i.succ) ^ 2) * (∑ i : Fin k, (v i.succ) ^ 2) <
      (u 0) ^ 2 * (v 0) ^ 2 := by
    calc
      _ ≤ (u 0) ^ 2 * (∑ i : Fin k, (v i.succ) ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hV
      _ < _ := mul_lt_mul_of_pos_left (by linarith) (sq_pos_of_pos hu.1)
  rw [dotProduct, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (u 0 * v 0 + ∑ i : Fin k, u i.succ * v i.succ)]

theorem jbar_dot_comm (u v : Fin (k + 1) → ℝ) :
    u ⬝ᵥ (Jbar k *ᵥ v) = v ⬝ᵥ (Jbar k *ᵥ u) := by
  simpa only [jbar_transpose] using Matrix.dotProduct_transpose_mulVec (Jbar k) u v

theorem gammaSq_add (u v : Fin (k + 1) → ℝ) :
    gammaSq (u + v) = gammaSq u + gammaSq v + 2 * (u ⬝ᵥ (Jbar k *ᵥ v)) := by
  simp only [gammaSq, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  rw [jbar_dot_comm v u]
  ring

theorem gammaSq_mulVec_of_conformal {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {l : ℝ} (hF : Fᵀ * Jbar k * F = l ^ 2 • Jbar k) (v : Fin (k + 1) → ℝ) :
    gammaSq (F *ᵥ v) = l ^ 2 * gammaSq v := by
  calc
    gammaSq (F *ᵥ v) = v ⬝ᵥ ((Fᵀ * Jbar k * F) *ᵥ v) := by
      rw [gammaSq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
    _ = l ^ 2 * gammaSq v := by
      rw [hF, Matrix.smul_mulVec, dotProduct_smul]
      rfl

theorem conformal_left_inverse {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {l : ℝ} (hl : 0 < l) (hF : Fᵀ * Jbar k * F = l ^ 2 • Jbar k) :
    ((l ^ 2)⁻¹ • (Jbar k * Fᵀ * Jbar k)) * F = 1 := by
  calc
    _ = (l ^ 2)⁻¹ • (Jbar k * (Fᵀ * Jbar k * F)) := by
      rw [smul_mul_assoc]
      congr 1
      noncomm_ring
    _ = (l ^ 2)⁻¹ • (Jbar k * (l ^ 2 • Jbar k)) := by rw [hF]
    _ = 1 := by simp [jbar_mul_self, smul_smul, hl.ne']

theorem conformal_isUnit {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {l : ℝ} (hl : 0 < l) (hF : Fᵀ * Jbar k * F = l ^ 2 • Jbar k) : IsUnit F :=
  F.isUnit_iff_isUnit_det.2 (Matrix.isUnit_det_of_left_inverse (conformal_left_inverse hl hF))

theorem conformal_inv_eq {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {l : ℝ} (hl : 0 < l) (hF : Fᵀ * Jbar k * F = l ^ 2 • Jbar k) :
    F⁻¹ = (l ^ 2)⁻¹ • (Jbar k * Fᵀ * Jbar k) :=
  Matrix.inv_eq_left_inv (conformal_left_inverse hl hF)

theorem conformal_swap {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {l : ℝ} (hl : 0 < l) (hF : Fᵀ * Jbar k * F = l ^ 2 • Jbar k) :
    F * Jbar k * Fᵀ = l ^ 2 • Jbar k := by
  have hi := F.mul_nonsing_inv (F.isUnit_iff_isUnit_det.1 (conformal_isUnit hl hF))
  rw [conformal_inv_eq hl hF, mul_smul_comm] at hi
  have hh := congrArg (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ =>
    (l ^ 2) • (M * Jbar k)) hi
  simpa only [smul_mul_assoc, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hl.ne'),
    one_smul, Matrix.mul_assoc, jbar_mul_self, Matrix.mul_one, Matrix.one_mul] using hh

theorem conformal_inv_metric {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {l : ℝ} (hl : 0 < l) (hF : Fᵀ * Jbar k * F = l ^ 2 • Jbar k) :
    F⁻¹ᵀ * Jbar k * F⁻¹ = (l⁻¹) ^ 2 • Jbar k := by
  have hi := F.mul_nonsing_inv (F.isUnit_iff_isUnit_det.1 (conformal_isUnit hl hF))
  have hh := congrArg (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ =>
    F⁻¹ᵀ * M * F⁻¹) hF
  have hleft : F⁻¹ᵀ * (Fᵀ * Jbar k * F) * F⁻¹ = Jbar k := by
    calc
      _ = (F * F⁻¹)ᵀ * Jbar k * (F * F⁻¹) := by
        rw [Matrix.transpose_mul]
        noncomm_ring
      _ = Jbar k := by rw [hi]; simp
  rw [hleft] at hh
  have hhh := congrArg (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ =>
    (l ^ 2)⁻¹ • M) hh
  simpa [mul_smul_comm, smul_mul_assoc, smul_smul, hl.ne', inv_pow] using hhh.symm

theorem aut_isUnit {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    (hF : IsSOCAut F) : IsUnit F := by
  obtain ⟨l, hl, hm, _⟩ := hF
  exact conformal_isUnit hl hm

theorem aut_transpose {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    (hF : IsSOCAut F) : IsSOCAut Fᵀ := by
  obtain ⟨l, hl, hm, h0⟩ := hF
  exact ⟨l, hl, by simpa only [Matrix.transpose_transpose] using conformal_swap hl hm, h0⟩

theorem aut_inv {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    (hF : IsSOCAut F) : IsSOCAut F⁻¹ := by
  obtain ⟨l, hl, hm, h0⟩ := hF
  refine ⟨l⁻¹, inv_pos.2 hl, conformal_inv_metric hl hm, ?_⟩
  rw [conformal_inv_eq hl hm]
  simpa [Jbar, Matrix.diagonal_mul, Matrix.mul_diagonal] using
    mul_pos (inv_pos.2 (sq_pos_of_pos hl)) h0

theorem aut_preserves_interior {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    (hF : IsSOCAut F) {v : Fin (k + 1) → ℝ} (hv : socInt v) :
    socInt (F *ᵥ v) := by
  obtain ⟨l, hl, hm, h0⟩ := hF
  have hs := congrArg (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ => M 0 0)
    (conformal_swap hl hm)
  have hr : gammaSq (F 0) = l ^ 2 := by
    simpa [gammaSq, Matrix.mul_mul_apply, Matrix.transpose_apply, Jbar] using hs
  refine ⟨soc_inner_pos ⟨h0, by rw [hr]; positivity⟩ hv, ?_⟩
  rw [gammaSq_mulVec_of_conformal hm]
  exact mul_pos (sq_pos_of_pos hl) hv.2

theorem conformal_j_inv {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {l : ℝ} (hl : 0 < l) (hF : Fᵀ * Jbar k * F = l ^ 2 • Jbar k) :
    Jbar k * F⁻¹ = (l ^ 2)⁻¹ • (Fᵀ * Jbar k) := by
  rw [conformal_inv_eq hl hF, mul_smul_comm]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, jbar_mul_self, Matrix.one_mul]

theorem conformal_j_transpose {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {l : ℝ} (hl : 0 < l) (hF : Fᵀ * Jbar k * F = l ^ 2 • Jbar k) :
    Jbar k * Fᵀ = l ^ 2 • (F⁻¹ * Jbar k) := by
  rw [conformal_inv_eq hl hF, smul_mul_assoc, smul_smul]
  simp only [mul_inv_cancel₀ (pow_ne_zero 2 hl.ne'), one_smul]
  rw [Matrix.mul_assoc, jbar_mul_self, Matrix.mul_one]

end SOCScaleProof

namespace SOCScaleProof
open Matrix SDPT3.ScaleInv
open scoped BigOperators

variable {k : ℕ}

theorem arw_decomposition (v : Fin (k+1) → ℝ) :
    arw v = -(v 0) • Jbar k + vecMulVec (e1 k) v + vecMulVec v (e1 k) := by
  ext i j
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · subst i; subst j; simp [arw, Jbar, e1, vecMulVec, Pi.single_apply]
  · subst i; simp [arw, Jbar, e1, vecMulVec, Pi.single_apply, hj, Ne.symm hj]
  · subst j; simp [arw, Jbar, e1, vecMulVec, Pi.single_apply, hi]
  · by_cases hij : i = j
    · subst j; simp [arw, Jbar, e1, vecMulVec, Pi.single_apply, hi]
    · simp [arw, Jbar, e1, vecMulVec, Pi.single_apply, hi, hj, hij]

theorem e1_dot (u : Fin (k+1) → ℝ) : e1 k ⬝ᵥ u = u 0 := by
  simp [e1, dotProduct, Pi.single_apply]

theorem arw_action (v u : Fin (k+1) → ℝ) :
    arw v *ᵥ u = -(v 0) • (Jbar k *ᵥ u) + (v ⬝ᵥ u) • e1 k + (u 0) • v := by
  rw [arw_decomposition, add_mulVec, add_mulVec, smul_mulVec,
    vecMulVec_mulVec, vecMulVec_mulVec, e1_dot]
  simp only [op_smul_eq_smul]

theorem arw_action_zero (v u : Fin (k+1) → ℝ) :
    (arw v *ᵥ u) 0 = v ⬝ᵥ u := by
  rw [arw_action]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, jbar_mulVec_zero, e1, Pi.single_eq_same] 
  ring

theorem arw_action_succ (v u : Fin (k+1) → ℝ) (i : Fin k) :
    (arw v *ᵥ u) i.succ = v 0 * u i.succ + u 0 * v i.succ := by
  rw [arw_action]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, jbar_mulVec_succ]
  simp [e1]

theorem arw_comm (v u : Fin (k+1) → ℝ) : arw v *ᵥ u = arw u *ᵥ v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [arw_action_zero, dotProduct_comm]
  · simp only [arw_action_succ]
    ring

theorem arw_e1 : arw (e1 k) = 1 := by
  ext i j
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · subst i; subst j; simp [arw,e1,Pi.single_apply]
  · subst i; simp [arw,e1,Pi.single_apply,hj,Ne.symm hj]
  · subst j; simp [arw,e1,Pi.single_apply,hi]
  · simp [arw,e1,Pi.single_apply,hi,hj,Matrix.one_apply]

theorem arw_kernel {v u : Fin (k+1) → ℝ} (hv : socInt v)
    (h : arw v *ᵥ u = 0) : u = 0 := by
  have h0 : v 0 * u 0 + ∑ i : Fin k, v i.succ * u i.succ = 0 := by
    have hh := congrFun h 0
    simpa only [arw_action_zero, dotProduct, Fin.sum_univ_succ, Pi.zero_apply] using hh
  have ht (i : Fin k) : v 0 * u i.succ + u 0 * v i.succ = 0 := by
    simpa only [arw_action_succ, Pi.zero_apply] using congrFun h i.succ
  have hs : v 0 * (∑ i : Fin k, v i.succ * u i.succ) +
      u 0 * (∑ i : Fin k, v i.succ ^ 2) = 0 := by
    calc
      _ = ∑ i : Fin k, v i.succ * (v 0 * u i.succ + u 0 * v i.succ) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by simp only [ht, mul_zero, Finset.sum_const_zero]
  have hq := gammaSq_eq_head_sub_tail v
  have hh : gammaSq v * u 0 = 0 := by
    have hm := congrArg (fun r : ℝ => v 0 * r) h0
    rw [hq]
    nlinarith
  have hu : u 0 = 0 := (mul_eq_zero.mp hh).resolve_left (ne_of_gt hv.2)
  funext i
  refine Fin.cases hu (fun j => ?_) i
  have hh := ht j
  rw [hu, zero_mul, add_zero] at hh
  exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt hv.1)

theorem arw_isUnit {v : Fin (k+1) → ℝ} (hv : socInt v) : IsUnit (arw v) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u w h
  have hh : arw v *ᵥ (u-w) = 0 := by rw [mulVec_sub,h,sub_self]
  exact sub_eq_zero.mp (arw_kernel hv hh)

theorem arw_jbar (v : Fin (k+1) → ℝ) :
    arw v *ᵥ (Jbar k *ᵥ v) = gammaSq v • e1 k := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [arw_action_zero, gammaSq, e1]
  · simp only [arw_action_succ,jbar_mulVec_zero,jbar_mulVec_succ,Pi.smul_apply,smul_eq_mul]
    simp [e1]

theorem arw_inv_e1 {v : Fin (k+1) → ℝ} (hv : socInt v) :
    (arw v)⁻¹ *ᵥ e1 k = (gammaSq v)⁻¹ • (Jbar k *ᵥ v) := by
  have hu := arw_isUnit hv
  have he : arw v *ᵥ ((gammaSq v)⁻¹ • (Jbar k *ᵥ v)) = e1 k := by
    rw [mulVec_smul, arw_jbar, smul_smul, inv_mul_cancel₀ (ne_of_gt hv.2), one_smul]
  calc
    (arw v)⁻¹ *ᵥ e1 k = (arw v)⁻¹ *ᵥ (arw v *ᵥ ((gammaSq v)⁻¹ • (Jbar k *ᵥ v))) := congrArg _ he.symm
    _ = _ := by rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ ((arw v).isUnit_iff_isUnit_det.mp hu), one_mulVec]

end SOCScaleProof

namespace SOCScaleProof
open Matrix SDPT3.ScaleInv
open scoped BigOperators

variable {k : ℕ}

noncomputable def boost (t : Fin (k+1) → ℝ) : Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
  -Jbar k + (1+t 0)⁻¹ • vecMulVec (t+e1 k) (t+e1 k)

theorem jbar_vecMul (v : Fin (k+1) → ℝ) : v ᵥ* Jbar k = Jbar k *ᵥ v := by
  simpa only [jbar_transpose] using vecMul_transpose (Jbar k) v

theorem jbar_action (v : Fin (k+1) → ℝ) :
    Jbar k *ᵥ v = (2*v 0) • e1 k - v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [jbar_mulVec_zero,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    simp [e1]
    ring
  · simp [jbar_mulVec_succ,e1]

theorem boost_transpose (t : Fin (k+1) → ℝ) : (boost t)ᵀ = boost t := by
  simp [boost, transpose_add, transpose_neg, transpose_smul, transpose_vecMulVec, jbar_transpose]

theorem boost_metric (t : Fin (k+1) → ℝ) (ht : 0 < t 0) (hq : gammaSq t = 1) :
    boost t * Jbar k * boost t = Jbar k := by
  let s := t+e1 k
  have hd : 1+t 0 ≠ 0 := ne_of_gt (by linarith)
  have hq' : s ⬝ᵥ (Jbar k *ᵥ s) = 2*(1+t 0) := by
    dsimp [s]
    rw [mulVec_add, jbar_e1]
    simp only [add_dotProduct, dotProduct_add]
    have h1 : t ⬝ᵥ e1 k = t 0 := by rw [dotProduct_comm,e1_dot]
    have h2 : e1 k ⬝ᵥ (Jbar k *ᵥ t) = t 0 := by rw [e1_dot,jbar_mulVec_zero]
    have h3 : e1 k ⬝ᵥ e1 k = 1 := by rw [e1_dot]; simp [e1]
    change gammaSq t + _ + (_ + _) = _
    rw [hq,h1,h2,h3]
    ring
  have hs : (s ᵥ* Jbar k) ⬝ᵥ s = 2*(1+t 0) := by
    rw [jbar_vecMul,dotProduct_comm]
    exact hq'
  let P := vecMulVec s s
  let C := (1+t 0)⁻¹ • P
  have hP : P * Jbar k * P = (2*(1+t 0)) • P := by
    dsimp [P]
    rw [vecMulVec_mul,vecMulVec_mul_vecMulVec,hs,vecMulVec_smul]
  have hC : C * Jbar k * C = 2 • C := by
    dsimp [C]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hP, smul_smul]
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, two_smul]
    field_simp [hd]
    ; ring
  calc
    _ = Jbar k * Jbar k * Jbar k - Jbar k * Jbar k * C -
        C * (Jbar k * Jbar k) + C * Jbar k * C := by
      change (-Jbar k+C)*Jbar k*(-Jbar k+C) = _
      noncomm_ring
    _ = Jbar k - C - C + 2 • C := by rw [jbar_mul_self,hC]; simp
    _ = Jbar k := by module

theorem boost_e1 (t : Fin (k+1) → ℝ) (ht : 0 < t 0) : boost t *ᵥ e1 k = t := by
  have hd : 1+t 0 ≠ 0 := ne_of_gt (by linarith)
  have hs : (t+e1 k) ⬝ᵥ e1 k = 1+t 0 := by
    rw [dotProduct_comm,e1_dot]
    simp [e1,add_comm]
  rw [boost,add_mulVec,neg_mulVec,jbar_e1,smul_mulVec,vecMulVec_mulVec,hs]
  simp only [op_smul_eq_smul,smul_smul]
  funext i
  simp only [Pi.add_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul]
  field_simp
  ; ring

theorem boost_zero_zero (t : Fin (k+1) → ℝ) (ht : 0 < t 0) : boost t 0 0 = t 0 := by
  have h := congrFun (boost_e1 t ht) 0
  simpa [mulVec,dotProduct,e1,Pi.single_apply] using h

theorem boost_aut (t : Fin (k+1) → ℝ) (ht : 0 < t 0) (hq : gammaSq t = 1) :
    IsSOCAut (boost t) := by
  refine ⟨1,by norm_num,?_,?_⟩
  · simpa [boost_transpose] using boost_metric t ht hq
  · simpa [boost_zero_zero t ht] using ht

theorem boost_inv (t : Fin (k+1) → ℝ) (ht : 0 < t 0) (hq : gammaSq t = 1) :
    (boost t)⁻¹ = Jbar k * boost t * Jbar k := by
  apply Matrix.inv_eq_left_inv
  calc
    (Jbar k * boost t * Jbar k) * boost t = Jbar k * (boost t * Jbar k * boost t) := by noncomm_ring
    _ = 1 := by rw [boost_metric t ht hq,jbar_mul_self]

theorem boost_square (t : Fin (k+1) → ℝ) (ht : 0 < t 0) (hq : gammaSq t = 1) :
    boost t * boost t = 2 • vecMulVec t t - Jbar k := by
  have hm := boost_metric t ht hq
  have he : boost t * vecMulVec (e1 k) (e1 k) * boost t = vecMulVec t t := by
    rw [mul_vecMulVec, boost_e1 t ht, vecMulVec_mul]
    have hv : e1 k ᵥ* boost t = t := by
      rw [← boost_transpose t, vecMul_transpose, boost_e1 t ht]
    rw [hv]
  rw [jbar_eq k] at hm
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, he] at hm
  rw [← jbar_eq k] at hm
  ext i j
  have hh := congrFun (congrFun hm i) j
  simp only [Matrix.sub_apply, two_smul, Matrix.add_apply] at hh ⊢
  linarith

theorem boost_inv_square (t : Fin (k+1) → ℝ) (ht : 0 < t 0) (hq : gammaSq t = 1) :
    (boost t)⁻¹ * (boost t)⁻¹ =
      2 • vecMulVec (Jbar k *ᵥ t) (Jbar k *ᵥ t) - Jbar k := by
  rw [boost_inv t ht hq]
  have he : (Jbar k * boost t * Jbar k) * (Jbar k * boost t * Jbar k) =
      Jbar k * (boost t * boost t) * Jbar k := by
    calc
      _ = Jbar k * boost t * (Jbar k * Jbar k) * boost t * Jbar k := by noncomm_ring
      _ = _ := by rw [jbar_mul_self]; simp [Matrix.mul_assoc]
  rw [he,boost_square t ht hq]
  simp [Matrix.mul_sub,Matrix.sub_mul,
    mul_vecMulVec,vecMulVec_mul,jbar_vecMul,jbar_mul_self]

end SOCScaleProof

namespace SOCScaleProof
open Matrix SDPT3.ScaleInv
open scoped BigOperators
variable {k : ℕ}

theorem normalized_soc {z : Fin (k+1) → ℝ} (hz : socInt z) :
    0 < ((gam z)⁻¹ • z) 0 ∧ gammaSq ((gam z)⁻¹ • z) = 1 := by
  constructor
  · exact mul_pos (inv_pos.2 (gam_pos hz)) hz.1
  · rw [gammaSq_smul,←gam_sq hz]
    field_simp [ne_of_gt (gam_pos hz)]

theorem hkm_eq_boost {z : Fin (k+1) → ℝ} (hz : socInt z) :
    GHKM z = gam z • boost ((gam z)⁻¹ • z) := by
  have hg := gam_pos hz
  have hd : gam z + z 0 ≠ 0 := ne_of_gt (add_pos hg hz.1)
  ext i j
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · subst i; subst j
    simp [GHKM,boost,Jbar,e1,vecMulVec,Pi.single_apply]
    field_simp
    ; ring
  · subst i
    simp [GHKM,boost,Jbar,e1,vecMulVec,Pi.single_apply,hj,Ne.symm hj]
    field_simp
    ; ring
  · subst j
    simp [GHKM,boost,Jbar,e1,vecMulVec,Pi.single_apply,hi]
    field_simp
    ; ring
  · by_cases hij : i = j
    · subst j
      simp [GHKM,boost,Jbar,e1,vecMulVec,Pi.single_apply,hi]
      field_simp
    · simp [GHKM,boost,Jbar,e1,vecMulVec,Pi.single_apply,hi,hj,hij]
      field_simp

theorem hkm_transpose (z : Fin (k+1) → ℝ) : (GHKM z)ᵀ = GHKM z := by
  ext i j
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · subst i; subst j; rfl
  · subst i; simp [GHKM,hj]
  · subst j; simp [GHKM,hi]
  · simp [GHKM,hi,hj,eq_comm,mul_comm]

theorem hkm_e1 {z : Fin (k+1) → ℝ} (hz : socInt z) : GHKM z *ᵥ e1 k = z := by
  rw [hkm_eq_boost hz,smul_mulVec,boost_e1 _ (normalized_soc hz).1,smul_smul]
  simp [ne_of_gt (gam_pos hz)]

theorem hkm_metric {z : Fin (k+1) → ℝ} (hz : socInt z) :
    (GHKM z)ᵀ * Jbar k * GHKM z = (gam z)^2 • Jbar k := by
  rw [hkm_transpose,hkm_eq_boost hz]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [boost_metric _ (normalized_soc hz).1 (normalized_soc hz).2]
  simp only [pow_two]

theorem hkm_isUnit {z : Fin (k+1) → ℝ} (hz : socInt z) : IsUnit (GHKM z) :=
  conformal_isUnit (gam_pos hz) (hkm_metric hz)

theorem hkm_inv_z {z : Fin (k+1) → ℝ} (hz : socInt z) : (GHKM z)⁻¹ *ᵥ z = e1 k := by
  have hu : IsUnit (GHKM z).det := (GHKM z).isUnit_iff_isUnit_det.mp (hkm_isUnit hz)
  calc
    _ = (GHKM z)⁻¹ *ᵥ (GHKM z *ᵥ e1 k) := by rw [hkm_e1 hz]
    _ = _ := by rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, one_mulVec]

theorem hkm_calE {z : Fin (k+1) → ℝ} (hz : socInt z) : calE (GHKM z) z = GHKM z := by
  rw [calE,hkm_inv_z hz,arw_e1,Matrix.one_mul]

theorem hkm_inv_e1 {z : Fin (k+1) → ℝ} (hz : socInt z) :
    (GHKM z)⁻¹ *ᵥ e1 k = (gammaSq z)⁻¹ • (Jbar k *ᵥ z) := by
  rw [conformal_inv_eq (gam_pos hz) (hkm_metric hz),smul_mulVec,
    ←mulVec_mulVec,←mulVec_mulVec,jbar_e1,hkm_transpose,hkm_e1 hz,gam_sq hz]

theorem hkm_normalized_matrix (x : Fin (k+1) → ℝ) {z : Fin (k+1) → ℝ} (hz : socInt z) :
    (calE (GHKM z) z)⁻¹ * calF (GHKM z) x =
      (gammaSq z)⁻¹ • (-(x ⬝ᵥ z) • Jbar k +
        vecMulVec x (Jbar k *ᵥ z) + vecMulVec (Jbar k *ᵥ z) x) := by
  let G := GHKM z
  have hu : IsUnit G.det := G.isUnit_iff_isUnit_det.mp (hkm_isUnit hz)
  have hinv : G⁻¹ᵀ = G⁻¹ := by rw [Matrix.transpose_nonsing_inv]; simp only [G,hkm_transpose]
  have hv : (G *ᵥ x) 0 = x ⬝ᵥ z := by
    rw [←e1_dot (G *ᵥ x), dotProduct_mulVec]
    have he : e1 k ᵥ* G = z := by
      rw [← show Gᵀ = G from hkm_transpose z,vecMul_transpose]
      exact hkm_e1 hz
    rw [he,dotProduct_comm]
  have hmetric : G⁻¹ * Jbar k * G⁻¹ = (gammaSq z)⁻¹ • Jbar k := by
    have hh := conformal_inv_metric (gam_pos hz) (hkm_metric hz)
    rw [hinv] at hh
    simpa [inv_pow,gam_sq hz] using hh
  have he : G⁻¹ *ᵥ e1 k = (gammaSq z)⁻¹ • (Jbar k *ᵥ z) := hkm_inv_e1 hz
  have hx : G⁻¹ *ᵥ (G *ᵥ x) = x := by rw [mulVec_mulVec,Matrix.nonsing_inv_mul _ hu,one_mulVec]
  have hxr : (G *ᵥ x) ᵥ* G⁻¹ = x := by rw [←hinv,vecMul_transpose,hx]
  have her : e1 k ᵥ* G⁻¹ = (gammaSq z)⁻¹ • (Jbar k *ᵥ z) := by rw [←hinv,vecMul_transpose,he]
  rw [hkm_calE hz,calF]
  change G⁻¹ * (arw (G *ᵥ x) * G⁻¹) = _
  rw [arw_decomposition,hv]
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
    ←Matrix.mul_assoc,mul_vecMulVec,vecMulVec_mul,hmetric,he,hx,hxr,her,
    vecMulVec_smul,smul_vecMulVec,smul_smul,smul_add]
  module

end SOCScaleProof

namespace SOCScaleProof
open Matrix SDPT3.ScaleInv
open scoped BigOperators
variable {k : ℕ}

theorem omega_pos {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    0 < omegaNT x z := Real.sqrt_pos.2 (div_pos (gam_pos hz) (gam_pos hx))

theorem omega_sq {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    omegaNT x z ^ 2 = gam z / gam x :=
  Real.sq_sqrt (div_nonneg (gam_pos hz).le (gam_pos hx).le)

theorem xi_formula (x z : Fin (k+1) → ℝ) :
    xiNT x z = (omegaNT x z)⁻¹ • z + omegaNT x z • (Jbar k *ᵥ x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [xiNT,jbar_mulVec_zero,div_eq_mul_inv,mul_comm]
  · simp [xiNT,jbar_mulVec_succ,div_eq_mul_inv,mul_comm,sub_eq_add_neg]

theorem omega_balance {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    omegaNT x z ^ 2 * gam x = gam z := by
  rw [omega_sq hx hz]
  exact div_mul_cancel₀ _ (ne_of_gt (gam_pos hx))

theorem xi_metric {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    gammaSq (xiNT x z) = 2*(gam x * gam z + x ⬝ᵥ z) := by
  have hw := omega_pos hx hz
  have hb := omega_balance hx hz
  rw [xi_formula,gammaSq_add,gammaSq_smul,gammaSq_smul,gammaSq_jbar,
    mulVec_smul,mulVec_mulVec,jbar_mul_self,one_mulVec,
    smul_dotProduct,dotProduct_smul,smul_eq_mul,smul_eq_mul,
    ←gam_sq hx,←gam_sq hz]
  rw [dotProduct_comm z x]
  field_simp
  nlinarith [sq_nonneg (omegaNT x z ^ 2 * gam x - gam z)]

theorem xi_balance {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    gammaSq (xiNT x z) = 2*omegaNT x z*(xiNT x z ⬝ᵥ x) := by
  have hw := omega_pos hx hz
  have hb := omega_balance hx hz
  rw [xi_metric hx hz,xi_formula,add_dotProduct,smul_dotProduct,smul_dotProduct]
  have hj : (Jbar k *ᵥ x) ⬝ᵥ x = gammaSq x := by rw [dotProduct_comm]; rfl
  rw [hj,←gam_sq hx,dotProduct_comm z x]
  simp only [smul_eq_mul]
  field_simp
  nlinarith [congrArg (fun r : ℝ => r * gam x) hb]

theorem xi_interior {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    socInt (xiNT x z) := by
  refine ⟨?_,?_⟩
  · simp only [xiNT,ite_true]
    exact add_pos (div_pos hz.1 (omega_pos hx hz)) (mul_pos (omega_pos hx hz) hx.1)
  · rw [xi_metric hx hz]
    exact mul_pos (by norm_num) (add_pos (mul_pos (gam_pos hx) (gam_pos hz)) (soc_inner_pos hx hz))

theorem t_normalized {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    0 < tNT x z 0 ∧ gammaSq (tNT x z) = 1 := normalized_soc (xi_interior hx hz)

theorem nt_eq_boost {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    GNT x z = omegaNT x z • boost (tNT x z) := by
  have ht := (t_normalized hx hz).1
  have hd : 1+tNT x z 0 ≠ 0 := ne_of_gt (by linarith)
  unfold GNT
  congr 1
  ext i j
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · subst i; subst j; simp [boost,Jbar,e1,vecMulVec,Pi.single_apply]; field_simp; ring
  · subst i; simp [boost,Jbar,e1,vecMulVec,Pi.single_apply,hj,Ne.symm hj]; field_simp; ring
  · subst j; simp [boost,Jbar,e1,vecMulVec,Pi.single_apply,hi]; field_simp; ring
  · by_cases hij : i = j
    · subst j; simp [boost,Jbar,e1,vecMulVec,Pi.single_apply,hi,div_eq_mul_inv,mul_comm]
    · simp [boost,Jbar,e1,vecMulVec,Pi.single_apply,hi,hj,hij,div_eq_mul_inv,mul_comm]

theorem nt_transpose {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    (GNT x z)ᵀ = GNT x z := by rw [nt_eq_boost hx hz]; simp [transpose_smul,boost_transpose]

theorem nt_metric {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    (GNT x z)ᵀ * Jbar k * GNT x z = omegaNT x z ^ 2 • Jbar k := by
  rw [nt_transpose hx hz,nt_eq_boost hx hz]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [
    boost_metric _ (t_normalized hx hz).1 (t_normalized hx hz).2]
  simp only [pow_two]

theorem nt_aut {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    IsSOCAut (GNT x z) := by
  refine ⟨omegaNT x z,omega_pos hx hz,nt_metric hx hz,?_⟩
  rw [nt_eq_boost hx hz]
  change 0 < omegaNT x z * boost (tNT x z) 0 0
  rw [boost_zero_zero _ (t_normalized hx hz).1]
  exact mul_pos (omega_pos hx hz) (t_normalized hx hz).1

theorem nt_isUnit {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    IsUnit (GNT x z) := aut_isUnit (nt_aut hx hz)

theorem nt_balance {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    GNT x z *ᵥ (GNT x z *ᵥ x) = z := by
  have hw := omega_pos hx hz
  have hg := gam_pos (xi_interior hx hz)
  have hgs := gam_sq (xi_interior hx hz)
  have hb := xi_balance hx hz
  rw [mulVec_mulVec,nt_eq_boost hx hz,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    boost_square _ (t_normalized hx hz).1 (t_normalized hx hz).2,
    smul_mulVec,sub_mulVec,smul_mulVec,vecMulVec_mulVec]
  simp only [op_smul_eq_smul,tNT,smul_dotProduct,smul_eq_mul,smul_smul]
  funext i
  simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,two_smul]
  have hxii := congrFun (xi_formula x z) i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hxii
  field_simp [ne_of_gt hw] at hxii
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  field_simp [ne_of_gt hg]
  have hh := congrArg (fun r : ℝ => r * (omegaNT x z * xiNT x z i)) hb
  have hhh := congrArg (fun r : ℝ => r * (z i + omegaNT x z ^ 2 * (Jbar k *ᵥ x) i)) hgs
  nlinarith [hh,hhh]

theorem nt_inv_z {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    (GNT x z)⁻¹ *ᵥ z = GNT x z *ᵥ x := by
  have hu := (GNT x z).isUnit_iff_isUnit_det.mp (nt_isUnit hx hz)
  calc
    _ = (GNT x z)⁻¹ *ᵥ (GNT x z *ᵥ (GNT x z *ᵥ x)) := by rw [nt_balance hx hz]
    _ = _ := by rw [mulVec_mulVec,Matrix.nonsing_inv_mul _ hu,one_mulVec]

theorem nt_calE_isUnit {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    IsUnit (calE (GNT x z) z) := by
  rw [calE,nt_inv_z hx hz]
  exact (arw_isUnit (aut_preserves_interior (nt_aut hx hz) hx)).mul (nt_isUnit hx hz)

theorem nt_normalized_matrix {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    (calE (GNT x z) z)⁻¹ * calF (GNT x z) x =
      (omegaNT x z ^ 2)⁻¹ •
        (-Jbar k + 2 • vecMulVec (Jbar k *ᵥ tNT x z) (Jbar k *ᵥ tNT x z)) := by
  let G := GNT x z
  have ha := (arw (G *ᵥ x)).isUnit_iff_isUnit_det.mp
    (arw_isUnit (aut_preserves_interior (nt_aut hx hz) hx))
  have he : (calE G z)⁻¹ * calF G x = G⁻¹ * G⁻¹ := by
    have hi : G⁻¹ *ᵥ z = G *ᵥ x := nt_inv_z hx hz
    simp only [calE,calF,hi,Matrix.mul_inv_rev]
    rw [Matrix.mul_assoc,←Matrix.mul_assoc (arw (G *ᵥ x))⁻¹,
      Matrix.nonsing_inv_mul _ ha,Matrix.one_mul]
  rw [he]
  have hi : G⁻¹ = (omegaNT x z)⁻¹ • (boost (tNT x z))⁻¹ := by
    apply Matrix.inv_eq_left_inv
    dsimp [G]
    rw [nt_eq_boost hx hz,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
      Matrix.nonsing_inv_mul _ ((boost (tNT x z)).isUnit_iff_isUnit_det.mp
        (aut_isUnit (boost_aut _ (t_normalized hx hz).1 (t_normalized hx hz).2)))]
    simp [ne_of_gt (omega_pos hx hz)]
  rw [hi,Matrix.smul_mul,Matrix.mul_smul,smul_smul,boost_inv_square _ (t_normalized hx hz).1 (t_normalized hx hz).2]
  simp only [pow_two,_root_.mul_inv_rev,sub_eq_add_neg,add_comm]

theorem nt_calE_inv_e1 {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    (calE (GNT x z) z)⁻¹ *ᵥ e1 k = (gammaSq z)⁻¹ • (Jbar k *ᵥ z) := by
  let G := GNT x z
  have hv := aut_preserves_interior (nt_aut hx hz) hx
  have hq : gammaSq (G *ᵥ x) = omegaNT x z ^ 2 * gammaSq x :=
    gammaSq_mulVec_of_conformal (nt_metric hx hz) x
  have hi : G⁻¹ * Jbar k * G = (omegaNT x z ^ 2)⁻¹ • (Jbar k * (G * G)) := by
    rw [conformal_inv_eq (omega_pos hx hz) (nt_metric hx hz),nt_transpose hx hz]
    simp only [Matrix.smul_mul,Matrix.mul_assoc,jbar_mul_self,Matrix.one_mul]
    rfl
  have hm : omegaNT x z ^ 4 * gammaSq x = gammaSq z := by
    rw [←gam_sq hx,←gam_sq hz]
    have hh := congrArg (fun r : ℝ => r^2) (omega_balance hx hz)
    nlinarith only [hh]
  have hqne := ne_of_gt hx.2
  have hw := ne_of_gt (omega_pos hx hz)
  rw [calE,nt_inv_z hx hz,Matrix.mul_inv_rev,←mulVec_mulVec,arw_inv_e1 hv,mulVec_smul]
  change _ • (G⁻¹ *ᵥ (Jbar k *ᵥ (G *ᵥ x))) = _
  rw [mulVec_mulVec,mulVec_mulVec,hi,smul_mulVec,←mulVec_mulVec,←mulVec_mulVec,nt_balance hx hz,smul_smul,hq]
  congr 1
  rw [←hm]
  field_simp

end SOCScaleProof

namespace SOCScaleProof
open Matrix SDPT3.ScaleInv
variable {k : ℕ}

theorem calE_isUnit (dir : Dir) {x z : Fin (k+1) → ℝ}
    (hx : socInt x) (hz : socInt z) : IsUnit (calE (Gdir dir x z) z) := by
  cases dir with
  | hkm => simpa only [Gdir,hkm_calE hz] using hkm_isUnit hz
  | nt => exact nt_calE_isUnit hx hz

theorem calE_inv_e1 (dir : Dir) {x z : Fin (k+1) → ℝ}
    (hx : socInt x) (hz : socInt z) :
    (calE (Gdir dir x z) z)⁻¹ *ᵥ e1 k = (gammaSq z)⁻¹ • (Jbar k *ᵥ z) := by
  cases dir with
  | hkm => simpa only [Gdir,hkm_calE hz] using hkm_inv_e1 hz
  | nt => exact nt_calE_inv_e1 hx hz

theorem calE_x (G : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (x z : Fin (k+1) → ℝ) : calE G z *ᵥ x = TG G x z := by
  rw [calE,TG,←mulVec_mulVec,arw_comm]

theorem normalized_complementarity_iff (dir : Dir) {x z : Fin (k+1) → ℝ}
    (hx : socInt x) (hz : socInt z) (s : ℝ) (dx dz : Fin (k+1) → ℝ) :
    calE (Gdir dir x z) z *ᵥ dx + calF (Gdir dir x z) x *ᵥ dz =
      s • e1 k - TG (Gdir dir x z) x z ↔
    dx + ((calE (Gdir dir x z) z)⁻¹ * calF (Gdir dir x z) x) *ᵥ dz =
      s • ((gammaSq z)⁻¹ • (Jbar k *ᵥ z)) - x := by
  let E := calE (Gdir dir x z) z
  have hu : IsUnit E.det := E.isUnit_iff_isUnit_det.mp (calE_isUnit dir hx hz)
  have hn : E⁻¹ * E = 1 := Matrix.nonsing_inv_mul _ hu
  have he : E⁻¹ *ᵥ e1 k = (gammaSq z)⁻¹ • (Jbar k *ᵥ z) := calE_inv_e1 dir hx hz
  have hi : Function.Injective E⁻¹.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    (E⁻¹.isUnit_iff_isUnit_det.mpr (E.isUnit_nonsing_inv_det hu))
  constructor
  · intro h
    have hh := congrArg E⁻¹.mulVec h
    rw [mulVec_add,mulVec_sub,mulVec_smul,←calE_x (Gdir dir x z) x z] at hh
    change E⁻¹ *ᵥ (E *ᵥ dx) + E⁻¹ *ᵥ (calF (Gdir dir x z) x *ᵥ dz) =
      s • (E⁻¹ *ᵥ e1 k) - E⁻¹ *ᵥ (E *ᵥ x) at hh
    simpa only [mulVec_mulVec,hn,one_mulVec,he] using hh
  · intro h
    apply hi
    rw [mulVec_add,mulVec_sub,mulVec_smul,←calE_x (Gdir dir x z) x z]
    change E⁻¹ *ᵥ (E *ᵥ dx) + E⁻¹ *ᵥ (calF (Gdir dir x z) x *ᵥ dz) =
      s • (E⁻¹ *ᵥ e1 k) - E⁻¹ *ᵥ (E *ᵥ x)
    simpa only [mulVec_mulVec,hn,one_mulVec,he] using h

end SOCScaleProof

open Matrix SDPT3.ScaleInv
open scoped BigOperators

namespace SOCScaleProof

variable {k : ℕ}

theorem pairing_transport {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    (hF : IsSOCAut F) (x z : Fin (k + 1) → ℝ) :
    (Fᵀ *ᵥ x) ⬝ᵥ (F⁻¹ *ᵥ z) = x ⬝ᵥ z := by
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    F.mul_nonsing_inv (F.isUnit_iff_isUnit_det.1 (aut_isUnit hF)), Matrix.one_mulVec]

theorem gam_mulVec_of_conformal {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {l : ℝ} (hl : 0 < l) (hF : Fᵀ * Jbar k * F = l ^ 2 • Jbar k)
    {v : Fin (k + 1) → ℝ} (hv : socInt v) : gam (F *ᵥ v) = l * gam v := by
  have hp : 0 < gammaSq (F *ᵥ v) := by
    rw [gammaSq_mulVec_of_conformal hF]
    exact mul_pos (sq_pos_of_pos hl) hv.2
  have hs : gam (F *ᵥ v) ^ 2 = l ^ 2 * gam v ^ 2 := by
    rw [gam, Real.sq_sqrt hp.le, gammaSq_mulVec_of_conformal hF, gam_sq hv]
  have hn : 0 ≤ gam (F *ᵥ v) := Real.sqrt_nonneg _
  have hvp := gam_pos hv
  have hprod := mul_pos hl hvp
  nlinarith

theorem gam_transpose_transport {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {l : ℝ} (hl : 0 < l) (hF : Fᵀ * Jbar k * F = l ^ 2 • Jbar k)
    {x : Fin (k + 1) → ℝ} (hx : socInt x) : gam (Fᵀ *ᵥ x) = l * gam x := by
  apply gam_mulVec_of_conformal hl _ hx
  simpa only [Matrix.transpose_transpose] using conformal_swap hl hF

theorem gam_inv_transport {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {l : ℝ} (hl : 0 < l) (hF : Fᵀ * Jbar k * F = l ^ 2 • Jbar k)
    {z : Fin (k + 1) → ℝ} (hz : socInt z) : gam (F⁻¹ *ᵥ z) = gam z / l := by
  simpa only [div_eq_mul_inv, mul_comm] using
    gam_mulVec_of_conformal (inv_pos.2 hl) (conformal_inv_metric hl hF) hz

theorem omega_transport {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {l : ℝ} (hl : 0 < l) (hF : Fᵀ * Jbar k * F = l ^ 2 • Jbar k)
    {x z : Fin (k + 1) → ℝ} (hx : socInt x) (hz : socInt z) :
    omegaNT (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z) = omegaNT x z / l := by
  unfold omegaNT
  rw [gam_transpose_transport hl hF hx, gam_inv_transport hl hF hz]
  have he : (gam z / l) / (l * gam x) = (gam z / gam x) / l ^ 2 := by ring
  rw [he, Real.sqrt_div (div_nonneg (gam_pos hz).le (gam_pos hx).le),
    Real.sqrt_sq hl.le]

theorem xiNT_vector_eq (x z : Fin (k + 1) → ℝ) :
    xiNT x z = (omegaNT x z)⁻¹ • z + omegaNT x z • (Jbar k *ᵥ x) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [xiNT, jbar_mulVec_zero, div_eq_mul_inv, mul_comm]
  · simp [xiNT, jbar_mulVec_succ, div_eq_mul_inv, mul_comm, sub_eq_add_neg]

theorem xi_transport {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {l : ℝ} (hl : 0 < l) (hF : Fᵀ * Jbar k * F = l ^ 2 • Jbar k)
    {x z : Fin (k + 1) → ℝ} (hx : socInt x) (hz : socInt z) :
    xiNT (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z) = l • (F⁻¹ *ᵥ xiNT x z) := by
  rw [xiNT_vector_eq, omega_transport hl hF hx hz, xiNT_vector_eq,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, conformal_j_transpose hl hF, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec]
  simp only [smul_add, smul_smul]
  rw [show (omegaNT x z / l)⁻¹ = l * (omegaNT x z)⁻¹ by simp [div_eq_mul_inv, _root_.mul_inv_rev]]
  have he : omegaNT x z / l * l ^ 2 = l * omegaNT x z := by
    field_simp
  rw [he]

theorem gam_xi_transport {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {l : ℝ} (hl : 0 < l) (hF : Fᵀ * Jbar k * F = l ^ 2 • Jbar k)
    {x z : Fin (k + 1) → ℝ} (hx : socInt x) (hz : socInt z) :
    gam (xiNT (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z)) = gam (xiNT x z) := by
  unfold gam
  rw [xi_transport hl hF hx hz, gammaSq_smul,
    gammaSq_mulVec_of_conformal (conformal_inv_metric hl hF)]
  congr 1
  field_simp

theorem t_transport {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {l : ℝ} (hl : 0 < l) (hF : Fᵀ * Jbar k * F = l ^ 2 • Jbar k)
    {x z : Fin (k + 1) → ℝ} (hx : socInt x) (hz : socInt z) :
    tNT (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z) = l • (F⁻¹ *ᵥ tNT x z) := by
  unfold tNT
  rw [gam_xi_transport hl hF hx hz, xi_transport hl hF hx hz, Matrix.mulVec_smul]
  simp only [smul_smul, mul_comm]

theorem inverse_jordan_transport {F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {l : ℝ} (hl : 0 < l) (hF : Fᵀ * Jbar k * F = l ^ 2 • Jbar k)
    {z : Fin (k + 1) → ℝ} (_hz : socInt z) :
    (gammaSq (F⁻¹ *ᵥ z))⁻¹ • (Jbar k *ᵥ (F⁻¹ *ᵥ z)) =
      Fᵀ *ᵥ ((gammaSq z)⁻¹ • (Jbar k *ᵥ z)) := by
  rw [gammaSq_mulVec_of_conformal (conformal_inv_metric hl hF), Matrix.mulVec_mulVec,
    conformal_j_inv hl hF, Matrix.smul_mulVec, Matrix.mulVec_smul,
    ← Matrix.mulVec_mulVec, smul_smul]
  congr 1
  field_simp

theorem outer_transport (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (u v : Fin (k + 1) → ℝ) :
    Fᵀ * Matrix.vecMulVec u v * F =
      Matrix.vecMulVec (Fᵀ *ᵥ u) (Fᵀ *ᵥ v) := by
  simp only [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mulVec_transpose]

theorem outer_smul (a b : ℝ) (u v : Fin (k + 1) → ℝ) :
    Matrix.vecMulVec (a • u) (b • v) = (a * b) • Matrix.vecMulVec u v := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

end SOCScaleProof

open Matrix SDPT3.ScaleInv
open scoped BigOperators

namespace SOCScaleProof

variable {k : ℕ}

theorem jbar_inverse_vector {F : Matrix (Fin (k+1)) (Fin (k+1)) ℝ}
    {l : ℝ} (hl : 0 < l) (hm : Fᵀ * Jbar k * F = l^2 • Jbar k)
    (v : Fin (k+1) → ℝ) :
    Jbar k *ᵥ (F⁻¹ *ᵥ v) = (l^2)⁻¹ • (Fᵀ *ᵥ (Jbar k *ᵥ v)) := by
  rw [mulVec_mulVec, conformal_j_inv hl hm, smul_mulVec, ← mulVec_mulVec]

theorem hkm_form_covariance {F : Matrix (Fin (k+1)) (Fin (k+1)) ℝ}
    (hF : IsSOCAut F) (x z : Fin (k+1) → ℝ) :
    (gammaSq (F⁻¹ *ᵥ z))⁻¹ •
      (-((Fᵀ *ᵥ x) ⬝ᵥ (F⁻¹ *ᵥ z)) • Jbar k +
        vecMulVec (Fᵀ *ᵥ x) (Jbar k *ᵥ (F⁻¹ *ᵥ z)) +
        vecMulVec (Jbar k *ᵥ (F⁻¹ *ᵥ z)) (Fᵀ *ᵥ x)) =
    Fᵀ * ((gammaSq z)⁻¹ •
      (-(x ⬝ᵥ z) • Jbar k + vecMulVec x (Jbar k *ᵥ z) +
        vecMulVec (Jbar k *ᵥ z) x)) * F := by
  obtain ⟨l, hl, hm, hh⟩ := hF
  have ha : IsSOCAut F := by exact ⟨l, hl, hm, hh⟩
  rw [pairing_transport ha, gammaSq_mulVec_of_conformal (conformal_inv_metric hl hm),
    jbar_inverse_vector hl hm]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    outer_transport, hm, vecMulVec_smul, smul_vecMulVec, smul_smul]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  field_simp

theorem nt_form_covariance {F : Matrix (Fin (k+1)) (Fin (k+1)) ℝ}
    (hF : IsSOCAut F) {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    (omegaNT (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z)^2)⁻¹ •
      (-Jbar k + (2:ℝ) • vecMulVec (Jbar k *ᵥ tNT (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z))
        (Jbar k *ᵥ tNT (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z))) =
    Fᵀ * ((omegaNT x z^2)⁻¹ •
      (-Jbar k + (2:ℝ) • vecMulVec (Jbar k *ᵥ tNT x z) (Jbar k *ᵥ tNT x z))) * F := by
  obtain ⟨l, hl, hm, hh⟩ := hF
  rw [omega_transport hl hm hx hz, t_transport hl hm hx hz, mulVec_smul,
    jbar_inverse_vector hl hm, smul_smul, outer_smul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_neg, Matrix.neg_mul, outer_transport, hm, smul_smul]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul]
  field_simp

end SOCScaleProof

open Matrix SDPT3.ScaleInv
open scoped BigOperators

namespace SOCScaleProof

variable {k : ℕ}

theorem normalized_matrix_covariance (dir : Dir)
    {F : Matrix (Fin (k+1)) (Fin (k+1)) ℝ} (hF : IsSOCAut F)
    {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z) :
    (calE (Gdir dir (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z)) (F⁻¹ *ᵥ z))⁻¹ *
        calF (Gdir dir (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z)) (Fᵀ *ᵥ x) =
      Fᵀ * ((calE (Gdir dir x z) z)⁻¹ * calF (Gdir dir x z) x) * F := by
  have hxt := aut_preserves_interior (aut_transpose hF) hx
  have hzt := aut_preserves_interior (aut_inv hF) hz
  cases dir with
  | hkm =>
    simp only [Gdir, hkm_normalized_matrix _ hz, hkm_normalized_matrix _ hzt]
    exact hkm_form_covariance hF x z
  | nt =>
    simp only [Gdir, nt_normalized_matrix hx hz, nt_normalized_matrix hxt hzt]
    simpa only [ofNat_smul_eq_nsmul] using nt_form_covariance hF hx hz

theorem complementarity_transport_iff (dir : Dir)
    {F : Matrix (Fin (k+1)) (Fin (k+1)) ℝ} (hF : IsSOCAut F)
    {x z : Fin (k+1) → ℝ} (hx : socInt x) (hz : socInt z)
    (s : ℝ) (dx dz : Fin (k+1) → ℝ) :
    (calE (Gdir dir x z) z *ᵥ dx + calF (Gdir dir x z) x *ᵥ dz =
      s • e1 k - TG (Gdir dir x z) x z) ↔
    (calE (Gdir dir (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z)) (F⁻¹ *ᵥ z) *ᵥ (Fᵀ *ᵥ dx) +
      calF (Gdir dir (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z)) (Fᵀ *ᵥ x) *ᵥ (F⁻¹ *ᵥ dz) =
      s • e1 k - TG (Gdir dir (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z)) (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z)) := by
  rw [normalized_complementarity_iff dir hx hz,
    normalized_complementarity_iff dir (aut_preserves_interior (aut_transpose hF) hx)
      (aut_preserves_interior (aut_inv hF) hz), normalized_matrix_covariance dir hF hx hz]
  obtain ⟨l, hl, hm, hh⟩ := hF
  have ha : IsSOCAut F := ⟨l, hl, hm, hh⟩
  rw [inverse_jordan_transport hl hm hz]
  have he (H : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) :
      (Fᵀ * H * F) *ᵥ (F⁻¹ *ᵥ dz) = Fᵀ *ᵥ (H *ᵥ dz) := by
    simp only [mulVec_mulVec, Matrix.mul_assoc,
      F.mul_nonsing_inv (F.isUnit_iff_isUnit_det.mp (aut_isUnit ha)), Matrix.mul_one]
  rw [he, ←mulVec_add]
  rw [←mulVec_smul Fᵀ s ((gammaSq z)⁻¹ • (Jbar k *ᵥ z)), ←mulVec_sub]
  exact (Matrix.mulVec_injective_iff_isUnit.mpr (aut_isUnit (aut_transpose ha))).eq_iff.symm

theorem primal_block_transport {m : ℕ}
    {F : Matrix (Fin (k+1)) (Fin (k+1)) ℝ} (hF : IsSOCAut F)
    (A : Matrix (Fin (k+1)) (Fin m) ℝ) (v : Fin (k+1) → ℝ) :
    (F⁻¹ * A)ᵀ *ᵥ (Fᵀ *ᵥ v) = Aᵀ *ᵥ v := by
  have hi : F⁻¹ᵀ * Fᵀ = 1 := by
    rw [←transpose_mul, F.mul_nonsing_inv (F.isUnit_iff_isUnit_det.mp (aut_isUnit hF)),
      transpose_one]
  rw [transpose_mul, mulVec_mulVec, Matrix.mul_assoc, hi, Matrix.mul_one]

theorem dual_block_transport_iff {m : ℕ}
    {F : Matrix (Fin (k+1)) (Fin (k+1)) ℝ} (hF : IsSOCAut F)
    (A : Matrix (Fin (k+1)) (Fin m) ℝ) (c z dz : Fin (k+1) → ℝ) (y dy : Fin m → ℝ) :
    (A *ᵥ dy + dz = c - z - A *ᵥ y) ↔
    ((F⁻¹ * A) *ᵥ dy + F⁻¹ *ᵥ dz = F⁻¹ *ᵥ c - F⁻¹ *ᵥ z - (F⁻¹ * A) *ᵥ y) := by
  rw [←mulVec_mulVec, ←mulVec_mulVec, ←mulVec_add, ←mulVec_sub, ←mulVec_sub]
  exact (Matrix.mulVec_injective_iff_isUnit.mpr (aut_isUnit (aut_inv hF))).eq_iff.symm

theorem muSOC_transport {nq : ℕ} {d : Fin nq → ℕ}
    (F : (i : Fin nq) → Matrix (Fin (d i+1)) (Fin (d i+1)) ℝ)
    (hF : ∀ i, IsSOCAut (F i)) (x z : (i : Fin nq) → Fin (d i+1) → ℝ) :
    muSOC (fun i => (F i)ᵀ *ᵥ x i) (fun i => (F i)⁻¹ *ᵥ z i) = muSOC x z := by
  unfold muSOC
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact pairing_transport (hF i) (x i) (z i)

end SOCScaleProof

namespace SDPT3.ScaleInv

open Matrix

theorem proposition_1 {nq m : ℕ} {d : Fin nq → ℕ} (dir : Dir)
    (A : (i : Fin nq) → Matrix (Fin (d i + 1)) (Fin m) ℝ) (b : Fin m → ℝ)
    (c x : (i : Fin nq) → Fin (d i + 1) → ℝ) (y : Fin m → ℝ)
    (z : (i : Fin nq) → Fin (d i + 1) → ℝ) (σ : ℝ)
    (hx : ∀ i, socInt (x i)) (hz : ∀ i, socInt (z i))
    (Fsc : (i : Fin nq) → Matrix (Fin (d i + 1)) (Fin (d i + 1)) ℝ) (hF : ∀ i, IsSOCAut (Fsc i))
    (Δx : (i : Fin nq) → Fin (d i + 1) → ℝ) (Δy : Fin m → ℝ)
    (Δz : (i : Fin nq) → Fin (d i + 1) → ℝ) :
    IsNewtonDir dir A b c x y z σ Δx Δy Δz ↔
      IsNewtonDir dir (fun i => (Fsc i)⁻¹ * A i) b (fun i => (Fsc i)⁻¹ *ᵥ c i)
        (fun i => (Fsc i)ᵀ *ᵥ x i) y (fun i => (Fsc i)⁻¹ *ᵥ z i) σ
        (fun i => (Fsc i)ᵀ *ᵥ Δx i) Δy (fun i => (Fsc i)⁻¹ *ᵥ Δz i) := by
  unfold IsNewtonDir
  apply and_congr
  · apply forall_congr'
    intro i
    exact SOCScaleProof.dual_block_transport_iff (hF i) (A i) (c i) (z i) (Δz i) y Δy
  · apply and_congr
    · simp only [SOCScaleProof.primal_block_transport (hF _), rp]
    · apply forall_congr'
      intro i
      simp only [Rc, SOCScaleProof.muSOC_transport Fsc hF]
      exact SOCScaleProof.complementarity_transport_iff dir (hF i) (hx i) (hz i)
        (σ * muSOC x z) (Δx i) (Δz i)

end SDPT3.ScaleInv

open Matrix SDPT3.ScaleInv

theorem solution {nq m : ℕ} {d : Fin nq → ℕ} (dir : Dir)
    (A : (i : Fin nq) → Matrix (Fin (d i + 1)) (Fin m) ℝ) (b : Fin m → ℝ)
    (c x : (i : Fin nq) → Fin (d i + 1) → ℝ) (y : Fin m → ℝ)
    (z : (i : Fin nq) → Fin (d i + 1) → ℝ) (σ : ℝ)
    (hx : ∀ i, socInt (x i)) (hz : ∀ i, socInt (z i))
    (Fsc : (i : Fin nq) → Matrix (Fin (d i + 1)) (Fin (d i + 1)) ℝ) (hF : ∀ i, IsSOCAut (Fsc i))
    (Δx : (i : Fin nq) → Fin (d i + 1) → ℝ) (Δy : Fin m → ℝ)
    (Δz : (i : Fin nq) → Fin (d i + 1) → ℝ) :
    IsNewtonDir dir A b c x y z σ Δx Δy Δz ↔
      IsNewtonDir dir (fun i => (Fsc i)⁻¹ * A i) b (fun i => (Fsc i)⁻¹ *ᵥ c i)
        (fun i => (Fsc i)ᵀ *ᵥ x i) y (fun i => (Fsc i)⁻¹ *ᵥ z i) σ
        (fun i => (Fsc i)ᵀ *ᵥ Δx i) Δy (fun i => (Fsc i)⁻¹ *ᵥ Δz i) :=
  SDPT3.ScaleInv.proposition_1 dir A b c x y z σ hx hz Fsc hF Δx Δy Δz
