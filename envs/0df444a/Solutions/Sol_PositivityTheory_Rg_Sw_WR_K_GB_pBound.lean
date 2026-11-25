-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:31.022268+00:00
-- url     : https://prove2.me/submissions/cc43078c-ce4b-4537-a361-9ebbc8f8729c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_cd_det
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_cd_affine
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_cdOn_inv
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_cdOn_detInv
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_cdOn_eval
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_eval_bound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pbwt_pos
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_one_le_wt
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pbwt_sq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_inv
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_det_le
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_norm_det_unitary
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_conj
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_conj_inv
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_conj_unit
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_conj_entry
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_cd_oneSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution : PBound := by
  intro n s hs p q R
  have ha : Complex.I * s = Complex.I ∨ Complex.I * s = -Complex.I := by rcases hs with rfl | rfl <;> simp
  have ham : -(Complex.I * s) = Complex.I ∨ -(Complex.I * s) = -Complex.I := by
    rcases ha with h | h <;> simp [h]
  have hplus : ∀ b : Mc n, (1 + (Complex.I * s) • b) = 1 - (-(Complex.I * s)) • b := by
    intro b; rw [neg_smul, sub_neg_eq_add]
  have he1 : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => (1 - (Complex.I * s) • b) i j) :=
    fun i j => pb_cd_oneSub _ i j
  have he2 : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => (1 + (Complex.I * s) • b) i j) := fun i j => by
    simpa [one_mul] using pb_cd_affine (Complex.I * s) 1 i j
  have hd1 := pb_cd_det he1
  have hd2 := pb_cd_det he2
  have hopen : IsOpen (Ugood (n := n) s) := by
    have e : Ugood (n := n) s = {b | (1 - (Complex.I * s) • b).det ≠ 0} ∩ {b | (1 + (Complex.I * s) • b).det ≠ 0} := by
      ext b; simp [Ugood, isUnit_iff_ne_zero]
    rw [e]
    exact (isOpen_ne_fun hd1.continuous continuous_const).inter (isOpen_ne_fun hd2.continuous continuous_const)
  have hne1 : ∀ b ∈ Ugood (n := n) s, (1 - (Complex.I * s) • b).det ≠ 0 := fun b hb => isUnit_iff_ne_zero.1 hb.1
  have hne2 : ∀ b ∈ Ugood (n := n) s, (1 + (Complex.I * s) • b).det ≠ 0 := fun b hb => isUnit_iff_ne_zero.1 hb.2
  have hsmooth : ContDiffOn ℂ (⊤ : ℕ∞) (Fr s p q R) (Ugood s) := by
    have hv : ∀ k : Bool × Fin n × Fin n, ContDiffOn ℂ (⊤ : ℕ∞) (fun b : Mc n => if k.1 then
        (1 + (Complex.I * s) • b)⁻¹ k.2.1 k.2.2 else (1 - (Complex.I * s) • b)⁻¹ k.2.1 k.2.2) (Ugood s) := by
      rintro ⟨t, i, j⟩
      cases t
      · simpa using pb_cdOn_inv he1 _ hne1 i j
      · simpa using pb_cdOn_inv he2 _ hne2 i j
    exact (((pb_cdOn_detInv he1 _ hne1).pow p).mul ((pb_cdOn_detInv he2 _ hne2).pow q)).mul
      (pb_cdOn_eval R _ _ hv)
  obtain ⟨CR, hCR⟩ := pb_eval_bound R ((n : ℝ) * ((n : ℝ) * 3))
  refine ⟨hopen, hsmooth, 1 / (4 * (n : ℝ) + 4),
    ((Nat.factorial n : ℝ) * 3 ^ n) ^ p * ((Nat.factorial n : ℝ) * 3 ^ n) ^ q * CR, by positivity, ?_⟩
  intro k hk lam b hb
  set K1 : ℝ := (Nat.factorial n : ℝ) * 3 ^ n with hK1def
  have hc₀ : (n : ℝ) * (1 / (4 * (n : ℝ) + 4)) ≤ 1 / 4 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
  have hb' : ∀ i j, ‖b i j - Matrix.diagonal (fun i => (lam i : ℂ)) i j‖ ≤
      (1 / (4 * (n : ℝ) + 4)) * (pbwt lam i * pbwt lam j) := by
    intro i j
    have := hb i j
    simpa [pbwt, Real.sqrt_mul (by positivity : (0:ℝ) ≤ 1 + |lam i|)] using this
  obtain ⟨hu1, hY1⟩ := pb_inv _ ha lam _ (by positivity) hc₀ b hb'
  obtain ⟨hu2, hY2⟩ := pb_inv _ ham lam _ (by positivity) hc₀ b hb'
  have c1 : 1 - (Complex.I * s) • (k * b * kᴴ) = k * (1 - (Complex.I * s) • b) * kᴴ := pb_conj _ k b hk
  have c2 : 1 + (Complex.I * s) • (k * b * kᴴ) = k * (1 - (-(Complex.I * s)) • b) * kᴴ := by
    rw [hplus]; exact pb_conj _ k b hk
  refine ⟨⟨by rw [c1]; exact pb_conj_unit _ k hk hu1, by rw [c2]; exact pb_conj_unit _ k hk hu2⟩, ?_⟩
  have i1 : (1 - (Complex.I * s) • (k * b * kᴴ))⁻¹ = k * (1 - (Complex.I * s) • b)⁻¹ * kᴴ := by
    rw [c1]; exact pb_conj_inv _ k hk hu1
  have i2 : (1 + (Complex.I * s) • (k * b * kᴴ))⁻¹ = k * (1 - (-(Complex.I * s)) • b)⁻¹ * kᴴ := by
    rw [c2]; exact pb_conj_inv _ k hk hu2
  set P : ℝ := ∏ i, (1 + |lam i|) with hPdef
  have hP : 0 < P := Finset.prod_pos fun i _ => by positivity
  have hPw : (∏ i, pbwt lam i) ^ 2 = P := by
    rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun i _ => pbwt_sq lam i
  have hdetY : ∀ (Y : Mc n), (∀ i j, ‖Y i j‖ ≤ 3 / (pbwt lam i * pbwt lam j)) → ‖Y.det‖ ≤ K1 / P := by
    intro Y hYb
    have := pb_det_le Y (pbwt lam) 3 hYb
    rw [hPw] at this
    calc ‖Y.det‖ ≤ (Nat.factorial n : ℝ) * (3 ^ n / P) := this
      _ = K1 / P := by rw [hK1def]; ring
  have hdc : ∀ (Y : Mc n), ‖(k * Y * kᴴ).det‖ = ‖Y.det‖ := by
    intro Y
    rw [Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, pb_norm_det_unitary k hk, Matrix.det_conjTranspose,
      norm_star, pb_norm_det_unitary k hk, one_mul, mul_one]
  have hdet1 : ‖(1 - (Complex.I * s) • (k * b * kᴴ))⁻¹.det‖ ≤ K1 / P := by
    rw [i1, hdc]; exact hdetY _ hY1
  have hdet2 : ‖(1 + (Complex.I * s) • (k * b * kᴴ))⁻¹.det‖ ≤ K1 / P := by
    rw [i2, hdc]; exact hdetY _ hY2
  have hent : ∀ (Y : Mc n), (∀ i j, ‖Y i j‖ ≤ 3 / (pbwt lam i * pbwt lam j)) →
      ∀ i j, ‖(k * Y * kᴴ) i j‖ ≤ (n : ℝ) * ((n : ℝ) * 3) := by
    intro Y hYb i j
    refine pb_conj_entry Y k hk 3 (fun a c => (hYb a c).trans ?_) i j
    rw [div_le_iff₀ (mul_pos (pbwt_pos lam a) (pbwt_pos lam c))]
    nlinarith [pb_one_le_wt lam a, pb_one_le_wt lam c]
  have hev : ‖MvPolynomial.eval (fun k' : Bool × Fin n × Fin n => if k'.1 then
      (1 + (Complex.I * s) • (k * b * kᴴ))⁻¹ k'.2.1 k'.2.2 else (1 - (Complex.I * s) • (k * b * kᴴ))⁻¹ k'.2.1 k'.2.2) R‖
      ≤ CR := by
    apply hCR
    rintro ⟨t, i, j⟩
    cases t
    · simp only [Bool.false_eq_true, if_false]; rw [i1]; exact hent _ hY1 i j
    · simp only [if_true]; rw [i2]; exact hent _ hY2 i j
  have hrp : P ^ (-((p + q : ℕ) : ℝ)) = (P ^ (p + q))⁻¹ := by
    rw [Real.rpow_neg hP.le, Real.rpow_natCast]
  show ‖(1 - (Complex.I * s) • (k * b * kᴴ))⁻¹.det ^ p * (1 + (Complex.I * s) • (k * b * kᴴ))⁻¹.det ^ q *
      MvPolynomial.eval (fun k' : Bool × Fin n × Fin n => if k'.1 then
      (1 + (Complex.I * s) • (k * b * kᴴ))⁻¹ k'.2.1 k'.2.2 else (1 - (Complex.I * s) • (k * b * kᴴ))⁻¹ k'.2.1 k'.2.2) R‖
      ≤ K1 ^ p * K1 ^ q * CR * P ^ (-((p + q : ℕ) : ℝ))
  rw [hrp, norm_mul, norm_mul, norm_pow, norm_pow]
  have hK1 : 0 ≤ K1 := by positivity
  calc _ ≤ (K1 / P) ^ p * (K1 / P) ^ q * CR := by gcongr
    _ = K1 ^ p * K1 ^ q * CR * (P ^ (p + q))⁻¹ := by
      rw [div_pow, div_pow, pow_add, mul_inv, div_eq_mul_inv, div_eq_mul_inv]; ring
end PositivityTheory.Rg.Sw.WR.K.GB
