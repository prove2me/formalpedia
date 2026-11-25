-- Prove2me | solution 1 for PI.ET.HornW.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:22.499406+00:00
-- url     : https://prove2.me/submissions/02449fe5-5cf2-4ce5-aa08-88ff572972e4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp
import Theorems.Thm_PI_ET_HornW_unit_star_mul
import Theorems.Thm_PI_ET_HornW_conj_herm
import Theorems.Thm_PI_ET_HornW_sq_conj
import Theorems.Thm_PI_ET_HornW_emb_isom
import Theorems.Thm_PI_ET_HornW_compress_conj
import Theorems.Thm_PI_ET_HornW_psum_add
import Theorems.Thm_PI_ET_HornW_norm_det_diag_exp
import Theorems.Thm_PI_ET_HornW_prod_exp_eq
import Theorems.Thm_PI_ET_HornW_anti_exp
import Theorems.Thm_PI_ET_HornW_isUnit_conj_exp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
open scoped MatrixOrder ComplexOrder
noncomputable section
namespace PI.ET
namespace HornW
variable {n : ℕ}
private lemma key_lemma' {k : ℕ} (B : Matrix (Fin n) (Fin k) ℂ) (hB : Function.Injective B.mulVec) :
    ∃ (V : Matrix (Fin n) (Fin k) ℂ) (P : Matrix (Fin k) (Fin k) ℂ), Vᴴ * V = 1 ∧ B = V * P := by
  have hG : (Bᴴ * B).PosDef := Matrix.PosDef.conjTranspose_mul_self B hB
  have hspec := hG.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hU1 := Unitary.star_mul_self_of_mem hG.1.eigenvectorUnitary.2
  have hU2 := Unitary.mul_star_self_of_mem hG.1.eigenvectorUnitary.2
  simp only [Matrix.star_eq_conjTranspose] at hspec hU1 hU2
  have hg : ∀ i, 0 < hG.1.eigenvalues i := hG.eigenvalues_pos
  set U : Matrix (Fin k) (Fin k) ℂ := (hG.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hU
  set g := hG.1.eigenvalues with hgdef
  let s : Fin k → ℂ := fun i => (((Real.sqrt (g i))⁻¹ : ℝ) : ℂ)
  let t : Fin k → ℂ := fun i => ((Real.sqrt (g i) : ℝ) : ℂ)
  have hst : (fun i => s i * t i) = fun _ => (1 : ℂ) := by
    funext i
    simp only [s, t]
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_pos.mpr (hg i)).ne', Complex.ofReal_one]
  have hsgs : (fun i => star s i * (RCLike.ofReal ∘ g) i * s i) = fun _ => (1 : ℂ) := by
    funext i
    have hs := Real.sqrt_pos.mpr (hg i)
    have hsq : Real.sqrt (g i) * Real.sqrt (g i) = g i := Real.mul_self_sqrt (hg i).le
    simp only [s, Pi.star_apply, Function.comp_apply, Complex.star_def, Complex.conj_ofReal]
    have key : (Real.sqrt (g i))⁻¹ * g i * (Real.sqrt (g i))⁻¹ = 1 := by
      rw [mul_comm _ (g i), mul_assoc, ← mul_inv, hsq, mul_inv_cancel₀ (hg i).ne']
    show (((Real.sqrt (g i))⁻¹ : ℝ) : ℂ) * ((g i : ℝ) : ℂ) * (((Real.sqrt (g i))⁻¹ : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, key, Complex.ofReal_one]
  refine ⟨B * U * diagonal s, diagonal t * Uᴴ, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_mul]
    calc (diagonal s)ᴴ * (Uᴴ * Bᴴ) * (B * U * diagonal s)
        = (diagonal s)ᴴ * (Uᴴ * (Bᴴ * B) * U) * diagonal s := by simp only [Matrix.mul_assoc]
      _ = (diagonal s)ᴴ * ((Uᴴ * U) * diagonal (RCLike.ofReal ∘ g) * (Uᴴ * U)) * diagonal s := by
          rw [hspec]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hU1, Matrix.one_mul, Matrix.mul_one, diagonal_conjTranspose, diagonal_mul_diagonal,
            diagonal_mul_diagonal, hsgs, diagonal_one]
  · calc B = B * (U * Uᴴ) := by rw [hU2, Matrix.mul_one]
      _ = B * U * diagonal (fun i => s i * t i) * Uᴴ := by
          rw [hst, diagonal_one, Matrix.mul_one, Matrix.mul_assoc]
      _ = B * U * diagonal s * (diagonal t * Uᴴ) := by
          rw [← diagonal_mul_diagonal]; simp only [Matrix.mul_assoc]
private lemma inv_smul_apply_smul_eq_of_smul_mem (hK : KyFanDet) {k : ℕ} (hk : k ≤ n) {p : Fin n → ℝ} (hp : Antitone p)
    (hp0 : ∀ i, 0 < p i) {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin k) ℂ) (hB : Function.Injective B.mulVec) :
    ‖(Bᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * B).det‖ ≤
      (∏ i : Fin k, p (Fin.castLE hk i)) * ‖(Bᴴ * B).det‖ := by
  obtain ⟨V, P, hV, rfl⟩ := key_lemma' B hB
  have h := hK n k hk p W V hp hp0 hW hV
  have e1 : (V * P)ᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * (V * P) =
      Pᴴ * (Vᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * V) * P := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have e2 : (V * P)ᴴ * (V * P) = Pᴴ * P := by
    rw [conjTranspose_mul]
    calc Pᴴ * Vᴴ * (V * P) = Pᴴ * (Vᴴ * V) * P := by simp only [Matrix.mul_assoc]
      _ = Pᴴ * P := by rw [hV, Matrix.mul_one]
  rw [e1, e2, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, norm_mul]
  have h0 : 0 ≤ ‖Pᴴ.det‖ * ‖P.det‖ := by positivity
  calc ‖Pᴴ.det‖ * ‖(Vᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * V).det‖ * ‖P.det‖
      = ‖(Vᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * V).det‖ * (‖Pᴴ.det‖ * ‖P.det‖) := by ring
    _ ≤ (∏ i : Fin k, p (Fin.castLE hk i)) * (‖Pᴴ.det‖ * ‖P.det‖) :=
        mul_le_mul_of_nonneg_right h h0
private lemma key_lemma_3 {k : ℕ} {B : Matrix (Fin n) (Fin k) ℂ} (L : Matrix (Fin k) (Fin n) ℂ)
    (hL : L * B = 1) : Function.Injective B.mulVec := by
  intro x y hxy
  have h1 := congrArg L.mulVec hxy
  simp only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] at h1
  exact h1
end HornW
end PI.ET
end
end

set_option autoImplicit false
open Matrix Finset
open scoped MatrixOrder ComplexOrder
noncomputable section
open PI PI.ET
open PI.ET.HornW
variable {n : ℕ}
namespace PI.ET.HornW
theorem _root_.solution (hK : KyFanDet) {Wx Wy Wz : Matrix (Fin n) (Fin n) ℂ}
    (hWx : Wx ∈ unitaryGroup (Fin n) ℂ) (hWy : Wy ∈ unitaryGroup (Fin n) ℂ)
    (hWz : Wz ∈ unitaryGroup (Fin n) ℂ) {ξ η ζ : Fin n → ℝ} (hξ : Antitone ξ) (hη : Antitone η)
    (hcc : (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) *
        (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) =
      (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) *
        ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) *
          (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ)) *
        (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ))
    (k : ℕ) (hk : k ≤ n) :
    psum ζ k ≤ psum (fun i => ξ i + η i) k := by
  have hV : (Wz * emb hk)ᴴ * (Wz * emb hk) = 1 := by
    rw [conjTranspose_mul]
    calc (emb hk)ᴴ * Wzᴴ * (Wz * emb hk) = (emb hk)ᴴ * (Wzᴴ * Wz) * emb hk := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [unit_star_mul hWz, Matrix.mul_one, emb_isom]
  have hinj : Function.Injective ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk)).mulVec := by
    apply key_lemma_3 ((Wz * emb hk)ᴴ * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)⁻¹)
    calc (Wz * emb hk)ᴴ * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)⁻¹ * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk)) = (Wz * emb hk)ᴴ * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)⁻¹ * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)) * (Wz * emb hk) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul _ (isUnit_conj_exp hWy η), Matrix.mul_one, hV]
  have hA : ‖((Wz * emb hk)ᴴ * ((Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ)) * (Wz * emb hk)).det‖ = Real.exp (2 * psum ζ k) := by
    rw [sq_conj hWz, compress_conj hWz hk, norm_det_diag_exp hk]
  rw [hcc] at hA
  have e1 : (Wz * emb hk)ᴴ * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ)) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)) * (Wz * emb hk) =
      ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk))ᴴ * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ)) * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk)) := by
    rw [conjTranspose_mul (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ), conj_herm]; simp only [Matrix.mul_assoc]
  rw [e1, sq_conj hWx] at hA
  have h2 := inv_smul_apply_smul_eq_of_smul_mem hK hk (anti_exp hξ) (fun i => Real.exp_pos _) hWx _ hinj
  rw [hA] at h2
  have e2 : ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk))ᴴ * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk)) = (Wz * emb hk)ᴴ * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)) * (Wz * emb hk) := by
    rw [conjTranspose_mul (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ), conj_herm]; simp only [Matrix.mul_assoc]
  rw [e2, sq_conj hWy] at h2
  have h3 := hK n k hk _ Wy (Wz * emb hk) (anti_exp hη) (fun i => Real.exp_pos _) hWy hV
  rw [prod_exp_eq hk] at h2
  rw [prod_exp_eq hk] at h3
  have h4 : Real.exp (2 * psum ζ k) ≤ Real.exp (2 * psum ξ k) * Real.exp (2 * psum η k) :=
    h2.trans (mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le)
  rw [← Real.exp_add, Real.exp_le_exp] at h4
  rw [psum_add]
  linarith
end PI.ET.HornW
