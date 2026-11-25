-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sc_det_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:05:57.936794+00:00
-- url     : https://prove2.me/submissions/4549e5cc-38e7-426c-9d25-a2386d19be2b

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.MultiplicativeHeights
open Matrix
open scoped ComplexOrder
private theorem one_lt_re_det_one_add_and_im_eq_zero_of_posDef {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {Q : Matrix m m ℂ} (hQ : Q.PosDef) : 1 < ((1 + Q).det).re ∧ ((1 + Q).det).im = 0 := by
  have hsp := hQ.isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hsp
  obtain ⟨U, hU⟩ : ∃ U : Matrix m m ℂ, U = (hQ.isHermitian.eigenvectorUnitary : Matrix m m ℂ) :=
    ⟨_, rfl⟩
  have hUU : U * star U = 1 := by
    rw [hU]
    exact Matrix.mem_unitaryGroup_iff.mp hQ.isHermitian.eigenvectorUnitary.2
  obtain ⟨d, hd⟩ : ∃ d : m → ℝ, d = hQ.isHermitian.eigenvalues := ⟨_, rfl⟩
  have hdpos : ∀ i, 0 < d i := fun i => by rw [hd]; exact hQ.eigenvalues_pos i
  rw [← hU, ← hd] at hsp

  have h1 : 1 + Q = U * (1 + diagonal (RCLike.ofReal ∘ d)) * star U := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU, ← hsp]
  have hdet : (1 + Q).det = ((∏ i, (1 + d i) : ℝ) : ℂ) := by
    rw [h1, det_mul, det_mul, mul_comm U.det, mul_assoc, ← det_mul, hUU, det_one, mul_one,
      ← diagonal_one, diagonal_add, det_diagonal]
    push_cast
    rfl
  rw [hdet, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  calc (1 : ℝ) = ∏ _i : m, (1 : ℝ) := by simp
    _ < ∏ i, (1 + d i) := Finset.prod_lt_prod_of_nonempty (fun _ _ => one_pos)
        (fun i _ => by linarith [hdpos i]) Finset.univ_nonempty
end ReciprocityTheory.MultiplicativeHeights
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {E S : Matrix m m ℂ} (hE : E.PosDef) (hSE : (S - E).PosDef) :
    0 < (E.det).re ∧ (E.det).re < (S.det).re := by
  have hEdet := hE.det_pos
  rw [Complex.lt_def] at hEdet
  simp only [Complex.zero_re, Complex.zero_im] at hEdet

  have hsp := hE.isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hsp
  obtain ⟨U, hU⟩ : ∃ U : Matrix m m ℂ, U = (hE.isHermitian.eigenvectorUnitary : Matrix m m ℂ) :=
    ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : m → ℝ, d = hE.isHermitian.eigenvalues := ⟨_, rfl⟩
  have hdpos : ∀ i, 0 < d i := fun i => by rw [hd]; exact hE.eigenvalues_pos i
  rw [← hU, ← hd] at hsp
  obtain ⟨Dh, hDh⟩ : ∃ Dh : Matrix m m ℂ, Dh = diagonal (fun i => ((Real.sqrt (d i) : ℝ) : ℂ)) :=
    ⟨_, rfl⟩
  have hDD : Dh * Dh = diagonal (RCLike.ofReal ∘ d) := by
    rw [hDh, diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hdpos i).le]
    rfl
  have hDhH : Dhᴴ = Dh := by
    rw [hDh, diagonal_conjTranspose]
    congr 1
    funext i
    simp
  obtain ⟨B, hB⟩ : ∃ B : Matrix m m ℂ, B = Dh * star U := ⟨_, rfl⟩
  have hBB : Bᴴ * B = E := by
    rw [hB, conjTranspose_mul, hDhH, hsp, ← hDD]
    simp only [Matrix.mul_assoc, star_eq_conjTranspose, conjTranspose_conjTranspose]
  have hBdet : B.det ≠ 0 := by
    intro h0
    have h1 : E.det = 0 := by rw [← hBB, det_mul, h0, mul_zero]
    rw [h1] at hEdet
    simp at hEdet
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hinj : Function.Injective (B⁻¹).mulVec := by
    intro v w hvw
    have h := congrArg (fun z => B *ᵥ z) hvw
    simpa [mulVec_mulVec, mul_nonsing_inv B hBu] using h
  have hQ : ((B⁻¹)ᴴ * (S - E) * B⁻¹).PosDef := hSE.conjTranspose_mul_mul_same hinj
  have hS : Bᴴ * (1 + (B⁻¹)ᴴ * (S - E) * B⁻¹) * B = S := by
    have hinv : B⁻¹ * B = 1 := nonsing_inv_mul B hBu
    have e1 : Bᴴ * ((B⁻¹)ᴴ * (S - E) * B⁻¹) * B = (B⁻¹ * B)ᴴ * (S - E) * (B⁻¹ * B) := by
      rw [conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hBB, e1, hinv, conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one]
    abel
  generalize (B⁻¹)ᴴ * (S - E) * B⁻¹ = Q at hQ hS
  have hdet : S.det = (1 + Q).det * E.det := by
    rw [← hS, det_mul, det_mul, ← hBB, det_mul]
    ring
  obtain ⟨hq1, hq2⟩ := one_lt_re_det_one_add_and_im_eq_zero_of_posDef hQ
  refine ⟨hEdet.1, ?_⟩
  rw [hdet, Complex.mul_re, hq2, ← hEdet.2]
  nlinarith [hEdet.1, hq1]
end ReciprocityTheory.MultiplicativeHeights
