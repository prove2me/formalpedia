-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sc_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:31:15.38931+00:00
-- url     : https://prove2.me/submissions/714e71a8-9b75-4289-805b-754c14cd2161

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_det_lt
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_contr_posDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r k m : Type*} [Fintype r] [Fintype k] [Fintype m] [DecidableEq k]
    [DecidableEq m] [Nonempty m] {H M : Matrix r r ℂ} (hH : H.PosDef)
    (hM : ∀ u : r → ℂ, u ≠ 0 → (star (M *ᵥ u) ⬝ᵥ (H *ᵥ (M *ᵥ u))).re < (star u ⬝ᵥ (H *ᵥ u)).re)
    (Bm : Matrix r k ℂ) (Cm : Matrix r m ℂ) (hW : Function.Injective (fromCols Bm Cm).mulVec)
    (hMB : M * Bm = 0) (hMC : Function.Injective (M * Cm).mulVec) :
    0 < ((M * Cm)ᴴ * H * (M * Cm)).det.re ∧ ((M * Cm)ᴴ * H * (M * Cm)).det.re <
      (Cmᴴ * H * Cm - (Cmᴴ * H * Bm) * (Bmᴴ * H * Bm)⁻¹ * (Bmᴴ * H * Cm)).det.re := by
  have hBinj : Function.Injective Bm.mulVec := by
    intro v w hvw
    have h : (fromCols Bm Cm) *ᵥ (Sum.elim v 0) = (fromCols Bm Cm) *ᵥ (Sum.elim w 0) := by
      rw [fromCols_mulVec, fromCols_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inl,
        Sum.elim_comp_inr, Sum.elim_comp_inr, hvw]
    have h' := hW h
    funext i
    exact congrFun h' (Sum.inl i)
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix k k ℂ, A = Bmᴴ * H * Bm := ⟨_, rfl⟩
  have hA : A.PosDef := by rw [hAdef]; exact hH.conjTranspose_mul_mul_same hBinj
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  obtain ⟨G, hG⟩ : ∃ G : Matrix k m ℂ, G = A⁻¹ * (Bmᴴ * H * Cm) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix r m ℂ, N = Cm - Bm * G := ⟨_, rfl⟩
  have hNW : ∀ v, N *ᵥ v = (fromCols Bm Cm) *ᵥ (Sum.elim (-(G *ᵥ v)) v) := by
    intro v
    rw [hN, fromCols_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, sub_mulVec, mulVec_neg,
      mulVec_mulVec]
    abel
  have hNinj : Function.Injective N.mulVec := by
    intro v w hvw
    rw [hNW, hNW] at hvw
    have h := hW hvw
    funext i
    exact congrFun h (Sum.inr i)
  have hGA : A * G = Bmᴴ * H * Cm := by
    rw [hG, ← Matrix.mul_assoc, mul_nonsing_inv A hAu, Matrix.one_mul]
  have hx : Gᴴ * (Bmᴴ * (H * (Bm * G))) = Gᴴ * (Bmᴴ * (H * Cm)) := by
    have h := congrArg (fun X => Gᴴ * X) hGA
    simpa [hAdef, Matrix.mul_assoc] using h

  have key : Nᴴ * H * N = Cmᴴ * H * Cm - Cmᴴ * H * Bm * G := by
    rw [hN, conjTranspose_sub, conjTranspose_mul]
    simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub]
    rw [hx]
    abel
  have hT : Cmᴴ * H * Cm - (Cmᴴ * H * Bm) * (Bmᴴ * H * Bm)⁻¹ * (Bmᴴ * H * Cm) =
      Cmᴴ * H * Cm - Cmᴴ * H * Bm * G := by
    rw [hG, ← hAdef]
    simp only [Matrix.mul_assoc]
  have hMN : M * N = M * Cm := by
    rw [hN, Matrix.mul_sub, ← Matrix.mul_assoc, hMB, Matrix.zero_mul, sub_zero]
  have hdiff : (Cmᴴ * H * Cm - (Cmᴴ * H * Bm) * (Bmᴴ * H * Bm)⁻¹ * (Bmᴴ * H * Cm)) -
      (M * Cm)ᴴ * H * (M * Cm) = Nᴴ * (H - Mᴴ * H * M) * N := by
    rw [hT, ← key, ← hMN, conjTranspose_mul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have hpd := (sc_contr_posDef hH hM).conjTranspose_mul_mul_same hNinj
  refine sc_det_lt (hH.conjTranspose_mul_mul_same hMC) ?_
  rw [hdiff]
  exact hpd
end ReciprocityTheory.MultiplicativeHeights
