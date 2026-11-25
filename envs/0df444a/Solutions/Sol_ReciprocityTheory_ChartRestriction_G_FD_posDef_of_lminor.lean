-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.posDef_of_lminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:11:55.173842+00:00
-- url     : https://prove2.me/submissions/b207b22a-eb7b-4a5e-8904-0a2f67b9ed19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_posDef_of_posSemidef_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_lminor_submatrix_castSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_lminor_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.IsHermitian →
    (∀ i : Fin (n + 1), 0 < (lminor A i).re) → A.PosDef
  | 0, A, hA, _ => ⟨hA, fun x hx => absurd (Subsingleton.elim x 0) hx⟩
  | n + 1, A, hA, hm => by
    set A' := A.submatrix Fin.castSucc Fin.castSucc with hA'def
    have hA'h : A'.IsHermitian := hA.submatrix _
    have hA' : A'.PosDef := solution n A' hA'h (fun i => by
      rw [lminor_submatrix_castSucc]; exact hm _)
    let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
    set B := (A.submatrix e e).toBlocks₁₂ with hB
    set D := (A.submatrix e e).toBlocks₂₂ with hD
    have h11 : (A.submatrix e e).toBlocks₁₁ = A' := by
      ext i j; simp [Matrix.toBlocks₁₁, A', e]; rfl
    have h21 : (A.submatrix e e).toBlocks₂₁ = Bᴴ := by
      ext i j
      simp only [hB, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.conjTranspose_apply, Matrix.of_apply,
        Matrix.submatrix_apply]
      exact (hA.apply _ _).symm
    have hblk : A.submatrix e e = fromBlocks A' B Bᴴ D := by
      rw [← h11, ← h21]; exact (fromBlocks_toBlocks _).symm
    let _ : Invertible A' := hA'.isUnit.invertible
    set S := D - Bᴴ * A'⁻¹ * B with hS
    have hdet : A.det = A'.det * S.det := by
      rw [← det_submatrix_equiv_self e A, hblk, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
    have hreal : ∀ {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}, M.IsHermitian → (M.det.im = 0) := by
      intro M hM
      have h := congrArg Matrix.det hM
      rw [det_conjTranspose] at h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hAd : A.det = ((A.det.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hreal hA])
    have hApos : 0 < A.det.re := by rw [← lminor_last]; exact hm _
    have hA'pos : 0 < A'.det := hA'.det_pos
    have hS00 : S.det = A.det / A'.det := by
      rw [hdet]; field_simp [hA'pos.ne']
    have hSpos : 0 < S.det := by
      rw [hS00, hAd]
      exact div_pos (by exact_mod_cast hApos) hA'pos
    have hSdet : S.det = S 0 0 := Matrix.det_unique S
    have hSh : S.IsHermitian := by
      ext i j
      rw [show i = 0 from Subsingleton.elim _ _, show j = 0 from Subsingleton.elim _ _]
      simp only [Matrix.conjTranspose_apply]
      rw [← hSdet, Complex.star_def, Complex.conj_eq_iff_im]
      exact (Complex.pos_iff.mp hSpos).2.symm
    have hSpsd : S.PosSemidef := by
      rw [posSemidef_iff_dotProduct_mulVec]
      refine ⟨hSh, fun x => ?_⟩
      simp only [dotProduct, mulVec, Fin.sum_univ_one, Pi.star_apply]
      have : star (x 0) * (S 0 0 * x 0) = S 0 0 * (star (x 0) * x 0) := by ring
      rw [this, ← hSdet]
      exact mul_nonneg hSpos.le (star_mul_self_nonneg _)
    have hMpsd : (A.submatrix e e).PosSemidef := by
      rw [hblk]; exact (PosDef.fromBlocks₁₁ B D hA').mpr hSpsd
    have hApsd : A.PosSemidef := (posSemidef_submatrix_equiv e).mp hMpsd
    exact posDef_of_posSemidef_det hApsd (fun h => by simp [h] at hApos)
end ReciprocityTheory.ChartRestriction.G.FD
