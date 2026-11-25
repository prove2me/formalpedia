-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DegAdd.log_det_gram_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:11:04.678113+00:00
-- url     : https://prove2.me/submissions/c8ca7ada-d849-40e1-aa72-5c50deafa305

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_EmbMatMulVecInjective
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_gramC_posDef
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_gramC_append_blocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DegAdd
open Matrix NumberField
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.DegAdd
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (c : Fin m → Fin r → K) (hH : H.PosDef) (hb : LinearIndependent K b)
    (h : LinearIndependent K (Fin.append b c)) :
    Real.log (gramC H σ (Fin.append b c)).det.re =
      Real.log (gramC H σ b).det.re + Real.log (quotGramC H σ b c).det.re := by
  have hG := (gramC_posDef H σ hH h).det_pos
  have hGb := (gramC_posDef H σ hH hb).det_pos
  have : Invertible (gramC H σ b) := (gramC_posDef H σ hH hb).isUnit.invertible
  have hdet : (gramC H σ (Fin.append b c)).det =
      (gramC H σ b).det * (quotGramC H σ b c).det := by
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv (gramC H σ (Fin.append b c)),
      gramC_append_blocks, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    rfl
  rw [hdet] at hG ⊢
  rw [Complex.pos_iff] at hG hGb
  have hre : ((gramC H σ b).det * (quotGramC H σ b c).det).re =
      (gramC H σ b).det.re * (quotGramC H σ b c).det.re := by
    simp [Complex.mul_re, ← hGb.2]
  have hy : 0 < (quotGramC H σ b c).det.re := by
    rw [hre] at hG
    exact (pos_iff_pos_of_mul_pos hG.1).mp hGb.1
  rw [hre, Real.log_mul hGb.1.ne' hy.ne']
end ReciprocityTheory.MultiplicativeHeights.DegAdd
