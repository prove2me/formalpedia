-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.quotientGram_eq_projector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:43:28.240978+00:00
-- url     : https://prove2.me/submissions/f320a223-5399-47fa-85f1-25bf7b6ba51a

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulEmbeddingColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthogonalProjector_conjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthogonalProjector_mul_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_crossGram_eq_embeddingColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gramMatrix_eq_embeddingColumns

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {m : ℕ} (c : Fin m → Fin r → K) (i j : Fin m) :
    ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c i j =
      star (hPm σ b *ᵥ fun l => σ (c i l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (c j l)) := by
  have key : ∀ (M : Matrix (Fin r) (Fin r) ℂ) (C : Matrix (Fin r) (Fin m) ℂ) (i j : Fin m),
      (Cᴴ * M * C) i j = star (fun l => C l i) ⬝ᵥ (M *ᵥ fun l => C l j) := by
    intro M C i j
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.star_apply,
      Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  have hq : ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c = (hBm σ c)ᴴ * hPm σ b * hBm σ c := by
    unfold ReciprocityTheory.MultiplicativeHeights.quotGramC
    rw [gramMatrix_eq_embeddingColumns, gramMatrix_eq_embeddingColumns, crossGram_eq_embeddingColumns, crossGram_eq_embeddingColumns]
    unfold hPm
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hq, key, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, orthogonalProjector_conjTranspose,
    orthogonalProjector_mul_self σ hb]
  rfl
end ReciprocityTheory.ChartRestriction.G.T0
