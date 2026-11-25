-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.orthogonalProjector_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:37:32.286175+00:00
-- url     : https://prove2.me/submissions/b51f85c4-8160-4f76-993e-33a1fda6d1be

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_embeddingColumns_conjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField ComplexConjugate NumberField.ComplexEmbedding
open scoped ComplexOrder Kronecker
section Gram
variable {K : Type} [Field K] [NumberField K] {r k m : ℕ}
private lemma map_star_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A⁻¹.map (starRingEnd ℂ) = (A.map (starRingEnd ℂ))⁻¹ := by
  have h : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map (starRingEnd ℂ) = Mᴴᵀ := by
    intro M
    ext i j
    simp [conjTranspose_apply]
  rw [h, h, ← transpose_nonsing_inv, conjTranspose_nonsing_inv]
end Gram
section GramDet
variable {K : Type} [Field K] [NumberField K] {r k m : ℕ}
end GramDet
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField ComplexConjugate NumberField.ComplexEmbedding
open scoped ComplexOrder Kronecker
variable {K : Type} [Field K] [NumberField K] {r k m : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    hPm (conjugate σ) b = (hPm σ b).map (starRingEnd ℂ) := by
  unfold hPm
  rw [embeddingColumns_conjugate σ b]
  have h1 : ((hBm σ b).map (starRingEnd ℂ))ᴴ = (hBm σ b)ᴴ.map (starRingEnd ℂ) := by
    ext i j
    simp [conjTranspose_apply]
  rw [h1, ← Matrix.map_mul, ← map_star_inv, Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul]
end ReciprocityTheory.ChartRestriction.G.T0
