-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.det_flowMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:42.748422+00:00
-- url     : https://prove2.me/submissions/203b593d-c5e1-4f0e-aa4c-56777bbd7fb1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_wv_dot_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_flowMat_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
theorem _root_.solution {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s : ℂ) :
    (X.flowMat ξ τ s).det = 1 := by
  rw [flowMat_eq, Matrix.vecMulVec_eq Unit, ← Matrix.smul_mul, ← Matrix.replicateCol_smul,
    Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, wv_dot_self X hξ,
    smul_zero, add_zero]
end ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
