-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.flowMat_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:51:28.674749+00:00
-- url     : https://prove2.me/submissions/861fd54c-8202-435a-9351-fbf8f6db13d6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_wv_dot
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
theorem _root_.solution (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (v : Fin r → ℂ) :
    X.flowMat ξ τ s *ᵥ v = v + ((-(I * X.c τ * s)) * hermC τ.1 X.Gm v (Data.emb τ.1 ξ)) •
      Data.emb τ.1 ξ := by
  rw [flowMat_eq, Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  ext a
  rw [← wv_dot X ξ τ v]
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
