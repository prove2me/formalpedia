-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.flowMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:10.222508+00:00
-- url     : https://prove2.me/submissions/55189dda-590f-4ba1-8939-f373c4d58955

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs

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
theorem _root_.solution (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) :
    X.flowMat ξ τ s = 1 + (-(I * X.c τ * s)) • vecMulVec (Data.emb τ.1 ξ) (wv X ξ τ) := by
  ext a b
  simp only [Data.flowMat, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    vecMulVec_apply, wv, Data.emb, smul_eq_mul]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
