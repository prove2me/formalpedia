-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.wv_dot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:37.629569+00:00
-- url     : https://prove2.me/submissions/8adebe8e-d6d6-4105-9760-d8d06d97afbb

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
theorem _root_.solution (ξ : Fin r → E) (τ : X.Ψ) (v : Fin r → ℂ) :
    wv X ξ τ ⬝ᵥ v = hermC τ.1 X.Gm v (Data.emb τ.1 ξ) := by
  simp only [dotProduct, wv, hermC, Data.emb, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
