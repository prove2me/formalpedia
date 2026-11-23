-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.flowMat_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:25.147894+00:00
-- url     : https://prove2.me/submissions/62401e4c-2c6c-4e85-8c57-4cc3f455bcac

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (v : Fin r → ℂ) :
    Matrix.mulVec (X.flowMat ξ τ s) v =
      v + (-(I * X.c τ * s) * hermC τ.1 X.Gm v (emb τ.1 ξ)) • emb τ.1 ξ := by
  funext a
  simp only [flowMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, hermC, emb, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.FD.Data
