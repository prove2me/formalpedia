-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.hC_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:04.560141+00:00
-- url     : https://prove2.me/submissions/c7c4114d-6383-42f8-bb7f-56491c968c25

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
variable {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → ℂ) :
    hermC τ G v u = conj (hermC τ G u v) := by
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← emb_cc, hG]
  ring
end ReciprocityTheory.ChartRestriction.G.FD
