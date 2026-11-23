-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices.Mmat_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:59.857389+00:00
-- url     : https://prove2.me/submissions/7603cb10-545b-4578-8799-810c72874c3f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpSpanRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (p : ℕ) (f g : Fin n → Fin r → ℂ)
namespace ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices
theorem _root_.solution (v : Fin r → ℂ) :
    Mmat τ G p f g *ᵥ v = v + ∑ k, (eps p k * hermC τ G v (f k)) • (g k - f k) := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Mmat, Matrix.of_apply, add_mul, Finset.sum_add_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, hermC, Pi.sub_apply]
  congr 1
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun m _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices
