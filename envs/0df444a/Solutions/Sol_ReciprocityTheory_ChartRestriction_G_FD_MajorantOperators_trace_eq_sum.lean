-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.trace_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:57.06904+00:00
-- url     : https://prove2.me/submissions/540a146c-c6dd-4b12-98e8-d107fb6d64c6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalLatticeDecomposition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators
theorem _root_.solution (a : E) :
    ((Algebra.trace ℚ E a : ℚ) : ℝ) = ∑ τ : X.Ψ, 2 * (τ.1 a).re := by
  classical

  have h1 : ((Algebra.trace ℚ E a : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ a := by
    rw [show ((Algebra.trace ℚ E a : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E a) from (eq_ratCast _ _).symm,
      trace_eq_sum_embeddings ℂ]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)

  have h2 : ∑ σ ∈ X.Ψᶜ, σ a = ∑ σ ∈ X.Ψ, conj (σ a) := by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      rw [Finset.mem_compl] at hσ
      rw [X.cmType, ComplexEmbedding.involutive_conjugate E σ]
      exact hσ
    · intro σ hσ
      rw [Finset.mem_compl]
      exact (X.cmType σ).mp hσ
    · intro σ _
      exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _
      exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _
      rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
  apply Complex.ofReal_injective
  push_cast
  rw [h1, ← Finset.sum_add_sum_compl X.Ψ (fun σ => σ a), h2, ← Finset.sum_add_distrib,
    ← Finset.sum_coe_sort X.Ψ]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Complex.add_conj]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators
