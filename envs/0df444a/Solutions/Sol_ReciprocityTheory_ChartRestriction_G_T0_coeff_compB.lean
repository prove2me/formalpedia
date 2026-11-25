-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.coeff_compB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:47:59.764266+00:00
-- url     : https://prove2.me/submissions/c565239e-271a-4c4c-ad08-2d0d75592e9d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DecompBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SupportFreeOfBlockSubstInvariant
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (b : Fin (D + 1)) (k : ℕ) (p : MvPolynomial (TVar D N) K) (t : TVar D N →₀ ℕ) :
    coeff t (compB b k p) = if degB b t = k then coeff t p else 0 := by
  unfold compB
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : degB b t = k
  · rw [if_pos h]
    by_cases ht : t ∈ p.support
    · have hm : t ∈ p.support.filter (fun s => degB b s = k) := Finset.mem_filter.mpr ⟨ht, h⟩
      rw [if_pos hm]
    · have hn : t ∉ p.support.filter (fun s => degB b s = k) := fun h' => ht (Finset.mem_filter.mp h').1
      rw [if_neg hn]
      exact (by simpa using ht : coeff t p = 0).symm
  · have hn : t ∉ p.support.filter (fun s => degB b s = k) := fun h' => h (Finset.mem_filter.mp h').2
    rw [if_neg h, if_neg hn]
end ReciprocityTheory.ChartRestriction.G.T0
