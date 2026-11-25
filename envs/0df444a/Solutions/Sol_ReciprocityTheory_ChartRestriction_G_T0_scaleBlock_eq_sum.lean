-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.scaleBlock_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:03:07.983026+00:00
-- url     : https://prove2.me/submissions/edae03a9-61dd-4caa-9fdf-8fc47824125c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DecompBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SupportFreeOfBlockSubstInvariant
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scaleEquiv_monomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply


section
namespace ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
section Comp
variable {K : Type} [Field K] {D N : ℕ}
private lemma sum_filter_block_eq_degB {D N : ℕ} (b : Fin (D + 1)) (s : TVar D N →₀ ℕ) :
    ∑ v ∈ Finset.univ.filter (fun v : TVar D N => v.1 = b), s v = degB b s := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp [degB]
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ b) h
end Comp
section Pres
variable {K : Type} [Field K] [CharZero K] {D N : ℕ}
end Pres
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (b : Fin (D + 1)) (u : Kˣ) (p : MvPolynomial (TVar D N) K) (M : ℕ)
    (hM : ∀ s ∈ p.support, degB b s < M) :
    sigP b u p = ∑ k ∈ Finset.range M, C ((u : K) ^ k) * compB b k p := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  simp only [sigP, scaleEquiv_monomial, sum_filter_block_eq_degB]
  simp only [compB, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (fun s hs => Finset.mem_range.mpr (hM s hs))]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s hs => ?_
  rw [(Finset.mem_filter.mp hs).2]
end ReciprocityTheory.ChartRestriction.G.T0
