-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.mk_xpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:47.019717+00:00
-- url     : https://prove2.me/submissions/5781cbec-c569-4977-a9a4-99d979e1a341

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (W : Ideal (MRing ι)) (i : ∀ k, ι k) (e : K → ℕ) :
    Ideal.Quotient.mk (dehomI W i) (xpow i e) = 1 := by
  unfold xpow
  rw [map_prod]
  apply Finset.prod_eq_one
  intro k _
  have hk : Ideal.Quotient.mk (dehomI W i) (X ⟨k, i k⟩) = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk (dehomI W i)), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
  rw [map_pow, hk, one_pow]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
