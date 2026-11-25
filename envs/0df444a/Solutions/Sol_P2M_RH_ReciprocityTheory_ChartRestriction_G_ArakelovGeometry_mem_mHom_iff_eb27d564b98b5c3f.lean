-- Prove2me | solution 1 for P2M_RH_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mem_mHom_iff_eb27d564b98b5c3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:45.747592+00:00
-- url     : https://prove2.me/submissions/c87d8b50-06c7-4946-a19c-7f0c9605f5ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqSumMultihomogeneousComponents
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_iff_coeff

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (s : MRing ι) (a : K → ℕ) : s ∈ mHom ι a ↔ IsMultiHomog s a := by
  constructor
  · intro hs
    induction hs using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => intro m hm; simp at hm
    | add x y _ _ hx hy =>
      rw [isMultiHomog_iff_coeff] at hx hy ⊢
      intro m hm
      rw [coeff_add] at hm
      by_cases h0 : coeff m x = 0
      · rw [h0, zero_add] at hm
        exact hy m hm
      · exact hx m h0
    | smul n x _ hx =>
      rw [isMultiHomog_iff_coeff] at hx ⊢
      intro m hm
      rw [coeff_smul] at hm
      exact hx m (fun h0 => hm (by rw [h0, smul_zero]))
  · intro hs
    exact Submodule.subset_span hs
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
