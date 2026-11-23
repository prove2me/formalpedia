-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:41.128809+00:00
-- url     : https://prove2.me/submissions/6d9067ad-766b-41e7-b5f6-2d52a53946b2

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_attained_at_coeff
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_le_of_coeff_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory NumberField
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {σ : Type*}
    (f : MvPolynomial σ K) (hf : f ≠ 0) :
    (Function.support fun w : FinitePlace K => Real.log (gaussAbs w f)).Finite := by
  have hfin : (⋃ s ∈ f.support, Function.mulSupport fun w : FinitePlace K => w (f.coeff s)).Finite :=
    Set.Finite.biUnion f.support.finite_toSet fun s hs =>
      FinitePlace.hasFiniteMulSupport (MvPolynomial.mem_support_iff.1 hs)
  refine hfin.subset fun w hw => ?_
  by_contra hnot
  apply hw
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hnot
  have h1 : gaussAbs w f = 1 := by
    apply le_antisymm
    · refine gauss_abs_le_of_coeff_le w f zero_le_one fun s => ?_
      by_cases hs : s ∈ f.support
      · exact (hnot s hs).le
      · rw [MvPolynomial.notMem_support_iff.1 hs, map_zero]
        exact zero_le_one
    · obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w f hf
      rw [h, hnot s hs]
  simp [h1]
end ReciprocityTheory.MultiplicativeHeights
