-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.real_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:23:56.284247+00:00
-- url     : https://prove2.me/submissions/5aa17a73-8007-4832-8d7a-ebd72f071892

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_conjSymm_canonical
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_conjSymm_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_eq_of_commMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (t : (E →+* ℂ) → ℂ) (ht : ConjSymm t) :
    ∃ c : Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ,
      t = ∑ k, c k • canonicalEmbedding E (integralBasis E k) := by
  refine ⟨fun k => (mixedEmbedding.latticeBasis E).repr (mixedEmbedding.commMap E t) k, ?_⟩
  apply eq_of_commMap t _ ht (conjSymm_sum Finset.univ
    (fun k => (mixedEmbedding.latticeBasis E).repr (mixedEmbedding.commMap E t) k)
    (fun k => canonicalEmbedding E (integralBasis E k)) fun k => conjSymm_canonical _)
  rw [map_sum]
  simp only [map_smul]
  conv_lhs => rw [← (mixedEmbedding.latticeBasis E).sum_repr (mixedEmbedding.commMap E t)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mixedEmbedding.latticeBasis_apply, mixedEmbedding.commMap_canonical_eq_mixed]
end ReciprocityTheory.ChartRestriction.G.I2
