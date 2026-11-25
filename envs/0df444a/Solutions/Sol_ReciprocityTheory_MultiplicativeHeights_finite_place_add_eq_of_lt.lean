-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.finite_place_add_eq_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:08:59.478339+00:00
-- url     : https://prove2.me/submissions/9a3a248c-2798-46e0-baaf-fe22191208a0

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_Lemmata_GeneralBFactLeftExtra_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type*} [Field K] [NumberField K] {σ : Type*}
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (w : FinitePlace K) (x y : K) (h : w y < w x) : w (x + y) = w x := by
  apply le_antisymm
  · exact (FinitePlace.add_le w x y).trans (max_le le_rfl h.le)
  · have h1 : w x ≤ max (w (x + y)) (w (-y)) := by
      have := FinitePlace.add_le w (x + y) (-y)
      rwa [add_neg_cancel_right] at this
    rw [map_neg_eq_map] at h1
    rcases le_max_iff.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 (not_le.2 h)
end ReciprocityTheory.MultiplicativeHeights
