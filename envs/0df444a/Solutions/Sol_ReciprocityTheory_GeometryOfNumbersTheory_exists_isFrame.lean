-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.exists_isFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:26:05.492444+00:00
-- url     : https://prove2.me/submissions/01979dac-34f7-433d-8c35-61e9435d5d29

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ArakelovDegreeEqDegreeOfFamily
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_IsFrame_length_eq_latticeRank
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_exists_isFullRankFamily_of_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (E : Submodule (𝓞 K) V) (hE : E.FG) :
    ∃ v : Fin (latRank K E) → V, IsFrame K E v := by
  obtain ⟨r, v, hv⟩ := exists_isFullRankFamily_of_fg E hE
  obtain rfl := hv.length_eq_latticeRank
  exact ⟨v, hv⟩
end ReciprocityTheory.GeometryOfNumbersTheory
