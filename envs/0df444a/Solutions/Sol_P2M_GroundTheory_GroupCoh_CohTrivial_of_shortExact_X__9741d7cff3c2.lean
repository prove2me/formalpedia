-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_CohTrivial_of_shortExact_X__9741d7cff3c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:18:53.410111+00:00
-- url     : https://prove2.me/submissions/931acd62-c5a2-4966-94da-56c3e0b9f03b

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Theorems.Thm_P2M_GroundTheory_GroupCoh_TateAcyclic_of_shortExact_X__c00637e206cb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [CommRing k] [Group G]
namespace GroundTheory.GroupCoh
namespace CohTrivial
theorem _root_.solution {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (h₂ : CohTrivial S.X₂) (h₃ : CohTrivial S.X₃) : CohTrivial S.X₁ := by
  intro H _
  have hS' : (S.map (resFunctor H.subtype)).ShortExact := (shortExact_res H.subtype).2 hS
  have a : TateAcyclic (S.map (resFunctor H.subtype)).X₂ := by
    rw [ShortComplex.map_X₂]; exact h₂ H
  have b : TateAcyclic (S.map (resFunctor H.subtype)).X₃ := by
    rw [ShortComplex.map_X₃]; exact h₃ H
  have c := TateAcyclic.of_shortExact_X₃ hS' a b
  rw [ShortComplex.map_X₁] at c
  exact c
end CohTrivial
end GroundTheory.GroupCoh
