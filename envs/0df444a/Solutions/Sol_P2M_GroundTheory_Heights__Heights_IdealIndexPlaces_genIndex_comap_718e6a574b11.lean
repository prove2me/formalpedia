-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IdealIndexPlaces_genIndex_comap_718e6a574b11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:18.000935+00:00
-- url     : https://prove2.me/submissions/3ca74f18-a76e-4653-a99c-f0f98891ba6e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIdealIndexPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.IdealIndexPlaces
namespace GroundTheory.Heights₂.Heights.IdealIndexPlaces
theorem _root_.solution {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G' →+ G)
    {A B : AddSubgroup G} (hA : A ≤ f.range) (hB : B ≤ f.range) :
    genIndex (A.comap f) (B.comap f) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_comap, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self hA,
    AddSubgroup.map_comap_eq_self hB]
end GroundTheory.Heights₂.Heights.IdealIndexPlaces
