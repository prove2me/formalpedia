-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_sum_castLE_6bb839077312
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:14.360708+00:00
-- url     : https://prove2.me/submissions/06f3ee81-756f-46ba-b840-3423bd2f3e2b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagPivotIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotIdentity
variable {R : Type} [CommRing R] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotIdentity
theorem _root_.solution {m k : ℕ} (h : k ≤ m) (f : Fin m → R) (hf : ∀ i : Fin m, k ≤ (i : ℕ) → f i = 0) :
    ∑ i : Fin k, f (Fin.castLE h i) = ∑ i : Fin m, f i := by
  have e : ∑ i : Fin k, f (Fin.castLE h i) = ∑ i ∈ Finset.univ.map (Fin.castLEEmb h), f i := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hf i ?_
  by_contra hlt
  push Not at hlt
  exact hi (Finset.mem_map.2 ⟨⟨i, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotIdentity
