-- Prove2me | solution 1 for QEC.Coding.BDL26RXDifferentialMasks.incidenceHull_le_every_commuting_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:45:55.531039+00:00
-- url     : https://prove2.me/submissions/4a27f0d6-a363-4d7d-93ac-a5ef4e3e86ef

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_native_mask_commutes_iff
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_commuting_lower_saturated
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_minimal
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_basisImage_mem_iff
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_basisImage_support
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXDifferentialMasks
theorem _root_.solution (h : i.val % 2 = 0)
    (seed A : Finset (state S i.val).presentation.Q)
    (B : Finset (FamilyZ S depth i.succ)) (hseed : seed ⊆ A)
    (hc : ∀ w, maskWord B (nativeDifferential S depth i w) =
      nativeDifferential S depth i (maskWord A w)) :
    incidenceHull S depth i seed ⊆ A ∧
      nativeRegion S depth i h (incidenceHull S depth i seed) ⊆ B := by
  have hl := incidenceHull_minimal S depth i seed A hseed
    (commuting_lower_saturated S depth i h A B hc)
  refine ⟨hl, ?_⟩
  intro p hp
  obtain ⟨q,hq,hp⟩ := Finset.mem_biUnion.mp hp
  have hm : p ∈ hammingSupport (basisImage S depth i q) :=
    (basisImage_support S depth i h q).symm ▸ hp
  obtain ⟨z,copy,hqz,rfl⟩ := (basisImage_mem_iff S depth i h q p).mp hm
  exact ((native_mask_commutes_iff S depth i h A B).mp hc q z copy hqz).mpr (hl hq)
end QEC.Coding.BDL26RXDifferentialMasks
