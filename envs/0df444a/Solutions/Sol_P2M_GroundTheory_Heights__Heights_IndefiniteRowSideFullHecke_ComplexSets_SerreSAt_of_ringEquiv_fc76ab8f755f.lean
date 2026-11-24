-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SerreSAt_of_ringEquiv_fc76ab8f755f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:13.589797+00:00
-- url     : https://prove2.me/submissions/4d6aeb8f-fa25-49b4-9c0a-11b042eb223c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatNormalFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreRFlatAscent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreSFlatAscent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatNormalFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing RingTheory.Sequence
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace SerreSAt
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) {k : ℕ} (h : SerreSAt A k) : SerreSAt B k := by
  obtain ⟨rs, hmem, hreg, hlen⟩ := h
  refine ⟨rs.map e, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    have := hmem s hs
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this ⊢
    exact fun hu => this ((isUnit_map_iff e s).mp hu)
  · refine (AddEquiv.isWeaklyRegular_congr (e := e.toAddEquiv) ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x => by
      simp [smul_eq_mul])
  · rwa [List.length_map, ← ringKrullDim_eq_of_ringEquiv e]
end SerreSAt
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
