-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalLocallyIrreducible_proof_adac72aa7195
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:11.914173+00:00
-- url     : https://prove2.me/submissions/bb67e20a-e5b6-407d-bcf7-839d0c779805

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVanishNearPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalLocallyIrreducible
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_zeroSetIn_subset_closure_diff_d630fe876a88

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
open MvPolynomial Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace NormalLocallyIrreducible
theorem _root_.solution (hvan : VanishNearPoint.Statement)
    (hcon : NormalComplementConnected.Statement) : NormalLocallyIrreducible.Statement := by
  intro σ _ I h w hI hnorm hh hw U hU
  obtain ⟨B, hBo, hwB, hBU, hpre⟩ := hcon σ I h w hI hnorm hh hw U hU
  refine ⟨B, hBo, hwB, hBU, hpre, ?_⟩
  rintro z ⟨hzZ, hzB⟩
  have h1 : z ∈ B ∩ closure (zeroSetIn I \ {z | eval z h = 0}) :=
    ⟨hzB, zeroSetIn_subset_closure_diff hvan I h hI hh hzZ⟩
  refine closure_mono ?_ (hBo.inter_closure h1)
  rintro y ⟨hyB, hyZ, hyh⟩
  exact ⟨⟨hyZ, hyB⟩, hyh⟩
end NormalLocallyIrreducible
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
