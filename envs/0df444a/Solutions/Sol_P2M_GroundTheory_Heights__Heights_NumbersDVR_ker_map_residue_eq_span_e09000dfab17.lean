-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ker_map_residue_eq_span_e09000dfab17
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:14.698892+00:00
-- url     : https://prove2.me/submissions/0ecaa38c-b49d-47a8-85d4-a8a9c2a1069f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {σ : Type*} :
    RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) : MvPolynomial σ O →+* _) =
      Ideal.span {C ϖ} := by
  rw [MvPolynomial.ker_map, IsLocalRing.ker_residue,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
    Set.image_singleton]
end GroundTheory.Heights₂.Heights.NumbersDVR
