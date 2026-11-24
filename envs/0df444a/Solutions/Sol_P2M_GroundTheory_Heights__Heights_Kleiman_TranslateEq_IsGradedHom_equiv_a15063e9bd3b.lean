-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_IsGradedHom_equiv_a15063e9bd3b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:34.237777+00:00
-- url     : https://prove2.me/submissions/a8a46561-229c-46df-b7a5-cad305867c3f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable (S : Type) [CommRing S] (N : ℕ)
variable (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
namespace IsGradedHom
theorem _root_.solution {M' : Type} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
    [IsScalarTower S (Poly S N) M'] (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (G' : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M')
    (f : M →ₗ[Poly S N] M') :
    IndefiniteRowSideFullHecke.Kleiman.IsGradedHom S N G G' f ↔
      ∃ g : Kleiman.GradedHom (gradedEquiv S N M G) (gradedEquiv S N M' G'), g.toLin = f :=
  ⟨fun hf => ⟨⟨f, fun c m hm => hf c m hm⟩, rfl⟩, fun ⟨g, hg⟩ c m hm => hg ▸ g.map_piece c m hm⟩
end IsGradedHom
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
