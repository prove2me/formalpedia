-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_length_residueField_15d11378cc0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:06.148643+00:00
-- url     : https://prove2.me/submissions/81479472-7c53-4613-b3db-69d782463686

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLengthFiniteAlgebra

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
open IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
variable {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]
omit [IsLocalRing O]
namespace GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
theorem _root_.solution (P : Ideal B) [P.IsMaximal] :
    Module.length O (ResidueField (Localization.AtPrime P)) = Module.length O (B ⧸ P) := by
  let e : (B ⧸ P) ≃+* ResidueField (Localization.AtPrime P) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)
  let e' : (B ⧸ P) ≃ₐ[B] ResidueField (Localization.AtPrime P) :=
    AlgEquiv.ofRingEquiv (f := e) fun x => rfl
  exact (e'.toLinearEquiv.restrictScalars O).length_eq.symm
end GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
