-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_length_quot_eq_bb547f6d4d84
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:14:07.25453+00:00
-- url     : https://prove2.me/submissions/e971ab72-6fe5-4ae8-8cea-53c6ae8ca992

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NefExtendIsoSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefExtendIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
variable {S : Type} [CommRing S] {F : Type} [Field F] [Algebra S F] {Ω : Type} [Field Ω] [Algebra S Ω]
  [Algebra F Ω] [IsScalarTower S F Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
theorem _root_.solution (hφ : Function.Bijective (algebraMap S F)) (X Y : Submodule S Ω)
    (X' Y' : Submodule F Ω) (hX : (X : Set Ω) = X') (hY : (Y : Set Ω) = Y') :
    Module.length S (X ⧸ Y.comap X.subtype) = Module.length F (X' ⧸ Y'.comap X'.subtype) := by
  obtain rfl : X = X'.restrictScalars S := SetLike.coe_injective hX
  obtain rfl : Y = Y'.restrictScalars S := SetLike.coe_injective hY
  rw [← Module.length_eq_of_surjective (S := S) hφ.2]
  exact (Submodule.Quotient.restrictScalarsEquiv S (Y'.comap X'.subtype)).length_eq
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
