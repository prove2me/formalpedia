-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_length_spanQuot_toNat_c531729d4c3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:56:45.209485+00:00
-- url     : https://prove2.me/submissions/dfbc5779-a1ef-4fe0-8e7d-4fb47f6a9c27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsGenericRestrLen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGenericRestrLen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isLocalizedModule_spanQuotMap_497062e331b3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {F : Type u} [Field F] [Algebra S F] [IsFractionRing S F]
  {Ω : Type w} [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (A B : Submodule S Ω) :
    (Module.length F (Submodule.span F (A : Set Ω) ⧸
        (Submodule.span F (B : Set Ω)).comap (Submodule.span F (A : Set Ω)).subtype)).toNat =
      Module.finrank S (A ⧸ B.comap A.subtype) := by
  have := isLocalizedModule_spanQuotMap (F := F) A B
  rw [Module.length_eq_rank, Cardinal.toNat_toENat]
  change Module.finrank F _ = _
  rw [IsLocalization.finrank_eq F (nonZeroDivisors S) le_rfl]
  exact IsLocalizedModule.finrank_eq (p := nonZeroDivisors S) (f := spanQuotMap F A B) (hp := le_rfl)
end GroundTheory.Heights₂.Heights.Kleiman
