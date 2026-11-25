-- Prove2me | solution 1 for PI.IsoDetW.Loc.relativeLength_localized_coeIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:41.300966+00:00
-- url     : https://prove2.me/submissions/8afd759b-4adb-4cae-8668-fcc1b99025ca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Theorems.Thm_PI_IsoDetW_Loc_relativeLength_localized_pow
import Theorems.Thm_PI_IsoDetW_Loc_localization_cI_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs IsDedekindDomain
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
namespace PI.IsoDetW.Loc
theorem _root_.solution (P : HeightOneSpectrum R) {J : Ideal R} (hJ : J ≠ 0) :
    relative₂ (localization₂ P.asIdeal (cI K J)) (localization₂ P.asIdeal (1 : Submodule R K)) =
      (Associates.mk P.asIdeal).count (Associates.mk J).factors := by
  rw [localization_cI_eq P hJ, relativeLength_localized_pow]
end PI.IsoDetW.Loc
