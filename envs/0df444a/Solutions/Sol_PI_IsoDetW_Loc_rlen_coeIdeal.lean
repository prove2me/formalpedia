-- Prove2me | solution 1 for PI.IsoDetW.Loc.rlen_coeIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:08:24.311811+00:00
-- url     : https://prove2.me/submissions/0a81fd06-5f63-4ca1-9de9-cfd80d07af32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Theorems.Thm_PI_IsoDetW_Loc_relativeLength_localized_coeIdeal


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
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
namespace PI.IsoDetW.Loc
theorem _root_.solution (P : HeightOneSpectrum R) {J : Ideal R} (hJ : J ≠ 0) :
    relative₂ (localization₂ P.asIdeal ((J : FI) : Submodule R K)) (localization₂ P.asIdeal (1 : Submodule R K)) =
      ((FractionalIdeal.count K P (J : FI)).toNat : ℕ∞) := by
  have := relativeLength_localized_coeIdeal (K := K) P hJ
  rw [FractionalIdeal.count_coe K P hJ, Int.toNat_natCast]
  exact this
end PI.IsoDetW.Loc
