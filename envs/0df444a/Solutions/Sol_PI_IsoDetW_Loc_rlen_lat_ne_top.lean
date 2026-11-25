-- Prove2me | solution 1 for PI.IsoDetW.Loc.rlen_lat_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:18.951692+00:00
-- url     : https://prove2.me/submissions/065b2be2-428b-456f-9bdc-9a87b8a927fc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
import Theorems.Thm_PI_IsoDetW_Loc_rlen_sc_ne_top
import Theorems.Thm_PI_IsoDetW_Loc_localization_mono
import Theorems.Thm_PI_IsoDetW_Loc_rlen_mono


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
  {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
omit [DecidableEq ι]
namespace PI.IsoDetW.Loc
theorem _root_.solution (P : HeightOneSpectrum R) {A : Submodule R (ι → K)} (hA : IsLat A) {r : R}
    (hr : r ≠ 0) (hrA : sc (algebraMap R K r) ≤ A) :
    relative₂ (localization₂ P.asIdeal (sc (algebraMap R K r))) (localization₂ P.asIdeal A) ≠ ⊤ := by
  obtain ⟨s, hs, -, hA2⟩ := hA
  exact ne_top_of_le_ne_top (rlen_sc_ne_top P hr hs)
    (rlen_mono le_rfl (localization_mono _ hrA) (localization_mono _ hA2))
end PI.IsoDetW.Loc
