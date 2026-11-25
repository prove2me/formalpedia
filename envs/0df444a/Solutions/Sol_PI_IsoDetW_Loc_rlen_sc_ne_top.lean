-- Prove2me | solution 1 for PI.IsoDetW.Loc.rlen_sc_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:24:43.954006+00:00
-- url     : https://prove2.me/submissions/0982fbfe-590b-4b1c-8df6-756de19a6f26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
import Theorems.Thm_PI_IsoDetW_Loc_span_le_span
import Theorems.Thm_P2M_PI_IsoDetW_Loc_algebraMap_ne_zero__6cbe823fda71
import Theorems.Thm_P2M_PI_IsoDetW_Loc_spanSingleton_ne_zero__2b9a00487365
import Theorems.Thm_PI_IsoDetW_Loc_localization_pi
import Theorems.Thm_PI_IsoDetW_Loc_rlen_ne_top
import Theorems.Thm_PI_IsoDetW_Loc_rlen_pi


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
theorem _root_.solution (P : HeightOneSpectrum R) {r s : R} (hr : r ≠ 0) (hs : s ≠ 0) :
    relative₂ (localization₂ P.asIdeal (sc (algebraMap R K r) : Submodule R (ι → K)))
      (localization₂ P.asIdeal (sc (algebraMap R K s)⁻¹)) ≠ ⊤ := by
  unfold sc
  rw [localization_pi, localization_pi, rlen_pi, ENat.sum_ne_top]
  intro i _
  refine rlen_ne_top P (spanSingleton_ne_zero' (algebraMap_ne_zero' hr)) (span_le_span (r * s) ?_)
  rw [map_mul, mul_assoc, mul_inv_cancel₀ (algebraMap_ne_zero' hs), mul_one]
end PI.IsoDetW.Loc
