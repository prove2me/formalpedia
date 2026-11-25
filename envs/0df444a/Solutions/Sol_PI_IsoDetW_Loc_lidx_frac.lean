-- Prove2me | solution 1 for PI.IsoDetW.Loc.lidx_frac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:24:57.720214+00:00
-- url     : https://prove2.me/submissions/11cfda25-1b7f-4bee-8797-2769320a9b68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Theorems.Thm_PI_IsoDetW_Loc_rlen_ne_top
import Theorems.Thm_PI_IsoDetW_Loc_lidx_one_left
import Theorems.Thm_PI_IsoDetW_Loc_exists_sandwich
import Theorems.Thm_PI_IsoDetW_Loc_spanSingleton_mul_le
import Theorems.Thm_PI_IsoDetW_Loc_spanSingleton_le_one
import Theorems.Thm_PI_IsoDetW_Loc_lidx_antisymm
import Theorems.Thm_PI_IsoDetW_Loc_lidx_cocycle


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
theorem _root_.solution (P : HeightOneSpectrum R) {I J : FI} (hI : I ≠ 0) (hJ : J ≠ 0) :
    lidx P.asIdeal (I : Submodule R K) (J : Submodule R K) =
      FractionalIdeal.count K P J - FractionalIdeal.count K P I := by
  obtain ⟨a, ha, haI, -⟩ := exists_sandwich I hI
  obtain ⟨b, hb, hbJ, -⟩ := exists_sandwich J hJ
  set D := FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K (a * b)) with hD
  have hD0 : D ≠ 0 := by
    rw [hD, ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff]
    exact mul_ne_zero ha hb
  have hDI : D ≤ I := (spanSingleton_mul_le a b).trans haI
  have hDJ : D ≤ J := (by rw [hD, mul_comm]; exact spanSingleton_mul_le b a : D ≤ _).trans hbJ
  have hD1 : D ≤ 1 := spanSingleton_le_one _
  rw [lidx_cocycle P.asIdeal (B := ((1 : FI) : Submodule R K))
    (FractionalIdeal.coe_le_coe.mpr hDI) (FractionalIdeal.coe_le_coe.mpr hD1)
    (FractionalIdeal.coe_le_coe.mpr hDJ)
    (rlen_ne_top P hD0 hDI) (rlen_ne_top P hD0 hD1) (rlen_ne_top P hD0 hDJ)]
  rw [lidx_antisymm P.asIdeal _ ((1 : FI) : Submodule R K), FractionalIdeal.coe_one,
    lidx_one_left P hI, lidx_one_left P hJ]
  ring
end PI.IsoDetW.Loc
