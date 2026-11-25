-- Prove2me | solution 1 for PI.IsoDetW.Loc.lat_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:35:16.112796+00:00
-- url     : https://prove2.me/submissions/35075809-6d32-4797-a047-1851d66cad5e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
import Theorems.Thm_PI_IsoDetW_Loc_span_le_span
import Theorems.Thm_PI_IsoDetW_Loc_sc_mono
import Theorems.Thm_PI_IsoDetW_Loc_rlen_lat_ne_top
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
  {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
omit [DecidableEq ι]
namespace PI.IsoDetW.Loc
theorem _root_.solution (P : HeightOneSpectrum R) {A B C : Submodule R (ι → K)} (hA : IsLat A) (hB : IsLat B)
    (hC : IsLat C) : lidx P.asIdeal A C = lidx P.asIdeal A B + lidx P.asIdeal B C := by
  obtain ⟨a, ha, hA1, -⟩ := id hA
  obtain ⟨b, hb, hB1, -⟩ := id hB
  obtain ⟨c, hc, hC1, -⟩ := id hC
  have hr : a * b * c ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) hc
  have hDA : sc (algebraMap R K (a * b * c)) ≤ A :=
    (sc_mono (span_le_span (b * c) (by simp only [map_mul]; try ring))).trans hA1
  have hDB : sc (algebraMap R K (a * b * c)) ≤ B :=
    (sc_mono (span_le_span (a * c) (by simp only [map_mul]; try ring))).trans hB1
  have hDC : sc (algebraMap R K (a * b * c)) ≤ C :=
    (sc_mono (span_le_span (a * b) (by simp only [map_mul]; try ring))).trans hC1
  exact lidx_cocycle P.asIdeal hDA hDB hDC (rlen_lat_ne_top P hA hr hDA) (rlen_lat_ne_top P hB hr hDB)
    (rlen_lat_ne_top P hC hr hDC)
end PI.IsoDetW.Loc
