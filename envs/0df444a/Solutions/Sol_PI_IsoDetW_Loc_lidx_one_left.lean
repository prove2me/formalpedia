-- Prove2me | solution 1 for PI.IsoDetW.Loc.lidx_one_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:19:50.949858+00:00
-- url     : https://prove2.me/submissions/137c64eb-d5de-4bff-95f3-36bc9f74cd09

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Theorems.Thm_PI_IsoDetW_Loc_lidx_mulR
import Theorems.Thm_PI_IsoDetW_Loc_exists_integral
import Theorems.Thm_PI_IsoDetW_Loc_rlen_ne_top
import Theorems.Thm_PI_IsoDetW_Loc_lidx_one_coeIdeal
import Theorems.Thm_PI_IsoDetW_Loc_spanSingleton_algebraMap
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
theorem _root_.solution (P : HeightOneSpectrum R) {I : FI} (hI : I ≠ 0) :
    lidx P.asIdeal (1 : Submodule R K) (I : Submodule R K) = FractionalIdeal.count K P I := by
  obtain ⟨a, ha, J, hJ, hIJ⟩ := exists_integral I hI
  have ha' : algebraMap R K a ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact ha
  have hsa : Ideal.span {a} ≠ (0 : Ideal R) := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha
  have hsaJ : Ideal.span {a} * J ≠ 0 := mul_ne_zero hsa hJ
  rw [← FractionalIdeal.coe_one, ← lidx_mulR P ha' 1 I, mul_one, hIJ, spanSingleton_algebraMap]

  have hD1 : (((Ideal.span {a} * J : Ideal R) : FI) : Submodule R K) ≤ ((Ideal.span {a} : Ideal R) : FI) := by
    apply FractionalIdeal.coe_le_coe.mpr
    rw [FractionalIdeal.coeIdeal_mul]
    exact mul_le_of_le_one_right' FractionalIdeal.coeIdeal_le_one
  have hD2 : (((Ideal.span {a} * J : Ideal R) : FI) : Submodule R K) ≤ ((J : FI) : Submodule R K) := by
    apply FractionalIdeal.coe_le_coe.mpr
    rw [FractionalIdeal.coeIdeal_mul]
    exact mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one
  have hD3 : (((Ideal.span {a} * J : Ideal R) : FI) : Submodule R K) ≤ ((1 : FI) : Submodule R K) :=
    FractionalIdeal.coe_le_coe.mpr FractionalIdeal.coeIdeal_le_one
  have hDne : ((Ideal.span {a} * J : Ideal R) : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hsaJ
  rw [lidx_cocycle P.asIdeal (B := ((1 : FI) : Submodule R K)) hD1 hD3 hD2
    (rlen_ne_top P hDne (FractionalIdeal.coe_le_coe.mp hD1))
    (rlen_ne_top P hDne (FractionalIdeal.coe_le_coe.mp hD3))
    (rlen_ne_top P hDne (FractionalIdeal.coe_le_coe.mp hD2))]
  rw [lidx_antisymm, FractionalIdeal.coe_one, lidx_one_coeIdeal P hsa, lidx_one_coeIdeal P hJ]
  have hc := congrArg (FractionalIdeal.count K P) hIJ
  rw [FractionalIdeal.count_mul K P (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha') hI,
    spanSingleton_algebraMap] at hc
  linarith
end PI.IsoDetW.Loc
