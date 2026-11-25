-- Prove2me | solution 1 for PI.IsoDetW.Loc.lidx_one_coeIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:14:53.347857+00:00
-- url     : https://prove2.me/submissions/09755b88-be21-4726-8271-67252cb7eab8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Theorems.Thm_PI_IsoDetW_Loc_rlen_coeIdeal
import Theorems.Thm_PI_IsoDetW_Loc_coe_le_one
import Theorems.Thm_PI_IsoDetW_Loc_lidx_eq_of_le
import Theorems.Thm_PI_IsoDetW_Loc_rlen_self


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
    lidx P.asIdeal (1 : Submodule R K) ((J : FI) : Submodule R K) = FractionalIdeal.count K P (J : FI) := by
  have hle : ((J : FI) : Submodule R K) ≤ 1 := coe_le_one FractionalIdeal.coeIdeal_le_one
  have hne : (J : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  rw [lidx_eq_of_le P.asIdeal (D := ((J : FI) : Submodule R K)) (le_inf hle le_rfl)
    (by rw [rlen_coeIdeal P hJ]; exact ENat.coe_ne_top _) (by rw [rlen_self]; exact ENat.zero_ne_top),
    rlen_coeIdeal P hJ, rlen_self]
  simp only [ENat.toNat_coe, ENat.toNat_zero, Nat.cast_zero, sub_zero]
  exact Int.toNat_of_nonneg (FractionalIdeal.count_coe_nonneg K P J)
end PI.IsoDetW.Loc
