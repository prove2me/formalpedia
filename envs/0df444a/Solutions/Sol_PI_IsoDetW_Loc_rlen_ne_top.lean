-- Prove2me | solution 1 for PI.IsoDetW.Loc.rlen_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:14:53.769668+00:00
-- url     : https://prove2.me/submissions/cd615eb3-14fe-4e47-abd6-f2f2e57af7f1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Theorems.Thm_PI_IsoDetW_Loc_rlen_mulR
import Theorems.Thm_PI_IsoDetW_Loc_rlen_coeIdeal
import Theorems.Thm_PI_IsoDetW_Loc_exists_integral
import Theorems.Thm_PI_IsoDetW_Loc_coe_le_one
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
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
namespace PI.IsoDetW.Loc
theorem _root_.solution (P : HeightOneSpectrum R) {D X : FI} (hD : D ≠ 0) (hDX : D ≤ X) :
    relative₂ (localization₂ P.asIdeal (D : Submodule R K)) (localization₂ P.asIdeal (X : Submodule R K)) ≠ ⊤ := by
  have hX : X ≠ 0 := by rintro rfl; exact hD (le_bot_iff.mp hDX)
  obtain ⟨a, ha, J, hJ, hXJ⟩ := exists_integral X hX
  have ha' : algebraMap R K a ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact ha
  rw [← rlen_mulR P ha' D X, hXJ]
  have hle : FractionalIdeal.spanSingleton _ (algebraMap R K a) * D ≤ (J : FI) :=
    hXJ ▸ (by gcongr)
  have hle1 : FractionalIdeal.spanSingleton _ (algebraMap R K a) * D ≤ 1 :=
    hle.trans (FractionalIdeal.coeIdeal_le_one)
  obtain ⟨J', hJ'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle1
  have hJ'0 : J' ≠ 0 := by
    rintro rfl
    have : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a) * D = 0 := by
      rw [← hJ']; simp
    rcases mul_eq_zero.mp this with h | h
    · exact ha' (FractionalIdeal.spanSingleton_eq_zero_iff.mp h)
    · exact hD h
  rw [← hJ']
  have h1 := rlen_mono (localization_mono P.asIdeal (le_refl ((J' : FI) : Submodule R K)))
    (localization_mono P.asIdeal (show ((J' : FI) : Submodule R K) ≤ ((J : FI) : Submodule R K) from
      by rw [hJ']; exact FractionalIdeal.coe_le_coe.mpr hle))
    (localization_mono P.asIdeal (coe_le_one FractionalIdeal.coeIdeal_le_one))
  rw [rlen_coeIdeal P hJ'0] at h1
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) h1
end PI.IsoDetW.Loc
