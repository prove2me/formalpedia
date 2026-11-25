-- Prove2me | solution 1 for PI.IsoDetW.Loc.localization_cI_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:46:09.321846+00:00
-- url     : https://prove2.me/submissions/3b6e88e0-743f-4363-8a6d-ee21f4c89047

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Theorems.Thm_PI_IsoDetW_Loc_mem_cI
import Theorems.Thm_PI_IsoDetW_Loc_algebraMap_mem_cI
import Theorems.Thm_PI_IsoDetW_Loc_smul_algebraMap
import Theorems.Thm_PI_IsoDetW_Loc_localization_mono


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
    localization₂ P.asIdeal (cI K J) =
      localization₂ P.asIdeal (cI K (P.asIdeal ^ (Associates.mk P.asIdeal).count (Associates.mk J).factors)) := by
  set k := (Associates.mk P.asIdeal).count (Associates.mk J).factors
  have hdvd : P.asIdeal ^ k ∣ J := by
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow,
      Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) P.associates_irreducible]
  obtain ⟨J', hJ'⟩ := hdvd
  have hJ'0 : J' ≠ 0 := by rintro rfl; exact hJ (by simpa using hJ')
  have hpk0 : P.asIdeal ^ k ≠ 0 := pow_ne_zero _ P.ne_bot

  have hc : FractionalIdeal.count K P (J' : FractionalIdeal (nonZeroDivisors R) K) = 0 := by
    have h1 := FractionalIdeal.count_coe K P hJ
    rw [hJ', FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul K P
      (FractionalIdeal.coeIdeal_ne_zero.mpr hpk0) (FractionalIdeal.coeIdeal_ne_zero.mpr hJ'0),
      FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow_self] at h1
    rw [← hJ'] at h1
    change (k : ℤ) + _ = (k : ℤ) at h1
    linarith
  have hnot : ¬ J' ≤ P.asIdeal := by
    intro hle
    have h2 := FractionalIdeal.count_mono K P (FractionalIdeal.coeIdeal_ne_zero.mpr hJ'0)
      (FractionalIdeal.coeIdeal_le_coeIdeal K |>.mpr hle)
    rw [hc, FractionalIdeal.count_self] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨s, hsJ', hsP⟩ := Set.not_subset.mp hnot
  apply le_antisymm
  · apply localization_mono
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_cI.mp hx
    rw [algebraMap_mem_cI]
    rw [hJ'] at hy
    exact (Ideal.mul_le_inf.trans inf_le_left : P.asIdeal ^ k * J' ≤ P.asIdeal ^ k) hy
  · rintro x ⟨t, ht, htx⟩
    obtain ⟨y, hy, hyx⟩ := mem_cI.mp htx
    refine ⟨s * t, ?_, ?_⟩
    · intro hst
      rcases Ideal.IsPrime.mem_or_mem (inferInstance) hst with h | h
      · exact hsP h
      · exact ht h
    · rw [mul_smul, ← hyx, smul_algebraMap, algebraMap_mem_cI, hJ']
      have := Ideal.mul_mem_mul hy hsJ'
      rwa [mul_comm y s] at this
end PI.IsoDetW.Loc
