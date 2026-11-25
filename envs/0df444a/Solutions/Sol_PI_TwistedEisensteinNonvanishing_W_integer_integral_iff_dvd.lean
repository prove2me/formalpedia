-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.integer_integral_iff_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:45:33.103238+00:00
-- url     : https://prove2.me/submissions/357d4dca-028b-48e0-b5e8-98b80ba8db2d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_iMul
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_iNat
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_iPow
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_q_ne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_not_int_inv_q
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_int_inv_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open NTA
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution : IntegerIntegralIffDvd := by
  intro E _ _ P hp hq i e
  have hq0 := q_ne P hp
  constructor
  · intro hI
    by_contra hnd
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hnd (dvd_zero _)
    obtain ⟨f, j, hj, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi0 (qOf P) hp.one_lt.ne'
    have hfe : f < e := by
      by_contra hfe
      push_neg at hfe
      exact hnd (Dvd.dvd.mul_right (pow_dvd_pow _ hfe) _)
    have h1 : IntAt P ((((qOf P ^ f * j : ℕ) : E) / (qOf P : E) ^ e) * (j : E)⁻¹ *
        (qOf P : E) ^ (e - f - 1)) :=
      iMul P (iMul P hI (int_inv_nat P hp hj)) (iPow P (iNat P _) _)
    have hj0 : (j : E) ≠ 0 := by
      have : j ≠ 0 := fun h => hj (h ▸ dvd_zero _)
      exact_mod_cast this
    have e2 : (((qOf P ^ f * j : ℕ) : E) / (qOf P : E) ^ e) * (j : E)⁻¹ * (qOf P : E) ^ (e - f - 1) =
        (qOf P : E)⁻¹ := by
      obtain ⟨g, rfl⟩ : ∃ g, e = f + g + 1 := ⟨e - f - 1, by omega⟩
      have hg : f + g + 1 - f - 1 = g := by omega
      rw [hg]
      push_cast
      field_simp
      ring
    rw [e2] at h1
    exact not_int_inv_q P hp h1
  · rintro ⟨k, rfl⟩
    have e2 : (((qOf P ^ e * k : ℕ) : E) / (qOf P : E) ^ e) = (k : E) := by
      push_cast
      field_simp
    rw [e2]
    exact iNat P k
end PI.TwistedEisensteinNonvanishing.W
