-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.unit_congruent_to_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:03:21.594981+00:00
-- url     : https://prove2.me/submissions/8aeba8a9-4c2f-4b9b-9ff2-13ab86aa863e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_iMul
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_iAdd
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_iSub
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_iNat
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_iPow
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_q_ne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_not_int_inv_q
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_integral_approximation_by_integer

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
theorem _root_.solution : UnitCongruentToInteger := by
  intro E _ _ P hp hq w N hw hwi hwii
  have hq0 := q_ne P hp
  cases N with
  | zero => exact ⟨1, Nat.coprime_one_left _, by simpa using iSub P hwi (iNat P 1)⟩
  | succ N =>
    obtain ⟨i, hi, hI⟩ := integral_approximation_by_integer E P hp hq w (N + 1) hwi
    refine ⟨i, ?_, hI⟩
    rw [Nat.coprime_comm]
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr ?_
    rintro ⟨j, rfl⟩
    apply not_int_inv_q P hp
    have h1 : IntAt P (w / (qOf P : E)) := by
      have e : w / (qOf P : E) = (w - ((qOf P * j : ℕ) : E)) / (qOf P : E) ^ (N + 1) *
          (qOf P : E) ^ N + (j : E) := by
        push_cast
        field_simp
        ring
      rw [e]
      exact iAdd P (iMul P hI (iPow P (iNat P _) N)) (iNat P j)
    have e2 : (qOf P : E)⁻¹ = w / (qOf P : E) * w⁻¹ := by
      field_simp
    rw [e2]
    exact iMul P h1 hwii
end PI.TwistedEisensteinNonvanishing.W
