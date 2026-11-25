-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:40.238781+00:00
-- url     : https://prove2.me/submissions/2116b50c-1bc5-4597-ace2-a77c56adb368

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_SmRight
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PI.UpqRep
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CapelliEig
namespace PI.UnitaryGroupMassFormula.CapelliEig
theorem _root_.solution : UHGrp := by
  intro k r a ha
  have hH : Hpk k r * Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hdet : IsUnit a.det := by
    have h1 := congrArg Matrix.det ha'
    rw [Matrix.det_mul, Matrix.det_mul] at h1
    have hHd : (Hpk k r).det * (Hpk k r).det = 1 := by rw [← Matrix.det_mul, hH, Matrix.det_one]
    refine isUnit_iff_ne_zero.mpr (fun h0 => ?_)
    rw [h0, mul_zero] at h1
    rw [← h1, zero_mul] at hHd
    exact zero_ne_one hHd
  refine ⟨(Matrix.isUnit_iff_isUnit_det a).mpr hdet, ?_, ?_⟩
  · show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
    have hai : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hdet
    calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
      _ = (a * a⁻¹)ᴴ * Hpk k r * (a * a⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [hai, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · intro b hb
    have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
    show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
    calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [ha', hb']
end PI.UnitaryGroupMassFormula.CapelliEig
