-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LowSmooth.conj_mem_Kset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:31:55.227198+00:00
-- url     : https://prove2.me/submissions/c28e85cd-dd83-40a5-8252-561eeaf983c4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_LowCyc
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LowSmooth
open PI.UpqRep
variable {k r : ℕ}
namespace PI.UnitaryGroupMassFormula.LowSmooth
theorem _root_.solution {ε : Fin (2 * r + k + 1) → Bool} {P g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : IsCayleyU k r ε P)
    (hg : g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)) :
    P * g * P⁻¹ ∈ Kset ε ∧ P⁻¹ * (P * g * P⁻¹) * P = g := by
  obtain ⟨⟨_, hJ⟩, hPu⟩ := hP
  obtain ⟨hgH, hgu⟩ := hg
  have hPs : P * Pᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hPu
    rwa [Matrix.star_eq_conjTranspose] at this
  have hsP : Pᴴ * P = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hPu
    rwa [Matrix.star_eq_conjTranspose] at this
  have hgs : g * gᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hgu
    rwa [Matrix.star_eq_conjTranspose] at this
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv hsP
  have hgH' : gᴴ * Hpk k r * g = Hpk k r := hgH

  have hcomm : g * Hpk k r = Hpk k r * g := by
    calc g * Hpk k r = g * (gᴴ * Hpk k r * g) := by rw [hgH']
      _ = (g * gᴴ) * Hpk k r * g := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * g := by rw [hgs, Matrix.one_mul]
  have hJm : Jm ε = P * Hpk k r * Pᴴ := by
    rw [← hJ]
    simp only [← Matrix.mul_assoc]
    rw [hPs, Matrix.one_mul, Matrix.mul_assoc, hPs, Matrix.mul_one]
  rw [hinv]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hPs' : Pᴴ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      exact hsP
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hPu hgu) hPs'
  · rw [hJm]
    calc P * g * Pᴴ * (P * Hpk k r * Pᴴ) = P * g * (Pᴴ * P) * Hpk k r * Pᴴ := by
          simp only [Matrix.mul_assoc]
      _ = P * (g * Hpk k r) * Pᴴ := by
          rw [hsP, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = P * (Hpk k r * g) * Pᴴ := by rw [hcomm]
      _ = P * Hpk k r * (Pᴴ * P) * g * Pᴴ := by
          rw [hsP, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = P * Hpk k r * Pᴴ * (P * g * Pᴴ) := by simp only [Matrix.mul_assoc]
  · calc Pᴴ * (P * g * Pᴴ) * P = (Pᴴ * P) * g * (Pᴴ * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hsP, Matrix.one_mul, Matrix.mul_one]
end PI.UnitaryGroupMassFormula.LowSmooth
