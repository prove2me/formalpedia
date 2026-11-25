-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_k_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:25.126383+00:00
-- url     : https://prove2.me/submissions/2fbda862-0b73-40e8-9b32-f1a45a8e7915

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_k_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos



set_option autoImplicit false
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution {k r : ℕ} {κ : Mat k r} (h : κ ∈ Kset k r) : κ⁻¹ ∈ GV k r := by
  obtain ⟨h1, h2⟩ := ea_k_iff.1 h
  have hinv : κ⁻¹ = κᴴ := Matrix.inv_eq_left_inv h2
  have h3 : κ * κᴴ = 1 := by
    first
      | exact mul_eq_one_comm.1 h2
      | (rw [← hinv]; exact Matrix.mul_nonsing_inv κ (Matrix.isUnit_det_of_left_inverse h2))
  have hH : κᴴ * Hpk k r * κ = Hpk k r := h1
  show (κ⁻¹)ᴴ * Hpk k r * κ⁻¹ = Hpk k r
  rw [hinv, Matrix.conjTranspose_conjTranspose]
  calc κ * Hpk k r * κᴴ = κ * (κᴴ * Hpk k r * κ) * κᴴ := by rw [hH]
    _ = (κ * κᴴ) * Hpk k r * (κ * κᴴ) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h3, Matrix.one_mul, Matrix.mul_one]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
