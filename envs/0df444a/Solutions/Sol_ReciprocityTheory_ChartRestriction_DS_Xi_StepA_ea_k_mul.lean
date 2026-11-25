-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_k_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:30.107203+00:00
-- url     : https://prove2.me/submissions/22ada358-5184-4499-84cb-01feeb53c96d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_k_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_gv_mul
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
theorem _root_.solution {k r : ℕ} {a b : Mat k r} (ha : a ∈ Kset k r) (hb : b ∈ Kset k r) : a * b ∈ Kset k r := by
  obtain ⟨ha1, ha2⟩ := ea_k_iff.1 ha
  obtain ⟨hb1, hb2⟩ := ea_k_iff.1 hb
  refine ea_k_iff.2 ⟨ea_gv_mul ha1 hb1, ?_⟩
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * (a * b) = bᴴ * (aᴴ * a) * b := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [ha2, Matrix.mul_one, hb2]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
