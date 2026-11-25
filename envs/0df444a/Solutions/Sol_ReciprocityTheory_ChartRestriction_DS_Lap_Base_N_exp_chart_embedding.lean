-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.exp_chart_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:39:40.149346+00:00
-- url     : https://prove2.me/submissions/222ee453-118d-4604-995b-aa30b6c20541

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsFil_exp_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_mem_lieN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_exp_injOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {F : ℕ → Submodule ℝ A} {L : ℕ} {f g : A → A}
variable [FiniteDimensional ℝ A] {st : A →ₗ[ℝ] A} [MeasurableSpace A] [BorelSpace A]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution (hF : IsFil F L) :
    MeasurableEmbedding (fun Y : lieN F st => NormedSpace.exp (Y : A)) := by
  have hY0 : ∀ Y : lieN F st, (Y : A) ∈ F 0 := fun Y => (mem_lieN.1 Y.2).1
  have hcont : Continuous (fun Y : lieN F st => NormedSpace.exp (Y : A)) := by
    have e : (fun Y : lieN F st => NormedSpace.exp (Y : A)) = fun Y : lieN F st =>
        1 + ((Y : A) + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • (Y : A) ^ (k + 2)) := by
      funext Y
      exact hF.exp_eq (hY0 Y)
    rw [e]
    exact continuous_const.add (continuous_subtype_val.add (continuous_finset_sum _ fun k _ =>
      (continuous_subtype_val.pow _).const_smul _))
  haveI : ProperSpace (lieN F st) := FiniteDimensional.proper_real _
  exact hcont.measurableEmbedding fun Y Y' h => Subtype.ext (exp_injOn hF (hY0 Y) (hY0 Y') h)
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
