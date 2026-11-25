-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.lg_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:39:43.983132+00:00
-- url     : https://prove2.me/submissions/91116b63-2d14-451c-8f13-2e21806573eb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsShear_iter_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsShear_right_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsFil_exp_shear
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_mem_lieN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_exp_neg_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_st_exp
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
variable [FiniteDimensional ℝ A]
variable {st : A →ₗ[ℝ] A}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution (hF : IsFil F L) (hst : IsAdj F st) {g : A} (hg : g ∈ grpN F st) :
    lg L g ∈ lieN F st ∧ NormedSpace.exp (lg L g) = g := by
  obtain ⟨hg1, hg2⟩ := hg
  have hE := hF.exp_shear
  have hY0 : lg L g ∈ F 0 := (IsShear.iter_mem hE hg1 L).1
  have hexp : NormedSpace.exp (lg L g) = g := by
    have h' : NormedSpace.exp (lg L g) - 1 = g - 1 := IsShear.right_inv hF hE hg1
    simpa using h'
  refine ⟨?_, hexp⟩
  rw [mem_lieN]
  refine ⟨hY0, ?_⟩
  have hinv := exp_neg_mul (lg L g)
  rw [hexp] at hinv
  have hst_g : st g = NormedSpace.exp (-(lg L g)) := by
    calc st g = st g * (g * NormedSpace.exp (-(lg L g))) := by rw [hinv.2, mul_one]
      _ = (st g * g) * NormedSpace.exp (-(lg L g)) := (mul_assoc _ _ _).symm
      _ = NormedSpace.exp (-(lg L g)) := by rw [hg2, one_mul]
  have h1 : NormedSpace.exp (st (lg L g)) = NormedSpace.exp (-(lg L g)) := by
    rw [← st_exp hF hst hY0, hexp, hst_g]
  exact exp_injOn hF (hst.mem _ hY0) ((F 0).neg_mem hY0) h1
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
