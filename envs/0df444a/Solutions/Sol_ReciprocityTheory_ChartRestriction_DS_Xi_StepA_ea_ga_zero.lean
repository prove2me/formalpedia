-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_ga_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:24:37.234149+00:00
-- url     : https://prove2.me/submissions/e23bc935-3357-4056-bd8a-52bdb4d2a920

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_StarLastDotLast
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
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution {k r : ℕ} (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) : Ga k r 0 Y = (star (Y 0) ⬝ᵥ Y 0).re := by
  have h1 : ∀ (m : ℕ), m = 0 → ∀ A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, A.det = A 0 0 := by
    rintro m rfl A; exact det_fin_one A
  unfold Ga
  rw [h1 (0 : Fin (r + 1)).val (by simp)]
  simp only [of_apply, Fin.castLE_zero]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
