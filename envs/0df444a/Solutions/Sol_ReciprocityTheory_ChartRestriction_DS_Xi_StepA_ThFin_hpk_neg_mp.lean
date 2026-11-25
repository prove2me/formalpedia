-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin.hpk_neg_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:28:34.039362+00:00
-- url     : https://prove2.me/submissions/6ea9a2be-fc0b-49aa-9cec-e61a571107ad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkNegMp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ThFin_sgn_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_hpk_mulVec
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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
theorem _root_.solution (k r' : ℕ) :
    MeasurePreserving (fun v : Fin (2 * r' + k + 1) → ℂ => Hpk k r' *ᵥ (-v)) volume volume := by
  have hP := volume_preserving_arrowCongr' (GS.sigE k r') (MeasurableEquiv.refl ℂ)
    (MeasurePreserving.id volume)
  have hS := volume_preserving_pi (f := fun (i : Fin (2 * r' + k + 1)) (z : ℂ) => (-GS.sgnI k r' i) * z)
    fun i => sgn_mp k r' i
  have e : (fun v : Fin (2 * r' + k + 1) → ℂ => Hpk k r' *ᵥ (-v)) =
      (fun (v : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) => (-GS.sgnI k r' i) * v i) ∘
        MeasurableEquiv.arrowCongr' (GS.sigE k r') (MeasurableEquiv.refl ℂ) := by
    funext v i
    simp only [Function.comp_apply, Pi.neg_apply, GS.hpk_mulVec, neg_mul, mul_neg]
    rfl
  rw [e]
  exact hS.comp hP
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
