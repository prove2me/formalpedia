-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_phiV_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:44.801698+00:00
-- url     : https://prove2.me/submissions/606de622-da70-4890-a99b-805a6897332d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
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
theorem _root_.solution {k r : ℕ} (b : Fin (r + 1)) (i : Fin (2 * r + k + 1)) :
    phiV k r b i = if b.val < r then (if i.val = 2 * r + k - b.val then 1 else 0) else
      ((Real.sqrt 2)⁻¹ : ℂ) * ((if i.val = r then 1 else 0) + (if i.val = r + k then 1 else 0)) := by
  simp only [phiV]
  by_cases h1 : b.val < r
  · rw [dif_pos h1, if_pos h1]
    simp only [bvec, Pi.single_apply, esI, Fin.ext_iff]
  · rw [dif_neg h1, if_neg h1]
    simp only [epsV, bvec, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.single_apply, wI, Fin.ext_iff,
      Fin.val_zero, Fin.val_last, Nat.add_zero]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
