-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.phiV_sc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:51.257788+00:00
-- url     : https://prove2.me/submissions/aa6f79de-fb24-49a6-8558-7adc202f0865

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_bvec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last

set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (a : Fin (r' + 1)) : phiV k (1 + r') (sc r' a) = liftVec k 1 r' (phiV k r' a) := by
  have ha := a.isLt
  by_cases h : a.val < r'
  · have h' : (sc r' a).val < 1 + r' := by
      simp only [sc]
      omega
    rw [phiV, dif_pos h', phiV, dif_pos h, lift_bvec]
    congr 1
    ext
    simp only [esI, sc, mp]
    omega
  · have h' : ¬ (sc r' a).val < 1 + r' := by
      simp only [sc]
      omega
    rw [phiV, dif_neg h', phiV, dif_neg h]
    simp only [epsV]
    have hlin : ∀ (c : ℂ) (x y : Fin (2 * r' + k + 1) → ℂ),
        liftVec k 1 r' (c • (x + y)) = c • (liftVec k 1 r' x + liftVec k 1 r' y) := by
      intro c x y
      funext q
      simp only [liftVec, Pi.smul_apply, Pi.add_apply]
      split_ifs <;> simp
    rw [hlin, lift_bvec, lift_bvec]
    congr 3 <;> (ext; simp only [wI, mp, Fin.val_zero, Fin.val_last]; omega)
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
