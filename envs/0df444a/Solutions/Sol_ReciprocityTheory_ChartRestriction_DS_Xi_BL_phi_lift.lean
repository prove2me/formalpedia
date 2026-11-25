-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.phi_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:23:21.125878+00:00
-- url     : https://prove2.me/submissions/dd951a35-6a61-4369-98dc-a252a7db56bc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_lv_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_lv_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_bvec_lv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable {k r' : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (a : Fin (r' + 1)) : liftVec k 1 r' (phiV k r' a) = phiV k (1 + r') (su a) := by
  unfold phiV
  by_cases h : a.val < r'
  · have h' : (su a).val < 1 + r' := by rw [su_val]; omega
    rw [dif_pos h, dif_pos h', ← bvec_lv]
    congr 1
    ext
    simp only [sh, esI, su_val, Fin.val_mk]
    omega
  · have h' : ¬ (su a).val < 1 + r' := by rw [su_val]; omega
    rw [dif_neg h, dif_neg h']
    unfold epsV
    have e0 : sh (wI k r' 0) = wI k (1 + r') 0 := by
      ext
      simp only [sh, wI, Fin.val_mk]
      omega
    have e1 : sh (wI k r' (Fin.last k)) = wI k (1 + r') (Fin.last k) := by
      ext
      simp only [sh, wI, Fin.val_mk]
      omega
    rw [lv_smul, lv_add, ← bvec_lv, ← bvec_lv, e0, e1]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
