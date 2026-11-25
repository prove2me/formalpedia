-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.FsE_oneStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:08:01.275286+00:00
-- url     : https://prove2.me/submissions/77f6c0db-eead-4749-ad24-d4b2e7e7ed1c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_Dl_Y_sc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_Dl_Y_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_Dl_oneStep
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


section
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
section lev
variable (k r' : ℕ)
end lev
section dl
variable (k r : ℕ)
end dl
section a1
variable (k r' : ℕ)
private lemma prod_fin_eq_zero_mul_prod_sc (F : Fin (1 + r' + 1) → ℝ≥0∞) :
    ∏ l, F l = F 0 * ∏ l : Fin (r' + 1), F (sc r' l) := by
  rw [Fin.prod_univ_succ]
  congr 1
  exact Fintype.prod_equiv (finCongr (by omega)) _ _ (fun l => congrArg F (Fin.ext (by simp [sc])))
end a1
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

set_option autoImplicit false
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (hHA : HeisAct) (hHM : HeisMem) (x x' : HPar k r') (c : ℂ) (g : Mat k r')
    (s : Fin (1 + r' + 1) → ℝ) :
    FsE k (1 + r') s (oneStep k r' x c g x') =
      (∏ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l)) * FsE k r' (fun l => s (sc r' l)) g := by
  simp only [FsE, Dl_oneStep k r' hHA hHM x x' c g]
  rw [prod_fin_eq_zero_mul_prod_sc, prod_fin_eq_zero_mul_prod_sc]
  simp only [Dl_Y_zero, Dl_Y_sc, nnnorm_mul, ENNReal.coe_mul]
  first
  | simp only [ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top]
  | simp only [ENNReal.coe_mul_rpow]
  rw [Finset.prod_mul_distrib]
  ring
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
