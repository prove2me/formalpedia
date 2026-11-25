-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.th_ident
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:14.014232+00:00
-- url     : https://prove2.me/submissions/269352c8-7f44-4036-b55e-9bb93731f044

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InnerCLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExponentShiftEqLevelExponent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_sc_ne_zero
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
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (s : Fin (1 + r' + 1) → ℝ) (aw : ℝ) (x : HPar k r') (hG0 : 0 < Ga k (1 + r') 0 (Yx k r' x))
    (hGl : ∀ l, 0 ≤ Ga k (1 + r') l (Yx k r' x)) :
    ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (Dx k r' x ^ (-(aw + 2))) =
      ∏ l, ENNReal.ofReal (Ga k (1 + r') l (Yx k r' x) ^
        (-(if l = 0 then aw + 2 - ∑ l' : Fin (r' + 1), s (sc r' l') else s l) / 2)) := by
  have hPsi : 0 ≤ Psi k r' s x := Finset.prod_nonneg fun l _ => Real.rpow_nonneg (div_nonneg (hGl _) hG0.le) _
  rw [← ENNReal.ofReal_mul hPsi, ← ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (hGl l) _)]
  congr 1
  rw [Fin.prod_univ_succ, if_pos rfl]
  have e : ∀ i : Fin (1 + r'), Fin.succ i = sc r' (Fin.cast (by omega) i) := fun i => Fin.ext (by simp [sc])
  simp only [e, sc_ne_zero, if_false]
  rw [Fin.prod_congr' (fun j => Ga k (1 + r') (sc r' j) (Yx k r' x) ^ (-s (sc r' j) / 2)) (by omega : 1 + r' = r' + 1)]
  unfold Psi Dx
  have hP : ∏ l : Fin (r' + 1), (Ga k (1 + r') (sc r' l) (Yx k r' x) / Ga k (1 + r') 0 (Yx k r' x)) ^ (-s (sc r' l) / 2)
      = (∏ l : Fin (r' + 1), Ga k (1 + r') (sc r' l) (Yx k r' x) ^ (-s (sc r' l) / 2)) *
        Ga k (1 + r') 0 (Yx k r' x) ^ (∑ l : Fin (r' + 1), s (sc r' l) / 2) := by
    rw [Real.rpow_sum_of_pos hG0, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [Real.div_rpow (hGl _) hG0.le, div_eq_mul_inv, ← Real.rpow_neg hG0.le]
    congr 2; ring
  have hD : Real.sqrt (Ga k (1 + r') 0 (Yx k r' x)) ^ (-(aw + 2)) = Ga k (1 + r') 0 (Yx k r' x) ^ (-(aw + 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hG0.le]; congr 1; ring
  rw [hP, hD, mul_assoc, ← Real.rpow_add hG0, mul_comm]
  congr 2
  rw [← Finset.sum_div]; ring
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
