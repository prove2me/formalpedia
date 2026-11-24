-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.hpk_mv_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:06:14.153797+00:00
-- url     : https://prove2.me/submissions/dd14790c-28e9-4077-97ac-f589619a0ed5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermExpand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_wp_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace BL
section ex
variable (k n : ℕ)
private theorem Hpk_apply_wp_eq_ite (i : Fin (k - 1)) (j : Fin (2 * n + k + 1)) :
    Hpk k n (wp k n i) j = if wp k n i = j then 1 else 0 := by
  have hi := i.isLt
  have hv := wp_val k n i
  have hj := j.isLt
  have hij : wp k n i = j ↔ (wp k n i).val = j.val := Fin.ext_iff
  unfold Hpk
  by_cases h : (wp k n i).val = j.val
  · rw [if_pos (hij.2 h), if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, hij.2 h⟩,
      if_neg (by omega)]
  · rw [if_neg (fun he => h (hij.1 he)), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
end ex
end BL
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable (k n : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (i : Fin (k - 1)) (y : Fin (2 * n + k + 1) → ℂ) : (Hpk k n *ᵥ y) (wp k n i) = y (wp k n i) := by
  simp only [mulVec, dotProduct, Hpk_apply_wp_eq_ite, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
