-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.hpk_bvec_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:57.491954+00:00
-- url     : https://prove2.me/submissions/92a791ab-b21f-4195-a6ab-fcb1e8a7c58c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermExpand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_wp_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_hpk_conjT

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
theorem _root_.solution (i : Fin (k - 1)) : Hpk k n *ᵥ wv k n i = wv k n i := by
  funext p
  have hc : Hpk k n p (wp k n i) = star (Hpk k n (wp k n i) p) := by
    have := congrFun (congrFun (hpk_conjT k n) p) (wp k n i)
    rw [Matrix.conjTranspose_apply] at this
    exact this.symm
  simp only [wv, bvec, mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hc, Hpk_apply_wp_eq_ite]
  by_cases h : wp k n i = p
  · subst h; simp
  · rw [if_neg h, if_neg (fun he => h he.symm), star_zero]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
