-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.tt_prodS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:25:03.90996+00:00
-- url     : https://prove2.me/submissions/d8db0349-444d-463b-80b9-b2ce68e80281

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_tt_su
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_tt_00
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_Iic_su

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
variable (τ : Matrix (Fin (r' + 1)) (Fin (r' + 1)) ℂ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (a : Fin (r' + 1)) :
    ∏ j ∈ Finset.Iic (su a), ‖tt τ j j‖ ^ 2 = ∏ j ∈ Finset.Iic a, ‖τ j j‖ ^ 2 := by
  rw [Iic_su, Finset.prod_insert, Finset.prod_map, tt_00]
  · rw [norm_one, one_pow, one_mul]
    refine Finset.prod_congr rfl fun x _ => ?_
    show ‖tt τ (su x) (su x)‖ ^ 2 = _
    rw [tt_su]
  · simp only [Finset.mem_map, not_exists, not_and]
    intro b _ h
    have h' := congrArg Fin.val h
    change (su b).val = (0 : Fin (1 + r' + 1)).val at h'
    rw [su_val] at h'
    simp at h'
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
