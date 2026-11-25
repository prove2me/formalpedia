-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.eps_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:34:11.452915+00:00
-- url     : https://prove2.me/submissions/cbcd40c9-f1a9-43c8-96a3-4511c7a980e9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_dot_bvec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_bvec_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_bvec_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_sq2_mul_sq2_eq_half
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_star_inv_sqrt_two

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
variable (k n : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (hk : 1 ≤ k) : star (epsV k n) ⬝ᵥ epsV k n = 1 := by
  unfold epsV
  have hne : (wI k n 0).val ≠ (wI k n (Fin.last k)).val := by simp only [wI, Fin.val_zero, Fin.val_last]; omega
  rw [star_smul, star_inv_sqrt_two, smul_dotProduct, dotProduct_smul, star_add, add_dotProduct, dot_bvec, dot_bvec]
  simp only [Pi.add_apply, bvec_self, bvec_ne _ _ hne, bvec_ne _ _ (Ne.symm hne), smul_eq_mul]
  linear_combination 2 * sq2_mul_sq2_eq_half
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
