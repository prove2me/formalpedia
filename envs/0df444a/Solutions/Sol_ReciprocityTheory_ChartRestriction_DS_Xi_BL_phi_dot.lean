-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.phi_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:58:11.502799+00:00
-- url     : https://prove2.me/submissions/f1639e44-bc85-4123-817b-d72181ee3e40

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_dot_bvec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_bvec_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_bvec_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_eps_dot

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
theorem _root_.solution (hk : 1 ≤ k) (a b : Fin (n + 1)) :
    star (phiV k n b) ⬝ᵥ phiV k n a = if a = b then 1 else 0 := by
  have hv : a = b ↔ a.val = b.val := Fin.ext_iff
  unfold phiV
  split_ifs with ha hb hab hb hab hb hab hb hab
  · subst hab; rw [dot_bvec, bvec_self]
  · rw [dot_bvec, bvec_ne]; simp only [esI, Fin.val_mk]; omega
  · omega
  · unfold epsV
    rw [dot_bvec, Pi.smul_apply, Pi.add_apply, bvec_ne, bvec_ne, add_zero, smul_zero]
    · simp only [esI, wI, Fin.val_mk]; simp; omega
    · simp only [esI, wI, Fin.val_mk]; simp; omega
  · omega
  · unfold epsV
    rw [star_smul, smul_dotProduct, star_add, add_dotProduct, dot_bvec, dot_bvec, bvec_ne, bvec_ne, add_zero, smul_zero]
    · simp only [esI, wI, Fin.val_mk]; simp; omega
    · simp only [esI, wI, Fin.val_mk]; simp; omega
  · exact eps_dot k n hk
  · omega
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
