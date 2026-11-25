-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.ell_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:13:02.014613+00:00
-- url     : https://prove2.me/submissions/ecbb6fc1-9c5c-413b-b2e1-54c744e16ecf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_ell_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_firstVector_apply_first
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_firstVector_apply_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_eI_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_hcol
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_sum_fin_one_add_eq_add_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_fvec_lift
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
section Lv2
variable {k r' : ℕ}
private lemma liftVec_apply_sh (v : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' v (sh q) = v q := by
  have h1 : 1 ≤ (sh q : Fin (2 * (1 + r') + k + 1)).val ∧
      (sh q : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1 := by
    have := q.isLt
    simp only [sh, Fin.val_mk]
    omega
  simp only [liftVec]
  rw [dif_pos h1]
  exact congrArg v (Fin.ext (by simp [sh]))
private lemma liftVec_apply_eI_zero_eq_zero (v : Fin (2 * r' + k + 1) → ℂ) (h : 0 < 1 + r') :
    liftVec k 1 r' v (eI k (1 + r') ⟨0, h⟩) = 0 := by
  simp [liftVec, eI]
end Lv2
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
variable {k r' : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (hHA : HeisAct) (z1 : Fin (2 * r' + k + 1) → ℂ) (m : Mat k r') (X : HPar k r') :
    ell k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m) =
      -herm (Hpk k r') (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) X.1 + ell k r' z1 m := by
  have key : ∀ a : Fin (1 + r'),
      ((heis0 k r' X * ιLev k 1 r' m) *ᵥ fvec k (1 + r') (liftVec k 1 r' z1) ⟨a.val + 1, by omega⟩)
        (eI k (1 + r') a) =
      liftVec k 1 r' (m *ᵥ fvec k r' z1 ⟨a.val, by omega⟩) (eI k (1 + r') a) -
        herm (Hpk k r') (m *ᵥ fvec k r' z1 ⟨a.val, by omega⟩) X.1 * e0 k r' (eI k (1 + r') a) := by
    intro a
    rw [fvec_lift, hcol hHA]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [ell_col, ell_col, sum_fin_one_add_eq_add_sum]
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun a' _ => ?_)
  · beta_reduce
    rw [key, firstVector_apply_first, liftVec_apply_eI_zero_eq_zero, mul_one, zero_sub]
  · beta_reduce
    rw [key, firstVector_apply_succ, mul_zero, sub_zero, eI_succ, liftVec_apply_sh]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
