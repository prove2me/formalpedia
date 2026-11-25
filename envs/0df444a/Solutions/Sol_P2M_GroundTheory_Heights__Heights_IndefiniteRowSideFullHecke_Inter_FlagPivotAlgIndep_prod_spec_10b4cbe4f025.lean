-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotAlgIndep_prod_spec_10b4cbe4f025
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:22.52586+00:00
-- url     : https://prove2.me/submissions/bb6fae42-426c-4b8a-aba6-7398e441c74f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagPivotAlgIndep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotAlgIndep_genFrac_ne_zero_89e087030152

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotAlgIndep
variable (F : Type) [Field F] (n : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotAlgIndep
theorem _root_.solution (m : ℕ) (hm : m < n) (c : Fin n) (hc : m ≤ (c : ℕ)) :
    (∏ i : Fin m, spec F n (⟨i, by omega⟩, ⟨i, by omega⟩)) * spec F n (⟨m, hm⟩, c) = genFrac F n (⟨m, hm⟩, c) := by
  induction m generalizing c with
  | zero => simp [spec]
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega) ⟨m, by omega⟩ le_rfl]
    have e : (⟨m + 1 - 1, by omega⟩ : Fin n) = ⟨m, by omega⟩ := Fin.ext (by simp)
    simp only [spec, show ¬ ((c : ℕ) < m + 1) by omega, if_false, show m + 1 ≠ 0 by omega, dif_neg, not_false_eq_true, e]
    exact mul_div_cancel₀ _ (genFrac_ne_zero F n _)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotAlgIndep
