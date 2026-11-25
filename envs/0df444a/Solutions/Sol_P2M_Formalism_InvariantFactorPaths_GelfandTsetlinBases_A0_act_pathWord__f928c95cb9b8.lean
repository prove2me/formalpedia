-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_act_pathWord__f928c95cb9b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:30.544097+00:00
-- url     : https://prove2.me/submissions/36ecd8b6-64b7-4101-9989-6134b522324d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_trInv_val
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_trInv_inv
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1hw_act_pathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actFormContract
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actFormWedge


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
theorem _root_.solution {A : Type} [CommRing A] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ)
    (Xr : ℕ → Fin n → A) (m : (Matrix (Fin n) (Fin n) A)ˣ) (j : ℕ) :
    pathWord isVec μ c (fun i => if isVec i then Matrix.vecMul (Xr i) (↑m : Matrix (Fin n) (Fin n) A)
        else Matrix.vecMul (Xr i) (↑m⁻¹ : Matrix (Fin n) (Fin n) A).transpose) j =
      actF (pathWord isVec μ c Xr j)
        (if 1 ≤ c then (↑m : Matrix (Fin n) (Fin n) A) else (↑m⁻¹ : Matrix (Fin n) (Fin n) A).transpose) := by
  by_cases h1 : 1 ≤ c
  · rw [if_pos h1]
    refine A1hw.act_pathWord actFormWedge actFormContract isVec μ c Xr _ m
      (fun i hi => ?_) (fun i hi => ?_) j
    · have : isVec i = true := by simpa [h1] using hi
      simp only [this, if_true]
    · have : isVec i = false := by simpa [h1] using hi
      simp only [this, Bool.false_eq_true, if_false]
  · rw [if_neg h1, ← trInv_val]
    refine A1hw.act_pathWord actFormWedge actFormContract isVec μ c Xr _ (trInv m)
      (fun i hi => ?_) (fun i hi => ?_) j
    · have : isVec i = false := by simpa [h1] using hi
      simp only [this, Bool.false_eq_true, if_false, trInv_val]
    · have : isVec i = true := by simpa [h1] using hi
      simp only [this, if_true, trInv_inv, Matrix.transpose_transpose]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
