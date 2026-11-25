-- Prove2me | solution 1 for P2M_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousLetters_blockPoly_isWeightedHomogeneous__4c12daa4a94f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:11:09.309515+00:00
-- url     : https://prove2.me/submissions/e51a767e-6ef0-49c6-8d07-b3eca56eb0cc

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IsWHLetterMinorK
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousLetters_wRowG_letter
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousLetters_isWH_letter_minorK
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousLetters_num_ch
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousLetters_num_mon
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_isWH_deg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_isWH_letter_minorK
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_isWH_minorK_row
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_isWH_rename
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_num_ch
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_num_mon
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod


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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
open Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters
open WeightHomogeneousMinors
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  (X : RowData C V d I J) (F : Flag X) (idx : ∀ g, I g → ℕ) (std : ∀ g t (c : Fin (X.rkF g t)), idx g (F.en g t c) = c.val)
include std
namespace Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters
theorem _root_.solution (b : GlobalTheory d) (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) :
    IsWeightedHomogeneous (wRowG X idx g0 t0 c0) (b.poly X F)
      (∑ k ∈ Finset.Icc (c0 + 1) (X.rkF g0 t0), b.wt X g0 t0 k) := by
  cases b with
  | ch g t u =>
    exact isWH_deg ((isWH_letter_minorK X F idx std g0 t0 c0 g t).pow u) (num_ch X g0 t0 c0 g t u)
  | bi g t i y =>
    refine isWH_deg (((isWH_letter_minorK X F idx std g0 t0 c0 g t).pow (V.l ^ i * y)).mul
      ((isWH_letter_minorK X F idx std g0 t0 c0 (1 - g) (t + (i : ZMod d))).pow y)) ?_
    simp only [GlobalTheory.wt]
    rw [Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) (num_ch X g0 t0 c0 g t _) (num_ch X g0 t0 c0 (1 - g) (t + (i : ZMod d)) y)
  | mon g e N =>
    refine isWH_deg (IsWeightedHomogeneous.prod _ _ _ fun t _ => isWH_rename _
      (IsWeightedHomogeneous.prod _ _ _ fun k _ =>
        (isWH_minorK_row (g = g0 ∧ t = t0) c0 fun x => wRowG_letter X F idx std g0 t0 c0 g t x).pow (e t k))) ?_
    simp only [GlobalTheory.wt]
    exact num_mon X g0 t0 c0 g e N
end Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters
