-- Prove2me | solution 1 for P2M_Formalism_L2_Indef_Tree_example_size_condition__be567d152dea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:52:06.757522+00:00
-- url     : https://prove2.me/submissions/f4d340b1-da7b-4e7a-b1e4-b4325054e0af

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsWeightedConditional
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ErrSum
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditionsOfExact
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Theorems.Thm_Formalism_L2_Indef_Tree_example_L_eq
import Theorems.Thm_Formalism_L2_Indef_Tree_example_b_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (K)
variable {K} (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K)))
variable (h3 : ∀ w ∈ Tw0, plc w = 3)
include h3
omit h3
namespace Formalism.L2.Indef.Tree
theorem _root_.solution : LeafSizes (exampleObject K v0 Tw0) := by
  have hY : (exampleObject K v0 Tw0).Y = 3 := by
    show (1 : ℝ) * 3 = 3
    norm_num
  have hb := example_b_ge v0 Tw0
  refine ⟨fun j => ⟨le_rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (0 : ℝ) ≤ 2 * 8 * (exampleObject K v0 Tw0).b
    linarith
  · rw [hY]
    norm_num
  · rw [hY, example_L_eq]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  · rw [hY]
    show (3 : ℝ) ≤ 1 * (exampleObject K v0 Tw0).b
    linarith
  · show (1 : ℝ) * (0 + 0) * (exampleObject K v0 Tw0).L ≤ 1 * (exampleObject K v0 Tw0).b
    rw [example_L_eq]
    linarith
  · show (1 : ℝ) ≤ 1
    exact le_rfl
  · show Real.log 1 ≤ (exampleObject K v0 Tw0).L
    rw [Real.log_one, example_L_eq]
    norm_num
  · rw [example_L_eq]
    norm_num
end Formalism.L2.Indef.Tree
