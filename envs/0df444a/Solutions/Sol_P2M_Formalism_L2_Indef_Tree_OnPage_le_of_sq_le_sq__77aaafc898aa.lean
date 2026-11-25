-- Prove2me | solution 1 for P2M_Formalism_L2_Indef_Tree_OnPage_le_of_sq_le_sq__77aaafc898aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:55:53.588679+00:00
-- url     : https://prove2.me/submissions/2e490893-0e2b-4af2-a803-c61424b73304

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage

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
open Formalism.L2.Indef.Tree.OnPage
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}
namespace Formalism.L2.Indef.Tree.OnPage
theorem _root_.solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hc
  push_neg at hc
  have h1 : b * b < a * a := mul_self_lt_mul_self hb hc
  nlinarith
end Formalism.L2.Indef.Tree.OnPage
