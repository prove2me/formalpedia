-- Prove2me | solution 1 for PebblingLean.FiniteProbability.one_sub_le_exp_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:58.3178+00:00
-- url     : https://prove2.me/submissions/dc35629b-a5ba-4d79-89a1-0d7949edceb1

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Concentration

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω : Type*}
namespace PebblingLean.FiniteProbability
theorem _root_.solution (u : ℝ) :
    1 - u ≤ Real.exp (-u) := by
  have h := Real.add_one_le_exp (-u)
  linarith
end PebblingLean.FiniteProbability
