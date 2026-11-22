-- Prove2me | solution 1 for PebblingLean.FiniteProbability.uniformProbabilityReal_lt_le_of_exponentialMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:31.808663+00:00
-- url     : https://prove2.me/submissions/d525fe71-9987-458b-923b-2d21ace0b95c

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Theorems.Thm_PebblingLean_FiniteProbability_uniformProbabilityReal_lt_le_exponentialMoment

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω : Type*}
namespace PebblingLean.FiniteProbability
theorem _root_.solution [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) {T lam B : ℝ} (hlam : 0 < lam)
    (hmoment :
      uniformExpectationReal (fun ω : Ω => Real.exp (lam * (T - X ω))) ≤ B) :
    uniformProbabilityReal (fun ω : Ω => X ω < T) ≤ B :=
  (uniformProbabilityReal_lt_le_exponentialMoment X hlam).trans hmoment
end PebblingLean.FiniteProbability
