-- Prove2me | solution 1 for PebblingLean.FiniteProbability.uniformProbabilityReal_lt_le_exp_neg_of_exponentialMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:13:59.395234+00:00
-- url     : https://prove2.me/submissions/4aded946-e0d2-4b21-a5ad-7106c3ced05b

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Theorems.Thm_PebblingLean_FiniteProbability_uniformProbabilityReal_lt_le_of_exponentialMoment_le

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω : Type*}
namespace PebblingLean.FiniteProbability
theorem _root_.solution [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) {T lam exponent : ℝ} (hlam : 0 < lam)
    (hmoment :
      uniformExpectationReal (fun ω : Ω => Real.exp (lam * (T - X ω))) ≤
        Real.exp (-exponent)) :
    uniformProbabilityReal (fun ω : Ω => X ω < T) ≤ Real.exp (-exponent) :=
  uniformProbabilityReal_lt_le_of_exponentialMoment_le X hlam hmoment
end PebblingLean.FiniteProbability
