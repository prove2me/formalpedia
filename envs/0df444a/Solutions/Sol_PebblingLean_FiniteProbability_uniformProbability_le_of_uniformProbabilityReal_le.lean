-- Prove2me | solution 1 for PebblingLean.FiniteProbability.uniformProbability_le_of_uniformProbabilityReal_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:14.827832+00:00
-- url     : https://prove2.me/submissions/b553e45f-1bfe-4628-8c91-6a4660b719c3

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Theorems.Thm_PebblingLean_FiniteProbability_uniformProbabilityReal_eq_coe_uniformProbability

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω : Type*}
namespace PebblingLean.FiniteProbability
theorem _root_.solution [Fintype Ω]
    {P : Ω → Prop} [DecidablePred P] {eps : ℚ}
    (h : uniformProbabilityReal P ≤ (eps : ℝ)) :
    uniformProbability P ≤ eps := by
  have hcast : ((uniformProbability P : ℚ) : ℝ) ≤ (eps : ℝ) := by
    simpa [uniformProbabilityReal_eq_coe_uniformProbability] using h
  exact_mod_cast hcast
end PebblingLean.FiniteProbability
