-- Prove2me | solution 1 for PebblingLean.FiniteProbability.uniformProbabilityReal_eq_coe_uniformProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:01.588832+00:00
-- url     : https://prove2.me/submissions/ccbbd1bb-880d-4f22-9081-4a2aae5d950a

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
theorem _root_.solution [Fintype Ω]
    (P : Ω → Prop) [DecidablePred P] :
    uniformProbabilityReal P = (uniformProbability P : ℝ) := by
  simp [uniformProbabilityReal, uniformProbability]
end PebblingLean.FiniteProbability
