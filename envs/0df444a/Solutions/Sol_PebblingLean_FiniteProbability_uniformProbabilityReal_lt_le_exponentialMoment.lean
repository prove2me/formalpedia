-- Prove2me | solution 1 for PebblingLean.FiniteProbability.uniformProbabilityReal_lt_le_exponentialMoment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:50.189287+00:00
-- url     : https://prove2.me/submissions/b601c8b2-67a4-4b82-873a-b5f69d6e152e

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Theorems.Thm_PebblingLean_FiniteProbability_uniformProbabilityReal_le_expect_div_of_event_le

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω : Type*}
namespace PebblingLean.FiniteProbability
theorem _root_.solution [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) {T lam : ℝ} (hlam : 0 < lam) :
    uniformProbabilityReal (fun ω : Ω => X ω < T) ≤
      uniformExpectationReal fun ω : Ω => Real.exp (lam * (T - X ω)) := by
  classical
  have hmarkov :=
    uniformProbabilityReal_le_expect_div_of_event_le
      (P := fun ω : Ω => X ω < T)
      (X := fun ω : Ω => Real.exp (lam * (T - X ω)))
      (a := 1)
      (by norm_num)
      (fun ω => Real.exp_nonneg _)
      (fun ω hlt => by
        have hdiff : 0 < T - X ω := sub_pos.mpr hlt
        have harg : 0 < lam * (T - X ω) := mul_pos hlam hdiff
        have hexp : Real.exp 0 < Real.exp (lam * (T - X ω)) :=
          Real.exp_lt_exp.mpr harg
        simpa using hexp.le)
  simpa using hmarkov
end PebblingLean.FiniteProbability
