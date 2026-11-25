-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dc_aeval_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:54.791202+00:00
-- url     : https://prove2.me/submissions/39145f67-0feb-4b3a-8cb9-aec90d6d552d

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
variable {T : Module.End ℂ Y} {S : Submodule ℂ Y} {B : Finset ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hT : ∀ f ∈ S, T f ∈ S) (p : ℂ[X]) : ∀ f ∈ S, aeval T p f ∈ S := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => intro f hf; simpa using S.add_mem (hp f hf) (hq f hf)
  | monomial k a =>
    intro f hf
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    refine S.smul_mem _ ?_
    induction k with
    | zero => simpa using hf
    | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact hT _ ih
end ReciprocityTheory.ChartRestriction.DS
