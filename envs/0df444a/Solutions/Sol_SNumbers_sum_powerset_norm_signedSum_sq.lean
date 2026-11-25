-- Prove2me | solution 1 for SNumbers.sum_powerset_norm_signedSum_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:10:57.519115+00:00
-- url     : https://prove2.me/submissions/f8acc33b-818c-4cbc-9aaf-5dd7a94ed7a1

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Theorems.Thm_SNumbers_signedSum_empty
public import Theorems.Thm_SNumbers_signedSum_insert_of_notMem
public import Theorems.Thm_SNumbers_signedSum_insert_insert
attribute [local simp] SNumbers.signedSum_empty

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers
variable {ι : Type*} [DecidableEq ι]
namespace SNumbers
theorem _root_.solution (𝕜 : Type*) [RCLike 𝕜] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (w : ι → H) (J : Finset ι) :
    ∑ S ∈ J.powerset, ‖signedSum w S J‖ ^ 2 = 2 ^ J.card * ∑ j ∈ J, ‖w j‖ ^ 2 := by
  induction J using Finset.induction_on with
  | empty => simp
  | insert a J ha ih =>
      -- The two sign patterns extending `S ⊆ J` differ by `± w a`.
      have key : ∀ S ∈ J.powerset,
          ‖signedSum w S (insert a J)‖ ^ 2
              + ‖signedSum w (insert a S) (insert a J)‖ ^ 2
            = 2 * (‖signedSum w S J‖ ^ 2 + ‖w a‖ ^ 2) := by
        intro S hS
        have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
        rw [signedSum_insert_of_notMem ha haS, signedSum_insert_insert ha]
        linarith [parallelogram_law_with_norm (𝕜 := 𝕜) (signedSum w S J) (w a)]
      have hsplit : ∑ S ∈ (insert a J).powerset, ‖signedSum w S (insert a J)‖ ^ 2
          = ∑ S ∈ J.powerset, (‖signedSum w S (insert a J)‖ ^ 2
              + ‖signedSum w (insert a S) (insert a J)‖ ^ 2) := by
        rw [Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
      rw [hsplit, Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.sum_add_distrib, ih,
        Finset.sum_const, Finset.card_powerset, Finset.card_insert_of_notMem ha,
        Finset.sum_insert ha, nsmul_eq_mul]
      push_cast
      ring
end SNumbers
