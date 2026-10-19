-- Prove2me | solution 1 for SoficGroups.finite_union_bad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/91ca8902-5871-4ce5-8d70-3dda6ef75d91

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {α : ℕ → Type*} [∀ n, DecidableEq (α n)]
    {ι : Type*} (I : Finset ι)
    (V : ∀ n, Finset (α n)) (B : ∀ n, ι → Finset (α n))
    (hbad : ∀ i ∈ I, Tendsto
      (fun n => (((V n ∩ B n i).card : ℝ) / (V n).card))
      atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        (((V n ∩ I.biUnion (B n)).card : ℝ) / (V n).card))
      atTop (𝓝 0) := by
  classical
  have hsum : Tendsto
      (fun n =>
        ∑ i ∈ I, (((V n ∩ B n i).card : ℝ) / (V n).card))
      atTop (𝓝 0) := by
    induction I using Finset.induction_on with
    | empty =>
        simp
    | @insert i I hi ih =>
        have hfirst := hbad i (Finset.mem_insert_self i I)
        have hrest := ih (fun j hj =>
          hbad j (Finset.mem_insert_of_mem hj))
        simpa [Finset.sum_insert, hi] using hfirst.add hrest
  refine squeeze_zero (fun n => by positivity) ?_ hsum
  intro n
  have hcard :
      ((V n ∩ I.biUnion (B n)).card : ℝ) ≤
        ∑ i ∈ I, ((V n ∩ B n i).card : ℝ) := by
    rw [Finset.inter_biUnion]
    exact_mod_cast
      (Finset.card_biUnion_le
        (s := I) (t := fun i => V n ∩ B n i))
  calc
    ((V n ∩ I.biUnion (B n)).card : ℝ) / (V n).card ≤
        (∑ i ∈ I, ((V n ∩ B n i).card : ℝ)) / (V n).card :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = ∑ i ∈ I, (((V n ∩ B n i).card : ℝ) / (V n).card) :=
      Finset.sum_div _ _ _
end SoficGroups
