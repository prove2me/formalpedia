-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.norm_normalizedIndicatorDisplacement_generator_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/762ef2b0-f685-4593-b2f2-42b4687857c1

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_permutation_indicator_displacement_norm_le_card_mul_markov_defect

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hdefect : permutationMarkov p (indicatorVector f) ≠
      indicatorVector f) (i : ι) :
    ‖normalizedIndicatorDisplacement p f (p i)‖ ≤
      (Fintype.card ι : ℝ) := by
  have hpos : 0 < ‖permutationMarkov p (indicatorVector f) -
      indicatorVector f‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hdefect)
  rw [normalizedIndicatorDisplacement, norm_smul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  apply (inv_mul_le_iff₀ hpos).mpr
  simpa [mul_comm] using
    permutation_indicator_displacement_norm_le_card_mul_markov_defect
      p f hf i
end SoficGroups.KunRootedIndicatorCrossing
