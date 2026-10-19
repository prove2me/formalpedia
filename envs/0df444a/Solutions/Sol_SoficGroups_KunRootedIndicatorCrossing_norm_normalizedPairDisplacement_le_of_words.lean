-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.norm_normalizedPairDisplacement_le_of_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/00725092-9ea1-4a30-8b43-570f21f2f84a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_norm_normalizedIndicatorDisplacement_list_prod_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {G ι V : Type*} [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hdefect : permutationMarkov p (indicatorVector f) ≠
      indicatorVector f)
    (σ : G → Equiv.Perm V) (w : G → List ι)
    (hw : ∀ g, σ g = ((w g).map p).prod) (g h : G) :
    ‖normalizedPairDisplacement p f σ (g, h)‖ ≤
      (Fintype.card ι : ℝ) *
        ((w g).length + (w h).length) := by
  unfold normalizedPairDisplacement
  calc
    ‖normalizedIndicatorDisplacement p f (σ g) -
      normalizedIndicatorDisplacement p f (σ h)‖ ≤
        ‖normalizedIndicatorDisplacement p f (σ g)‖ +
          ‖normalizedIndicatorDisplacement p f (σ h)‖ :=
      norm_sub_le _ _
    _ ≤ (Fintype.card ι : ℝ) * (w g).length +
          (Fintype.card ι : ℝ) * (w h).length := by
      rw [hw g, hw h]
      exact add_le_add
        (norm_normalizedIndicatorDisplacement_list_prod_le
          p f hf hdefect (w g))
        (norm_normalizedIndicatorDisplacement_list_prod_le
          p f hf hdefect (w h))
    _ = (Fintype.card ι : ℝ) *
          ((w g).length + (w h).length) := by
      ring
end SoficGroups.KunRootedIndicatorCrossing
