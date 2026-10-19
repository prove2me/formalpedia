-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.norm_normalizedIndicatorDefect_markov_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/53cd1449-e13e-47e1-86ed-ca27b1affb55

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedWordPower_permutationMarkovLinear_pow_apply

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) (k : ℕ) :
    ‖((permutationMarkov p)^[k])
        (normalizedIndicatorDefect p f)‖ =
      ‖((permutationMarkovLinear p) ^ k)
          (permutationMarkov p (indicatorVector f) -
            indicatorVector f)‖ /
        ‖permutationMarkov p (indicatorVector f) -
          indicatorVector f‖ := by
  rw [← permutationMarkovLinear_pow_apply]
  simp [normalizedIndicatorDefect, map_smul,
    norm_smul, norm_inv, div_eq_mul_inv,
    Complex.norm_real, mul_comm]
end SoficGroups.KunRootedWordPower
