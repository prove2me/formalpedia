-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.linear_pairedWordAverage_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/e45d3241-4c9e-4f42-b534-ef5d3824a0a8

import Mathlib
import Definitions.Def_NonSoficGroup

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
    {G ι E : Type*} [Group G] [Fintype ι]
    [AddCommMonoid E] [Module ℂ E]
    (s : ι → G) (L : E →ₗ[ℂ] E)
    (z : G × G → E)
    (hbase : ∀ q, L (z q) = pairedWordAverage s z 1 q)
    (k : ℕ) (q : G × G) :
    (L ^ k) (z q) = pairedWordAverage s z k q := by
  induction k generalizing q with
  | zero => simp [pairedWordAverage]
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, hbase q,
        pairedWordAverage, pairedWordAverage,
        map_smul, map_sum]
      apply congrArg (fun x => (Fintype.card ι : ℂ)⁻¹ • x)
      exact Finset.sum_congr rfl fun i _ =>
        ih (s i * q.1, s i * q.2)
end SoficGroups.KunRootedWordPower
