-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.eventually_linear_pairedWordAverage_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/29facf75-4a31-4b42-b153-e88b238cdccb

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
    {G ι N : Type*} [Group G] [Fintype ι]
    {E : N → Type*}
    [∀ n, AddCommMonoid (E n)]
    [∀ n, Module ℂ (E n)]
    (l : Filter N) (s : ι → G)
    (L : ∀ n, E n →ₗ[ℂ] E n)
    (z : ∀ n, G × G → E n)
    (hbase : ∀ q, ∀ᶠ n in l,
      L n (z n q) = pairedWordAverage s (z n) 1 q)
    (k : ℕ) (q : G × G) :
    ∀ᶠ n in l,
      ((L n) ^ k) (z n q) = pairedWordAverage s (z n) k q := by
  induction k generalizing q with
  | zero =>
      exact Filter.Eventually.of_forall fun n => by
        simp [pairedWordAverage]
  | succ k ih =>
      have hnodes :
          ∀ᶠ n in l, ∀ i : ι,
            ((L n) ^ k) (z n (s i * q.1, s i * q.2)) =
              pairedWordAverage s (z n) k
                (s i * q.1, s i * q.2) :=
        (Filter.eventually_all).2 fun i =>
          ih (s i * q.1, s i * q.2)
      filter_upwards [hbase q, hnodes] with n hn hnode
      rw [pow_succ, Module.End.mul_apply, hn,
        pairedWordAverage, pairedWordAverage, map_smul, map_sum]
      apply congrArg (fun x => (Fintype.card ι : ℂ)⁻¹ • x)
      exact Finset.sum_congr rfl fun i _ => hnode i
end SoficGroups.KunRootedWordPower
