-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.eventually_linear_pairedDefectWordAverage_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/a828d72a-e375-4a75-a2df-79df605e1c65

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedWordPower_eventually_linear_pairedWordAverage_pow

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
    (k : ℕ) :
    ∀ᶠ n in l,
      ((L n) ^ k) (pairedDefectWordAverage s (z n) 0) =
        pairedDefectWordAverage s (z n) k := by
  have hnodes :
      ∀ᶠ n in l, ∀ i : ι,
        ((L n) ^ k) (z n (s i, 1)) =
          pairedWordAverage s (z n) k (s i, 1) :=
    (Filter.eventually_all).2 fun i =>
      eventually_linear_pairedWordAverage_pow l s L z hbase k
        (s i, 1)
  filter_upwards [hnodes] with n hn
  simp only [pairedDefectWordAverage, pairedWordAverage,
    map_smul, map_sum]
  exact congrArg (fun x => (Fintype.card ι : ℂ)⁻¹ • x)
    (Finset.sum_congr rfl fun i _ => hn i)
end SoficGroups.KunRootedWordPower
