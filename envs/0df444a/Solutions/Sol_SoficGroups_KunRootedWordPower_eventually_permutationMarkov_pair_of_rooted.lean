-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.eventually_permutationMarkov_pair_of_rooted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/b7e61b07-ec3f-444b-8e51-7b57a329e08f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedWordPower_permutationMarkov_pair_of_rooted

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
    {G ι : Type*} [Group G] [Fintype ι]
    {V : ℕ → Type*} [∀ n, Fintype (V n)]
    (p : ∀ n, ι → Equiv.Perm (V n))
    (f : ∀ n, V n → ℝ)
    (σ : ∀ n, G → Equiv.Perm (V n))
    (s : ι → G)
    (hgenerator : ∀ n i, σ n (s i) = p n i)
    (hroot : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x)
    (q : G × G) :
    ∀ᶠ n in Filter.atTop,
      permutationMarkov (p n)
        (normalizedPairDisplacement (p n) (f n) (σ n) q) =
        pairedWordAverage s
          (normalizedPairDisplacement (p n) (f n) (σ n)) 1 q := by
  have hnodes :
      ∀ᶠ n in Filter.atTop, ∀ i : ι,
        (∀ x : V n, indicatorVector (f n) x ≠ 0 →
          σ n (s i * q.1) x =
            (σ n (s i) * σ n q.1) x) ∧
        (∀ x : V n, indicatorVector (f n) x ≠ 0 →
          σ n (s i * q.2) x =
            (σ n (s i) * σ n q.2) x) :=
    (Filter.eventually_all).2 fun i =>
      (hroot (s i) q.1).and (hroot (s i) q.2)
  filter_upwards [hnodes] with n hn
  exact permutationMarkov_pair_of_rooted
    (p n) (f n) (σ n) s (hgenerator n) q hn
end SoficGroups.KunRootedWordPower
