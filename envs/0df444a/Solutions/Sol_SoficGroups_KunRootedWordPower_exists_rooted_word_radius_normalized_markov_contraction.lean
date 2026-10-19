-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.exists_rooted_word_radius_normalized_markov_contraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/658dd0b7-ecca-4f3e-b499-27f26f5bca09

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedWordPower_eventually_normalizedIndicatorDefect_markov_pow_lt_of_rooted
import Theorems.Thm_SoficGroups_KunRootedWordPower_eventually_rooted_of_growing_word_radius

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
    {G : Type u} [Group G]
    (P : SoficGroups.KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, ∀ X : RootedIndicatorMarkovModel G ↥S,
      X.IsGenerated (fun i : ↥S => (i : G)) w →
      X.IsRootedAtRadius w r →
      permutationMarkov X.generator (indicatorVector X.indicator) ≠
        indicatorVector X.indicator →
      ‖((permutationMarkov X.generator)^[k])
          (normalizedIndicatorDefect X.generator X.indicator)‖ <
        kazhdanMarkovContractionFactor P S ^ k + ε := by
  classical
  letI : Nonempty (↥S) := ⟨⟨1, honeS⟩⟩
  by_contra h
  push Not at h
  choose X hgenerated hradius hdefect hbad using h
  let V : ℕ → Type u := fun n => (X n).carrier
  let p : ∀ n, ↥S → Equiv.Perm (V n) :=
    fun n => (X n).generator
  let f : ∀ n, V n → ℝ := fun n => (X n).indicator
  let σ : ∀ n, G → Equiv.Perm (V n) :=
    fun n => (X n).evaluation
  have hf : ∀ n x, f n x = 0 ∨ f n x = 1 :=
    fun n => (hgenerated n).indicator_mem
  have hw : ∀ n g, σ n g = ((w g).map (p n)).prod :=
    fun n => (hgenerated n).word_evaluation
  have hone : ∀ n, σ n 1 = 1 :=
    fun n => (hgenerated n).identity_evaluation
  have hgenerator : ∀ n (i : ↥S), σ n (i : G) = p n i :=
    fun n => (hgenerated n).generator_evaluation
  have hroots : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x := by
    intro a g
    exact eventually_rooted_of_growing_word_radius
      X w hradius a g
  have hstrict :=
    eventually_normalizedIndicatorDefect_markov_pow_lt_of_rooted
      P S honeS hcover hsymmetric p f σ w hf hdefect
        hw hone hgenerator hroots k ε hε
  have hbad' : ∀ n,
      kazhdanMarkovContractionFactor P S ^ k + ε ≤
        ‖((permutationMarkov (p n))^[k])
          (normalizedIndicatorDefect (p n) (f n))‖ :=
    hbad
  obtain ⟨n, hlt, hge⟩ :=
    (hstrict.and (Filter.Eventually.of_forall hbad')).exists
  exact (not_lt_of_ge hge) hlt
end SoficGroups.KunRootedWordPower
