-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.tendsto_norm_normalizedIndicatorDefect_markov_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/b590b6df-f535-4793-b01d-9eff639eea76

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedWordPower_tendsto_norm_pairedDefectWordAverage_of_gram
import Theorems.Thm_SoficGroups_KunRootedWordPower_permutationMarkovLinear_pow_apply
import Theorems.Thm_SoficGroups_KunRootedWordPower_eventually_permutationMarkov_pair_of_rooted
import Theorems.Thm_SoficGroups_KunRootedWordPower_eventually_linear_pairedDefectWordAverage_pow
import Theorems.Thm_SoficGroups_KunRootedWordPower_pairedDefectWordAverage_zero_eq_normalizedIndicatorDefect

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
    {G ι H : Type*} [Group G] [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {V : ℕ → Type*} [∀ n, Fintype (V n)]
    (p : ∀ n, ι → Equiv.Perm (V n))
    (f : ∀ n, V n → ℝ)
    (σ : ∀ n, G → Equiv.Perm (V n))
    (s : ι → G)
    (v : G × G → H)
    (hone : ∀ n, σ n 1 = 1)
    (hgenerator : ∀ n i, σ n (s i) = p n i)
    (hroot : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x)
    (hgram : ∀ q r,
      Tendsto
        (fun n =>
          ⟪normalizedPairDisplacement (p n) (f n) (σ n) q,
            normalizedPairDisplacement (p n) (f n) (σ n) r⟫_ℂ)
        (Filter.hyperfilter ℕ)
        (𝓝 ⟪v q, v r⟫_ℂ))
    (k : ℕ) :
    Tendsto
      (fun n =>
        ‖((permutationMarkov (p n))^[k])
          (normalizedIndicatorDefect (p n) (f n))‖)
      (Filter.hyperfilter ℕ)
      (𝓝 ‖pairedDefectWordAverage s v k‖) := by
  let z : ∀ n, G × G → EuclideanSpace ℂ (V n) :=
    fun n => normalizedPairDisplacement (p n) (f n) (σ n)
  let L : ∀ n, EuclideanSpace ℂ (V n) →ₗ[ℂ]
      EuclideanSpace ℂ (V n) :=
    fun n => permutationMarkovLinear (p n)
  have hbase : ∀ q, ∀ᶠ n in Filter.atTop,
      L n (z n q) = pairedWordAverage s (z n) 1 q := by
    intro q
    simpa only [L, permutationMarkovLinear_apply, z] using
      eventually_permutationMarkov_pair_of_rooted
        p f σ s hgenerator hroot q
  have hp := eventually_linear_pairedDefectWordAverage_pow
    Filter.atTop s L z hbase k
  have hpow :
      ∀ᶠ n in Filter.atTop,
        ((permutationMarkov (p n))^[k])
          (normalizedIndicatorDefect (p n) (f n)) =
            pairedDefectWordAverage s (z n) k := by
    filter_upwards [hp] with n hn
    rw [← permutationMarkovLinear_pow_apply]
    change ((L n) ^ k) (normalizedIndicatorDefect (p n) (f n)) =
      pairedDefectWordAverage s (z n) k
    rw [← pairedDefectWordAverage_zero_eq_normalizedIndicatorDefect
      (p n) (f n) (σ n) s (hone n) (hgenerator n)]
    exact hn
  have hlimit :=
    tendsto_norm_pairedDefectWordAverage_of_gram
      (Filter.hyperfilter ℕ) s z v hgram k
  have heq :
      (fun n =>
        ‖((permutationMarkov (p n))^[k])
          (normalizedIndicatorDefect (p n) (f n))‖) =ᶠ[
            (Filter.hyperfilter ℕ : Filter ℕ)]
        (fun n => ‖pairedDefectWordAverage s (z n) k‖) :=
    (hpow.filter_mono Nat.hyperfilter_le_atTop).mono
      fun n hn => congrArg norm hn
  exact hlimit.congr' heq.symm
end SoficGroups.KunRootedWordPower
