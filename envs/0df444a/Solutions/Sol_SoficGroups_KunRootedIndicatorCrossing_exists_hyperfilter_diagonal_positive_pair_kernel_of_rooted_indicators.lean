-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.exists_hyperfilter_diagonal_positive_pair_kernel_of_rooted_indicators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/0500910c-b739-49fe-9081-121724227cc6

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_normalizedPairDisplacement_inner_diagonal
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_normalizedPairDisplacement_add
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_norm_normalizedPairDisplacement_le_of_words
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_exists_hyperfilter_diagonal_positive_pair_kernel

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {G ι : Type*} [Group G] [Fintype ι] [Nonempty ι]
    {V : ℕ → Type*} [∀ n, Fintype (V n)]
    (p : ∀ n, ι → Equiv.Perm (V n))
    (f : ∀ n, V n → ℝ)
    (σ : ∀ n, G → Equiv.Perm (V n))
    (w : G → List ι)
    (hf : ∀ n x, f n x = 0 ∨ f n x = 1)
    (hdefect : ∀ n, permutationMarkov (p n) (indicatorVector (f n)) ≠
      indicatorVector (f n))
    (hw : ∀ n g, σ n g = ((w g).map (p n)).prod)
    (hroot : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x) :
    ∃ K : Matrix (G × G) (G × G) ℂ,
      K.PosSemidef ∧
      (∀ a g h j k : G,
        K (a * g, a * h) (a * j, a * k) = K (g, h) (j, k)) ∧
      (∀ g h j : G, ∀ q : G × G,
        K (g, h) q + K (h, j) q = K (g, j) q) ∧
      ∀ q r,
        Tendsto
          (fun n =>
            ⟪normalizedPairDisplacement (p n) (f n) (σ n) q,
              normalizedPairDisplacement (p n) (f n) (σ n) r⟫_ℂ)
          (Filter.hyperfilter ℕ) (𝓝 (K q r)) := by
  let v : ∀ n, G × G → EuclideanSpace ℂ (V n) :=
    fun n q => normalizedPairDisplacement (p n) (f n) (σ n) q
  let B : G × G → ℝ := fun q =>
    (Fintype.card ι : ℝ) * ((w q.1).length + (w q.2).length)
  apply exists_hyperfilter_diagonal_positive_pair_kernel v B
  · intro n q
    exact norm_normalizedPairDisplacement_le_of_words
      (p n) (f n) (hf n) (hdefect n) (σ n) w (hw n) q.1 q.2
  · intro a g h j k
    filter_upwards [hroot a g, hroot a h, hroot a j, hroot a k]
      with n hg hh hj hk
    exact normalizedPairDisplacement_inner_diagonal
      (p n) (f n) (σ n) a g h j k hg hh hj hk
  · intro n g h j
    exact normalizedPairDisplacement_add (p n) (f n) (σ n) g h j
end SoficGroups.KunRootedIndicatorCrossing
