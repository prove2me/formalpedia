-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.exists_hyperfilter_diagonal_positive_pair_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/a3ca54f1-2189-46d7-af08-bfa969f2aff0

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_exists_hyperfilter_positive_gram_kernel_of_pointwise_bound

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {G : Type*} [Group G] {H : ℕ → Type*}
    [∀ n, SeminormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (v : ∀ n, G × G → H n) (B : G × G → ℝ)
    (hbound : ∀ n q, ‖v n q‖ ≤ B q)
    (hdiagonal : ∀ a g h j k : G,
      ∀ᶠ n in Filter.atTop,
        ⟪v n (a * g, a * h), v n (a * j, a * k)⟫_ℂ =
          ⟪v n (g, h), v n (j, k)⟫_ℂ)
    (hadd : ∀ n (g h j : G),
      v n (g, h) + v n (h, j) = v n (g, j)) :
    ∃ K : Matrix (G × G) (G × G) ℂ,
      K.PosSemidef ∧
      (∀ a g h j k : G,
        K (a * g, a * h) (a * j, a * k) = K (g, h) (j, k)) ∧
      (∀ g h j : G, ∀ q : G × G,
        K (g, h) q + K (h, j) q = K (g, j) q) ∧
      ∀ q r, Tendsto (fun n => ⟪v n q, v n r⟫_ℂ)
        (Filter.hyperfilter ℕ) (𝓝 (K q r)) := by
  obtain ⟨K, hpositive, hconv⟩ :=
    exists_hyperfilter_positive_gram_kernel_of_pointwise_bound
      v B hbound
  refine ⟨K, hpositive, ?_, ?_, hconv⟩
  · intro a g h j k
    have hevent :
        (fun n =>
          ⟪v n (a * g, a * h), v n (a * j, a * k)⟫_ℂ) =ᶠ[
          (Filter.hyperfilter ℕ : Filter ℕ)]
            (fun n => ⟪v n (g, h), v n (j, k)⟫_ℂ) :=
      (hdiagonal a g h j k).filter_mono Nat.hyperfilter_le_atTop
    exact tendsto_nhds_unique
      (hconv (a * g, a * h) (a * j, a * k))
      (Tendsto.congr' hevent.symm (hconv (g, h) (j, k)))
  · intro g h j q
    have haddconv :=
      (hconv (g, h) q).add (hconv (h, j) q)
    have hfunctions :
        (fun n =>
          ⟪v n (g, h), v n q⟫_ℂ +
            ⟪v n (h, j), v n q⟫_ℂ) =
          (fun n => ⟪v n (g, j), v n q⟫_ℂ) := by
      funext n
      rw [← inner_add_left, hadd]
    exact tendsto_nhds_unique haddconv
      (by rw [hfunctions]; exact hconv (g, j) q)
end SoficGroups.KunRootedIndicatorCrossing
