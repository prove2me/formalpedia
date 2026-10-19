-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.exists_hyperfilter_positive_gram_kernel_of_pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/83e4b850-f73e-45f7-8edc-91c9522098de

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_exists_hyperfilter_gram_limit_of_pointwise_bound
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_gram_posSemidef_infinite

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {I : Type*} {H : ℕ → Type*}
    [∀ n, SeminormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (v : ∀ n, I → H n) (B : I → ℝ)
    (hbound : ∀ n i, ‖v n i‖ ≤ B i) :
    ∃ K : Matrix I I ℂ,
      K.PosSemidef ∧
      ∀ i j, Tendsto (fun n => ⟪v n i, v n j⟫_ℂ)
        (Filter.hyperfilter ℕ) (𝓝 (K i j)) := by
  obtain ⟨K, hconv⟩ :=
    exists_hyperfilter_gram_limit_of_pointwise_bound v B hbound
  have hhermitian : K.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    apply tendsto_nhds_unique (hconv j i).star
    have hsymm :
        (fun n => star ⟪v n j, v n i⟫_ℂ) =
          (fun n => ⟪v n i, v n j⟫_ℂ) := by
      funext n
      exact inner_conj_symm _ _
    rw [hsymm]
    exact hconv i j
  refine ⟨K, ⟨hhermitian, ?_⟩, hconv⟩
  intro c
  have hquadratic :
      Tendsto
        (fun n => c.sum fun i z =>
          c.sum fun j w => star z * ⟪v n i, v n j⟫_ℂ * w)
        (Filter.hyperfilter ℕ)
        (𝓝 (c.sum fun i z =>
          c.sum fun j w => star z * K i j * w)) := by
    simpa only [Finsupp.sum] using
      tendsto_finsetSum c.support (fun i _ =>
        tendsto_finsetSum c.support (fun j _ =>
          (tendsto_const_nhds.mul (hconv i j)).mul
            tendsto_const_nhds))
  apply ge_of_tendsto hquadratic
  exact Eventually.of_forall fun n =>
    (gram_posSemidef_infinite (v n)).2 c
end SoficGroups.KunRootedIndicatorCrossing
