-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.tendsto_norm_sq_smul_finset_sum_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/c6472028-88a9-4b71-8522-8473bad47dae

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_inner_smul_finset_sum_self

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {N I H : Type*} {E : N → Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [∀ n, NormedAddCommGroup (E n)]
    [∀ n, InnerProductSpace ℂ (E n)]
    (l : Filter N) (z : ∀ n, I → E n) (v : I → H)
    (hgram : ∀ i j,
      Tendsto (fun n => ⟪z n i, z n j⟫_ℂ) l
        (𝓝 ⟪v i, v j⟫_ℂ))
    (F : Finset I) (c : ℂ) :
    Tendsto (fun n => ‖c • ∑ i ∈ F, z n i‖ ^ 2) l
      (𝓝 (‖c • ∑ i ∈ F, v i‖ ^ 2)) := by
  have hsum :
      Tendsto
        (fun n => ∑ i ∈ F, ∑ j ∈ F, ⟪z n i, z n j⟫_ℂ) l
        (𝓝 (∑ i ∈ F, ∑ j ∈ F, ⟪v i, v j⟫_ℂ)) :=
    tendsto_finsetSum F fun i _ =>
      tendsto_finsetSum F fun j _ => hgram i j
  have hinner :
      Tendsto
        (fun n => ⟪c • ∑ i ∈ F, z n i,
          c • ∑ i ∈ F, z n i⟫_ℂ) l
        (𝓝 ⟪c • ∑ i ∈ F, v i,
          c • ∑ i ∈ F, v i⟫_ℂ) := by
    simpa only [inner_smul_finset_sum_self] using
      (tendsto_const_nhds.mul hsum).mul tendsto_const_nhds
  have hreal := (Complex.continuous_re.tendsto _).comp hinner
  change Tendsto
    (fun n => (⟪c • ∑ i ∈ F, z n i,
      c • ∑ i ∈ F, z n i⟫_ℂ).re) l
    (𝓝 (⟪c • ∑ i ∈ F, v i,
      c • ∑ i ∈ F, v i⟫_ℂ).re) at hreal
  convert hreal using 1
  · funext n
    exact norm_sq_eq_re_inner (𝕜 := ℂ) (c • ∑ i ∈ F, z n i)
  · congr 1
    exact norm_sq_eq_re_inner (𝕜 := ℂ) (c • ∑ i ∈ F, v i)
end SoficGroups.KunRootedIndicatorCrossing
