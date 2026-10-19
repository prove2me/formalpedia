-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.norm_smul_finset_sum_eq_one_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/8337b909-4952-4305-9484-3a9f08a35cb8

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_tendsto_norm_sq_smul_finset_sum_of_gram

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
    (l : Filter N) [NeBot l]
    (z : ∀ n, I → E n) (v : I → H)
    (hgram : ∀ i j,
      Tendsto (fun n => ⟪z n i, z n j⟫_ℂ) l
        (𝓝 ⟪v i, v j⟫_ℂ))
    (F : Finset I) (c : ℂ)
    (hnorm : ∀ n, ‖c • ∑ i ∈ F, z n i‖ = 1) :
    ‖c • ∑ i ∈ F, v i‖ = 1 := by
  have hlimit :=
    tendsto_norm_sq_smul_finset_sum_of_gram l z v hgram F c
  have hone :
      Tendsto (fun n => ‖c • ∑ i ∈ F, z n i‖ ^ 2) l
        (𝓝 (1 : ℝ)) := by
    simpa only [hnorm, one_pow] using
      (tendsto_const_nhds :
        Tendsto (fun _ : N => (1 : ℝ)) l (𝓝 1))
  have hsq : ‖c • ∑ i ∈ F, v i‖ ^ 2 = 1 :=
    tendsto_nhds_unique hlimit hone
  nlinarith [norm_nonneg (c • ∑ i ∈ F, v i)]
end SoficGroups.KunRootedIndicatorCrossing
