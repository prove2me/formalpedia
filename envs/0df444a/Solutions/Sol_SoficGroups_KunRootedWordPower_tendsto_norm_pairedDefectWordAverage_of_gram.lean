-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.tendsto_norm_pairedDefectWordAverage_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/19493b59-e7a4-4bd2-b344-93b9de620252

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_tendsto_norm_sq_smul_finset_sum_of_gram
import Theorems.Thm_SoficGroups_KunRootedWordPower_tendsto_inner_pairedWordAverage_of_gram

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
    {G ι N H : Type*} [Group G] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {E : N → Type*}
    [∀ n, NormedAddCommGroup (E n)]
    [∀ n, InnerProductSpace ℂ (E n)]
    (l : Filter N) (s : ι → G)
    (z : ∀ n, G × G → E n) (v : G × G → H)
    (hgram : ∀ q r,
      Tendsto (fun n => ⟪z n q, z n r⟫_ℂ) l
        (𝓝 ⟪v q, v r⟫_ℂ))
    (k : ℕ) :
    Tendsto
      (fun n => ‖pairedDefectWordAverage s (z n) k‖)
      l
      (𝓝 ‖pairedDefectWordAverage s v k‖) := by
  have hsq :
      Tendsto
        (fun n => ‖pairedDefectWordAverage s (z n) k‖ ^ 2)
        l
        (𝓝 (‖pairedDefectWordAverage s v k‖ ^ 2)) := by
    simpa only [pairedDefectWordAverage] using
      SoficGroups.KunRootedIndicatorCrossing.tendsto_norm_sq_smul_finset_sum_of_gram
        l
        (fun n (i : ι) =>
          pairedWordAverage s (z n) k (s i, 1))
        (fun i : ι => pairedWordAverage s v k (s i, 1))
        (fun i j =>
          tendsto_inner_pairedWordAverage_of_gram l s z v hgram k
            (s i, 1) (s j, 1))
        Finset.univ (Fintype.card ι : ℂ)⁻¹
  have hroot :=
    (Real.continuous_sqrt.tendsto
      (‖pairedDefectWordAverage s v k‖ ^ 2)).comp hsq
  convert hroot using 1
  · funext n
    change ‖pairedDefectWordAverage s (z n) k‖ =
      Real.sqrt (‖pairedDefectWordAverage s (z n) k‖ ^ 2)
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  · congr 1
    rw [Real.sqrt_sq (norm_nonneg _)]
end SoficGroups.KunRootedWordPower
