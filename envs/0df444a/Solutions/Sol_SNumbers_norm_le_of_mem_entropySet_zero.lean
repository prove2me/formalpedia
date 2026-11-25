-- Prove2me | solution 1 for SNumbers.norm_le_of_mem_entropySet_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:21:43.872985+00:00
-- url     : https://prove2.me/submissions/961dde26-59dd-46c6-891d-2732d187f724

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_ContinuousLinearMap_opNorm_le_of_unit_closedBall
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_entropyNumber_zero_op
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] John.rankOneSA_apply
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.entropyNumber_zero_op
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution {S : X →L[𝕜] Y} {ε : ℝ} (hε : ε ∈ entropySet S 0) :
    ‖S‖ ≤ ε := by
  obtain ⟨hε0, N, hN, hcov⟩ := hε
  have hmem : ∀ z : X, ‖z‖ ≤ 1 → ∃ y ∈ N, ‖S z - y‖ ≤ ε := by
    intro z hz
    have hz' := hcov ⟨z, by simpa using hz, rfl⟩
    simp only [Set.mem_iUnion, Metric.mem_closedBall, exists_prop, dist_eq_norm] at hz'
    obtain ⟨y, hy, hd⟩ := hz'
    exact ⟨y, by simpa using hy, hd⟩
  refine S.opNorm_le_of_unit_closedBall fun x hx => ?_
  obtain ⟨y, hy, hd⟩ := hmem x hx
  obtain ⟨y', hy', hd'⟩ := hmem (-x) (by rwa [norm_neg])
  have hN1 : N.card ≤ 1 := by simpa using hN
  have hyy : y' = y := Finset.card_le_one.mp hN1 _ hy' _ hy
  rw [hyy, map_neg] at hd'
  have h2 : S x + S x = (S x - y) - (-S x - y) := by abel
  have h3 : ‖S x + S x‖ ≤ 2 * ε := by
    rw [h2]; linarith [norm_sub_le (S x - y) (-S x - y)]
  rw [← two_smul 𝕜 (S x), norm_smul, RCLike.norm_two] at h3
  linarith
end SNumbers
