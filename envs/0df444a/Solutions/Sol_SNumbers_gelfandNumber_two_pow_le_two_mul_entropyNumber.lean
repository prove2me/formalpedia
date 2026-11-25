-- Prove2me | solution 1 for SNumbers.gelfandNumber_two_pow_le_two_mul_entropyNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:50:13.219937+00:00
-- url     : https://prove2.me/submissions/6192d7a6-6351-4fd8-8edb-2eb74fc27e7a

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_SNumbers_gelfandNumber_le_two_mul_of_fin_net
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_P2M_SNumbers_gelfandNumber_antitone__140691ee51a6
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_entropyNumber_def
public import Theorems.Thm_SNumbers_entropyNumber_zero_op
public import Theorems.Thm_SNumbers_entropySet_nonempty
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


section
@[expose] public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
private lemma exists_fin_net_of_mem_entropySet {S : X →L[𝕜] Y} {n : ℕ} {ε : ℝ}
    (hε : ε ∈ entropySet S n) :
    ∃ (k : ℕ) (y : Fin k → Y), k ≤ 2 ^ n ∧
      ∀ x : X, ‖x‖ ≤ 1 → ∃ i, ‖S x - y i‖ ≤ ε := by
  classical
  obtain ⟨-, N, hN_card, hcov⟩ := hε
  refine ⟨N.card, fun i => ((N.equivFin.symm i : ↥N) : Y), hN_card, fun x hx => ?_⟩
  have hmem : S x ∈ ⋃ w ∈ (N : Set Y), Metric.closedBall w ε :=
    hcov ⟨x, mem_closedBall_zero_iff.mpr hx, rfl⟩
  simp only [Set.mem_iUnion, Metric.mem_closedBall, exists_prop] at hmem
  obtain ⟨w, hw, hdist⟩ := hmem
  refine ⟨N.equivFin ⟨w, by simpa using hw⟩, ?_⟩
  simpa [dist_eq_norm] using hdist
section Identity
open MeasureTheory
end Identity
section Hilbert
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
end Hilbert
end SNumbers
end
end

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
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S (2 ^ n) ≤ 2 * entropyNumber S n := by
  have key : gelfandNumber S (2 ^ n) / 2 ≤ entropyNumber S n := by
    rw [entropyNumber_def]
    refine le_csInf (entropySet_nonempty S n) fun ε hε => ?_
    obtain ⟨k, y, hk, hnet⟩ := exists_fin_net_of_mem_entropySet hε
    have h := (gelfandNumber_antitone' S hk).trans
      (gelfandNumber_le_two_mul_of_fin_net hnet)
    linarith
  linarith
end SNumbers
