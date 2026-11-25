-- Prove2me | solution 1 for SNumbers.tendsto_gelfandNumber_of_totallyBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:20:03.214807+00:00
-- url     : https://prove2.me/submissions/2a9249f6-8f9e-408c-9af5-8baf47a12572

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
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
public import Theorems.Thm_SNumbers_entropyNumber_zero_op
public import Theorems.Thm_SNumbers_gelfandNumber_le_two_mul_of_fin_net
public import Theorems.Thm_SNumbers_gelfandNumber_nonneg
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
open scoped Cardinal
namespace SNumbers
section TotallyBounded
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
private lemma exists_fin_net_of_totallyBounded {s : Set Y} (hs : TotallyBounded s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (y : Fin k → Y), ∀ z ∈ s, ∃ i, ‖z - y i‖ ≤ ε := by
  classical
  obtain ⟨t, ht_fin, ht_cov⟩ := Metric.totallyBounded_iff.mp hs ε hε
  have : Fintype ↥t := ht_fin.fintype
  refine ⟨Fintype.card ↥t,
    fun i => (((Fintype.equivFin ↥t).symm i : ↥t) : Y), fun z hz => ?_⟩
  have hmem := ht_cov hz
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hmem
  obtain ⟨w, hw, hdist⟩ := hmem
  refine ⟨Fintype.equivFin ↥t ⟨w, hw⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact le_of_lt (by rwa [← dist_eq_norm])
end TotallyBounded
section Kolmogorov
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
end Kolmogorov
section Gelfand
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
end Gelfand
end SNumbers
namespace SVD
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
end SVD
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution {S : X →L[𝕜] Y}
    (hS : TotallyBounded (⇑S '' Metric.closedBall 0 1)) :
    Tendsto (gelfandNumber S) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨k, y, hnet⟩ := exists_fin_net_of_totallyBounded hS hε3
  have hk : gelfandNumber S k ≤ 2 * (ε / 3) :=
    gelfandNumber_le_two_mul_of_fin_net fun x hx =>
      hnet (S x) ⟨x, mem_closedBall_zero_iff.mpr hx, rfl⟩
  refine ⟨k, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (gelfandNumber_nonneg S n)]
  calc gelfandNumber S n
      ≤ gelfandNumber S k := gelfandNumber_antitone' S hn
    _ ≤ 2 * (ε / 3) := hk
    _ < ε := by linarith
end SNumbers
