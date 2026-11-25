-- Prove2me | solution 1 for SNumbers.totallyBounded_of_tendsto_gelfandNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:07:42.131045+00:00
-- url     : https://prove2.me/submissions/cd3a0318-9782-4fb1-82ff-f2dd7d5ad26a

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
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
public import Theorems.Thm_SNumbers_deviationFromRestriction_nonneg
public import Theorems.Thm_SNumbers_entropyNumber_zero_op
public import Theorems.Thm_SNumbers_gelfandSet_nonempty
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_Submodule_liftQL_mkQL
public import Theorems.Thm_Submodule_norm_mkQL_apply_le
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
open scoped Cardinal
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution {S : X →L[𝕜] Y}
    (hS : Tendsto (gelfandNumber S) atTop (𝓝 0)) :
    TotallyBounded (⇑S '' Metric.closedBall 0 1) := by
  classical
  refine Metric.totallyBounded_iff.mpr fun η hη => ?_
  have hε : 0 < η / 6 := by positivity
  have hpos : (0 : ℝ) < ‖S‖ + 1 := by positivity
  have hne : (‖S‖ + 1) ≠ 0 := ne_of_gt hpos
  set δ : ℝ := min 1 ((η / 2) / (‖S‖ + 1)) with hδ_def
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδS : ‖S‖ * δ ≤ η / 2 := by
    have h1 : δ ≤ (η / 2) / (‖S‖ + 1) := min_le_right _ _
    calc ‖S‖ * δ ≤ (‖S‖ + 1) * δ := by nlinarith [hδ.le]
      _ ≤ (‖S‖ + 1) * ((η / 2) / (‖S‖ + 1)) :=
          mul_le_mul_of_nonneg_left h1 hpos.le
      _ = η / 2 := by field_simp
  -- A closed subspace of finite codimension on which `S` is small.
  obtain ⟨n, hn⟩ := (hS.eventually_lt_const hε).exists
  obtain ⟨-, ⟨M, hM_closed, hM_rank, rfl⟩, hM_lt⟩ :=
    exists_lt_of_csInf_lt (gelfandSet_nonempty S n) hn
  have : IsClosed (M : Set X) := hM_closed
  have : FiniteDimensional 𝕜 (X ⧸ M) :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hM_rank (Cardinal.natCast_lt_aleph0))
  have : ProperSpace (X ⧸ M) := FiniteDimensional.proper 𝕜 (X ⧸ M)
  -- The image of the unit ball in the finite-dimensional quotient.
  have hq : TotallyBounded (⇑M.mkQL '' Metric.closedBall (0 : X) 1) := by
    refine TotallyBounded.subset ?_
      (isCompact_closedBall (0 : X ⧸ M) 1).totallyBounded
    rintro _ ⟨x, hx, rfl⟩
    simpa using (M.norm_mkQL_apply_le x).trans (mem_closedBall_zero_iff.mp hx)
  obtain ⟨t, ht_sub, ht_fin, ht_cov⟩ := Metric.finite_approx_of_totallyBounded hq δ hδ
  -- Lift the centres of the net back to the unit ball of `X`.
  have hpre : ∀ w : X ⧸ M, w ∈ t → ∃ u : X, ‖u‖ ≤ 1 ∧ M.mkQL u = w := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := ht_sub hw
    exact ⟨u, mem_closedBall_zero_iff.mp hu, rfl⟩
  choose! u hu_norm hu_eq using hpre
  refine ⟨(fun w => S (u w)) '' t, ht_fin.image _, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  -- Find a net point close to `[x]`.
  have hmem := ht_cov ⟨x, hx, rfl⟩
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hmem
  obtain ⟨w, hw, hwd⟩ := hmem
  -- Correct `x - u w` by an element of `M`.
  have hMne : (M : Set X).Nonempty := ⟨0, M.zero_mem⟩
  have hquot : ‖M.mkQL (x - u w)‖ < δ := by
    rw [map_sub, hu_eq w hw, ← dist_eq_norm]
    exact hwd
  have heq : ‖M.mkQL (x - u w)‖ = Metric.infDist (x - u w) M :=
    QuotientAddGroup.norm_mk (S := M.toAddSubgroup) (x - u w)
  rw [heq] at hquot
  obtain ⟨m, hm_mem, hmd⟩ := (Metric.infDist_lt_iff hMne).mp hquot
  rw [dist_eq_norm] at hmd
  -- `‖m‖ ≤ 2 + δ ≤ 3`, independently of the codimension of `M`.
  have hm_norm : ‖m‖ ≤ 3 := by
    have h1 : ‖x - u w‖ ≤ 2 := by
      calc ‖x - u w‖ ≤ ‖x‖ + ‖u w‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add hx1 (hu_norm w hw)
        _ = 2 := by norm_num
    calc ‖m‖ ≤ ‖x - u w‖ + ‖(x - u w) - m‖ := by
          simpa using norm_sub_le (x - u w) ((x - u w) - m)
      _ ≤ 2 + δ := add_le_add h1 hmd.le
      _ ≤ 3 := by linarith
  -- `S m` is small because `m ∈ M`.
  -- Strictly less than `η/2`: the deviation is *strictly* below `η/6`.
  have hSm : ‖S m‖ < η / 2 := by
    have h1 : ‖S m‖ ≤ deviationFromRestriction S M * ‖m‖ := by
      have := (S.comp M.subtypeL).le_opNorm ⟨m, hm_mem⟩
      simpa [deviationFromRestriction] using this
    have h2 : (0 : ℝ) ≤ deviationFromRestriction S M :=
      deviationFromRestriction_nonneg S M
    calc ‖S m‖ ≤ deviationFromRestriction S M * ‖m‖ := h1
      _ ≤ deviationFromRestriction S M * 3 := mul_le_mul_of_nonneg_left hm_norm h2
      _ < (η / 6) * 3 := mul_lt_mul_of_pos_right hM_lt (by norm_num)
      _ = η / 2 := by ring
  refine Set.mem_biUnion ⟨w, hw, rfl⟩ ?_
  rw [Metric.mem_ball, dist_eq_norm]
  -- `S x - S (u w) = S m + S ((x - u w) - m)`.
  have hsplit : S x - S (u w) = S m + S ((x - u w) - m) := by
    rw [map_sub, map_sub]; abel
  have hSrest : ‖S ((x - u w) - m)‖ ≤ ‖S‖ * δ :=
    (S.le_opNorm _).trans (mul_le_mul_of_nonneg_left hmd.le (norm_nonneg _))
  calc ‖S x - S (u w)‖
      = ‖S m + S ((x - u w) - m)‖ := by rw [hsplit]
    _ ≤ ‖S m‖ + ‖S ((x - u w) - m)‖ := norm_add_le _ _
    _ < η := by linarith
end SNumbers
