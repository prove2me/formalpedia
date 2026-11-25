-- Prove2me | solution 1 for SNumbers.totallyBounded_of_tendsto_kolmogorovNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:11:33.461077+00:00
-- url     : https://prove2.me/submissions/93eeeb5c-279f-4fe9-8b65-a805fc93ef71

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
public import Theorems.Thm_SNumbers_entropyNumber_zero_op
public import Theorems.Thm_SNumbers_kolmogorovSet_nonempty
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
open scoped Cardinal
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution {S : X →L[𝕜] Y}
    (hS : Tendsto (kolmogorovNumber S) atTop (𝓝 0)) :
    TotallyBounded (⇑S '' Metric.closedBall 0 1) := by
  refine Metric.totallyBounded_iff.mpr fun η hη => ?_
  have hε : 0 < η / 3 := by positivity
  obtain ⟨n, hn⟩ := (hS.eventually_lt_const hε).exists
  obtain ⟨-, ⟨V, hV_rank, rfl⟩, hV_lt⟩ :=
    exists_lt_of_csInf_lt (kolmogorovSet_nonempty S n) hn
  have : FiniteDimensional 𝕜 V :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hV_rank (Cardinal.natCast_lt_aleph0))
  -- Every point of `S(B_X)` is `η/3`-close to a point of `V` of norm `≤ ‖S‖ + η/3`.
  have hVne : (V : Set Y).Nonempty := ⟨0, V.zero_mem⟩
  have key : ∀ x : X, ‖x‖ ≤ 1 →
      ∃ v : Y, v ∈ V ∧ ‖v‖ ≤ ‖S‖ + η / 3 ∧ ‖S x - v‖ < η / 3 := by
    intro x hx
    have hop : ‖V.mkQL (S x)‖ ≤ deviationFromSubspace S V := by
      simpa [deviationFromSubspace] using (V.mkQL.comp S).unit_le_opNorm x hx
    have h1 : ‖V.mkQL (S x)‖ < η / 3 := lt_of_le_of_lt hop hV_lt
    have heq : ‖V.mkQL (S x)‖ = Metric.infDist (S x) V :=
      QuotientAddGroup.norm_mk (S := V.toAddSubgroup) (S x)
    rw [heq] at h1
    obtain ⟨v, hv, hdv⟩ := (Metric.infDist_lt_iff hVne).mp h1
    rw [dist_eq_norm] at hdv
    refine ⟨v, hv, ?_, hdv⟩
    have hSx : ‖S x‖ ≤ ‖S‖ := S.unit_le_opNorm x hx
    have hvx : ‖v - S x‖ ≤ η / 3 := by rw [norm_sub_rev]; exact hdv.le
    have hveq : S x + (v - S x) = v := by abel
    calc ‖v‖ = ‖S x + (v - S x)‖ := by rw [hveq]
      _ ≤ ‖S x‖ + ‖v - S x‖ := norm_add_le _ _
      _ ≤ ‖S‖ + η / 3 := add_le_add hSx hvx
  -- The relevant piece of `V` is compact, hence has a finite `η/3`-net.
  have hK : TotallyBounded
      (⇑V.subtypeL '' Metric.closedBall (0 : V) (‖S‖ + η / 3)) :=
    ((isCompact_closedBall (0 : V) (‖S‖ + η / 3)).image
      V.subtypeL.continuous).totallyBounded
  obtain ⟨t, ht_fin, ht_cov⟩ := Metric.totallyBounded_iff.mp hK (η / 3) hε
  refine ⟨t, ht_fin, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨v, hv_mem, hv_norm, hv_dist⟩ := key x (mem_closedBall_zero_iff.mp hx)
  have hvK : v ∈ ⇑V.subtypeL '' Metric.closedBall (0 : V) (‖S‖ + η / 3) :=
    ⟨⟨v, hv_mem⟩, by simpa using hv_norm, rfl⟩
  have hmem := ht_cov hvK
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hmem
  obtain ⟨w, hw, hwd⟩ := hmem
  refine Set.mem_biUnion hw ?_
  have : dist (S x) w ≤ dist (S x) v + dist v w := dist_triangle _ _ _
  rw [Metric.mem_ball, dist_eq_norm] at *
  calc ‖S x - w‖ ≤ ‖S x - v‖ + ‖v - w‖ := by
        simpa [dist_eq_norm] using dist_triangle (S x) v w
    _ < η / 3 + η / 3 := add_lt_add hv_dist hwd
    _ < η := by linarith
end SNumbers
