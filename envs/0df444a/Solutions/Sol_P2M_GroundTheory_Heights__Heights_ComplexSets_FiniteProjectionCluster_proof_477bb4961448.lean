-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_proof_477bb4961448
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:54:50.176277+00:00
-- url     : https://prove2.me/submissions/b76c890c-efc3-40ad-9441-af1cd2bcd2af

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_isClosed_zeroSet_64df82fb2a22
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_exists_bound_bdfa0b8c26e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_fibre_finite_7d46f66826ee

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Topology
noncomputable section
open FiniteProjectionCluster
namespace GroundTheory.Heights₂.Heights.ComplexSets
namespace FiniteProjectionCluster
theorem _root_.solution : FiniteProjectionCluster.Statement := by
  intro n d J A w U hA hw hU
  have hcont : Continuous fun x : Fin n → ℂ => A.mulVec x :=
    Continuous.matrix_mulVec continuous_const continuous_id
  obtain ⟨C, hC⟩ := exists_bound J A hA (A.mulVec w) 1
  have hF := fibre_finite J A hA (A.mulVec w)
  obtain ⟨ε0, hε0, hballU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨ε, ⟨hε, hεlt⟩, hεF⟩ :=
    ((Set.Ioo_infinite hε0).sdiff (hF.image fun x => dist x w)).nonempty
  set K := zeroSet J ∩ {x | dist (A.mulVec x) (A.mulVec w) ≤ 1} ∩ Metric.sphere w ε with hKdef
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact ((isClosed_zeroSet J).inter (isClosed_le (hcont.dist continuous_const)
        continuous_const)).inter Metric.isClosed_sphere
    · exact (Metric.isBounded_closedBall (x := 0) (r := C)).subset fun x hx =>
        mem_closedBall_zero_iff.2 (hC x hx.1.1 hx.1.2)
  have hT : IsCompact (A.mulVec '' K) := hKc.image hcont
  have hnot : A.mulVec w ∉ A.mulVec '' K := by
    rintro ⟨x, ⟨⟨hx, _⟩, hxs⟩, hxA⟩
    exact hεF ⟨x, ⟨hx, hxA⟩, hxs⟩
  obtain ⟨r0, hr0, hr0T⟩ := Metric.isOpen_iff.1 hT.isClosed.isOpen_compl _ hnot
  refine ⟨min r0 1, Metric.ball w ε, (Metric.closedBall w ε)ᶜ, lt_min hr0 one_pos, Metric.isOpen_ball,
    Metric.isClosed_closedBall.isOpen_compl, Metric.mem_ball_self hε,
    (Metric.ball_subset_ball hεlt.le).trans hballU,
    Set.disjoint_left.2 fun x hx hx' => hx' (Metric.ball_subset_closedBall hx), ?_, ?_⟩
  · rintro x ⟨hx, hxr⟩
    have hxr' : dist (A.mulVec x) (A.mulVec w) < min r0 1 := hxr
    by_cases h : dist x w < ε
    · exact Or.inl h
    · refine Or.inr fun hcb => ?_
      have heq : dist x w = ε := le_antisymm hcb (not_lt.1 h)
      have hxK : x ∈ K := ⟨⟨hx, hxr'.le.trans (min_le_right _ _)⟩, heq⟩
      exact hr0T (Metric.mem_ball.2 (hxr'.trans_le (min_le_left _ _))) ⟨x, hxK, rfl⟩
  · refine (Metric.isBounded_closedBall (x := 0) (r := C)).subset fun x hx => ?_
    have hxr' : dist (A.mulVec x) (A.mulVec w) < min r0 1 := hx.2
    exact mem_closedBall_zero_iff.2 (hC x hx.1 (hxr'.le.trans (min_le_right _ _)))
end FiniteProjectionCluster
end GroundTheory.Heights₂.Heights.ComplexSets
