-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FramePlaneGraph_proof_80ec7a065eb8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:04.948073+00:00
-- url     : https://prove2.me/submissions/e94d64c0-1a46-4306-87db-199dc387b7d7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFramePlaneGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFramePlaneGraph
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FramePlaneGraph_zeroSetEuc_sup_span_494301978f7d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FramePlaneGraph_dim_sup_span_lt_659941234b1e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
noncomputable section
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace FramePlaneGraph
theorem _root_.solution (hG : FrameGraphGeneric.Statement) : FramePlaneGraph.Statement := by
  intro n d J hJ hd b
  obtain ⟨I₀, q, hcard, hq, hloc⟩ := hG n d J hJ hd b
  refine ⟨I₀, J ⊔ Ideal.span {q}, hcard, FramePlaneGraph.dim_sup_span_lt hJ hd hq, ?_⟩
  set W : Set (EuclideanSpace ℂ (Fin n)) := {z | eval (fun i => z i) q ≠ 0} with hWdef
  have hS : zeroSetEuc J \ zeroSetEuc (J ⊔ Ideal.span {q}) = zeroSetEuc J ∩ W := by
    rw [FramePlaneGraph.zeroSetEuc_sup_span]
    ext z
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, hWdef]
    tauto
  have hW : IsOpen W := isOpen_ne_fun ((MvPolynomial.continuous_eval q).comp
    (by fun_prop : Continuous fun z : EuclideanSpace ℂ (Fin n) => fun i => z i)) continuous_const
  rw [hS]
  intro z hz
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hg, hπ, hgraph⟩ := hloc z hz.1 hz.2
  refine ⟨Ω ∩ g ⁻¹' W, V ∩ W, g, hg.continuousOn.isOpen_inter_preimage hΩ hW, hV.inter hW,
    ⟨hzV, hz.2⟩, hg.mono Set.inter_subset_left, fun w hw => hπ w hw.1, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨hxJ, hxW⟩, hxV, -⟩
    have hx : x ∈ g '' Ω := hgraph ▸ ⟨hxJ, hxV⟩
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨w, ⟨hw, hxW⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hwW⟩, rfl⟩
    have hx : g w ∈ zeroSetEuc J ∩ V := hgraph.symm ▸ ⟨w, hw, rfl⟩
    exact ⟨⟨hx.1, hwW⟩, hx.2, hwW⟩
end FramePlaneGraph
end GroundTheory.Heights₂.Heights
