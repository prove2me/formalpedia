-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FrameGraphGeneric_proof_0d2e8b72cdc7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:40.9813+00:00
-- url     : https://prove2.me/submissions/9cff852f-2e1d-4e35-9e93-cb100625d733

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameGraphGeneric

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
namespace FrameGraphGeneric
theorem _root_.solution (hA : FrameJacobianGeneric.Statement) (hB : FrameImplicitGraph.Statement) :
    FrameGraphGeneric.Statement := by
  intro n d J hJ hd b
  obtain ⟨I₀, f, s, hcard, hfJ, hs, hM, hgen⟩ := hA n d J hJ hd b
  refine ⟨I₀, frameJacobianDet b I₀ f * s, hcard, fun h => (hJ.mem_or_mem h).elim hM hs, ?_⟩
  intro z hz hq
  rw [map_mul] at hq
  set W : Set (EuclideanSpace ℂ (Fin n)) := {x | eval (fun i => x i) s ≠ 0} with hWdef
  have hW : IsOpen W := isOpen_ne_fun ((MvPolynomial.continuous_eval s).comp
    (by fun_prop : Continuous fun x : EuclideanSpace ℂ (Fin n) => fun i => x i)) continuous_const
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hVW, hg, hproj, hgraph⟩ :=
    hB n b I₀ f z (fun k => hz _ (hfJ k)) (left_ne_zero_of_mul hq) W hW (right_ne_zero_of_mul hq)
  refine ⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, ?_⟩
  rw [← hgraph]
  ext x
  simp only [zeroSetEuc, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hxV⟩
    exact ⟨fun k => hx _ (hfJ k), hxV⟩
  · rintro ⟨hx, hxV⟩
    refine ⟨fun p hp => ?_, hxV⟩
    have hle : Ideal.span (Set.range f) ≤ RingHom.ker (eval fun i => x i) :=
      Ideal.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact RingHom.mem_ker.mpr (hx k))
    have h0 := RingHom.mem_ker.mp (hle (hgen p hp))
    rw [map_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hVW hxV)
end FrameGraphGeneric
end GroundTheory.Heights₂.Heights
