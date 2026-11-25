-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_proof_b5407db643ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:55:43.783487+00:00
-- url     : https://prove2.me/submissions/145b0bde-37cb-40a4-b4f7-ee7ea2db7ba6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameImplicitGraph
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HasStrictFDerivAtEval
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_hasStrictFDerivAt_phi_7970470bf85b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_phiDeriv_equiv_27e53d43c6a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_continuous_eval_c29a4cd0acc4

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
open GroundTheory.Heights₂.Heights.FrameImplicitGraph
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.FrameImplicitGraph
theorem _root_.solution : FrameImplicitGraph.Statement := by
  intro n b I f z hz hdet U hU hzU
  obtain ⟨e0, he0⟩ := phiDeriv_equiv b I f z hdet
  have hs : HasStrictFDerivAt (phi b I f)
      (e0 : EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ)) z :=
    he0 ▸ hasStrictFDerivAt_phi b I f z
  let e := hs.toOpenPartialHomeomorph (phi b I f)
  have hecoe : (e : EuclideanSpace ℂ (Fin n) → (I → ℂ) × ({j // j ∉ I} → ℂ)) = phi b I f := rfl
  let W := {x : EuclideanSpace ℂ (Fin n) | eval (fun i => x i) (frameJacobianDet b I f) ≠ 0}
  have hW : IsOpen W := isOpen_ne_fun (continuous_eval _) continuous_const
  let V := e.source ∩ U ∩ W
  have hV : IsOpen V := (e.open_source.inter hU).inter hW
  let ι : (I → ℂ) → (I → ℂ) × ({j // j ∉ I} → ℂ) := fun w => (w, 0)
  have hι : Continuous ι := continuous_id.prodMk continuous_const
  refine ⟨ι ⁻¹' (e.target ∩ e.symm ⁻¹' V), V, fun w => e.symm (ι w),
    (e.continuousOn_symm.isOpen_inter_preimage e.open_target hV).preimage hι, hV,
    ⟨⟨hs.mem_toOpenPartialHomeomorph_source, hzU⟩, hdet⟩, fun x hx => hx.1.2, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨ex, hex⟩ := phiDeriv_equiv b I f _ hw.2.2
    have hd : HasFDerivAt e (ex : EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ))
        (e.symm (ι w)) := by
      rw [hecoe, hex]
      exact (hasStrictFDerivAt_phi b I f _).hasFDerivAt
    have hιd : HasFDerivAt ι ((ContinuousLinearMap.id ℂ (I → ℂ)).prod 0) w :=
      (hasFDerivAt_id w).prodMk (hasFDerivAt_const 0 w)
    exact ((e.hasFDerivAt_symm hw.1 hd).comp w hιd).differentiableAt.differentiableWithinAt
  · intro w hw
    have := congrArg Prod.fst (e.right_inv hw.1)
    rw [hecoe] at this
    exact this
  · ext x
    constructor
    · rintro ⟨hx0, hxV⟩
      have hex : e x = ι (frameProj b I x) := by
        rw [hecoe]
        exact Prod.ext rfl (funext hx0)
      refine ⟨frameProj b I x, ⟨?_, ?_⟩, ?_⟩
      · rw [← hex]; exact e.map_source hxV.1.1
      · show e.symm (ι (frameProj b I x)) ∈ V
        rw [← hex, e.left_inv hxV.1.1]; exact hxV
      · show e.symm (ι (frameProj b I x)) = x
        rw [← hex, e.left_inv hxV.1.1]
    · rintro ⟨w, hw, rfl⟩
      refine ⟨fun k => ?_, hw.2⟩
      have := congrArg (fun p => p.2 k) (e.right_inv hw.1)
      rw [hecoe] at this
      exact this
end GroundTheory.Heights₂.Heights.FrameImplicitGraph
