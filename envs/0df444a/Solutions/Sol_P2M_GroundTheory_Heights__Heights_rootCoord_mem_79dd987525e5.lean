-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_rootCoord_mem_79dd987525e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:12:50.781117+00:00
-- url     : https://prove2.me/submissions/730d6997-313e-4953-846c-68630ec4320f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_anchor_minor_b307d35ccb1e

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) :
    rootCoord ζ ∈ mcPts (rootPointIdeal ζ) := by
  refine ⟨fun k => ⟨plAnchor j m, ?_⟩, fun g hg => ?_⟩
  · simp [rootCoord, anchor_minor]
  · have h : mConeMap (rootCoord ζ) g = 0 := hg
    have h2 := congrArg (MvPolynomial.eval (fun _ : Fin f => (1 : ℂ))) h
    have key : (MvPolynomial.eval (fun _ : Fin f => (1 : ℂ))).comp
        (mConeMap (rootCoord ζ) : MRing (plBlocks f j m) →+* MvPolynomial (Fin f) ℂ) =
        (eval (rootCoord ζ)).comp (map (Int.castRingHom ℂ)) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro i; simp [mConeMap]
    have := congrArg (fun φ => φ g) key
    simp only [RingHom.comp_apply, RingHom.coe_coe, h, map_zero] at this
    exact this.symm
end GroundTheory.Heights₂.Heights
