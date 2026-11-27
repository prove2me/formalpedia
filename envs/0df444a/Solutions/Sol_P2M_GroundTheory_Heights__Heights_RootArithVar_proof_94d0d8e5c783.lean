-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootArithVar_proof_94d0d8e5c783
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:09:04.633972+00:00
-- url     : https://prove2.me/submissions/7ee82514-487d-4b2b-8b68-8bd144749e74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_rootCoord_fd120b423998
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
open RootArithmeticVariety
namespace GroundTheory.Heights₂.Heights
namespace RootArithVar
theorem _root_.solution (h : CoordConeArithVar.Statement) : RootArithVar.Statement := by
  intro f j m ζ hf hζ
  have hK : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩
  have := h (Fin f) (plBlocks f j m) ℂ (rootCoord ζ) (fun _ => plAnchor j m) 0 Fin.elim0 hK
    (fun k => by simp [rootCoord, anchor_minor]) (algebraicIndependent_empty_type)
    (fun i => Fin.elim0 i) ?_
  · simpa [rootPointIdeal] using this
  · rintro r ⟨p, rfl⟩
    have h1 : IsIntegral ℚ (rootCoord ζ p / rootCoord ζ ⟨p.1, plAnchor j m⟩) := by
      simp only [rootCoord, anchor_minor, div_one]
      exact (isIntegral_rootCoord ζ hζ p).tower_top
    exact (h1.tower_top (A := IntermediateField.adjoin ℚ (Set.range (Fin.elim0 : Fin 0 → ℂ)))).isAlgebraic
end RootArithVar
end GroundTheory.Heights₂.Heights
