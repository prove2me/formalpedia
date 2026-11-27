-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassHeightBound_proof_cec452e5a7c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:56:30.578477+00:00
-- url     : https://prove2.me/submissions/8e3c4926-6315-4515-b263-b494e1757b50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassHeightBound

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
open ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights
namespace GrassHeightBound
theorem _root_.solution (hArith : GrassArithVar.Statement) (hRoot : RootArithVar.Statement)
    (hSemi : FsLineSemipositive.Statement) (hNef : NefOfNonneg.Statement)
    (hConj : FsConjInvariant.Statement) (hLe : GrassLeRoot.Statement) (hHt : RootHeight.Statement)
    (hDense : RootDense.Statement) : GrassHeightBound.Statement := by
  intro hZ2 f j m hf II hII
  refine hZ2 (Fin f) (plBlocks f j m) (grassIdeal f j m) ⊥ (f * j * m) (fsMulti (plBlocks f j m))
    (grassConst f j m) (rootFamily f j m) II hII (hArith f j m hf) bot_le (hSemi _ _ _)
    (hNef _ _ _ _ fun _ => ?_) (hConj _ _) ?_ (hDense f j m)
  · show (0 : ℤ) ≤ 1
    exact zero_le_one
  · rintro W ⟨ζ, hζ, rfl⟩
    exact ⟨hRoot f j m ζ hf hζ, hLe f j m ζ, hHt f j m ζ hf hζ II hII⟩
end GrassHeightBound
end GroundTheory.Heights₂.Heights
