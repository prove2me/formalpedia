-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassLeRoot_proof_b73533a30168
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:03:26.551686+00:00
-- url     : https://prove2.me/submissions/fbda0f4a-adfd-440f-aeb5-ede9e5d7dea0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianRootBound_map_cone_faca59ddb66f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianRootBound_eval_grassPolyCoord_a7272b63b5bb

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
open GrassmannianRootBound
namespace GroundTheory.Heights₂.Heights
namespace GrassLeRoot
theorem _root_.solution : GrassLeRoot.Statement := by
  intro f j m ζ g hg
  have h0 : mConeMap (grassCoord f j m) g = 0 := hg
  have h1 : cone (grassPolyCoord f j m) g = 0 := by
    apply MvPolynomial.map_injective (algebraMap (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m))
      (IsFractionRing.injective _ _)
    rw [map_cone, map_zero]
    exact h0
  have h2 := congrArg (MvPolynomial.map
    (aeval fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2).toRingHom) h1
  rw [map_cone, map_zero] at h2
  show (aeval fun p => MvPolynomial.C (rootCoord ζ p) * MvPolynomial.X p.1) g = 0
  simpa [cone, eval_grassPolyCoord] using h2
end GrassLeRoot
end GroundTheory.Heights₂.Heights
