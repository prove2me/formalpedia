-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NefOnFibresRelabel_proof_2c46a00adf28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:47.990353+00:00
-- url     : https://prove2.me/submissions/5ab2d9b9-9834-4bc0-be14-43e99d9e20c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mCoordIdeal_relabel_94e74e80e57c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_nefOnFibres_map_relabel_36f78da6ae3d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace NefOnFibresRelabel
theorem _root_.solution : NefOnFibresRelabel.Statement := by
  intro K K' _ _ ι ι' _ _ ε h Ω _ y a
  rw [nefOnFibres_map_relabel ε h, mCoordIdeal_relabel ε h y,
    Ideal.map_comap_of_surjective _ (relabelRingEquiv ε h).surjective]
end NefOnFibresRelabel
end GroundTheory.Heights₂.Heights
