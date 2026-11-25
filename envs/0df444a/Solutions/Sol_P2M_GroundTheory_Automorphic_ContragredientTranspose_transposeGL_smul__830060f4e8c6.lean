-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_ContragredientTranspose_transposeGL_smul__830060f4e8c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:05:16.932708+00:00
-- url     : https://prove2.me/submissions/63b18991-e7c5-433e-9765-d7f186068173

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_transposeGL_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MulAction Matrix GroundTheory.Automorphic.Whittaker
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
omit [TopologicalSpace F] [IsTopologicalRing F]
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (h : ConjAct (GL (Fin n) F)) (x : GL (Fin n) F) :
    transposeGL (h • x) = thetaC h • transposeGL x :=
  transposeGL_smul h x
end GroundTheory.Automorphic.ContragredientTranspose
