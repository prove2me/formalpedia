-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_gaussBasis_one_d101bba40995
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:43:43.411616+00:00
-- url     : https://prove2.me/submissions/926d2a1b-f676-422d-afc5-245f90b1158b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Automorphic Matrix
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution : gaussBasis 1 = ⟨0, 1⟩ := by
  simp [gaussBasis, QuadraticAlgebra.basis]
end GroundTheory.Heights₂.Theta
