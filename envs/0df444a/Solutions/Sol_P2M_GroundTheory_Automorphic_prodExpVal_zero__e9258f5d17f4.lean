-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_prodExpVal_zero__e9258f5d17f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:33.309485+00:00
-- url     : https://prove2.me/submissions/0de6e254-31b3-4671-aeca-e7cf11201dae

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
import Theorems.Thm_GroundTheory_Automorphic_prodExpVal_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
namespace GroundTheory.Automorphic
theorem _root_.solution {d : ℕ} (X : Fin d → 𝔸) : prodExpVal X (fun _ => 0) = 1 :=
  prodExpVal_zero X
end GroundTheory.Automorphic
