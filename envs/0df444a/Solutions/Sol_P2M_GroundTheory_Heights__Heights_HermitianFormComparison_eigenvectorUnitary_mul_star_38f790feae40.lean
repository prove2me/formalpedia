-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianFormComparison_eigenvectorUnitary_mul_star_38f790feae40
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:14.821899+00:00
-- url     : https://prove2.me/submissions/a7e3b22b-531a-4f32-bbc6-806cf6ea8b69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare

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
open Matrix
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.HermitianFormComparison
namespace GroundTheory.Heights₂.Heights.HermitianFormComparison
theorem _root_.solution {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 :=
  Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
end GroundTheory.Heights₂.Heights.HermitianFormComparison
