-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_restTransport_isHomogeneous_e751977fd44f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:26.990359+00:00
-- url     : https://prove2.me/submissions/b3d02c51-db78-4abd-ab38-215854101442

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutIKillsIdeal

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k)
    {A : RestTerms.RootRing f N} {d : ℕ} (hA : A.IsHomogeneous d) :
    (restTransport f j k N e A).IsHomogeneous d := by
  show (rename (fun p : Fin f × Fin N => (p.1, e p.2)) (map (algebraMap ℚ ℝ) A)).IsHomogeneous d
  exact (hA.map _).rename_isHomogeneous
end GroundTheory.Heights₂.Heights
