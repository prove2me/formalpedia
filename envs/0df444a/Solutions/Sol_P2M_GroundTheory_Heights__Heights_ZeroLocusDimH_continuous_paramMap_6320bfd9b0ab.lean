-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_continuous_paramMap_6320bfd9b0ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:02.903384+00:00
-- url     : https://prove2.me/submissions/6c218b87-7ab0-4472-b4d2-ed811726e5f8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo

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
open Metric Filter Topology Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH
namespace GroundTheory.Heights₂.Heights.ZeroLocusDimH
theorem _root_.solution {n r : ℕ} (π : Fin r → MvPolynomial (Fin n) ℂ) :
    Continuous (paramMap π) :=
  continuous_pi fun _ => MvPolynomial.continuous_eval _
end GroundTheory.Heights₂.Heights.ZeroLocusDimH
