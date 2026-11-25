-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_solve_inr_ae6d804b71ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:24:22.615163+00:00
-- url     : https://prove2.me/submissions/13db3aa9-1aad-47b2-b5e4-cfb985ce0e01

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
namespace GroundTheory.Heights₂.Heights.Vertical.SpecChart
theorem _root_.solution {L : Type*} [CommRing L] {u x ci S : L} (h : u * x + S = 1) (hc : ci * x = 1) :
    ci * (1 - S) = u := by
  linear_combination (-ci) * h + u * hc
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
