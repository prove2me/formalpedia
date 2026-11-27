-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_hypotheses_inhabited_44215666a402
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:09:12.806593+00:00
-- url     : https://prove2.me/submissions/2300ed4a-8f95-4940-bb8b-05af990c6817

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Inhabitants

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
namespace GroundTheory.Heights₂.Heights.Vertical
namespace LengthDecomp
theorem _root_.solution :
    Module.length ℤ_[2] (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2])}) ≠ ⊤ :=
  Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero two_ne_zero)
end LengthDecomp
end GroundTheory.Heights₂.Heights.Vertical
