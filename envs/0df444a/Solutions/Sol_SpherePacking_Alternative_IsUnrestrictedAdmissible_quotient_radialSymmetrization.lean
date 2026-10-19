-- Prove2me | solution 1 for SpherePacking.Alternative.IsUnrestrictedAdmissible.quotient_radialSymmetrization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/b62953da-2b18-4c9a-8656-4e81fff6590a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_Alternative_quotient_eq_of_radialSymmetrizationAverage

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory
open scoped FourierTransform Real Topology
open SpherePacking SpherePacking.Alternative
namespace SpherePacking.Alternative
namespace IsUnrestrictedAdmissible
theorem _root_.solution
    {d : ℕ} {f : Schwartz d}
    (_hf : IsUnrestrictedAdmissible f) :
    quotient (radialSymmetrization f) = quotient f := by
  exact quotient_eq_of_radialSymmetrizationAverage
    (radialSymmetrization_apply f)
    (radialSymmetrization_fourier_average_apply_for_admissibility f)
end IsUnrestrictedAdmissible
end SpherePacking.Alternative
