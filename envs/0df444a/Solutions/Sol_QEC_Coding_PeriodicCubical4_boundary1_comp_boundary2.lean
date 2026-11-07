-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.boundary1_comp_boundary2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:53.142557+00:00
-- url     : https://prove2.me/submissions/2b6fbbc9-9f0f-4cd1-b0f3-0b8059c640c5

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Cellulation
import Theorems.Thm_QEC_Coding_PeriodicCubical4_boundary1_plaquetteBoundary

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PeriodicCubical4
open scoped Classical
variable {L : Nat} [NeZero L]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution :
    (boundary1 (L := L)).comp boundary2 = 0 :=
  linearize_comp_linearize_eq_zero
    plaquetteBoundary linkBoundary boundary1_plaquetteBoundary
end QEC.Coding.PeriodicCubical4
