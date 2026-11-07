-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.boundary3_comp_boundary4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:58.408315+00:00
-- url     : https://prove2.me/submissions/f32d15ce-c219-4263-b55e-46a3932e482a

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Cellulation
import Theorems.Thm_QEC_Coding_PeriodicCubical4_boundary3_hypercubeBoundary

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PeriodicCubical4
open scoped Classical
variable {L : Nat} [NeZero L]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution :
    (boundary3 (L := L)).comp boundary4 = 0 :=
  linearize_comp_linearize_eq_zero
    hypercubeBoundary cubeBoundary boundary3_hypercubeBoundary
end QEC.Coding.PeriodicCubical4
