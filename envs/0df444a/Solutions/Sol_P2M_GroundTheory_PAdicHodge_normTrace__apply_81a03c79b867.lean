-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:17.405794+00:00
-- url     : https://prove2.me/submissions/4a316a86-7ce7-4868-adb6-c0c31450eee6

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
variable (F : Type*) {Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable [CharZero F] [Algebra.IsIntegral F Ω]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (y : Ω) : normTraceₗ F y = normTrace F y := rfl
end GroundTheory.PAdicHodge
