-- Prove2me | solution 1 for Reformulated.TransposeInverseTheory.map_transposeInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:33:12.524274+00:00
-- url     : https://prove2.me/submissions/a6256598-028b-45b8-b906-34ea78090300

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_TransposeInverse_TransposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm

set_option autoImplicit false
open Reformulated Reformulated.TransposeInverseTheory
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
namespace Reformulated.TransposeInverseTheory
theorem _root_.solution {S : Type*} [CommRing S] (f : R →+* S) (g : GL n R) :
    GeneralLinearGroup.map f (transposeInv g) = transposeInv (GeneralLinearGroup.map f g) := by
  apply Units.ext
  rfl
end Reformulated.TransposeInverseTheory
