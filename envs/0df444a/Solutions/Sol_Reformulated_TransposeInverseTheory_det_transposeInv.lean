-- Prove2me | solution 1 for Reformulated.TransposeInverseTheory.det_transposeInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:33:06.16501+00:00
-- url     : https://prove2.me/submissions/d7f94e52-e92b-45bb-847a-b88eb8f2e02a

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
theorem _root_.solution (g : GL n R) :
    GeneralLinearGroup.det (transposeInv g) = (GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  apply Units.ext
  simp only [GeneralLinearGroup.val_det_apply, coe_transposeInv, det_transpose]
end Reformulated.TransposeInverseTheory
