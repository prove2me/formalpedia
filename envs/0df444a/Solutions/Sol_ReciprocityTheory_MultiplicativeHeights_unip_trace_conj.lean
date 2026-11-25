-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.unip_trace_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:05:49.776342+00:00
-- url     : https://prove2.me/submissions/44e52c74-3879-4912-b849-66b3dcbbebd8

import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentA
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentB
import Definitions.Def_ReciprocityTheory_SemistableReduction_Unipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r : ℕ} (Q M : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.det ≠ 0) :
    (Q * M * Q⁻¹).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ), Matrix.one_mul]
end ReciprocityTheory.MultiplicativeHeights
