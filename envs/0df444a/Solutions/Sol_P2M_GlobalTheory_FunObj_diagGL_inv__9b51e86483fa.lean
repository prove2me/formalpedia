-- Prove2me | solution 1 for P2M_GlobalTheory_FunObj_diagGL_inv__9b51e86483fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:31:31.991262+00:00
-- url     : https://prove2.me/submissions/c8430c91-e008-49da-97d9-5c913923d95a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InverseUnipotentVolumeConjDiagonalUnitsGLMul
import Theorems.Thm_P2M_GlobalTheory_FunObj_diagGL_mul__bb3860aff896

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open Matrix
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.FunObj
theorem _root_.solution (d : n → kˣ) : diagGL d⁻¹ = (diagGL d)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← diagGL_mul']; exact Units.ext (by simp))
end GlobalTheory.FunObj
