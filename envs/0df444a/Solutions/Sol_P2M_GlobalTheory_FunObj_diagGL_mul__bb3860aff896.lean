-- Prove2me | solution 1 for P2M_GlobalTheory_FunObj_diagGL_mul__bb3860aff896
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:57.305804+00:00
-- url     : https://prove2.me/submissions/05ff57a3-2ff6-4368-b629-921b786b6d40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InverseUnipotentVolumeConjDiagonalUnitsGLMul

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
theorem _root_.solution (d e : n → kˣ) : diagGL (d * e) = diagGL d * diagGL e :=
  Units.ext (by simp [diagonal_mul_diagonal])
end GlobalTheory.FunObj
