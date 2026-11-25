-- Prove2me | solution 1 for P2M_GlobalTheory_IndLine_Iwasawa_map_star_mul__5f024dfe3853
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:32:04.869838+00:00
-- url     : https://prove2.me/submissions/c2ceb0c7-6e19-4577-8012-c5e399a1cd0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open GlobalTheory GlobalTheory.IndLine GlobalTheory.IndLine.Iwasawa
variable {m : Type} [Fintype m] [DecidableEq m]
namespace GlobalTheory.IndLine.Iwasawa
theorem _root_.solution {m n p : Type} [Fintype n] (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    (A * B).map star = A.map star * B.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)
end GlobalTheory.IndLine.Iwasawa
