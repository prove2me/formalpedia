-- Prove2me | solution 1 for P2M_GlobalTheory_IndLine_Iwasawa_Hyp_r__88144f190e49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:58.810982+00:00
-- url     : https://prove2.me/submissions/023e843e-5b2a-405b-8117-09e677e2dd18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_P2M_GlobalTheory_IndLine_Iwasawa_Hyp_p__3c8c698927f0
import Theorems.Thm_P2M_GlobalTheory_IndLine_Iwasawa_Hyp_q__f8a8d2591abe

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
variable {A A' : Type} [CommRing A] [CommRing A'] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {c : A →+* A} {c' : A' →+* A'} {J : Matrix m m A} {x y : m → A} {ι : Matrix m n A} {ι' : Matrix n m A}
open GlobalTheory.IndLine.Iwasawa.Hyp
variable (h : Hyp c J x y ι ι')
include h
namespace GlobalTheory.IndLine.Iwasawa.Hyp
theorem _root_.solution : (1 - prX c J x y - prY c J x y) * ι = ι := by
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, h.pι, h.qι, sub_zero, sub_zero]
end GlobalTheory.IndLine.Iwasawa.Hyp
