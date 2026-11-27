-- Prove2me | solution 1 for P2M_GlobalTheory_IndLine_Iwasawa_Hyp_levi___78c2cece847b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:51:24.757797+00:00
-- url     : https://prove2.me/submissions/3d92f69a-870a-47b1-9b25-155a37ffab88

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
theorem _root_.solution {g : Matrix m m A} (hp : g * prX c J x y = prX c J x y * g) (hq : g * prY c J x y = prY c J x y * g) :
    g * ι = ι * (ι' * g * ι) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.right, Matrix.sub_mul _ _ g, Matrix.sub_mul _ _ g, ← hp, ← hq,
    Matrix.one_mul, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc g, Matrix.mul_assoc g, h.pι, h.qι]
  simp
end GlobalTheory.IndLine.Iwasawa.Hyp
