-- Prove2me | solution 1 for P2M_GlobalTheory_IndLine_Iwasawa_Hyp_q__f8a8d2591abe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:01.767643+00:00
-- url     : https://prove2.me/submissions/90f15fd2-7f01-43af-ba49-1e6a70600eab

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
variable {A A' : Type} [CommRing A] [CommRing A'] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {c : A →+* A} {c' : A' →+* A'} {J : Matrix m m A} {x y : m → A} {ι : Matrix m n A} {ι' : Matrix n m A}
open GlobalTheory.IndLine.Iwasawa.Hyp
variable (h : Hyp c J x y ι ι')
include h
namespace GlobalTheory.IndLine.Iwasawa.Hyp
theorem _root_.solution : prY c J x y * ι = 0 := by rw [prY, Matrix.neg_mul, Matrix.vecMulVec_mul, h.ιx, neg_eq_zero]; ext; simp [Matrix.vecMulVec_apply]
end GlobalTheory.IndLine.Iwasawa.Hyp
