-- Prove2me | solution 1 for P2M_GlobalTheory_IndLine_Iwasawa_Hyp_ext__f02e101d5eb6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:51:23.258964+00:00
-- url     : https://prove2.me/submissions/8c0f0fe8-e6d3-403b-941b-eb3b51e3e79a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Hyp_mul_p
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Hyp_mul_q

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
theorem _root_.solution {g g' : Matrix m m A} (hx : g *ᵥ x = g' *ᵥ x) (hy : g *ᵥ y = g' *ᵥ y) (hι : g * ι = g' * ι) : g = g' := by
  have e : (1 : Matrix m m A) = ι * ι' + prX c J x y + prY c J x y := by rw [h.right]; abel
  rw [← Matrix.mul_one g, ← Matrix.mul_one g', e]
  simp only [Matrix.mul_add, mul_p, mul_q, ← Matrix.mul_assoc, hx, hy, hι]
end GlobalTheory.IndLine.Iwasawa.Hyp
