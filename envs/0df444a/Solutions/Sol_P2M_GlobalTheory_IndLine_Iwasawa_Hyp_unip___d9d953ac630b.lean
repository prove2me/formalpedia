-- Prove2me | solution 1 for P2M_GlobalTheory_IndLine_Iwasawa_Hyp_unip___d9d953ac630b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:51:39.499029+00:00
-- url     : https://prove2.me/submissions/126bc0b8-c8c5-4307-bdc8-4f35076b2570

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_prX_mulVec
import Theorems.Thm_P2M_GlobalTheory_IndLine_Iwasawa_Hyp_r__88144f190e49

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
theorem _root_.solution {g : Matrix m m A}
    (hg : (1 - prX c J x y) * g * (1 - prX c J x y - prY c J x y) = 1 - prX c J x y - prY c J x y) (z : n → A) :
    ∃ a : A, g *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x := by
  have e : g * ι = ι + prX c J x y * (g * ι) := by
    have := congrArg (· * ι) hg
    simp only [Matrix.mul_assoc, h.rι] at this
    rw [Matrix.sub_mul, Matrix.one_mul] at this
    exact sub_eq_iff_eq_add.1 this
  refine ⟨((g * ι) *ᵥ z) ⬝ᵥ J *ᵥ (c ∘ y), ?_⟩
  rw [← prX_mulVec (x := x), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← e]
end GlobalTheory.IndLine.Iwasawa.Hyp
