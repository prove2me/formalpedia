-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.lenId_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:53:24.012498+00:00
-- url     : https://prove2.me/submissions/d15c9144-4a1b-41cb-a7df-67c276a356af

import Definitions.Def_ReciprocityTheory_DualLattices_LenIdStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MemOfSumSingleEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_LenIdBStatement
import Theorems.Thm_ReciprocityTheory_PGsh_Up_xModE_len

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R] {g m : ℕ}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution
    (hS2 : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
      v.Integers R → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R),
      HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)))
    (hB : LenIdBStatement) : LenIdStatement := by
  intro C _ v R _ _ hv g m Ht Bt E cp hcp hE hform εT εL π hπ hεT hsumT hεL hsumL hHt hBt hεE i d hd
    c₁ c₂ hc₁ hc₂
  obtain ⟨y, hy, hyc⟩ := hB C v R hv g m Ht Bt E cp hcp hE hform εT εL π hπ hεT hsumT hεL hsumL hHt hBt
    hεE i d hd c₁ hc₁
  refine ⟨y * c₂, xModE_len (hS2 C v R hv) Ht Bt εT εL π i (hHt i) (hBt i) hy hc₂, ?_⟩
  rw [mul_right_comm, hyc]
end ReciprocityTheory.PGsh.Up
