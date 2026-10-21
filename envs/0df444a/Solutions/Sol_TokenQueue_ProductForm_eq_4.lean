-- Prove2me | solution 1 for TokenQueue.ProductForm.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:34:40.743597+00:00
-- url     : https://prove2.me/submissions/fd2195d9-58f0-4556-866f-a3f40c88b26b

import Mathlib
import Definitions.Def_TokenQueue_ProductForm_Model

open TokenQueue.ProductForm Finset

theorem solution {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (x : State T) :
    mu P x.1 = P.eta (phi x.1) * kfun P (toks x.1) := by
  unfold mu muTok kfun
  rw [Finset.mul_sum]
  simp [toks]
