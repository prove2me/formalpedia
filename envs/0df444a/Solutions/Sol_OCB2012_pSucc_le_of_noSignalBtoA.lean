-- Prove2me | solution 1 for OCB2012.pSucc_le_of_noSignalBtoA
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-08T23:14:16.583719+00:00
-- url     : https://prove2.me/submissions/b726c176-6fef-46fc-aabc-a7027b2b662e

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Theorems.Thm_OCB2012_prob_nonneg
import Theorems.Thm_OCB2012_prob_eq_of_noSignalBtoA

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012Sol
open OCB2012

lemma prob_add_left {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2] [Fintype b1] [Fintype b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) (MA MA' : Matrix (a1 × a2) (a1 × a2) ℂ) (MB : Matrix (b1 × b2) (b1 × b2) ℂ) :
    prob W (MA + MA') MB = prob W MA MB + prob W MA' MB := by
  simp only [prob, add_kronecker, Matrix.mul_add, trace_add]

lemma prob_add_right {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2] [Fintype b1] [Fintype b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (MB MB' : Matrix (b1 × b2) (b1 × b2) ℂ) :
    prob W MA (MB + MB') = prob W MA MB + prob W MA MB' := by
  simp only [prob, kronecker_add, Matrix.mul_add, trace_add]

lemma bool_cptp {x1 x2 : Type*} [Fintype x1] [Fintype x2] [DecidableEq x1]
    (M : Bool → Matrix (x1 × x2) (x1 × x2) ℂ) (h : IsCPTP_CJ (∑ x, M x)) :
    IsCPTP_CJ (M true + M false) := by
  simpa [Fintype.sum_bool] using h

end OCB2012Sol

open OCB2012 OCB2012Sol in
theorem solution {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2]
    [Fintype b1] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) (hW : IsProcessMatrix W) (hf : IsNoSignalBtoA W)
    (MA : Bool → Bool → Matrix (a1 × a2) (a1 × a2) ℂ) (hMA : IsAliceInstrument MA)
    (MB : Bool → Bool → Bool → Matrix (b1 × b2) (b1 × b2) ℂ) (hMB : IsBobInstrument MB) :
    pSucc W MA MB ≤ 3 / 4 := by
  set N := MB true false false + MB false false false
  have hN : IsCPTP_CJ N := bool_cptp (fun y => MB y false false) (hMB.2 false false)
  -- Alice's marginal does not depend on Bob's setting (no signalling from Bob to Alice)
  have key : ∀ x a b b', (prob W (MA x a) (MB true b b')).re + (prob W (MA x a) (MB false b b')).re
      = (prob W (MA x a) N).re := by
    intro x a b b'
    rw [← Complex.add_re, ← prob_add_right]
    congr 1
    refine prob_eq_of_noSignalBtoA W hf _ _ _ ?_
    rw [(bool_cptp (fun y => MB y b b') (hMB.2 b b')).2, hN.2]
  -- normalization (condition (5))
  have norm : ∀ a, (prob W (MA true a) N).re + (prob W (MA false a) N).re = 1 := by
    intro a
    rw [← Complex.add_re, ← prob_add_left,
      hW.2 _ _ (bool_cptp (fun x => MA x a) (hMA.2 a)) hN, Complex.one_re]
  -- non-negative probabilities (condition (4))
  have nn : ∀ x a y b b', 0 ≤ (prob W (MA x a) (MB y b b')).re := fun x a y b b' =>
    (Complex.le_def.mp (prob_nonneg W hW.1 _ (hMA.1 x a) _ (hMB.1 y b b'))).1
  simp only [pSucc, Fintype.sum_bool]
  linarith [key true true true true, key true true true false, key true true false true, key true true false false, key true false true true, key true false true false, key true false false true, key true false false false, key false true true true, key false true true false, key false true false true, key false true false false, key false false true true, key false false true false, key false false false true, key false false false false, norm true, norm false, nn true true true true true, nn true true true false true, nn true true false true true, nn true true false false true, nn true false true true true, nn true false true false true, nn true false false true true, nn true false false false true, nn false true true true true, nn false true true false true, nn false true false true true, nn false true false false true, nn false false true true true, nn false false true false true, nn false false false true true, nn false false false false true]
