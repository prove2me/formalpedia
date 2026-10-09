-- Prove2me | solution 1 for OCB2012.pSucc_le_of_noSignalAtoB
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-08T23:14:18.063882+00:00
-- url     : https://prove2.me/submissions/61563c39-8250-4638-80f7-97cffe4b42ea

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Theorems.Thm_OCB2012_prob_nonneg
import Theorems.Thm_OCB2012_prob_eq_of_noSignalAtoB

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
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) (hW : IsProcessMatrix W) (hf : IsNoSignalAtoB W)
    (MA : Bool → Bool → Matrix (a1 × a2) (a1 × a2) ℂ) (hMA : IsAliceInstrument MA)
    (MB : Bool → Bool → Bool → Matrix (b1 × b2) (b1 × b2) ℂ) (hMB : IsBobInstrument MB) :
    pSucc W MA MB ≤ 3 / 4 := by
  set N := MA true false + MA false false
  have hN : IsCPTP_CJ N := bool_cptp (fun x => MA x false) (hMA.2 false)
  -- Bob's marginal does not depend on Alice's setting (no signalling from Alice to Bob)
  have key : ∀ y a b b', (prob W (MA true a) (MB y b b')).re + (prob W (MA false a) (MB y b b')).re
      = (prob W N (MB y b b')).re := by
    intro y a b b'
    rw [← Complex.add_re, ← prob_add_left]
    congr 1
    refine prob_eq_of_noSignalAtoB W hf _ _ _ ?_
    rw [(bool_cptp (fun x => MA x a) (hMA.2 a)).2, hN.2]
  -- normalization (condition (5))
  have norm : ∀ b b', (prob W N (MB true b b')).re + (prob W N (MB false b b')).re = 1 := by
    intro b b'
    rw [← Complex.add_re, ← prob_add_right,
      hW.2 _ _ hN (bool_cptp (fun y => MB y b b') (hMB.2 b b')), Complex.one_re]
  -- non-negative probabilities (condition (4))
  have nn : ∀ x a y b b', 0 ≤ (prob W (MA x a) (MB y b b')).re := fun x a y b b' =>
    (Complex.le_def.mp (prob_nonneg W hW.1 _ (hMA.1 x a) _ (hMB.1 y b b'))).1
  simp only [pSucc, Fintype.sum_bool]
  linarith [key true true true true, key true true true false, key true true false true, key true true false false, key true false true true, key true false true false, key true false false true, key true false false false, key false true true true, key false true true false, key false true false true, key false true false false, key false false true true, key false false true false, key false false false true, key false false false false, norm true true, norm true false, norm false true, norm false false, nn true true true true false, nn true true true false false, nn true true false true false, nn true true false false false, nn true false true true false, nn true false true false false, nn true false false true false, nn true false false false false, nn false true true true false, nn false true true false false, nn false true false true false, nn false true false false false, nn false false true true false, nn false false true false false, nn false false false true false, nn false false false false false]
