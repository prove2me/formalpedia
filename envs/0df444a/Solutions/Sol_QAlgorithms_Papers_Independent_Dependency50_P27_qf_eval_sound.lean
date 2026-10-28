-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.qf_eval_sound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:23:39.875983+00:00
-- url     : https://prove2.me/submissions/48c588bc-f083-470c-be31-68e853a7850e

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P27
open Polynomial


theorem solution {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (e : List R) (f : Formula R) (hf : qfForm f = true) :
    holds e f ↔ qfEval e f = true := by
  induction f with
  | bool b => simp [holds, qfEval]
  | equal a b => simp [holds, qfEval]
  | lt a b => simp [holds, qfEval]
  | le a b => simp [holds, qfEval]
  | and a b iha ihb =>
    simp only [qfForm, Bool.and_eq_true] at hf
    simp [holds, qfEval, iha hf.1, ihb hf.2]
  | or a b iha ihb =>
    simp only [qfForm, Bool.and_eq_true] at hf
    simp [holds, qfEval, iha hf.1, ihb hf.2]
  | implies a b iha ihb =>
    simp only [qfForm, Bool.and_eq_true] at hf
    simp only [holds, qfEval, iha hf.1, ihb hf.2]
    cases qfEval e a <;> cases qfEval e b <;> simp
  | not a iha =>
    simp only [qfForm] at hf
    simp [holds, qfEval, iha hf]
  | ex i a => simp [qfForm] at hf
  | all i a => simp [qfForm] at hf

end
