-- Prove2me | solution 1 for ShiShallow.majority3_accum
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T07:17:20.347256+00:00
-- url     : https://prove2.me/submissions/44c89590-3122-47a3-8997-9403d6f637c2

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

open ShiShallow

private lemma shiMaj_xor4_swap (e a b c : Bool) :
    xor (xor (xor e c) b) a = xor (xor (xor e a) b) c := by
  cases e <;> cases a <;> cases b <;> cases c <;> rfl

theorem solution {n : ℕ} (w0 w1 w2 t : Fin n)
    (hw0t : w0 ≠ t) (hw1t : w1 ≠ t) (hw2t : w2 ≠ t)
    (TOF : Fin n → Fin n → Fin n → QState n → QState n)
    (hTOF : ∀ (p q r : Fin n) (ψ : QState n),
      TOF p q r ψ = fun x => ψ (Function.update x r (xor (x r) (x p && x q))))
    (ψ : QState n) :
    TOF w2 w0 t (TOF w1 w2 t (TOF w0 w1 t ψ))
      = fun x => ψ (Function.update x t
          (xor (xor (xor (x t) (x w0 && x w1)) (x w1 && x w2)) (x w2 && x w0))) := by
  funext x
  simp only [hTOF, Function.update_of_ne hw0t, Function.update_of_ne hw1t,
    Function.update_of_ne hw2t, Function.update_self, Function.update_idem]
  exact congrArg (fun v => ψ (Function.update x t v))
    (shiMaj_xor4_swap (x t) (x w0 && x w1) (x w1 && x w2) (x w2 && x w0))
