-- Prove2me | solution 1 for ShiShallow.majority_readout_scratch_accept_weight_eq_majority_weight
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T08:54:01.785048+00:00
-- url     : https://prove2.me/submissions/beb5fc97-8705-44c3-a383-2990462d4723

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

open ShiShallow

theorem solution {n : ℕ}
    (w0 w1 w2 t : Fin n) (h0 : w0 ≠ t) (h1 : w1 ≠ t) (h2 : w2 ≠ t)
    (ψ : QState n)
    (hInit : ∀ z : Bits n, z t = true → ψ z = 0)
    (TOF : Fin n → Fin n → Fin n → QState n → QState n)
    (hRead : ∀ φ : QState n,
      TOF w2 w0 t (TOF w1 w2 t (TOF w0 w1 t φ))
        = fun x : Bits n => φ (Function.update x t
            (xor (xor (xor (x t) (x w0 && x w1)) (x w1 && x w2)) (x w2 && x w0))))
    (hMaj : ∀ a b c : Bool,
      xor (xor (a && b) (b && c)) (c && a)
        = (if (2 : ℕ) ≤ (if a then (1 : ℕ) else 0) + (if b then (1 : ℕ) else 0)
            + (if c then (1 : ℕ) else 0) then true else false)) :
    (∑ y : Bits n, (if y t = true then
        ‖TOF w2 w0 t (TOF w1 w2 t (TOF w0 w1 t ψ)) y‖ ^ 2 else 0))
      = ∑ z : Bits n, (if z t = false ∧ (2 : ℕ) ≤ (if z w0 then (1 : ℕ) else 0)
          + (if z w1 then (1 : ℕ) else 0) + (if z w2 then (1 : ℕ) else 0)
          then ‖ψ z‖ ^ 2 else 0) := by
  have hb : ∀ a A B C : Bool, xor (xor (xor a A) B) C = xor a (xor (xor A B) C) := by
    intro a A B C
    cases a <;> cases A <;> cases B <;> cases C <;> decide
  have hact : ∀ x : Bits n,
      TOF w2 w0 t (TOF w1 w2 t (TOF w0 w1 t ψ)) x
        = ψ (Function.update x t (xor (x t)
            (if (2 : ℕ) ≤ (if x w0 then (1 : ℕ) else 0) + (if x w1 then (1 : ℕ) else 0)
              + (if x w2 then (1 : ℕ) else 0) then true else false))) := by
    intro x
    simp only [hRead]
    rw [hb, hMaj]
  have hinv : ∀ z : Bits n,
      Function.update (Function.update z t (!(z t))) t
          (!((Function.update z t (!(z t))) t)) = z := by
    intro z
    have e : (Function.update z t (!(z t))) t = !(z t) := Function.update_self t _ z
    first
      | (simp; done)
      | (rw [e, Bool.not_not, Function.update_idem, Function.update_eq_self]; done)
  refine Finset.sum_nbij' (fun y : Bits n => Function.update y t (!(y t)))
      (fun y : Bits n => Function.update y t (!(y t)))
      (fun z _ => Finset.mem_univ _) (fun z _ => Finset.mem_univ _)
      (fun z _ => hinv z) (fun z _ => hinv z) ?_
  intro y _
  simp only [hact, Function.update_of_ne h0, Function.update_of_ne h1,
    Function.update_of_ne h2, Function.update_self]
  by_cases hP : (2 : ℕ) ≤ (if y w0 then (1 : ℕ) else 0) + (if y w1 then (1 : ℕ) else 0)
      + (if y w2 then (1 : ℕ) else 0)
  · cases hy : y t
    · simp [hP]
    · simp [hP]
  · cases hy : y t
    · simp [hP]
    · have hz : ψ (Function.update y t true) = 0 := hInit _ (Function.update_self t true y)
      simp [hP, hz]
