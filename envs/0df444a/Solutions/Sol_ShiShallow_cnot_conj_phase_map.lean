-- Prove2me | solution 1 for ShiShallow.cnot_conj_phase_map
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T05:56:37.278564+00:00
-- url     : https://prove2.me/submissions/8c2d5f5c-0f47-42eb-9817-e009847285a8

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

open ShiShallow

private lemma shiCnj_update_involution {n : ℕ} (x : Bits n) (i j : Fin n) (hij : i ≠ j) :
    Function.update (Function.update x j (xor (x j) (x i))) j
      (xor ((Function.update x j (xor (x j) (x i))) j)
           ((Function.update x j (xor (x j) (x i))) i)) = x := by
  funext k
  by_cases hk : k = j
  · subst hk
    rw [Function.update_self, Function.update_self, Function.update_of_ne hij]
    cases x k <;> cases x i <;> decide
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]

theorem solution {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ψ : QState n)
    (F : QState n → QState n) (a : Bits n → ℂ)
    (hF : ∀ (φ : QState n) (y : Bits n), F φ y = a y * φ y) :
    cnotState i j hij (F (cnotState i j hij ψ))
      = fun x => a (Function.update x j (xor (x j) (x i))) * ψ x := by
  funext x
  show F (cnotState i j hij ψ) (Function.update x j (xor (x j) (x i)))
      = a (Function.update x j (xor (x j) (x i))) * ψ x
  rw [hF]
  congr 1
  show ψ (Function.update (Function.update x j (xor (x j) (x i))) j
        (xor ((Function.update x j (xor (x j) (x i))) j)
             ((Function.update x j (xor (x j) (x i))) i))) = ψ x
  rw [shiCnj_update_involution x i j hij]
