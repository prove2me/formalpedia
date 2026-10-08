-- Prove2me | solution 1 for SchedComplexity.NoWait.procTimes_pos
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:53:56.993958+00:00
-- url     : https://prove2.me/submissions/f6c9e51c-563e-4fe6-b025-4f5c1f3eb35e

import Mathlib
import Definitions.Def_SchedComplexity_NoWait_Construction



namespace SchedComplexity.NoWait

section cons
variable {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ) (lam mu : ℕ)

theorem ps_bd (ℓ : Fin n) (i : ℕ) :
    (i : ℤ) * mu - lam - 1 ≤ partialSum adj ι lam mu ℓ i ∧
      partialSum adj ι lam mu ℓ i ≤ (i : ℤ) * mu + lam + 1 := by
  have : (0:ℤ) ≤ lam := by positivity
  unfold partialSum
  split_ifs <;> constructor <;> linarith

theorem procTimes_pos_core (hι : Admissible n ι) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu)
    (ℓ : Fin n) (r : Fin (numMachines n)) : 1 ≤ procTimeInt adj ι lam mu ℓ r := by
  have h1 : (1:ℤ) ≤ lam := by exact_mod_cast hlam
  have h2 : (2:ℤ) * lam + 3 ≤ mu := by exact_mod_cast hmu
  unfold procTimeInt
  split_ifs with h
  · have := (ps_bd adj ι lam mu ℓ 1).1
    push_cast at this
    linarith
  · have a := (ps_bd adj ι lam mu ℓ (r.val+1)).1
    have b := (ps_bd adj ι lam mu ℓ r.val).2
    push_cast at a b
    linarith

end cons
end SchedComplexity.NoWait

open SchedComplexity.NoWait


theorem solution {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ)
    (hι : Admissible n ι) (lam mu : ℕ) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu)
    (ℓ : Fin n) (r : Fin (numMachines n)) :
    1 ≤ procTimeInt adj ι lam mu ℓ r := by
  exact procTimes_pos_core adj ι lam mu hι hlam hmu ℓ r
