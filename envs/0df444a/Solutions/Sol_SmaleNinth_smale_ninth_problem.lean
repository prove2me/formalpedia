-- Prove2me | solution 1 for SmaleNinth.smale_ninth_problem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T18:49:18.920997+00:00
-- url     : https://prove2.me/submissions/99ac2ee7-4623-446e-81b1-3fcd09eb005b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_SmaleNinth_smale_ninth_real_ram
import Theorems.Thm_SmaleNinth_ram_to_bss_quadratic_nonneg
import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine
import Definitions.Def_SmaleNinth_RealRAM

/-!
Reduction of the goal to the random-access formulation: a strongly polynomial
program of the real pointer machine, compiled to the tape machine with
quadratic overhead, is a strongly polynomial tape program. The standard
encoding vanishes on negative cells, as the compilation theorem requires.
-/

open SmaleNinth Matrix LinearOptimization

lemma encodeLP_neg' {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : ℤ)
    (hc : c < 0) : encodeLP A b c = 0 := by
  unfold encodeLP
  have hmn : (0 : ℤ) ≤ (m : ℤ) * n := by positivity
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_neg (by omega)]

theorem solution :
    ∃ (P : BSSProgram) (C d : ℕ),
      ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          BSSDecidesInTime P (encodeLP A b) (C * (m * n + m + 2) ^ d) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) := by
  obtain ⟨R, C, d, hR⟩ := SmaleNinth.smale_ninth_real_ram
  obtain ⟨P, K, hP⟩ := SmaleNinth.ram_to_bss_quadratic_nonneg R
  refine ⟨P, 4 * K * (C + 1) ^ 2, 2 * d, fun m n A b => ?_⟩
  obtain ⟨result, hdec, hres⟩ := hR m n A b
  refine ⟨result, ?_, hres⟩
  obtain ⟨t, ht, hh⟩ := hP _ (fun c hc => encodeLP_neg' A b c hc) _ _ hdec
  refine ⟨t, le_trans ht ?_, hh⟩
  set N := m * n + m + 2 with hN
  have hN1 : 1 ≤ N ^ d := Nat.one_le_pow _ _ (by omega)
  calc K * (C * N ^ d + 1) ^ 2 ≤ K * ((C + 1) * N ^ d) ^ 2 := by
        gcongr
        nlinarith
    _ = K * (C + 1) ^ 2 * N ^ (2 * d) := by rw [pow_mul']; ring
    _ ≤ 4 * K * (C + 1) ^ 2 * N ^ (2 * d) := by nlinarith [Nat.zero_le (K * (C + 1) ^ 2 * N ^ (2 * d))]
