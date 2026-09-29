-- Prove2me | solution 1 for SmaleNinth.smale_ninth_real_ram
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T12:17:19.46402+00:00
-- url     : https://prove2.me/submissions/84e6976d-4584-4f23-bb9e-0ceaf10829c7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine
import Definitions.Def_SmaleNinth_RealRAM
import Theorems.Thm_SmaleNinth_awoniyi_certificate_solver
import Theorems.Thm_SmaleNinth_farkas_lemma

open Matrix LinearOptimization SmaleNinth

theorem solution :
    ∃ (R : RAMProgram) (C d : ℕ),
      ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          RAMDecidesInTime R (encodeLP A b) (C * (m * n + m + 2) ^ d) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) := by
  obtain ⟨R, C, d, hR⟩ := SmaleNinth.awoniyi_certificate_solver
  refine ⟨R, C, d, ?_⟩
  intro m n A b
  obtain ⟨result, hdec, htrue, hfalse⟩ := hR m n A b
  refine ⟨result, hdec, ?_⟩
  constructor
  · intro hresult
    obtain ⟨x, y, hx, hy0, hyA, hcomp⟩ := htrue.mp hresult
    exact ⟨x, hx⟩
  · intro hp
    cases result with
    | true => rfl
    | false =>
        obtain ⟨y, hy0, hyA, hyb⟩ := hfalse.mp rfl
        have hno := (SmaleNinth.farkas_lemma A b).mp hp
        exact False.elim (hno ⟨y, hy0, hyA, hyb⟩)
