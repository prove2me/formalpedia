-- Prove2me | solution 1 for SmaleNinth.real_ram_certifies_two_variable_lp_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T15:06:55.957347+00:00
-- url     : https://prove2.me/submissions/8aa05b4e-fad4-4933-99ce-f08b12d67f22

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine
import Definitions.Def_SmaleNinth_RealRAM
import Theorems.Thm_SmaleNinth_farkas_lemma
import Theorems.Thm_SmaleNinth_real_ram_decides_two_variable_lp_quadratic

open Matrix LinearOptimization SmaleNinth

theorem solution :
    ∃ (R : RAMProgram) (C : ℕ),
      ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 2) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          RAMDecidesInTime R (encodeLP A b) (C * (m + 1) ^ 2) result ∧
          (result = true ↔ ∃ x : Fin 2 → ℝ, x ∈ polyhedron A b) ∧
          (result = false ↔
            ∃ y : Fin m → ℝ,
              (∀ i, 0 ≤ y i) ∧
              (∀ k, ∑ i, y i * A i k = 0) ∧
              0 < ∑ i, y i * b i) := by
  obtain ⟨R, C, hR⟩ := SmaleNinth.real_ram_decides_two_variable_lp_quadratic
  refine ⟨R, C, ?_⟩
  intro m A b
  obtain ⟨result, hdec, hverdict⟩ := hR m A b
  refine ⟨result, hdec, ?_, ?_⟩
  · constructor
    · intro htrue
      obtain ⟨x, hx⟩ := hverdict.mp htrue
      exact ⟨x, hx⟩
    · intro hx
      exact hverdict.mpr hx
  · constructor
    · intro hfalse
      have hno : ¬ (polyhedron A b).Nonempty := by
        intro hp
        have htrue : result = true := hverdict.mpr hp
        cases result with
        | true => cases hfalse
        | false => cases htrue
      have hcert : ∃ y : Fin m → ℝ,
            (∀ i, 0 ≤ y i) ∧
            (∀ k, ∑ i, y i * A i k = 0) ∧
            0 < ∑ i, y i * b i := by
        apply Classical.byContradiction
        intro hnoCert
        exact hno ((SmaleNinth.farkas_lemma A b).mpr hnoCert)
      exact hcert
    · intro hy
      have hno : ¬ (polyhedron A b).Nonempty := by
        intro hp
        have hncert : ¬ (∃ y : Fin m → ℝ,
            (∀ i, 0 ≤ y i) ∧
            (∀ k, ∑ i, y i * A i k = 0) ∧
            0 < ∑ i, y i * b i) :=
          (SmaleNinth.farkas_lemma A b).mp hp
        exact hncert hy
      cases result with
      | true => exact False.elim (hno (hverdict.mp rfl))
      | false => rfl
