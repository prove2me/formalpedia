-- Prove2me | solution 1 for ThreeSum.TernaryPairedSelector.exists_cross_multiplied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:35.66488+00:00
-- url     : https://prove2.me/submissions/e01c1316-e8b2-44a2-a6f1-09cf694501a5

import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
import Theorems.Thm_ThreeSum_TernaryPairedSelector_exists_three_objectives

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedSelector
open Finset
open scoped BigOperators
variable {Ω : Type*} [DecidableEq Ω]
namespace ThreeSum.TernaryPairedSelector
theorem _root_.solution (S : Finset Ω) (hS : S.Nonempty)
    (f : Fin 3 → Ω → ℕ) (numerator denominator : Fin 3 → ℕ)
    (hd : ∀ i, 0 < denominator i)
    (havg : ∀ i, denominator i*(∑ seed ∈ S, f i seed) ≤ 3*S.card*numerator i) :
    ∃ seed ∈ S, ∀ i, denominator i*f i seed ≤ 9*numerator i := by
  have hden (i : Fin 3) : (0 : ℚ) < denominator i := by exact_mod_cast hd i
  obtain ⟨seed,hseed,hscore⟩ := exists_three_objectives S hS
    (fun i seed => (f i seed : ℚ))
    (fun i => 3*(numerator i : ℚ)/(denominator i : ℚ))
    (by intro i seed; positivity) (by intro i; positivity) (by
      intro i
      have hh : (denominator i : ℚ)*(∑ seed ∈ S, (f i seed : ℚ)) ≤
          3*(S.card : ℚ)*(numerator i : ℚ) := by exact_mod_cast havg i
      have hh' : (∑ seed ∈ S, (f i seed : ℚ)) ≤
          3*(S.card : ℚ)*(numerator i : ℚ)/(denominator i : ℚ) :=
        (le_div_iff₀ (hden i)).mpr (by nlinarith [hh])
      convert hh' using 1 <;> ring)
  refine ⟨seed,hseed, ?_⟩
  intro i
  have hh := hscore i
  have he : (3 : ℚ)*(3*(numerator i : ℚ)/(denominator i : ℚ)) =
      9*(numerator i : ℚ)/(denominator i : ℚ) := by ring
  rw [he] at hh
  have hmul := (le_div_iff₀ (hden i)).mp hh
  have hm : (denominator i : ℚ)*(f i seed : ℚ) ≤ 9*(numerator i : ℚ) := by nlinarith
  exact_mod_cast hm
end ThreeSum.TernaryPairedSelector
