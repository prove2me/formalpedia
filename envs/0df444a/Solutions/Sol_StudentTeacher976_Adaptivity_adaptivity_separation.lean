-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.adaptivity_separation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:13:32.359331+00:00
-- url     : https://prove2.me/submissions/a213a62a-16c6-41b5-9a61-28c890bbf03b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StudentTeacher976_Adaptivity_sigma_witness_presentation
import Theorems.Thm_StudentTeacher976_Adaptivity_auxiliary_upper_game
import Theorems.Thm_StudentTeacher976_Adaptivity_auxiliary_lower_advice

open StudentTeacher976.Adaptivity
set_option autoImplicit false

theorem solution (i : ℕ) (hardness : ¬ StudentTeacher976.Adaptivity.Sigma (i + 1) ⊆ DeltaPoly i)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q) :
    ¬ ST i (fun m => r m + 1) (fun _ => 1) ⊆ ST i r q := by
  intro hinc
  apply hardness
  intro L hL
  obtain ⟨W⟩ := sigma_witness_presentation i L hL
  exact auxiliary_lower_advice i L W r q hr hq
    (hinc (auxiliary_upper_game i L W r hr))
