-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.theorem_5_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:27:17.143476+00:00
-- url     : https://prove2.me/submissions/f5e29b88-b194-477a-a69f-865a71a22cbf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ZeroFreeRRG_Hardcore_theorem_5_1_endpoint
import Theorems.Thm_ZeroFreeRRG_Hardcore_theorem_5_1_nontrivial
open scoped Classical
open ZeroFreeRRG.Hardcore

theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) :
    (∀ t : ℝ, m.Nontrivial t → Condition1 m d t → Condition2 m d t →
      ∃ U : Set ℂ, IsOpen U ∧ (t : ℂ) ∈ U ∧
        PottsRapidMixing.WithHighProb d (fun n G => ∀ z ∈ U, m.Zgraph d G z ≠ 0)) ∧
    (∃ U : Set ℂ, IsOpen U ∧ ((m.indepEndpoint : ℝ) : ℂ) ∈ U ∧
        PottsRapidMixing.WithHighProb d (fun n G => ∀ z ∈ U, m.Zgraph d G z ≠ 0)) :=
  ⟨theorem_5_1_nontrivial m hm d hd, theorem_5_1_endpoint m hm d hd⟩
