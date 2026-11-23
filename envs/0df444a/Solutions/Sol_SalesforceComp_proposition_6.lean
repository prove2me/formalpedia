-- Prove2me | solution 1 for SalesforceComp.proposition_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T01:16:59.650855+00:00
-- url     : https://prove2.me/submissions/bced133d-48b8-49e9-b4d8-1393b642c905
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SalesforceComp_Model
import Theorems.Thm_SalesforceComp_propositions_2_3_CD
import Theorems.Thm_SalesforceComp_propositions_2_3_CS
import Theorems.Thm_SalesforceComp_proposition_5_DD
import Theorems.Thm_SalesforceComp_proposition_5_DS

set_option autoImplicit false

open SalesforceComp

theorem solution (M : Model) (rs Qs : ℝ → ℝ) (hsol : M.SolvesFOC rs Qs)
    (hD : M.CondD rs) (hS : M.CondS rs Qs) :
    IsGreatest M.profitsCD (M.Vstar rs Qs) ∧ IsGreatest M.profitsCS (M.Vstar rs Qs) ∧
      IsGreatest M.profitsDD (M.Vstar rs Qs) ∧ IsGreatest M.profitsDS (M.Vstar rs Qs) := by
  obtain ⟨-, e1, g1⟩ := SalesforceComp.propositions_2_3_CD M rs Qs hsol hD
  obtain ⟨-, e2, g2⟩ := SalesforceComp.propositions_2_3_CS M rs Qs hsol hS
  obtain ⟨-, e3, g3⟩ := SalesforceComp.proposition_5_DD M rs Qs hsol hD
  obtain ⟨-, e4, g4⟩ := SalesforceComp.proposition_5_DS M rs Qs hsol hS
  rw [e1] at g1
  rw [e2] at g2
  rw [e3] at g3
  rw [e4] at g4
  exact ⟨g1, g2, g3, g4⟩
