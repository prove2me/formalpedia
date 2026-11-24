-- Prove2me | solution 1 for RankCutFacility.Shifted.Supplement.lb_metric
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:08:52.633079+00:00
-- url     : https://prove2.me/submissions/76647cb2-841b-4ab1-867e-c3637c11e44c

import Definitions.Def_RankCutFacility_Shifted_Supplement_Online

set_option autoImplicit false

noncomputable section

open RankCutFacility.Shifted.Supplement

theorem solution (N : ℕ) (hN : 2 ≤ N) :
    (∀ a b : LBPoint N, lbDist N a b = 0 ↔ a = b) ∧
    (∀ a b : LBPoint N, lbDist N a b = lbDist N b a) ∧
    (∀ a b c : LBPoint N, lbDist N a c ≤ lbDist N a b + lbDist N b c) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (i | I) (j | J) <;> simp only [lbDist] <;> split_ifs <;> simp_all
  · rintro (i | I) (j | J) <;> simp only [lbDist] <;> split_ifs <;> simp_all [eq_comm]
  · rintro (i | I) (j | J) (k | K) <;> simp only [lbDist] <;> split_ifs <;> subst_vars <;>
      first | (norm_num; done) | simp_all
