-- Prove2me | solution 1 for TenChallenges.challenge_06_r0
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:05:21.06825+00:00
-- url     : https://prove2.me/submissions/4b5817f9-afdb-41d6-bb19-fda81ebf0c5c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TenChallenges_challenge_06_r1

open SimpleGraph Ordinal

universe u

private theorem isAlphaWQO_zero_iff {Q : Type u} (le : Q → Q → Prop) :
    IsAlphaWQO le 0 ↔ IsWQO le := by
  constructor
  · intro h f
    obtain ⟨i, j, hij, hrel⟩ :=
      h (fun n => cast (VStar_zero Q).symm (f n))
    refine ⟨i, j, hij, ?_⟩
    simpa [leStar] using hrel
  · intro h f
    obtain ⟨i, j, hij, hrel⟩ := h (fun n => cast (VStar_zero Q) (f n))
    refine ⟨i, j, hij, ?_⟩
    simpa [leStar] using hrel

theorem solution : TenChallenges.statement_06 0 := by
  have h12 : (1 : Ordinal.{0}) < 2 := one_lt_two
  have hAll : IsAlphaWQO FiniteGraph.MinorLE 0 := by
    simpa [TenChallenges.statement_06, Ordinal.mod_eq_of_lt h12,
      Ordinal.div_eq_zero_of_lt h12] using TenChallenges.challenge_06_r1
  rw [isAlphaWQO_zero_iff] at hAll
  have hPlanar : IsAlphaWQO PlanarGraph.MinorLE 0 := by
    rw [isAlphaWQO_zero_iff]
    intro f
    obtain ⟨i, j, hij, hminor⟩ := hAll (fun n => (f n).val)
    exact ⟨i, j, hij, hminor⟩
  simpa [TenChallenges.statement_06] using hPlanar
