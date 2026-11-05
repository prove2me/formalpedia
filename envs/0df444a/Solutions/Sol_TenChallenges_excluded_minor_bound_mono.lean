-- Prove2me | solution 1 for TenChallenges.excluded_minor_bound_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:19.401115+00:00
-- url     : https://prove2.me/submissions/b8ef7649-32c9-4ddd-b717-f28a1708addf

import Definitions.Def_TenChallenges_Challenge_02

/-- Bounds may be enlarged while the range of prime powers is restricted. -/
theorem solution {r r' B B' : ℕ} (hr : r' ≤ r) (hB : B ≤ B')
    (h : TenChallenges.statement_02 r B) : TenChallenges.statement_02 r' B' := by
  intro p m hp hm hpm
  obtain ⟨S, hS, hcover⟩ := h p m hm (hpm.trans hr)
  exact ⟨S, hS.trans hB, hcover⟩

#print axioms solution
