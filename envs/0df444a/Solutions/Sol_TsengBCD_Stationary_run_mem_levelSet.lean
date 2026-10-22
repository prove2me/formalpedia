-- Prove2me | solution 1 for TsengBCD.Stationary.run_mem_levelSet
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:52:10.243247+00:00
-- url     : https://prove2.me/submissions/949de14d-1e4e-46aa-b604-8ef0e79004f0

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting

set_option autoImplicit false
open Filter Topology TsengBCD.Stationary

theorem solution {N : ℕ} {n : Fin N → ℕ} (f : X n → EReal) (x0 : X n)
    (hx0 : f x0 ≠ ⊤) (hcpt : IsCompact (levelSet f x0))
    (s : ℕ → Fin N) (x : ℕ → X n) (hx : x 0 = x0) (hrun : IsBCDRun f s x) :
    (∀ r, f (x (r + 1)) ≤ f (x r) ∧ x (r + 1) ∈ levelSet f x0) ∧
      Bornology.IsBounded (Set.range x) := by
  have hdec : ∀ r, f (x (r + 1)) ≤ f (x r) := by
    intro r
    have h := (hrun.2 r).2 (x r (s r))
    simpa using h
  have hlev : ∀ r, x r ∈ levelSet f x0 := by
    intro r
    induction r with
    | zero => simp [levelSet, hx]
    | succ r ih => exact (hdec r).trans ih
  refine ⟨fun r => ⟨hdec r, hlev (r + 1)⟩, ?_⟩
  refine hcpt.isBounded.subset ?_
  rintro _ ⟨r, rfl⟩
  exact hlev r
