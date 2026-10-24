-- Prove2me | solution 1 for ObfImpossibility.RiceNoSize.theorem_A_4
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-23T22:34:22.531984+00:00
-- url     : https://prove2.me/submissions/665b7e77-7e77-4bb6-9737-4c15514ad902

import Theorems.Thm_ObfImpossibility_RiceNoSize_Pi_closed
import Theorems.Thm_ObfImpossibility_RiceNoSize_Pi_decidable
import Theorems.Thm_ObfImpossibility_RiceNoSize_Z_profile
import Theorems.Thm_ObfImpossibility_RiceNoSize_finite_queries
import Theorems.Thm_ObfImpossibility_RiceNoSize_exists_N
import Theorems.Thm_ObfImpossibility_RiceNoSize_N_mem_PiY

open ObfImpossibility.RiceNoSize

theorem solution : ¬ ConjectureA3 := by
  intro h
  have disjoint : Disjoint PiY PiN := by
    apply Set.disjoint_left.mpr
    intro M hY hN
    obtain ⟨x, _, hx⟩ := hY.2
    have heq : Part.some (1 : ℕ) = Part.some 0 := hx.symm.trans (hN.2 x)
    simpa using heq
  obtain ⟨S, hY, hN⟩ := h PiY PiN disjoint Pi_closed Pi_decidable
  obtain ⟨n, hn⟩ := finite_queries S Z 0 (hN Z Z_profile.2)
  obtain ⟨r, _, hyes⟩ := N_mem_PiY n
  obtain ⟨N, hfn, hbounded⟩ := exists_N n r
  have hzero : simRun S N = Part.some 0 := hn N (by
    intro t x _ hx
    exact hbounded x hx t)
  have hone : simRun S N = Part.some 1 := hY N (hyes N hfn)
  have heq : Part.some (1 : ℕ) = Part.some 0 := hone.symm.trans hzero
  simpa using heq
