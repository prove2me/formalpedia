-- Prove2me | solution 1 for QualityEncroach.NoCommit.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:08:55.193393+00:00
-- url     : https://prove2.me/submissions/c8e7b8de-3cac-4684-9680-d8195df4fc20

import Theorems.Thm_QualityEncroach_NoCommit_stage3_no_uniform
open QualityEncroach.NoCommit

theorem solution (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (σ : Profile) (hσ : IsSPE k c σ)
    (henc : Encroaches σ) (hR : 0 < σ.path.qR) :
    σ.path.uM ≠ σ.path.uR := by
  have huR : 0 < σ.uR := hσ.2.2.1
  have hs := hσ.1 σ.w σ.uR (σ.order σ.w σ.uR) huR hR.le
  intro heq
  exact stage3_no_uniform k c hk hc σ.w σ.uR (σ.order σ.w σ.uR)
    (σ.stage3 σ.w σ.uR (σ.order σ.w σ.uR)).1
    (σ.stage3 σ.w σ.uR (σ.order σ.w σ.uR)).2
    huR hR hs.1 hs.2.1 hs.2.2 ⟨heq, henc⟩
