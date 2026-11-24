-- Prove2me | solution 1 for ULHC.end_alt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:50:36.954993+00:00
-- url     : https://prove2.me/submissions/e2a51a2e-3cd5-4699-b273-69fe813237f8

import Definitions.Def_ULHC_Cr2
import Definitions.Def_ULHC_CrPath
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back_cellJ_succ


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {σ : StripSpec} (h2 : 2 ≤ σ.n) (he : σ.n % 2 = 0)
    (hp : StripPat F σ.c σ.s σ.n) :
    lat1 (endCell σ) σ.s ∈ F ∧ lat2 (endCell σ) σ.s ∈ F ∧ back (endCell σ) σ.s ∉ F ∧
      front (endCell σ) σ.s ∉ F := by
  obtain ⟨k, hk⟩ : ∃ k, σ.n = k + 2 := ⟨σ.n - 2, by omega⟩
  have hend : endCell σ = cellJ σ.c σ.s (k + 1) := by unfold endCell; rw [hk]; rfl
  rw [hend]
  rw [hk] at hp
  obtain ⟨_, hl, hf⟩ := hp
  refine ⟨(hl (k + 1) (by omega)).1.2 (by omega), (hl (k + 1) (by omega)).2.2 (by omega), ?_, ?_⟩
  · rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
  · intro h; have := (hf (k + 1) (by omega)).1 h; omega
end ULHC
