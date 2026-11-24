-- Prove2me | solution 1 for ULHC.stripPat_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:42:22.222094+00:00
-- url     : https://prove2.me/submissions/eb02bc24-08a5-4f9d-8715-66524f56771e

import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
import Theorems.Thm_ULHC_back_mem_zero
import Theorems.Thm_ULHC_front_mem_self
import Theorems.Thm_ULHC_lat1_mem_self
import Theorems.Thm_ULHC_lat2_mem_self


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {G G' : Finset Edge} {c : Pt} {s : Side} {n : ℕ}
    (h : ∀ j < n + 1, ∀ e ∈ cellE (cellJ c s j), (e ∈ G' ↔ e ∈ G)) :
    StripPat G' c s (n + 1) ↔ StripPat G c s (n + 1) := by
  have hb : back c s ∈ cellE (cellJ c s 0) := back_mem_zero c s
  unfold StripPat
  rw [h 0 (by omega) _ hb]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun j hj => ?_, fun j hj => ?_⟩
    · rw [← h j hj _ (lat1_mem_self c s j), ← h j hj _ (lat2_mem_self c s j)]; exact h2 j hj
    · rw [← h j hj _ (front_mem_self c s j)]; exact h3 j hj
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun j hj => ?_, fun j hj => ?_⟩
    · rw [h j hj _ (lat1_mem_self c s j), h j hj _ (lat2_mem_self c s j)]; exact h2 j hj
    · rw [h j hj _ (front_mem_self c s j)]; exact h3 j hj
end ULHC
