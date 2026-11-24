-- Prove2me | solution 1 for ULHC.pat_flip_off
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:44:05.35368+00:00
-- url     : https://prove2.me/submissions/27be4e32-34db-43db-afee-c416c42fdf78

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_mem_flip_off
import Theorems.Thm_ULHC_stripPat_congr


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {F : Finset Edge} {u : Pt} {w : StripSpec} (h1 : 1 ≤ w.n)
    (hoff : ∀ j < w.n, ∀ x ∈ cellE (cellJ w.c w.s j), x ∉ cellE u) :
    StripPat (flip F u) w.c w.s w.n ↔ StripPat F w.c w.s w.n := by
  obtain ⟨n, hn⟩ : ∃ n, w.n = n + 1 := ⟨w.n - 1, by omega⟩
  rw [hn] at hoff ⊢
  exact stripPat_congr (fun j hj e he => mem_flip_off (hoff j hj e he))
end ULHC
