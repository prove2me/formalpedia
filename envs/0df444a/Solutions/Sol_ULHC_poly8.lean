-- Prove2me | solution 1 for ULHC.poly8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:27:02.560258+00:00
-- url     : https://prove2.me/submissions/a6c96fe5-cdb2-4b5b-b618-4f97171b8a34

import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_CostTwoFactor
import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostAlg

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (N n : ℕ) (hN : 1 ≤ N) (hn : n ≤ 24 * N ^ 2) :
    n ^ 2 + n * (n * (n * (300 * N ^ 2 + n + 5) + 4)) + n * (160 * N ^ 2 + n + 3) + n + 4 ≤
      5000000 * N ^ 8 := by
  calc n ^ 2 + n * (n * (n * (300 * N ^ 2 + n + 5) + 4)) + n * (160 * N ^ 2 + n + 3) + n + 4
      ≤ (24 * N ^ 2) ^ 2 + (24 * N ^ 2) * ((24 * N ^ 2) * ((24 * N ^ 2) *
          (300 * N ^ 2 + 24 * N ^ 2 + 5) + 4)) + (24 * N ^ 2) * (160 * N ^ 2 + 24 * N ^ 2 + 3) +
          24 * N ^ 2 + 4 := by
        gcongr
    _ ≤ 5000000 * N ^ 8 := by
        set M := N ^ 2 with hM
        have h1 : 1 ≤ M := Nat.one_le_pow _ _ hN
        have h8 : N ^ 8 = M ^ 4 := by rw [hM, ← pow_mul]
        rw [h8]
        have a1 : M ≤ M ^ 2 := by nlinarith
        have a2 : M ^ 2 ≤ M ^ 3 := by nlinarith
        have a3 : M ^ 3 ≤ M ^ 4 := by nlinarith
        nlinarith
end ULHC
