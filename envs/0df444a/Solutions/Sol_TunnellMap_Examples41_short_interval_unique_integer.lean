-- Prove2me | solution 1 for TunnellMap.Examples41.short_interval_unique_integer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:39:21.273894+00:00
-- url     : https://prove2.me/submissions/91c82988-654b-4d82-b3d2-f2e78b8b8ae4

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator
import Theorems.Thm_TunnellMap_Examples41_short_interval_example

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution (b : ℤ)
    (hb : bLower 41 frame41 20 1 ≤ b ∧ b ≤ bUpper 41 frame41 20 1) :
    b = -4 := by
  have hlo : bLower 41 frame41 20 1 = -4 := short_interval_example.2.2.2.2.1
  have hhi : bUpper 41 frame41 20 1 = -4 := short_interval_example.2.2.2.2.2.1
  rw [hlo, hhi] at hb
  omega
end TunnellMap.Examples41
