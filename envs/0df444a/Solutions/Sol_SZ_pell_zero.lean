-- Prove2me | solution 1 for SZ.pell_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:54:56.15604+00:00
-- url     : https://prove2.me/submissions/3b54d9ba-9814-43a7-bf5e-95015d79bf4f

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver

set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution : pell 0 = 0 := rfl
end SZ
