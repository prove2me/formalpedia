-- Prove2me | solution 1 for SZ.pell_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:01.326246+00:00
-- url     : https://prove2.me/submissions/4e7bbdb6-5731-4854-95ca-5973625e9a00

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver

set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution : pell 1 = 1 := rfl
end SZ
