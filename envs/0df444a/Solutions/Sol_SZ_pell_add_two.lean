-- Prove2me | solution 1 for SZ.pell_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:52:42.996977+00:00
-- url     : https://prove2.me/submissions/8809bfc0-3e72-41b4-a9b2-eb0357e4fa81

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver

set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution (n : ℕ) : pell (n + 2) = 2 * pell (n + 1) + pell n := rfl
end SZ
