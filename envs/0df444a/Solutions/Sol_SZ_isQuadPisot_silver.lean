-- Prove2me | solution 1 for SZ.isQuadPisot_silver
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:39.014897+00:00
-- url     : https://prove2.me/submissions/ee881a1d-bd29-4d75-987a-0f7cceca9abe

import Definitions.Def_SZ_Silver
import Definitions.Def_SZ_Tijdeman
import Definitions.Def_SZ_QuadThm6
import Definitions.Def_SZ_GoldenS
import Mathlib.Tactic.LinearCombination
import Definitions.Def_SZ_Classification
import Theorems.Thm_SZ_silver_conj_neg
import Theorems.Thm_SZ_silver_pair


set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution : IsQuadPisot (1 + Real.sqrt 2) :=
  ⟨silver_pair.one_lt, 1 - Real.sqrt 2, 2, 1, ne_of_lt silver_conj_neg,
    silver_pair.absLt, silver_pair.sum, silver_pair.prod⟩
end SZ
