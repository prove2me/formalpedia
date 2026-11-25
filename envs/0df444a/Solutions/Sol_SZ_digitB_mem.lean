-- Prove2me | solution 1 for SZ.digitB_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:07:42.784441+00:00
-- url     : https://prove2.me/submissions/8b615df5-ade8-4f49-b793-ff2ddf113167

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_pick_snd_mem

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (k : ℕ) : digitB k = 0 ∨ digitB k = 2 := pick_snd_mem (W k)
end SZ
