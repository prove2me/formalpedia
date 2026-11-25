-- Prove2me | solution 1 for SZ.evenDigit_pick
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:13:05.56398+00:00
-- url     : https://prove2.me/submissions/16a57cc3-6134-4160-a4c1-e50513ab75ba

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_pick_fst_mem
import Theorems.Thm_SZ_pick_snd_mem


set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (w : ℝ) : EvenDigit (pick w) := ⟨pick_fst_mem w, pick_snd_mem w⟩
end SZ
