-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.minorZ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:22:35.942615+00:00
-- url     : https://prove2.me/submissions/d4d43276-edf6-4a56-ae4a-17568a551777

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorZ
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_divZ_C_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_pow_dvd_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open Polynomial
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (hF : MinorFormula) : MinorZ := by
  intro n s hs m i N hiN I J
  rw [hF n s hs m false (m + i) N I J]
  apply divZ_C_mul
  apply Dvd.dvd.mul_left
  apply pow_dvd_prod N (m + i) i _ hiN
  intro l hl
  refine ⟨m + l, by omega, ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_add, map_sub, map_add]
  ring
end PositivityTheory.Rg.Sw.SP
