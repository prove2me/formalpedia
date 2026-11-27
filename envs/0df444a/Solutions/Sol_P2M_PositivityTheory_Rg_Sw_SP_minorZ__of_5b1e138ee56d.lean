-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_SP_minorZ__of_5b1e138ee56d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:14:31.067206+00:00
-- url     : https://prove2.me/submissions/1ff6205d-ac47-43d8-b196-e2143e408fed

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
theorem _root_.solution (hF : MinorFormula) : MinorZ' := by
  intro n s hs m j N hjN I J
  rw [hF n s hs m true j N I J]
  apply divZ_C_mul
  apply Dvd.dvd.mul_left
  apply pow_dvd_prod N j j _ hjN
  intro l hl
  refine ⟨l, hl, ?_⟩
  simp only [↓reduceIte, sub_self, map_zero, sub_zero]
end PositivityTheory.Rg.Sw.SP
