-- Prove2me | solution 2 for RH.Transport.SupportedMass.supported_term_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:23:30.582074+00:00
-- url     : https://prove2.me/submissions/51350c2a-eddb-4281-b894-f1a0bed4e737

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass

set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section
namespace RH.Transport.SupportedMass
theorem _root_.solution {q T : ℝ} (hT : 0 < T) (hq : T ≤ q) :
    q ^ (-2 : ℝ) ≤ T ^ (-(1 / 2 : ℝ)) * q ^ (-(3 / 2 : ℝ)) := by
  have hq0 : 0 < q := lt_of_lt_of_le hT hq
  have hm : q ^ (-(1 / 2 : ℝ)) ≤ T ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hT hq (by norm_num)
  calc
    q ^ (-2 : ℝ) = q ^ (-(1 / 2 : ℝ)) * q ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hq0]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hq0.le _)
end RH.Transport.SupportedMass
