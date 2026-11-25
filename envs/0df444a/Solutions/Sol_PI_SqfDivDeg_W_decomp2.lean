-- Prove2me | solution 1 for PI.SqfDivDeg.W.decomp2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:24:20.825839+00:00
-- url     : https://prove2.me/submissions/3a78c308-2c5e-493b-9d5a-144a578ab93c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_CardMonicTwoRootsLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W
open Classical
namespace PI.SqfDivDeg.W
theorem _root_.solution {g : ℕ} [Fact g.Prime] {f : (ZMod g)[X]} {c d : ZMod g} (hcd : c ≠ d)
    (hc : f.IsRoot c) (hd : f.IsRoot d) :
    (X - C c) * ((X - C d) * ((f /ₘ (X - C c)) /ₘ (X - C d))) = f := by
  have h1 := mul_divByMonic_eq_iff_isRoot.mpr hc
  have hd1 : (f /ₘ (X - C c)).IsRoot d := by
    rw [← h1] at hd
    simp only [IsRoot, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero] at hd
    rcases hd with hd | hd
    · exact absurd (sub_eq_zero.mp hd).symm hcd
    · exact hd
  rw [mul_divByMonic_eq_iff_isRoot.mpr hd1, h1]
end PI.SqfDivDeg.W
