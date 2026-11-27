-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hups_cardUX_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:19:08.579796+00:00
-- url     : https://prove2.me/submissions/c9e4f094-422a-4145-834d-46d6dadb4dcb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_MinkSat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SatDegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsChooseRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PolyL2EqSqrtCoeffSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hups_choose_strict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (D N n n' deF u : ℕ) (h1 : 1 ≤ deF) (hn : deF ≤ n) :
    cardUX D N (n - deF) (n' - u) < cardUX D N n n' := by
  unfold cardUX
  have ha : (n - deF + D + 1).choose (D + 1) < (n + D + 1).choose (D + 1) :=
    hups_choose_strict D (show n - deF < n by omega)
  have hb : (n' - u + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) ≤
      (n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) :=
    Nat.choose_le_choose _ (by omega)
  have hb0 : 0 < (n' - u + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) :=
    Nat.choose_pos (by omega)
  calc _ < (n + D + 1).choose (D + 1) * (n' - u + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) :=
        Nat.mul_lt_mul_of_pos_right ha hb0
    _ ≤ _ := Nat.mul_le_mul_left _ hb
end ReciprocityTheory.ChartRestriction.G.T0
