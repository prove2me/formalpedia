-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.tof_two_le_dstar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:18:54.749942+00:00
-- url     : https://prove2.me/submissions/12a74791-b2c3-4779-ba70-d0a1411b2529

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofFinrankIRLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {X : PT E} {DF : ℕ} (P : Par X DF) : 2 ≤ dstar (E := E) P.m := by
  have h1 : 1 ≤ PT.f E := le_trans (Nat.one_le_pow _ _ P.hm1) P.hmf
  have h2 := P.hm1
  unfold dstar
  calc 2 = 2 * 1 * 1 := by norm_num
    _ ≤ 2 * PT.f E * P.m := by gcongr
end ReciprocityTheory.ChartRestriction.G.I2
