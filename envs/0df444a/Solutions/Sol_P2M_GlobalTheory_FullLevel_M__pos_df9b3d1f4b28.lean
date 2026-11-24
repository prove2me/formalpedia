-- Prove2me | solution 1 for P2M_GlobalTheory_FullLevel_M__pos_df9b3d1f4b28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:20:39.560803+00:00
-- url     : https://prove2.me/submissions/8ff11f1c-e80e-427a-9e3b-4dbf7785655b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_WeilIsUniqueOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FullLevel
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.FullLevel
theorem _root_.solution (l : Level H) : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
end GlobalTheory.FullLevel
