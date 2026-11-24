-- Prove2me | solution 1 for P2M_Formalism_L2_FormalSeriesBounds_fin_two_eq_one_sub_of_ne__93512bbd28f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:09:37.196161+00:00
-- url     : https://prove2.me/submissions/ceb27ccd-1776-434f-aa05-55cffc36f35a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution : ∀ g g' : Fin 2, g' ≠ g → g' = 1 - g := by decide
end Formalism.L2.FormalSeriesBounds
