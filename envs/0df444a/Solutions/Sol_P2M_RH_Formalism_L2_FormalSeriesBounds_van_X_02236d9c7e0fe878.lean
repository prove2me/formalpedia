-- Prove2me | solution 1 for P2M_RH_Formalism_L2_FormalSeriesBounds_van_X_02236d9c7e0fe878
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:02:51.530136+00:00
-- url     : https://prove2.me/submissions/bd75ec0d-2276-4e3d-a71e-259747bc67c7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {τ : Type} {T : Set τ} {q : τ} (hq : q ∈ T) : Van T (X q : MvPowerSeries τ C) := by
  intro ν hν
  rw [MvPowerSeries.coeff_X]
  split_ifs with h
  · exfalso
    exact hν q (by rw [h]; simp) hq
  · rfl
end Formalism.L2.FormalSeriesBounds
