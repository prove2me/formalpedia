-- Prove2me | solution 1 for P2M_RH_Formalism_L2_FormalSeriesBounds_van_univ_d6ee8c839a455956
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:13:19.656964+00:00
-- url     : https://prove2.me/submissions/c4fff550-76e9-497f-b385-c4d369c8396b

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
theorem _root_.solution {τ : Type} {f : MvPowerSeries τ C} (hf : constantCoeff f = 0) : Van Set.univ f := by
  intro ν hν
  have h0 : ν = 0 := by
    ext w
    by_contra h
    exact hν w (Finsupp.mem_support_iff.mpr h) (Set.mem_univ _)
  subst h0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact hf
end Formalism.L2.FormalSeriesBounds
