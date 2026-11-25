-- Prove2me | solution 1 for P2M_Formalism_L2_FormalSeriesBounds_MapFB_map_expS__5faa65c8ae0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:33:29.882824+00:00
-- url     : https://prove2.me/submissions/20c3ec49-aa3a-4169-91fe-ff95759fe967

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGaugeMapSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePNabMapSt

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.MapFB
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {K C : Type} [Field K] [Field C] (φ : K →+* C) {d : ℕ}
namespace Formalism.L2.FormalSeriesBounds.MapFB
theorem _root_.solution [Algebra ℚ K] [Algebra ℚ C] {n : ℕ} (f : PS K n d) (hf : constantCoeff f = 0) :
    MvPowerSeries.map φ (FB.expS K f) = FB.expS C (MvPowerSeries.map φ f) := by
  unfold FB.expS
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf), PowerSeries.map_exp]
end Formalism.L2.FormalSeriesBounds.MapFB
