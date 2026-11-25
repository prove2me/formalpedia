-- Prove2me | solution 1 for P2M_Formalism_L2_FormalSeriesBounds_VP_subst_add__0bf35129255b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:15.663587+00:00
-- url     : https://prove2.me/submissions/c240510f-eda3-4c48-9fc9-34841f562292

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValU
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_hs
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f g : MvPowerSeries σ C) :
    MvPowerSeries.subst a (f + g) = MvPowerSeries.subst a f + MvPowerSeries.subst a g := by
  rw [← MvPowerSeries.coe_substAlgHom (VP.hs ha)]
  exact map_add _ f g
end Formalism.L2.FormalSeriesBounds.VP
