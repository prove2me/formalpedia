-- Prove2me | solution 1 for P2M_Formalism_L2_FormalSeriesBounds_VP_subst_pow__05906f14b766
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:52:12.070786+00:00
-- url     : https://prove2.me/submissions/aae79f07-d601-4718-a32a-cbcd6e6de8ef

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValBr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) (k : ℕ) :
    MvPowerSeries.subst a (f ^ k) = MvPowerSeries.subst a f ^ k := by
  have hb : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  first
    | exact MvPowerSeries.subst_pow hb f k
    | (rw [← MvPowerSeries.coe_substAlgHom hb, map_pow])
end Formalism.L2.FormalSeriesBounds.VP
