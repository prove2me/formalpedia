-- Prove2me | solution 1 for P2M_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_subst_one__ed2a31d9d191
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:03.15627+00:00
-- url     : https://prove2.me/submissions/0a750723-8b90-4726-90cd-b64e8f9fa0d0

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks

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
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
theorem _root_.solution {σ τ : Type} (a : σ → MvPowerSeries τ C) :
    MvPowerSeries.subst a (1 : MvPowerSeries σ C) = 1 := by
  rw [← MvPolynomial.coe_one, MvPowerSeries.subst_coe, map_one]
end Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
