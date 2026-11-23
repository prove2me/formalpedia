-- Prove2me | solution 1 for P2M_Formalism_G_LogP_subst_zero__b4a287294211
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:22.67937+00:00
-- url     : https://prove2.me/submissions/65d190fd-8184-44d4-93c5-9b12497425e9

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]
namespace Formalism.G.LogP
theorem _root_.solution {σ τ : Type*} {b : σ → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b) :
    (0 : MvPowerSeries σ R).subst b = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom hb, map_zero]
end Formalism.G.LogP
