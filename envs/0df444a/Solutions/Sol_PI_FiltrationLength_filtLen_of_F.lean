-- Prove2me | solution 1 for PI.FiltrationLength.filtLen_of_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:15:32.697866+00:00
-- url     : https://prove2.me/submissions/7530f035-f6b6-4219-809e-454be923cae9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FiltLen
import Definitions.Def_Formalism_PeriodIntegrals_FiltLenF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiltrationLength_LengthQuotLeOfKerLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiltrationLength_FiltLenFMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FiltrationLength
open Submodule
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
namespace PI.FiltrationLength
theorem _root_.solution : PI.FiltLenF → PI.FiltLen := by
  intro hF R W _ _ _ F a hanti h0 ha V _ _ φ hinj M N P Q hNM hP hQ
  refine hF R W F a hanti h0 ha V (fun k => (φ k).comp (F k).subtype)
    (fun k x hx => hinj k x x.2 hx) M N P Q hNM ?_ ?_
  · intro k hk
    rw [Submodule.map_comp, Submodule.map_comap_subtype, inf_comm]
    exact hP k hk
  · intro k hk
    rw [Submodule.map_comp, Submodule.map_comap_subtype, inf_comm]
    exact hQ k hk
end PI.FiltrationLength
