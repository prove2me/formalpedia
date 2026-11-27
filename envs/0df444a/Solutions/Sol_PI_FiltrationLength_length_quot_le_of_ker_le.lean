-- Prove2me | solution 1 for PI.FiltrationLength.length_quot_le_of_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:15:38.086816+00:00
-- url     : https://prove2.me/submissions/840203a7-facf-498e-8532-c1d4d713f5bb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FiltLen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiltrationLength_LengthQuotLeOfKerLe

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
theorem _root_.solution {X Y : Type} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] (g : X →ₗ[R] Y) (K : Submodule R X) (hK : LinearMap.ker g ≤ K) :
    Module.length R (X ⧸ K) ≤ Module.length R Y := by
  have h1 : Module.length R (X ⧸ K) ≤ Module.length R (X ⧸ LinearMap.ker g) :=
    Module.length_le_of_surjective (Submodule.mapQ _ _ LinearMap.id (by simpa using hK))
      (by
        intro y
        induction y using Submodule.Quotient.induction_on with
        | _ x => exact ⟨Submodule.Quotient.mk x, by simp⟩)
  have h2 : Module.length R (X ⧸ LinearMap.ker g) = Module.length R (LinearMap.range g) :=
    (g.quotKerEquivRange).length_eq
  have h3 : Module.length R (LinearMap.range g) ≤ Module.length R Y :=
    Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.subtype_injective _)
  exact h1.trans (h2.le.trans h3)
end PI.FiltrationLength
