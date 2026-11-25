-- Prove2me | solution 1 for PI.Dv.IdxW.lenS_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:31.998273+00:00
-- url     : https://prove2.me/submissions/6e6ba580-497b-495d-b5b6-92549e06c9bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ElementDenominator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.IdxW
open Module
variable {R : Type*} [CommRing R] (S : Submonoid R)
namespace PI.Dv.IdxW
theorem _root_.solution {A B C : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Module.length (Localization S) (LocalizedModule S B) =
      Module.length (Localization S) (LocalizedModule S A) +
        Module.length (Localization S) (LocalizedModule S C) :=
  Module.length_eq_add_of_exact (LocalizedModule.map S f) (LocalizedModule.map S g)
    (LocalizedModule.map_injective S f hf) (LocalizedModule.map_surjective S g hg)
    (LocalizedModule.map_exact S f g hfg)
end PI.Dv.IdxW
