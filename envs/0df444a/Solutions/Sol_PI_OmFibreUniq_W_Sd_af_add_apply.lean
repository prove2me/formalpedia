-- Prove2me | solution 1 for PI.OmFibreUniq.W.Sd.af_add_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:59:39.633802+00:00
-- url     : https://prove2.me/submissions/dcc1753d-ed3a-40da-a1bf-07c67b5917d9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SmulMemHermR
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_FundamentalContinuity_AdelicIsomorphismStatement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_AdditiveCharacterNontrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.Sd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Topology
open scoped TensorProduct
namespace PI.OmFibreUniq.W.Sd
theorem _root_.solution {F : Type} [Field F] [NumberField F] (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) :
    (a + b) w = a w + b w := rfl
end PI.OmFibreUniq.W.Sd
