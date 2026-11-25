-- Prove2me | solution 1 for PI.OmFibreUniq.W.Sd.af_natCast_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:04:50.313356+00:00
-- url     : https://prove2.me/submissions/f508bf83-4896-44fe-a815-c2a15db8577a

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
theorem _root_.solution {F : Type} [Field F] [NumberField F] (N : ℕ) (w : HeightOneSpectrum (𝓞 F)) :
    (N : Af F) w = (N : Fv F w) := rfl
end PI.OmFibreUniq.W.Sd
