-- Prove2me | solution 1 for P2M_PI_TwistedEisensteinNonvanishing_W_redP_sum__a67c2a3dc9b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:47:45.24617+00:00
-- url     : https://prove2.me/submissions/20caa5b0-acb4-4681-87bf-a140ebe0c555

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Theorems.Thm_P2M_PI_TwChrOne_Pf_reduction_sum__8241acdd8e6b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  exact PI.TwChrOne.Pf.reduction_sum₂ P s f hf
end PI.TwistedEisensteinNonvanishing.W
