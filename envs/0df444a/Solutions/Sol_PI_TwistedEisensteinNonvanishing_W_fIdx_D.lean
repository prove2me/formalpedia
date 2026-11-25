-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.fIdx_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:31:06.819859+00:00
-- url     : https://prove2.me/submissions/9b50c936-a763-4cef-b8b9-0a8a4c63ac6b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw

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
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {k₀ c n kj p : ℕ} (hk : k₀ ≤ kj) (hp1 : kj + c ≤ p) (hp2 : p < n + c) :
    kj ≤ fIdx k₀ c n p ∧ fIdx k₀ c n p < n := by
  unfold fIdx
  split_ifs <;> omega
end PI.TwistedEisensteinNonvanishing.W
