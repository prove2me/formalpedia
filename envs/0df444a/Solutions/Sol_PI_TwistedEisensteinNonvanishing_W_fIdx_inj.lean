-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.fIdx_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:44.334347+00:00
-- url     : https://prove2.me/submissions/3b854b09-b3f2-4c8a-97cd-29160862286b

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
theorem _root_.solution {k₀ c n p p' : ℕ} (hp : p < n + c) (hp' : p' < n + c) (hk : k₀ ≤ n)
    (h : fIdx k₀ c n p = fIdx k₀ c n p') : p = p' := by
  unfold fIdx at h
  split_ifs at h <;> omega
end PI.TwistedEisensteinNonvanishing.W
