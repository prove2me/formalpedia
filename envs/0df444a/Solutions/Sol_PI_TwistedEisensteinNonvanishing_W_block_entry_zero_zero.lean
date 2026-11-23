-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.block_entry_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:43.796789+00:00
-- url     : https://prove2.me/submissions/8f19e895-a7ac-4261-a921-68774c7b99c4

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
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {N' N : ℕ} (q k₀ c' n' c n : ℕ) (x : HomE E N' N) (p p' : ℕ) :
    entB q k₀ c' n' c n 0 0 x p p' = atN (x (eN E N' (fIdx k₀ c' n' p'))) (fIdx k₀ c n p) := by
  simp [entB, scE]
end PI.TwistedEisensteinNonvanishing.W
