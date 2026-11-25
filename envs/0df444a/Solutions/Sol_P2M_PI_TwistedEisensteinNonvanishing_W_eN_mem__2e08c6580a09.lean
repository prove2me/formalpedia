-- Prove2me | solution 1 for P2M_PI_TwistedEisensteinNonvanishing_W_eN_mem__2e08c6580a09
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:47:58.709657+00:00
-- url     : https://prove2.me/submissions/08852ac3-6f89-40f8-8964-1a38fe064ccc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_mem_stdAt__54b003285def
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_one
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_zero


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
theorem _root_.solution (n j : ℕ) : eN E n j ∈ stdAt E n P := by
  rw [mem_stdAt']
  intro l
  unfold eN
  split_ifs
  · exact ia_one (P := P)
  · exact ia_zero (P := P)
end PI.TwistedEisensteinNonvanishing.W
