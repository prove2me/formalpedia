-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.phi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:19.982383+00:00
-- url     : https://prove2.me/submissions/3728f76b-5ddd-42c8-9268-d353850b9ac4

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
variable (P)
variable {P}
open Classical
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution (q : ℕ) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) :
    PhiQ q ξ k₀ r c' n' c n x =
      if CondQ P q k₀ r c' n' c n x then unitV ξ (AYm q k₀ r c' n' c n x).det else 0 := by
  unfold PhiQ CondQ AYm
  split_ifs with ha hb hb <;> first | rfl | exact absurd ha hb | exact absurd hb ha
end PI.TwistedEisensteinNonvanishing.W
