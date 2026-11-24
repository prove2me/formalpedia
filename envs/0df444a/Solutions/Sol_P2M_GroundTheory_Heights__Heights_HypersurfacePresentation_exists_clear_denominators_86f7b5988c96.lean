-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_clear_denominators_86f7b5988c96
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:18.247631+00:00
-- url     : https://prove2.me/submissions/d7a9e2be-27d1-4a16-82d6-96f63448c3d7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHypersurfacePresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.HypersurfacePresentation
variable {R A E L : Type} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Field E] [Algebra R E] [IsFractionRing R E] [CharZero E]
  [Field L] [Algebra A L] [IsFractionRing A L] [Algebra R L] [IsScalarTower R A L]
  [Algebra E L] [IsScalarTower R E L]
omit [CharZero E] [IsDomain A]
namespace GroundTheory.Heights₂.Heights.HypersurfacePresentation
theorem _root_.solution (p : Polynomial E) :
    ∃ b : R, b ≠ 0 ∧ ∃ p' : Polynomial R,
      p'.map (algebraMap R E) = Polynomial.C (algebraMap R E b) * p := by
  obtain ⟨b, hb, h⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  exact ⟨b, nonZeroDivisors.ne_zero hb, _, by rw [h, Algebra.smul_def, Polynomial.algebraMap_apply]⟩
end GroundTheory.Heights₂.Heights.HypersurfacePresentation
