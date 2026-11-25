-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_mul_eq_aeval_af68aaf6f222
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:50.827824+00:00
-- url     : https://prove2.me/submissions/46b48680-4149-417b-937f-5d20bc571550

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHypersurfacePresentation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_clear_denominators_86f7b5988c96

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
theorem _root_.solution {θ : A} (hθ : IsIntegral R θ)
    (hgen : IntermediateField.adjoin E {algebraMap A L θ} = ⊤) (x : A) :
    ∃ b : R, b ≠ 0 ∧ ∃ q : Polynomial R, Polynomial.aeval θ q = algebraMap R A b * x := by
  have hθE : IsIntegral E (algebraMap A L θ) := (hθ.map (IsScalarTower.toAlgHom R A L)).tower_top
  have hx : algebraMap A L x ∈ (IntermediateField.adjoin E {algebraMap A L θ}).toSubalgebra := by
    rw [hgen]; trivial
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθE.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨p, hp⟩ := hx
  obtain ⟨b, hb, q, hq⟩ := exists_clear_denominators (R := R) p
  refine ⟨b, hb, q, IsFractionRing.injective A L ?_⟩
  have h1 := congrArg (Polynomial.aeval (algebraMap A L θ)) hq
  rw [Polynomial.aeval_map_algebraMap, map_mul, Polynomial.aeval_C] at h1
  rw [← Polynomial.aeval_algebraMap_apply, h1, map_mul, ← IsScalarTower.algebraMap_apply R A L,
    IsScalarTower.algebraMap_apply R E L]
  exact congrArg _ hp
end GroundTheory.Heights₂.Heights.HypersurfacePresentation
