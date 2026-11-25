-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_minpoly_separable_up_to_f836c61939fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:53.22177+00:00
-- url     : https://prove2.me/submissions/6611caeb-a1e9-46e3-8dde-7d73364575ea

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
omit [IsDomain A]
include E L
namespace GroundTheory.Heights₂.Heights.HypersurfacePresentation
theorem _root_.solution [IsIntegrallyClosed R] {θ : A} (hθ : IsIntegral R θ) :
    ∃ δ : R, δ ≠ 0 ∧ ∃ u v : Polynomial R,
      u * minpoly R θ + v * Polynomial.derivative (minpoly R θ) = Polynomial.C δ := by
  have hθL : IsIntegral R (algebraMap A L θ) := hθ.map (IsScalarTower.toAlgHom R A L)
  have hm : minpoly R (algebraMap A L θ) = minpoly R θ :=
    minpoly.algHom_eq (IsScalarTower.toAlgHom R A L) (IsFractionRing.injective A L) θ
  have hE : minpoly E (algebraMap A L θ) = (minpoly R θ).map (algebraMap R E) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' E hθL, hm]
  obtain ⟨a, b, hab⟩ := (minpoly.irreducible (hθL.tower_top (A := E))).separable
  rw [hE, Polynomial.derivative_map] at hab
  obtain ⟨ba, hba, a', ha'⟩ := exists_clear_denominators (R := R) a
  obtain ⟨bb, hbb, b', hb'⟩ := exists_clear_denominators (R := R) b
  refine ⟨ba * bb, mul_ne_zero hba hbb, Polynomial.C bb * a', Polynomial.C ba * b', ?_⟩
  apply Polynomial.map_injective (algebraMap R E) (IsFractionRing.injective R E)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ha', hb', map_mul]
  linear_combination (Polynomial.C (algebraMap R E ba) * Polynomial.C (algebraMap R E bb)) * hab
end GroundTheory.Heights₂.Heights.HypersurfacePresentation
