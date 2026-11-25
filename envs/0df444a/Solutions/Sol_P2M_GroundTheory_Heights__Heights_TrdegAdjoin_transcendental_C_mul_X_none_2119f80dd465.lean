-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TrdegAdjoin_transcendental_C_mul_X_none_2119f80dd465
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:47.455901+00:00
-- url     : https://prove2.me/submissions/0e4ae965-0584-4df7-bc93-406d7e95061e

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_transcendental_C_mul_X_0818576c1779
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_optionEquivLeft_rename_some_481ac7e59e20

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TrdegAdjoin
open MvPolynomial Algebra Cardinal
attribute [local instance] MvPolynomial.algebraMvPolynomial
noncomputable section
variable {M : Type} [CommRing M] [IsDomain M] [Algebra ℚ M]
namespace GroundTheory.Heights₂.Heights.TrdegAdjoin
theorem _root_.solution {K κ : Type} [Field K] [Algebra ℚ K]
    (S : Subalgebra ℚ (MvPolynomial (Option κ) K))
    (hS : ∀ r ∈ S, ∃ a, r = rename some a) {c : K} (hc : c ≠ 0) :
    Transcendental S (C c * X none : MvPolynomial (Option κ) K) := by
  let gℚ : MvPolynomial (Option κ) K →ₐ[ℚ] Polynomial (MvPolynomial κ K) :=
    ((optionEquivLeft K κ : MvPolynomial (Option κ) K →ₐ[K] Polynomial (MvPolynomial κ K))).restrictScalars ℚ
  have hg : Function.Injective gℚ := (optionEquivLeft K κ).injective
  let f : S ≃ₐ[ℚ] S.map gℚ := Subalgebra.equivMapOfInjective S gℚ hg
  refine (transcendental_ringHom_iff_of_comp_eq f.toRingEquiv gℚ hg (RingHom.ext fun _ ↦ rfl)).mp ?_
  have he : gℚ (C c * X none) = Polynomial.C (C c) * Polynomial.X := by
    simp [gℚ, optionEquivLeft_C, optionEquivLeft_X_none]
  rw [he]
  refine transcendental_C_mul_X (S.map gℚ) ?_ (by rwa [Ne, MvPolynomial.C_eq_zero])
  rintro _ ⟨r, hr, rfl⟩
  obtain ⟨a, rfl⟩ := hS r hr
  exact ⟨a, optionEquivLeft_rename_some a⟩
end GroundTheory.Heights₂.Heights.TrdegAdjoin
