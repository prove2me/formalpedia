-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TrdegAdjoin_transcendental_C_mul_X_0818576c1779
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:22:25.561119+00:00
-- url     : https://prove2.me/submissions/1b0c8cd9-39ae-4341-84c5-9a84021a7ae1

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff

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
theorem _root_.solution (S : Subalgebra ℚ (Polynomial M))
    (hS : ∀ r ∈ S, ∃ a, r = Polynomial.C a) {m : M} (hm : m ≠ 0) :
    Transcendental S (Polynomial.C m * Polynomial.X) := by
  rw [transcendental_iff]
  intro p hp
  let κ : S →+* M := Polynomial.constantCoeff.comp (S.val : S →+* Polynomial M)
  have hκ : ∀ r : S, (r : Polynomial M) = Polynomial.C (κ r) := by
    intro r
    obtain ⟨a, ha⟩ := hS r r.2
    simp [κ, ha]
  have hinj : Function.Injective κ := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    apply Subtype.ext
    rw [hκ r, hr, map_zero]
    rfl
  have halg : algebraMap S (Polynomial M) = Polynomial.C.comp κ := RingHom.ext fun r ↦ hκ r
  have h1 : Polynomial.aeval (Polynomial.C m * Polynomial.X) p =
      (p.map κ).comp (Polynomial.C m * Polynomial.X) := by
    rw [Polynomial.aeval_def, halg, ← Polynomial.eval₂_map]
    rfl
  rw [h1] at hp
  rcases Polynomial.comp_eq_zero_iff.mp hp with h | ⟨_, h⟩
  · exact Polynomial.map_injective κ hinj (by rw [h, Polynomial.map_zero])
  · exfalso
    have h2 := congrArg (fun q : Polynomial M ↦ q.coeff 1) h
    simp only [Polynomial.coeff_C_mul_X, Polynomial.coeff_C] at h2
    simp at h2
    exact hm h2
end GroundTheory.Heights₂.Heights.TrdegAdjoin
