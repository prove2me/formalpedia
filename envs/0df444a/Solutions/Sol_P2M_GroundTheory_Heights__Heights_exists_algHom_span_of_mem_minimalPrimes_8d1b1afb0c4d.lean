-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_algHom_span_of_mem_minimalPrimes_8d1b1afb0c4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:24.683444+00:00
-- url     : https://prove2.me/submissions/6ec5a6c0-41b5-4649-aec6-3c9eeb3f6189

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_finset_span_integral_of_div_cb55b2e17947

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
open MvPolynomial ComplexSets FieldNumbers
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ}
    {O : Type} [CommRing O] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f) {p : Ideal O} (hp : p ∈ minimalPrimes O) :
    ∃ g : FractionRing O →ₐ[O] FractionRing (O ⧸ p), ∃ t : Finset (FractionRing (O ⧸ p)),
      ∀ x : FractionRing O, IsIntegral O x → g x ∈ Submodule.span O (t : Set (FractionRing (O ⧸ p))) := by
  have := Ideal.IsMinimalPrime.isPrime hp
  have hu : ∀ y : nonZeroDivisors O, IsUnit (Algebra.ofId O (FractionRing (O ⧸ p)) y) := by
    intro y
    refine IsUnit.mk0 _ fun h ↦ notMem_nonZeroDivisors_of_mem_mem_minimalPrimes ?_ hp y.2
    have h' : algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p y) =
        algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) 0 := by rw [map_zero]; exact h
    exact Ideal.Quotient.eq_zero_iff_mem.1 (IsFractionRing.injective _ _ h')
  obtain ⟨t, ht⟩ := exists_finset_span_integral_of_div hN φ hφ (Ω := FractionRing (O ⧸ p)) fun x ↦ by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O ⧸ p) x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨a, b, rfl⟩
  exact ⟨IsLocalization.liftAlgHom (M := nonZeroDivisors O) hu, t, fun x hx ↦ ht _ (hx.map _)⟩
end GroundTheory.Heights₂.Heights
