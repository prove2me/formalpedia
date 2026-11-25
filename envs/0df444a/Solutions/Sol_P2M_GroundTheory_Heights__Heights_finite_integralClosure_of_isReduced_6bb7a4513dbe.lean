-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finite_integralClosure_of_isReduced_6bb7a4513dbe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:52.707126+00:00
-- url     : https://prove2.me/submissions/fb23ed58-5a8e-4f7a-96e4-12c88196110b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_algHom_span_of_mem_minimalPrimes_8d1b1afb0c4d

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
theorem _root_.solution (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ} {O : Type}
    [CommRing O] [IsReduced O] [IsNoetherianRing O] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f) :
    Module.Finite O (integralClosure O (FractionRing O)) := by
  have := (minimalPrimes.finite_of_isNoetherianRing O).to_subtype
  choose g t ht using fun p : minimalPrimes O ↦ exists_algHom_span_of_mem_minimalPrimes hN φ hφ p.2
  let F : integralClosure O (FractionRing O) →ₗ[O]
      ((p : minimalPrimes O) → Submodule.span O (t p : Set (FractionRing (O ⧸ (p : Ideal O))))) :=
    LinearMap.pi fun p ↦ LinearMap.codRestrict _
      ((g p).toLinearMap ∘ₗ (integralClosure O (FractionRing O)).val.toLinearMap) fun x ↦ ht p x x.2
  refine Module.Finite.of_injective F ((injective_iff_map_eq_zero F).2 fun x hx ↦ ?_)
  have h0 : ∀ p : minimalPrimes O, g p x = 0 := fun p ↦ congrArg Subtype.val (congr_fun hx p)
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) (x : FractionRing O)
  have ha : a ∈ sInf (minimalPrimes O) := by
    refine Ideal.mem_sInf.2 fun p hp ↦ ?_
    have := Ideal.IsMinimalPrime.isPrime hp
    have e : algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p a) =
        algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) 0 := by
      rw [map_zero]
      change algebraMap O (FractionRing (O ⧸ p)) a = 0
      rw [← (g ⟨p, hp⟩).commutes, ← hab, map_mul, h0, zero_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.1 (IsFractionRing.injective _ _ e)
  rw [Ideal.sInf_minimalPrimes, Ideal.mem_radical_iff] at ha
  obtain ⟨k, hk⟩ := ha
  have ha0 : a = 0 := IsNilpotent.eq_zero ⟨k, by simpa using hk⟩
  rw [ha0, map_zero, (IsLocalization.map_units (FractionRing O) b).mul_left_eq_zero] at hab
  exact Subtype.ext hab
end GroundTheory.Heights₂.Heights
