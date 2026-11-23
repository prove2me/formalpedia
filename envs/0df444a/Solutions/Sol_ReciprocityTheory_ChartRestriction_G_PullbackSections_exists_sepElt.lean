-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:14.101867+00:00
-- url     : https://prove2.me/submissions/cac28b92-b4bc-41db-b39e-c73243a2c6af

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_LieBridgeC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open Polynomial NumberField IntermediateField Module
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {E : Type} [Field E] [NumberField E] {F : Type} [Field F] (j : F →+* ℂ)
    (χ : (E →+* ℂ) → (𝓞 E →+* F)) (hχ : ∀ τ a, j (χ τ a) = τ (a : E)) :
    ∃ α : 𝓞 E, Function.Injective (fun τ => χ τ α) ∧
      (∃ f : ℤ[X], aeval α f = 0 ∧ f.map (Int.castRingHom F) = ∏ τ, (X - C (χ τ α))) ∧
      ∀ a : 𝓞 E, ∃ (N : ℤ) (g : ℤ[X]), N ≠ 0 ∧ (N : 𝓞 E) * a = aeval α g := by
  classical
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ ({θ} : Finset E)
  have hint : IsIntegral ℤ (y • θ) := hyi θ (Finset.mem_singleton_self θ)
  let α : 𝓞 E := ⟨y • θ, hint⟩
  have hintα : IsIntegral ℤ ((α : 𝓞 E) : E) := hint
  have hαE : ((α : 𝓞 E) : E) = (y : E) * θ := by simp [α, zsmul_eq_mul]

  have htop : ℚ⟮((α : 𝓞 E) : E)⟯ = ⊤ := by
    rw [eq_top_iff, ← hθ, adjoin_simple_le_iff]
    have hy : (y : E) ≠ 0 := Int.cast_ne_zero.2 hy0
    have : θ = ((y : ℚ)⁻¹ : ℚ) • ((α : 𝓞 E) : E) := by
      rw [hαE, Rat.smul_def, ← mul_assoc, Rat.cast_inv, Rat.cast_intCast, inv_mul_cancel₀ hy, one_mul]
    rw [this]
    exact smul_mem _ (mem_adjoin_simple_self ℚ _)
  have hintQ : IsIntegral ℚ ((α : 𝓞 E) : E) := .of_finite ℚ _
  have hadj : Algebra.adjoin ℚ {((α : 𝓞 E) : E)} = ⊤ := by
    rw [← adjoin_simple_toSubalgebra_of_isAlgebraic hintQ.isAlgebraic, htop]
    rfl
  have hinj : Function.Injective (fun τ => χ τ α) := by
    intro τ τ' h
    have h' : τ ((α : 𝓞 E) : E) = τ' ((α : 𝓞 E) : E) := by
      rw [← hχ, ← hχ]; exact congrArg j h
    have := AlgHom.ext_of_adjoin_eq_top hadj (φ₁ := τ.toRatAlgHom) (φ₂ := τ'.toRatAlgHom)
      (by intro z hz; rw [Set.mem_singleton_iff.1 hz]; exact h')
    exact RingHom.ext fun z => congrArg (fun φ : E →ₐ[ℚ] ℂ => φ z) this
  have hinjE : Function.Injective (algebraMap (𝓞 E) E) := FaithfulSMul.algebraMap_injective (𝓞 E) E
  refine ⟨α, hinj, ⟨minpoly ℤ ((α : 𝓞 E) : E), ?_, ?_⟩, ?_⟩
  · apply hinjE
    rw [← Polynomial.aeval_algebraMap_apply, map_zero]
    exact minpoly.aeval ℤ _
  · have hp : (∏ τ, (X - C (χ τ α))).Monic := Polynomial.monic_prod_X_sub_C _ _
    have hq : ((minpoly ℤ ((α : 𝓞 E) : E)).map (Int.castRingHom F)).Monic := (minpoly.monic hintα).map _
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hp hq ?_ ?_
    · refine Finset.prod_dvd_of_coprime (fun τ _ τ' _ h => Polynomial.pairwise_coprime_X_sub_C hinj h)
        fun τ _ => Polynomial.dvd_iff_isRoot.2 ?_
      have hχa : aeval (χ τ α) (minpoly ℤ ((α : 𝓞 E) : E)) = χ τ (aeval α (minpoly ℤ ((α : 𝓞 E) : E))) :=
        Polynomial.aeval_algHom_apply (χ τ).toIntAlgHom α _
      have h0 : aeval α (minpoly ℤ ((α : 𝓞 E) : E)) = 0 := by
        apply hinjE
        rw [← Polynomial.aeval_algebraMap_apply, map_zero]
        exact minpoly.aeval ℤ _
      rw [Polynomial.IsRoot, Polynomial.eval_map, ← algebraMap_int_eq, ← Polynomial.aeval_def, hχa, h0, map_zero]
    · rw [(minpoly.monic hintα).natDegree_map, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ,
        NumberField.Embeddings.card E ℂ, ← IntermediateField.finrank_top', ← htop, IntermediateField.adjoin.finrank hintQ,
        minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hintα, (minpoly.monic hintα).natDegree_map]
  · intro a
    have ha : ((a : 𝓞 E) : E) ∈ Algebra.adjoin ℚ {((α : 𝓞 E) : E)} := by rw [hadj]; trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨r, hr⟩ := ha
    obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) r
    refine ⟨(b : ℤ), IsLocalization.integerNormalization (nonZeroDivisors ℤ) r, nonZeroDivisors.coe_ne_zero b, ?_⟩
    apply hinjE
    have hr' : aeval (algebraMap (𝓞 E) E α) r = algebraMap (𝓞 E) E a := hr
    rw [← Polynomial.aeval_algebraMap_apply, ← Polynomial.aeval_map_algebraMap ℚ, hb, map_zsmul, hr', map_mul,
      map_intCast, zsmul_eq_mul]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
