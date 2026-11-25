-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_finset_span_integral_of_div_cb55b2e17947
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:54:24.619866+00:00
-- url     : https://prove2.me/submissions/5fbe7509-fd36-4d3b-a38f-467398053776

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_finset_integral_span_73e78e11898a


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
theorem _root_.solution (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ} {O Ω : Type}
    [CommRing O] [Field Ω] [Algebra O Ω] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f)
    (hΩ : ∀ x : Ω, ∃ a b : O, x = algebraMap O Ω a / algebraMap O Ω b) :
    ∃ t : Finset Ω, ∀ x : Ω, IsIntegral O x → x ∈ Submodule.span O (t : Set Ω) := by
  let ψ : MvPolynomial (Fin n) ℂ →+* Ω := (algebraMap O Ω).comp φ
  let _ : Algebra ℂ Ω := (ψ.comp C).toAlgebra
  let S : Set Ω := Set.range fun i ↦ ψ (X i)
  have hpoly : ∀ f, ψ f ∈ Algebra.adjoin ℂ S := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c => exact Subalgebra.algebraMap_mem _ c
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | mul_X f i hf => rw [map_mul]; exact mul_mem hf (Algebra.subset_adjoin ⟨i, rfl⟩)
  let A : Subalgebra ℂ Ω :=
    { toSubsemiring := (algebraMap O Ω).rangeS, algebraMap_mem' := fun c ↦ ⟨φ (C c), rfl⟩ }
  have hRA : Algebra.adjoin ℂ S ≤ A := Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact ⟨φ (X i), rfl⟩)
  have hloc : ∀ a ∈ A, ∃ r ∈ Algebra.adjoin ℂ S, ∃ d ∈ Algebra.adjoin ℂ S, d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹ := by
    rintro _ ⟨o, rfl⟩
    obtain ⟨f, s, hs, ho⟩ := hφ o
    refine ⟨ψ f, hpoly f, ψ s, hpoly s, (hs.map (algebraMap O Ω)).ne_zero, ⟨↑hs.unit⁻¹, ?_⟩, ?_⟩
    · change algebraMap O Ω ↑hs.unit⁻¹ = (algebraMap O Ω (φ s))⁻¹
      rw [map_units_inv, IsUnit.unit_spec]
    · refine (eq_mul_inv_iff_mul_eq₀ (hs.map (algebraMap O Ω)).ne_zero).2 ?_
      change algebraMap O Ω o * algebraMap O Ω (φ s) = algebraMap O Ω (φ f)
      rw [← map_mul, ho]
  have hE : ∀ x : Ω, x ∈ IntermediateField.adjoin ℂ S := by
    have hA : ∀ a ∈ A, a ∈ IntermediateField.adjoin ℂ S := by
      intro a ha
      obtain ⟨r, hr, d, hd, -, -, rfl⟩ := hloc a ha
      exact mul_mem (IntermediateField.algebra_adjoin_le_adjoin ℂ S hr)
        (inv_mem (IntermediateField.algebra_adjoin_le_adjoin ℂ S hd))
    intro x
    obtain ⟨a, b, rfl⟩ := hΩ x
    exact div_mem (hA _ ⟨a, rfl⟩) (hA _ ⟨b, rfl⟩)
  have hfin : FiniteDimensional (IntermediateField.adjoin ℂ S)
      (IntermediateField.extendScalars (le_refl (IntermediateField.adjoin ℂ S))) := by
    rw [IntermediateField.extendScalars_self]; infer_instance
  obtain ⟨t, -, ht⟩ := exists_finset_integral_span hN (Set.finite_range _) A _ hRA hloc le_rfl hfin
  let _ : Algebra O A := ((algebraMap O Ω).codRestrict A fun o ↦ (⟨o, rfl⟩ : algebraMap O Ω o ∈ (algebraMap O Ω).rangeS)).toAlgebra
  have : IsScalarTower O A Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hsur : Function.Surjective (algebraMap O A) := by rintro ⟨_, o, rfl⟩; exact ⟨o, rfl⟩
  refine ⟨t, fun x hx ↦ ?_⟩
  rw [← Submodule.restrictScalars_span O A hsur]
  exact ht x (hE x) hx.tower_top
end GroundTheory.Heights₂.Heights
