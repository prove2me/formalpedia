-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.up_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:20:42.617803+00:00
-- url     : https://prove2.me/submissions/6616e454-e712-4169-9a4c-966eae36e711

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_LocalSum
import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FibreFamilySmul
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExistsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuousStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_SdTransport
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_up_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (a b : ℝ≥0) (c e : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd a c → IsUnitProd b e → a ≠ 0 ∧ (∀ v, c v ≠ 0) ∧ IsUnitProd (a * b) (fun v => c v * e v) ∧ IsUnitProd a⁻¹ (fun v => (c v)⁻¹) ∧ IsUnitProd (a / b) (fun v => c v / e v) ∧ IsUnitProd (NNReal.sqrt a) (fun v => NNReal.sqrt (c v)) ∧ (∀ n : ℕ, IsUnitProd (a ^ n) (fun v => c v ^ n)) ∧ ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → (∀ v, v ∉ S → c v = 1) ∧ a * ∏ v ∈ S, c v = 1 := by
  intro F _ _ a b c e hc he
  classical
  have hom : ∀ (f : ℝ≥0 →* ℝ≥0) {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0}, IsUnitProd a c →
      IsUnitProd (f a) fun v => f (c v) := fun f a c h => by
    obtain ⟨S, hS⟩ := up_fin.1 h
    exact up_fin.2 ⟨S, fun T hT => ⟨fun v hv => by rw [(hS T hT).1 v hv, map_one], by
      rw [← map_prod, ← map_mul, (hS T hT).2, map_one]⟩⟩
  have mul : ∀ {a b : ℝ≥0} {c e : HeightOneSpectrum (𝓞 F) → ℝ≥0}, IsUnitProd a c → IsUnitProd b e →
      IsUnitProd (a * b) fun v => c v * e v := fun hc he => by
    obtain ⟨S, hS⟩ := up_fin.1 hc
    obtain ⟨S', hS'⟩ := up_fin.1 he
    refine up_fin.2 ⟨S ∪ S', fun T hT => ?_⟩
    obtain ⟨a1, a2⟩ := hS T (Finset.subset_union_left.trans hT)
    obtain ⟨b1, b2⟩ := hS' T (Finset.subset_union_right.trans hT)
    exact ⟨fun v hv => by rw [a1 v hv, b1 v hv, one_mul], by
      rw [Finset.prod_mul_distrib, mul_mul_mul_comm, a2, b2, one_mul]⟩
  obtain ⟨S, hS⟩ := up_fin.1 hc
  refine ⟨left_ne_zero_of_mul_eq_one hc.2, fun v => ?_, mul hc he, hom invMonoidHom hc, ?_,
    hom (NNReal.sqrtHom : ℝ≥0 →*₀ ℝ≥0) hc, fun n => hom (powMonoidHom n) hc, S, hS⟩
  · exact Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul_eq_one (hS (insert v S) (Finset.subset_insert _ _)).2) v
      (Finset.mem_insert_self _ _)
  · simp only [div_eq_mul_inv]
    exact mul hc (hom invMonoidHom he)
end PositivityTheory.PlacePermOperatorBicommutantSpan
