-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.up_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:04.567841+00:00
-- url     : https://prove2.me/submissions/39250bc7-4d17-4b2f-8fec-cef312943c82

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
theorem _root_.solution {F : Type} [Field F] [NumberField F] {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} :
    IsUnitProd a c ↔ ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → (∀ v, v ∉ S → c v = 1) ∧ a * ∏ v ∈ S, c v = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    have hf := Filter.eventually_cofinite.1 h1
    refine ⟨hf.toFinset, fun S hS => ⟨fun v hv => by_contra fun h => hv (hS (hf.mem_toFinset.2 h)), ?_⟩⟩
    rw [← finprod_eq_prod_of_mulSupport_subset c fun v hv => hS (hf.mem_toFinset.2 hv), h2]
  · rintro ⟨S, h⟩
    obtain ⟨h1, h2⟩ := h S le_rfl
    exact ⟨S.eventually_cofinite_notMem.mono h1, by
      rw [finprod_eq_prod_of_mulSupport_subset c fun v hv => by_contra fun h => hv (h1 v h), h2]⟩
end PositivityTheory.PlacePermOperatorBicommutantSpan
