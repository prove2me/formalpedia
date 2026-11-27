-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.theta_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:20:24.455959+00:00
-- url     : https://prove2.me/submissions/17bf1df3-3b85-4b95-8ebd-79b411173810

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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → (∃ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ) ∧ ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ → ∀ (t : ℝ) (w : InfinitePlace F), ‖θ t w‖ = |t| := by
  intro F _ _ hF
  have hw : ∀ w : InfinitePlace F, w.IsReal := hF.isReal
  refine ⟨⟨Pi.ringHom fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (hw w)).symm.toRingHom,
    continuous_pi fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (hw w)).symm.continuous⟩,
    fun θ _ t w => ?_⟩
  have h1 : ((InfinitePlace.Completion.ringEquivRealOfIsReal (hw w)).toRingHom.comp
      ((Pi.evalRingHom _ w).comp θ)) = RingHom.id ℝ := Subsingleton.elim _ _
  have h2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal (hw w) (θ t w) = t := DFunLike.congr_fun h1 t
  rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (hw w)).norm_map_of_map_zero (map_zero _), h2,
    Real.norm_eq_abs]
end PositivityTheory.PlacePermOperatorBicommutantSpan
