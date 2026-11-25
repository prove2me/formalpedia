-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_continuous_tmul_one_568389719e18
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:01:34.76969+00:00
-- url     : https://prove2.me/submissions/a6f16350-02e5-436f-a932-94d50c831cfa

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GermFormPulledBackCombinationsExpandMonomials
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductUniqueness

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (fun α : R => α ⊗ₜ[F] (1 : E)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
  have h : Continuous (fun α : R => α • (1 : R ⊗[F] E)) :=
    continuous_smul.comp (continuous_id.prodMk continuous_const)
  convert h using 2 with α
  rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
end GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo
