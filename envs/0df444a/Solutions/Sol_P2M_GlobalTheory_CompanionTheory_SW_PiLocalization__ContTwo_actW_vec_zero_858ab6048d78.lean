-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_actW_vec_zero_858ab6048d78
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:01:27.157653+00:00
-- url     : https://prove2.me/submissions/a0261ecc-9c79-4879-bc52-5ad694d6f3b8

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
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {N n : ℕ}
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (J' : Matrix (Fin (N + 1)) (Fin (N + 1)) E)
    (h : HA R σ J') (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E) (X : Fin n → Fin N → R ⊗[F] E) (i : Fin (N + 1)) :
    actW R σ J' h (vec A c X) 0 i =
      actW R σ J' h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) 0 i * A := by
  have hv : (Fin.cons A (fun _ => 0) : Fin (N + 1) → R ⊗[F] E) = A • Fin.cons 1 (fun _ => 0) := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k <;> simp
  simp only [actW, actTup, vec, Fin.cons_zero]
  rw [hv, Matrix.mulVec_smul]
  simp [mul_comm]
end GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo
