-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Coord_schurM_mem_0a609de872e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:01:52.589042+00:00
-- url     : https://prove2.me/submissions/d049cb3e-5c08-4340-950d-5a68c94ee46b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hinv : ∀ y : R ⊗[F] E, sigR R σ (sigR R σ y) = y) {n : ℕ} (t : F) (a : R → Rˣ)
    (S : HermR R σ (n + 1)) :
    schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by
  intro i j
  have hS := S.2 i.succ j.succ
  have ht : sigR R σ (inclR R (algebraMap F E t)) = inclR R (algebraMap F E t) := by
    simp [sigR, inclR]
  simp only [schurM, map_sub, map_mul, hinv, ht]
  rw [hS]
  ring
end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord
