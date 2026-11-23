-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__GramCoord_corner_half_trace_of_pure_tensor_9938135d429c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:32.921497+00:00
-- url     : https://prove2.me/submissions/976c1e13-8b51-4a87-b58f-5d2a6745ee96

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramBlockOneFirstVectorFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductMeasurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord
theorem _root_.solution (hfr : Module.finrank F E = 2) {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) (r : R)
    (h : S 0 0 = r ⊗ₜ[F] (1 : E)) : s0 R S = r := by
  rcases subsingleton_or_nontrivial R with h' | h'
  · exact Subsingleton.elim _ _
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hK : Module.finrank R (R ⊗[F] E) = 2 := by rw [Module.finrank_baseChange]; exact hfr
  have hc : (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) = algebraMap R (R ⊗[F] E) r := rfl
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    have : (2 : R) = algebraMap F R 2 := (map_ofNat (algebraMap F R) 2).symm
    rw [this, ← map_mul]; simp
  unfold s0
  rw [h, hc, Algebra.trace_algebraMap, hK, two_nsmul, ← two_mul, ← mul_assoc, h2, one_mul]
end GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord
