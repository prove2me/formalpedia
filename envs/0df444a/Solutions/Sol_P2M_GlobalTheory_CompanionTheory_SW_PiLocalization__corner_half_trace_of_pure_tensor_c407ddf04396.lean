-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__corner_half_trace_of_pure_tensor_c407ddf04396
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:29:44.845968+00:00
-- url     : https://prove2.me/submissions/0427cbe8-8dd2-49fc-9c02-937d8f089cc2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductMeasurableStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductFold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂
theorem _root_.solution [CharZero F] {d : ℕ} (b : Module.Basis (Fin d) F E) (hd : Module.finrank F E = 2)
    (x : R) (S : Matrix (Fin (0 + 1)) (Fin (0 + 1)) (R ⊗[F] E)) (h : S 0 0 = x ⊗ₜ[F] (1 : E)) :
    s0 R S = x := by
  have hd2 : d = 2 := by
    rw [← hd, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd2
  have e : x ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) x := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [s0, h, e, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b), Fintype.card_fin,
    two_nsmul, ← two_mul, ← mul_assoc]
  have : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul]
    simp
  rw [this, one_mul]
end GlobalTheory.CompanionTheory.SW.PiLocalization₂
