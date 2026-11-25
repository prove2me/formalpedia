-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_half_trace_tmul_6dbb14eaff81
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:01:21.729442+00:00
-- url     : https://prove2.me/submissions/897a86cb-66c9-4a65-a9e0-896f06927bed

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductInvariance

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit
theorem _root_.solution (h2F : (2 : F) ≠ 0) (b : Module.Basis (Fin 2) F E) (r : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] (1 : E)) = r := by
  have h : (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) = algebraMap R (R ⊗[F] E) r := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [h, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b)]
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul, one_div, inv_mul_cancel₀ h2F, map_one]
  simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  rw [← mul_assoc, h2, one_mul]
end GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit
