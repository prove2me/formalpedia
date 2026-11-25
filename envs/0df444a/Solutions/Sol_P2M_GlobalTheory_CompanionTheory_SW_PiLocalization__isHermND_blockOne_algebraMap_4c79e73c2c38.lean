-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isHermND_blockOne_algebraMap_4c79e73c2c38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:38:09.913797+00:00
-- url     : https://prove2.me/submissions/233de349-2b03-4838-a3b4-67214e9ae05a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerate
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__det_blockOne_eq_mul_03c1cf12390f

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → IsHermND σ (blockOne (algebraMap F E t) J) := by
  intro F E _ _ _ _ _ σ M J hJ t ht
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [blockOne]
    · simp [blockOne]
    · simp [blockOne]
    · simpa [blockOne] using hJ.1 i j
  · rw [det_blockOne_eq_mul]
    exact mul_ne_zero ((map_ne_zero _).2 ht) hJ.2
end GlobalTheory.CompanionTheory.SW.PiLocalization₂
