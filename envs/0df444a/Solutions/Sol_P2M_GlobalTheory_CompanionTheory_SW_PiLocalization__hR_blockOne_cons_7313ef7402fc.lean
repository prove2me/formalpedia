-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__hR_blockOne_cons_7313ef7402fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:29:53.648634+00:00
-- url     : https://prove2.me/submissions/9092434e-31f3-4e1b-bfd6-4ff3b29214bf

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramBlockOneFirstVectorFormula

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
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (t : E) (x₀ y₀ : R ⊗[F] E) (x y : Fin M → R ⊗[F] E) :
    hR R σ (blockOne t J) (Fin.cons x₀ x : Fin (M + 1) → R ⊗[F] E) (Fin.cons y₀ y) =
      sigR R σ x₀ * inclR R t * y₀ + hR R σ J x y := by
  simp only [hR, hform, JR, Fin.sum_univ_succ, blockOne, Matrix.map_apply, Matrix.of_apply,
    Fin.cons_zero, Fin.cons_succ, map_zero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    zero_add]
end GlobalTheory.CompanionTheory.SW.PiLocalization₂
