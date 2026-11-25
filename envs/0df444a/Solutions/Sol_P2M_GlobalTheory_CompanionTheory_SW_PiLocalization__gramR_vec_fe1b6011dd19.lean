-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__gramR_vec_fe1b6011dd19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:39:51.689847+00:00
-- url     : https://prove2.me/submissions/87917989-7273-453f-af91-81f93e3911bc

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramBlockOneFirstVectorFormula
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__hR_blockOne_cons_7313ef7402fc
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__hR_zero_left_101df9318131
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__sigR_tmul_one_e4a1507eaac4
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__tmul_one_mul_inclR_658628a98b31
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__tmul_algebraMap_931f1ce29a7a

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
theorem _root_.solution (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] (u : R)
    (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) 0 0 =
        (u ^ 2 * algebraMap F R t) ⊗ₜ[F] (1 : E) ∧
      (∀ j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) 0 j.succ =
        (u ⊗ₜ[F] (algebraMap F E t)) * c j) ∧
      ∀ i j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) i.succ j.succ =
        sigR R σ (c i) * inclR R (algebraMap F E t) * c j + gramR R σ J X i j := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [gramR, vec, Fin.cons_zero]
    rw [hR_blockOne_cons, hR_zero_left, add_zero, sigR_tmul_one, tmul_one_mul_inclR,
      tmul_algebraMap, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    ring
  · intro j
    simp only [gramR, vec, Fin.cons_zero, Fin.cons_succ]
    rw [hR_blockOne_cons, hR_zero_left, add_zero, sigR_tmul_one, tmul_one_mul_inclR]
  · intro i j
    simp only [gramR, vec, Fin.cons_succ]
    rw [hR_blockOne_cons]
end GlobalTheory.CompanionTheory.SW.PiLocalization₂
