-- Prove2me | solution 1 for PI.GreenLabelSurjWork.glEquiv_mem_unip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:47:44.250904+00:00
-- url     : https://prove2.me/submissions/54cfcfcc-8a36-443f-b62c-25a60a0f0f87

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Theorems.Thm_PI_GreenLabelSurjWork_glEquiv_val
import Theorems.Thm_PI_GreenLabelSurjWork_blockUT_reindex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
open PI PI.GreenLabelSurjWork
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace PI.GreenLabelSurjWork
theorem _root_.solution {s : ℕ} (e : ι ≃ κ) (b : κ → Fin s) (u : GL ι K)
    (hu : u ∈ unip K (b ∘ e)) : glEquiv K e u ∈ unip K b := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [glEquiv_val]; exact blockUT_reindex e b _ h1
  · rw [← map_inv, glEquiv_val]; exact blockUT_reindex e b _ h2
  · intro i j hij
    rw [glEquiv_val]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [h3 _ _ (by simpa using hij)]
    simp [e.symm.injective.eq_iff]
end PI.GreenLabelSurjWork
