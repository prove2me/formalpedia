-- Prove2me | solution 1 for PI.GreenLabelSurjWork.blockUT_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:34.358161+00:00
-- url     : https://prove2.me/submissions/7c7c144d-f4d5-4c3f-8364-80b35503e289

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp

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
theorem _root_.solution {s : ℕ} (e : ι ≃ κ) (b : κ → Fin s) (M : Matrix ι ι K)
    (h : IsBlockUT K (b ∘ e) M) : IsBlockUT K b (Matrix.reindex e e M) := by
  intro i j hij
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact h _ _ (by simpa using hij)
end PI.GreenLabelSurjWork
