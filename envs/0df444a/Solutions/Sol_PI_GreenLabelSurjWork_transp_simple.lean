-- Prove2me | solution 1 for PI.GreenLabelSurjWork.transp_simple
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:09.226442+00:00
-- url     : https://prove2.me/submissions/5c462497-12d2-4ad0-b6bb-ac21d3ae5e65

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
theorem _root_.solution (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)) (h : Simple τ) : Simple (transp e τ) := by
  rw [FDRep.simple_iff_char_is_norm_one] at h ⊢
  have hc : ∀ g, (transp e τ).character g = τ.character ((glEquiv K e).symm g) := fun g => rfl
  simp only [hc, map_inv]
  rw [Nat.card_congr (glEquiv K e).toEquiv.symm, ← h]
  exact Fintype.sum_equiv (glEquiv K e).symm.toEquiv _ _ (fun g => rfl)
end PI.GreenLabelSurjWork
