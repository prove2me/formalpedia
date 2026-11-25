-- Prove2me | solution 1 for PI.UMultOne.UnitaryGroupMassFormula.emb_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:33:16.321127+00:00
-- url     : https://prove2.me/submissions/5c1683d6-1f2a-4c98-b280-e92490a20346

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitarySecondCountable_Assembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UMultOne PI.UMultOne.UnitaryGroupMassFormula
open Matrix Set
namespace PI.UMultOne.UnitaryGroupMassFormula
theorem _root_.solution (n : ℕ) (ι : Matrix.unitaryGroup (Fin n) ℂ →* Matrix.unitaryGroup (Fin (n + 1)) ℂ)
    (hι : ∀ g, ((ι g : Matrix.unitaryGroup (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))) :
    Continuous ι := by
  apply continuous_induced_rng.2
  have h : (Subtype.val ∘ ι) = fun g : Matrix.unitaryGroup (Fin n) ℂ =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
    funext g; exact hι g
  rw [h]
  exact (continuous_subtype_val.matrix_fromBlocks continuous_const continuous_const
    continuous_const).matrix_reindex _ _
end PI.UMultOne.UnitaryGroupMassFormula
