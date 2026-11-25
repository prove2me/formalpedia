-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.inst_fix_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:12.530178+00:00
-- url     : https://prove2.me/submissions/3c772256-49e8-4c6e-9195-a600aadedab8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstTop
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory NumberField Matrix
open scoped ENNReal Pointwise
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {I : Formalism.MainNotions.S.AutInst} (v : InfinitePlace I.F) {r : ℕ} (e f : Fin r → Fin I.n → I.E)
    (z : Fin I.n → I.E) (m : Matrix (Fin I.n) (Fin I.n) ℂ) (hm : m * instBmat I v e f z = instBmat I v e f z) :
    ∀ x ∈ frameSet I e f z, m *ᵥ rv I v x = rv I v x := by
  intro x hx
  obtain ⟨j, rfl⟩ : ∃ j, instFvec e f z j = x := by
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hx
    · exact ⟨Sum.inl a, rfl⟩
    · exact ⟨Sum.inr (Sum.inl a), rfl⟩
    · exact ⟨Sum.inr (Sum.inr ()), (Set.mem_singleton_iff.1 hx).symm⟩
  rw [← inst_col v e f z j, Matrix.mulVec_mulVec, hm]
end PI.ScMuExists.UnitaryGroupMassFormula
