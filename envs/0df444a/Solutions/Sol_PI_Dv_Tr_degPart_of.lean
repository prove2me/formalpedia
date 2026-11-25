-- Prove2me | solution 1 for PI.Dv.Tr.degPart_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:46.205889+00:00
-- url     : https://prove2.me/submissions/bebe797b-8aca-410b-9d42-eee764962131

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv
namespace PI.Dv.Tr
theorem _root_.solution (h1 : SplitBound) (h2 : PerSBound) : DegPart := by
  intro K _ _ _ _ G _ _ T P0 P hM A ρ hA
  have hs := h1 K G T P0 P hM A ρ hA
  have hp := h2 K G T P0 P hM A ρ hA
  set a := degL A (cut A ρ (eps P * eG T) A.L)
  set c : T.S → ℝ := fun s => degL A (cut A ρ (eps P * eS T s) A.L)
  set b : T.S → ℝ := fun s => degL A (cut A ρ (eps P0 * eS T s) A.L)
  have hsum : |∑ s, (c s - (nS T P s : ℝ) * b s)| ≤ 5 * laG G * (rkT T P0 P A ρ : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun s _ => hp s).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, rkT]
    push_cast
    rfl
  calc |a - ∑ s, (nS T P s : ℝ) * b s|
      = |(a - ∑ s, c s) + ∑ s, (c s - (nS T P s : ℝ) * b s)| := by
        rw [Finset.sum_sub_distrib]; ring_nf
    _ ≤ |a - ∑ s, c s| + |∑ s, (c s - (nS T P s : ℝ) * b s)| := abs_add_le _ _
    _ ≤ 5 * laG G * (rkT T P0 P A ρ : ℝ) + 5 * laG G * (rkT T P0 P A ρ : ℝ) := add_le_add hs hsum
    _ = 10 * laG G * (rkT T P0 P A ρ : ℝ) := by ring
end PI.Dv.Tr
