-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_single_mem_leadingLattice_83159460311d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:53.457874+00:00
-- url     : https://prove2.me/submissions/c2415eb7-6a56-4247-a935-c6211d07783d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspLeadingMinima

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.CuspLeadingMinima
namespace GroundTheory.Heights₂.Heights.CuspLeadingMinima
theorem _root_.solution {g r : ℕ} (h : r ≤ g) (j : Fin r) :
    Pi.single (Fin.castLE h j) (1 : ℂ) ∈ leadingLattice g r := by
  refine ⟨Pi.single (Fin.castLE h j) 1, fun k hk => ?_, ?_⟩
  · have hne : k ≠ Fin.castLE h j := by
      intro e
      have := j.isLt
      rw [e] at hk
      simp at hk
      omega
    simp [hne]
  · ext k
    by_cases e : k = Fin.castLE h j
    · subst e; simp [intVecC]
    · simp [intVecC, e]
end GroundTheory.Heights₂.Heights.CuspLeadingMinima
