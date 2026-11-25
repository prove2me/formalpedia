-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_hermValue_single_36ddafe20269
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:50.358807+00:00
-- url     : https://prove2.me/submissions/9da97cf3-18b9-4690-8c5c-da81e3bb5beb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspLeadingMinima
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCSchur_hermValue_eq_qf_16537984ce33


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
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (k : ι) :
    hermValue A (Pi.single k (1 : ℂ)) = A k k := by
  rw [MCSchur.hermValue_eq_qf]
  have hre : (fun l => ((Pi.single k (1 : ℂ) : ι → ℂ) l).re) = Pi.single k (1 : ℝ) := by
    ext l
    by_cases e : l = k
    · subst e; simp
    · simp [e]
  have him : (fun l => ((Pi.single k (1 : ℂ) : ι → ℂ) l).im) = 0 := by
    ext l
    by_cases e : l = k
    · subst e; simp
    · simp [e]
  rw [hre, him]
  simp [MCSchur.qf, mulVec_single]
end GroundTheory.Heights₂.Heights.CuspLeadingMinima
