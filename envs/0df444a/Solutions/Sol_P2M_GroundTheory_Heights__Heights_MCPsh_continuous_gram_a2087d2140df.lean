-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_continuous_gram_a2087d2140df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:19:56.822025+00:00
-- url     : https://prove2.me/submissions/7232080a-f6a6-48ba-a533-c7be96b08acd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLogDetGramContinuous

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
open Matrix Metric MCPsh
open scoped MatrixOrder ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.MCPsh
namespace GroundTheory.Heights₂.Heights.MCPsh
theorem _root_.solution (g rk : ℕ) :
    Continuous (fun p : Matrix (Fin g) (Fin rk) ℂ × Matrix (Fin g) (Fin g) ℝ =>
      p.1ᴴ * p.2.map (fun x : ℝ => (x : ℂ)) * p.1) := by
  have h1 : Continuous (fun p : Matrix (Fin g) (Fin rk) ℂ × Matrix (Fin g) (Fin g) ℝ => p.1) :=
    continuous_fst
  have h2 : Continuous (fun p : Matrix (Fin g) (Fin rk) ℂ × Matrix (Fin g) (Fin g) ℝ =>
      p.2.map (fun x : ℝ => (x : ℂ))) := continuous_snd.matrix_map Complex.continuous_ofReal
  exact (h1.matrix_conjTranspose.matrix_mul h2).matrix_mul h1
end GroundTheory.Heights₂.Heights.MCPsh
