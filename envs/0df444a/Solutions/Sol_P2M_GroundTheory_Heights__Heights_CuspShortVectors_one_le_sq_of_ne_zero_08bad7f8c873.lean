-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CuspShortVectors_one_le_sq_of_ne_zero_08bad7f8c873
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:57.655101+00:00
-- url     : https://prove2.me/submissions/c7e8f517-541b-4bff-8ecc-a55dc3f8890b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspShortVectors

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
open GroundTheory.Heights₂.Heights.CuspShortVectors
namespace GroundTheory.Heights₂.Heights.CuspShortVectors
theorem _root_.solution {m : ℤ} (hm : m ≠ 0) : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
  have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
  have h2 : (1 : ℤ) ≤ m ^ 2 := by nlinarith [sq_abs m]
  exact_mod_cast h2
end GroundTheory.Heights₂.Heights.CuspShortVectors
