-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockData_elt_div_elt_eac7066069af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:25.958841+00:00
-- url     : https://prove2.me/submissions/e4c24e70-6541-419a-8d99-dc77121b8f01

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ChartPowNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_chartPow_ne_zero_0ca6bf248649

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.AddBlockData
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.AddBlockData
theorem _root_.solution {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (i j : Fin (D.size + 1)) :
    D.elt i / D.elt j = D.xi c i * (D.xi c j)⁻¹ := by
  have hp := chartPow_ne_zero hc D.deg
  simp only [xi]
  field_simp
end GroundTheory.Heights₂.Heights.AddBlockData
