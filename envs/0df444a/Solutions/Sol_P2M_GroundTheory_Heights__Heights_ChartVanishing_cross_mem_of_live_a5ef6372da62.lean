-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartVanishing_cross_mem_of_live_a5ef6372da62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:52:00.58373+00:00
-- url     : https://prove2.me/submissions/597bb0bf-d171-4989-9aab-8be2368ae927

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroTer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


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
open GroundTheory.Heights₂.Heights.ChartVanishing
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.ChartVanishing
theorem _root_.solution {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {c c' : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (hc' : P.IsLive c')
    (j : Fin (D.size + 1)) :
    chartMonomial c' d * g c j - chartMonomial c d * g c' j ∈ P.ideal := by
  rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc, hg.value c' hc']
  ring
end GroundTheory.Heights₂.Heights.ChartVanishing
