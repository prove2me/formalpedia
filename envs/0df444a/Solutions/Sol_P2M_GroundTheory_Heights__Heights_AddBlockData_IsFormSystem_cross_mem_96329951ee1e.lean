-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockData_IsFormSystem_cross_mem_96329951ee1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:01:03.615825+00:00
-- url     : https://prove2.me/submissions/c4eade7b-42a5-4c1b-93b0-378af810e635

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExtMapLiftOldOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_chartMonomial_mem_of_not_isLive_a21aa707419f
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.AddBlockData
variable {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.AddBlockData
namespace IsFormSystem
theorem _root_.solution {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) (c c' : (k : ι) → Fin (n k + 1)) (j : Fin (D.size + 1)) :
    chartMonomial c' d * g c j - chartMonomial c d * g c' j ∈ P.ideal := by
  by_cases hc : P.IsLive c
  · by_cases hc' : P.IsLive c'
    · rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc j, hg.value c' hc' j]
      ring
    · rw [hg.dead c' hc' j, mul_zero, sub_zero]
      exact P.ideal.mul_mem_right _ (chartMonomial_mem_of_not_isLive hc' hg.pos)
  · rw [hg.dead c hc j, mul_zero, zero_sub]
    exact P.ideal.neg_mem_iff.mpr (P.ideal.mul_mem_right _ (chartMonomial_mem_of_not_isLive hc hg.pos))
end IsFormSystem
end GroundTheory.Heights₂.Heights.AddBlockData
