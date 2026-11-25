-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockData_liftOld_mem_extIdeal_ea5e70b5cf5c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:45:06.816868+00:00
-- url     : https://prove2.me/submissions/0ba795c8-a7ed-4992-8197-675daa72f893

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExtMapLiftOldOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_liftOld_of_isWeightedHomogeneous_026a3ff1a179
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
theorem _root_.solution {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ P.ideal) :
    D.liftOld f ∈ D.extIdeal := by
  rw [extIdeal, RingHom.mem_ker]
  conv_lhs => rw [← sum_weightedHomogeneousComponent (coordDeg n) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  rw [map_sum, map_sum]
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  rw [D.extMap_liftOld_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous m f),
    (P.mkF_eq_zero_iff _).mpr (P.homogeneous f hf m), map_zero, zero_mul]
end GroundTheory.Heights₂.Heights.AddBlockData
