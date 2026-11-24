-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_sum_8ff9631ad41f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:45.532927+00:00
-- url     : https://prove2.me/submissions/9c806d65-9891-4706-bbfc-3cf73f6b4843

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_C_mul_map_9d8219af7fc0

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
open GroundTheory.Heights₂.Heights.ChowFormExtend
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Y : Type*}
variable {β : Type*} [DecidableEq β]
namespace GroundTheory.Heights₂.Heights.ChowFormExtend
theorem _root_.solution (b : Module.Basis β K L) (S : Finset β) (h : β → MvPolynomial Y K) (c : β) :
    coordPoly (b.coord c) (∑ c' ∈ S, C (b c') * map (algebraMap K L) (h c')) =
      if c ∈ S then h c else 0 := by
  rw [map_sum]
  simp_rw [coordPoly_C_mul_map, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp [apply_ite C, ite_mul]
end GroundTheory.Heights₂.Heights.ChowFormExtend
