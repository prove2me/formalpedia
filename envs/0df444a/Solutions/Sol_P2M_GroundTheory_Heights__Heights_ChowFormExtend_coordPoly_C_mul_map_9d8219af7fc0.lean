-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_C_mul_map_9d8219af7fc0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:15.443986+00:00
-- url     : https://prove2.me/submissions/b0184789-8d5a-4a75-833a-71b04d44f595

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coeff_coordPoly_539797cde10d

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
namespace GroundTheory.Heights₂.Heights.ChowFormExtend
theorem _root_.solution (φ : L →ₗ[K] K) (a : L) (q : MvPolynomial Y K) :
    coordPoly φ (C a * map (algebraMap K L) q) = C (φ a) * q := by
  ext m
  rw [coeff_coordPoly, coeff_C_mul, coeff_C_mul, coeff_map, mul_comm, ← Algebra.smul_def, map_smul,
    smul_eq_mul, mul_comm]
end GroundTheory.Heights₂.Heights.ChowFormExtend
