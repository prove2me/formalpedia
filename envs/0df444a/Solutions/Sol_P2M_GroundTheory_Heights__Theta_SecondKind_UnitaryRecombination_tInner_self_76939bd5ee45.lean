-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_self_76939bd5ee45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:03:07.981838+00:00
-- url     : https://prove2.me/submissions/870f7f47-b2fc-43a5-8b02-4bc14b49e4ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hs_sq_0bd4fc15945c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Theta.SecondKind
open GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution (X : Matrix ι ι ℂ) : tInner X X = hs X ^ 2 := by
  rw [hs_sq, tInner, trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diag, mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
