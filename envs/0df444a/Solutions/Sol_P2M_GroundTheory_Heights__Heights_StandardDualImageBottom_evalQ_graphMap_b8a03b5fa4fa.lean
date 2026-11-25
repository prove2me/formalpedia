-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_evalQ_graphMap_b8a03b5fa4fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:24.597919+00:00
-- url     : https://prove2.me/submissions/9a7016f2-142f-4044-becb-836e0e87996b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_SingleMemDualLatticeStandard
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdImageBot
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_aeval_linForm_02446fc9a431

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.StandardDualImageBottom
open DualArithmeticVariety
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]
namespace GroundTheory.Heights₂.Heights.StandardDualImageBottom
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (f : MRing (PBlk i)) :
    evalQ b (graphMap (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))
      (rename (inrV (ι := dualBlocks T) (ι₂ := PBlk i)) f)) = aeval (genPt K i) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [graphMap, evalQ]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p q hp =>
    rw [map_mul, map_mul, map_mul, hp, map_mul, aeval_X, rename_X, ← aeval_linForm b q]
    simp [graphMap, inrV, evalQ]
end GroundTheory.Heights₂.Heights.StandardDualImageBottom
