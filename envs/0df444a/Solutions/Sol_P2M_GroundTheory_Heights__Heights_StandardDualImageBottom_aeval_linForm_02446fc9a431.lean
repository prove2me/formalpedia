-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_aeval_linForm_02446fc9a431
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:39:39.174017+00:00
-- url     : https://prove2.me/submissions/a428b6eb-5368-49f0-9ab4-f884a6c51a96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_SingleMemDualLatticeStandard
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdImageBot
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_dualLatticeCoord_eq_ca49334a53b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_dualStdCoordMat_sum_425dd1ff37fe


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
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (q : Σ _ : Unit, Fin i) :
    aeval (dualLatticeCoord b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b) q) = genPt K i q := by
  obtain ⟨⟨⟩, j⟩ := q
  have hs := congrArg (evalForm (K := K) i) (dualStdCoordMat_sum b j)
  rw [map_sum, evalForm, Fintype.linearCombination_apply_single, one_smul, ← evalForm] at hs
  rw [genPt, ← hs, linForm, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, aeval_C, aeval_X, map_zsmul, ← dualLatticeCoord_eq, zsmul_eq_mul, eq_intCast]
end GroundTheory.Heights₂.Heights.StandardDualImageBottom
