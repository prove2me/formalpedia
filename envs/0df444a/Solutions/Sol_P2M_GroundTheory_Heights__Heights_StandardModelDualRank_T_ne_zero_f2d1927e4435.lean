-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardModelDualRank_T_ne_zero_f2d1927e4435
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:56.225713+00:00
-- url     : https://prove2.me/submissions/e35c52c1-4e36-4bbf-a097-80618bdde0bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField DualArithmeticVariety
noncomputable section
open GroundTheory.Heights₂.Heights.StandardModelDualRank
variable {K : Type} [Field K] {i : ℕ}
variable [NumberField K]
variable {T : Type}
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights.StandardModelDualRank
theorem _root_.solution : dualStdModelT K i ≠ 0 := by
  rw [dualStdModelT]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i)))
    (dualStdModelField K i))).mpr (X_ne_zero _)
end GroundTheory.Heights₂.Heights.StandardModelDualRank
