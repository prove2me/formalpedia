-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_evalForm_ne_zero_eeeb6c3d9f4a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:07.888378+00:00
-- url     : https://prove2.me/submissions/f42c2050-cf8c-43db-aa3b-db6dd82217e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_algebraicIndependent_gen_854857cd4c30

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualArithmeticVariety
variable {K : Type} [Field K]
namespace GroundTheory.Heights₂.Heights.DualArithmeticVariety
theorem _root_.solution {m : ℕ} {φ : Fin m → K} (hφ : φ ≠ 0) : evalForm m φ ≠ 0 := by
  intro h0
  apply hφ
  funext j
  exact Fintype.linearIndependent_iff.mp (algebraicIndependent_gen m).linearIndependent φ
    (by rw [← Fintype.linearCombination_apply]; exact h0) j
end GroundTheory.Heights₂.Heights.DualArithmeticVariety
