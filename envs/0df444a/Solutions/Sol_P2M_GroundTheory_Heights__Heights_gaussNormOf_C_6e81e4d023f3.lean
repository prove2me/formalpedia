-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_gaussNormOf_C_6e81e4d023f3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:49.164012+00:00
-- url     : https://prove2.me/submissions/a1bd4f10-19e2-4376-84c6-e10879f9c2ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_gaussNormOf_6379dd47bf35
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_le_2169d258a813

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
open MvPolynomial NumberField
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*} (w : AbsoluteValue R ℝ)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (c : R) : gaussNormOf w (C c : MvPolynomial ι R) = w c := by
  classical
  apply le_antisymm
  · refine gaussNormOf_le w (w.nonneg c) fun m => ?_
    rw [coeff_C]
    split_ifs
    · exact le_rfl
    · rw [map_zero]
      exact w.nonneg c
  · simpa using le_gaussNormOf w (C c : MvPolynomial ι R) 0
end GroundTheory.Heights₂.Heights
