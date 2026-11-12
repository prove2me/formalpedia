-- Prove2me | solution 1 for QEC.Coding.FixedCoboundaryGibbs.zero_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:23:57.846705+00:00
-- url     : https://prove2.me/submissions/69ab77af-b876-410d-814f-896cc72f8a96

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
import Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_containment_zero
import Theorems.Thm_QEC_Coding_CSSGibbs_sum_rowProbability


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FixedCoboundaryGibbs
open Classical
open scoped BigOperators
variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
attribute [local instance] QEC.Coding.FixedCoboundaryGibbs.imageFintype
namespace QEC.Coding.FixedCoboundaryGibbs
theorem _root_.solution (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K) (t : ℝ) :
    mass P t (containment P 0)=1 := by
  rw [containment_zero]
  exact CSSGibbs.sum_rowProbability P t
end QEC.Coding.FixedCoboundaryGibbs
