-- Prove2me | solution 1 for QEC.Coding.FixedCoboundaryGibbs.mass_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:11:43.142268+00:00
-- url     : https://prove2.me/submissions/f48b94dc-681b-4a9d-aa65-e3c41fcc6cd1

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
import Theorems.Thm_QEC_Coding_CSSGibbs_rowProbability_selection_bounds


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FixedCoboundaryGibbs
open Classical
open scoped BigOperators
variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
attribute [local instance] QEC.Coding.FixedCoboundaryGibbs.imageFintype
namespace QEC.Coding.FixedCoboundaryGibbs
theorem _root_.solution (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (A : Finset (LinearMap.range P)) :
    0 ≤ mass P t A ∧ mass P t A ≤ 1 :=
  CSSGibbs.rowProbability_selection_bounds P t A
end QEC.Coding.FixedCoboundaryGibbs
