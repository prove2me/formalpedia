-- Prove2me | solution 1 for QEC.Coding.FixedCoboundaryGibbs.family_mass_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:17:17.517996+00:00
-- url     : https://prove2.me/submissions/284068ef-9b6f-4e57-b602-866c9679ffa7

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
import Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_containment_mass_le
import Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_family_mass_le_sum
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FixedCoboundaryGibbs
open Classical
open scoped BigOperators
variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
attribute [local instance] QEC.Coding.FixedCoboundaryGibbs.imageFintype
namespace QEC.Coding.FixedCoboundaryGibbs
theorem _root_.solution (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (W : Finset (LinearMap.range P)) :
    mass P t (familyEvent P W) ≤ ∑ τ∈W, Real.exp (-t*(HammingWeight τ.val : ℝ)) := by
  exact (family_mass_le_sum P t W).trans
    (Finset.sum_le_sum (fun τ _ => containment_mass_le P t τ))
end QEC.Coding.FixedCoboundaryGibbs
