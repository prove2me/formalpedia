-- Prove2me | solution 1 for QEC.Coding.FixedCoboundaryGibbs.containment_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:12:06.886611+00:00
-- url     : https://prove2.me/submissions/8b32b61d-0147-4b64-a178-05b5246e0837

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
import Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_mass_bounds
import Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_containment_mass_exact

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FixedCoboundaryGibbs
open Classical
open scoped BigOperators
variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
attribute [local instance] QEC.Coding.FixedCoboundaryGibbs.imageFintype
namespace QEC.Coding.FixedCoboundaryGibbs
theorem _root_.solution (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (τ : LinearMap.range P) :
    mass P t (containment P τ) ≤ Real.exp (-t*(HammingWeight τ.val : ℝ)) := by
  rw [containment_mass_exact]
  exact (mul_le_mul_of_nonneg_left (mass_bounds P t (translated P τ)).2
    (Real.exp_pos _).le).trans_eq (mul_one _)
end QEC.Coding.FixedCoboundaryGibbs
