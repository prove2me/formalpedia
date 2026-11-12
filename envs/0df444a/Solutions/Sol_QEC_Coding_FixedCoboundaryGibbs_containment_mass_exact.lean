-- Prove2me | solution 1 for QEC.Coding.FixedCoboundaryGibbs.containment_mass_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:08:08.953869+00:00
-- url     : https://prove2.me/submissions/6d20c7a1-31bb-4034-9a68-7ee2e447153d

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
import Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_probability_factor

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
    mass P t (containment P τ) =
      Real.exp (-t*(HammingWeight τ.val : ℝ)) * mass P t (translated P τ) := by
  unfold mass translated
  rw [Finset.sum_map, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact probability_factor P t τ s hs
end QEC.Coding.FixedCoboundaryGibbs
