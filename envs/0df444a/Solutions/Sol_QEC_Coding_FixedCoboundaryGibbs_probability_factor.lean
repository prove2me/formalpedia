-- Prove2me | solution 1 for QEC.Coding.FixedCoboundaryGibbs.probability_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:03:24.627808+00:00
-- url     : https://prove2.me/submissions/f2f54e58-6dc1-46bc-8a79-9155ad3bb417

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
import Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_weight_remove
import Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_mem_containment

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FixedCoboundaryGibbs
open Classical
open scoped BigOperators
variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
attribute [local instance] QEC.Coding.FixedCoboundaryGibbs.imageFintype
namespace QEC.Coding.FixedCoboundaryGibbs
theorem _root_.solution (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (τ s : LinearMap.range P) (hs : s∈containment P τ) :
    CSSGibbs.rowProbability P t s =
      Real.exp (-t*(HammingWeight τ.val : ℝ)) * CSSGibbs.rowProbability P t (shift P τ s) := by
  have hw := weight_remove s.val τ.val ((mem_containment P τ s).mp hs)
  unfold CSSGibbs.rowProbability
  change Real.exp (-t*(HammingWeight s.val : ℝ)) / CSSGibbs.rowPartition P t =
    Real.exp (-t*(HammingWeight τ.val : ℝ)) *
      (Real.exp (-t*(HammingWeight (s.val+τ.val) : ℝ)) / CSSGibbs.rowPartition P t)
  rw [hw, Nat.cast_add, mul_add, Real.exp_add]
  ring
end QEC.Coding.FixedCoboundaryGibbs
