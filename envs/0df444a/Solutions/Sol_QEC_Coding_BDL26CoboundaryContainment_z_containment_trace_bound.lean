-- Prove2me | solution 1 for QEC.Coding.BDL26CoboundaryContainment.z_containment_trace_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:25:05.702718+00:00
-- url     : https://prove2.me/submissions/f89623d9-3a88-4f1e-bead-dec1e6db5b2e

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
import Theorems.Thm_QEC_Coding_BDL26CoboundaryContainment_z_mass_le
import Theorems.Thm_QEC_Coding_BDL26CoboundaryContainment_z_containment_trace

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CoboundaryContainment
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26TwoSectorBadProjector
open scoped BigOperators
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.xImageFintype
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.zImageFintype
namespace QEC.Coding.BDL26CoboundaryContainment
theorem _root_.solution (S : OddScale) (n : Nat) (β : ℝ) (τ : ZImage S n) :
    (LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * zSelected S n (zContainment S n τ))).re ≤
      Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) := by
  rw [z_containment_trace,Complex.ofReal_re]
  exact z_mass_le S n β τ
end QEC.Coding.BDL26CoboundaryContainment
