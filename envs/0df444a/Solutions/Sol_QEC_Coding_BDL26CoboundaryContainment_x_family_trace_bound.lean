-- Prove2me | solution 1 for QEC.Coding.BDL26CoboundaryContainment.x_family_trace_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:25:21.014755+00:00
-- url     : https://prove2.me/submissions/f40e66ad-f404-4265-b2b0-3361735152bf

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
import Theorems.Thm_QEC_Coding_BDL26CoboundaryContainment_x_family_le
import Theorems.Thm_QEC_Coding_BDL26CoboundaryContainment_x_family_trace

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CoboundaryContainment
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26TwoSectorBadProjector
open scoped BigOperators
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.xImageFintype
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.zImageFintype
namespace QEC.Coding.BDL26CoboundaryContainment
theorem _root_.solution (S : OddScale) (n : Nat) (β : ℝ) (W : Finset (XImage S n)) :
    (LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * xSelected S n (xFamily S n W))).re ≤
      ∑ τ∈W, Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) := by
  rw [x_family_trace,Complex.ofReal_re]
  exact x_family_le S n β W
end QEC.Coding.BDL26CoboundaryContainment
