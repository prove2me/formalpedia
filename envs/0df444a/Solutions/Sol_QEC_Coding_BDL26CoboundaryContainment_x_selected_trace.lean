-- Prove2me | solution 1 for QEC.Coding.BDL26CoboundaryContainment.x_selected_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:14:00.710194+00:00
-- url     : https://prove2.me/submissions/ae374a04-21f5-4155-8623-c1a6bd4a9b88

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
import Theorems.Thm_QEC_Coding_CSSGibbs_gibbs_rectangle_trace
import Theorems.Thm_QEC_Coding_CSSGibbs_sum_rowProbability


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CoboundaryContainment
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26TwoSectorBadProjector
open scoped BigOperators
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.xImageFintype
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.zImageFintype
namespace QEC.Coding.BDL26CoboundaryContainment
theorem _root_.solution (S : OddScale) (n : Nat) (β : ℝ) (A : Finset (XImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * xSelected S n A) = ((pX S n β A : ℝ) : ℂ) := by
  change LinearMap.trace ℂ _ (_ * CSSGibbs.selectedProjector _ _ _ (A ×ˢ Finset.univ)) = _
  rw [CSSGibbs.gibbs_rectangle_trace,CSSGibbs.sum_rowProbability,mul_one]
  rfl
end QEC.Coding.BDL26CoboundaryContainment
