-- Prove2me | solution 1 for QEC.Coding.BDL26CoboundaryContainment.z_selected_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:14:14.335196+00:00
-- url     : https://prove2.me/submissions/7518c269-cb18-4ec9-b386-b331b5995451

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
theorem _root_.solution (S : OddScale) (n : Nat) (β : ℝ) (A : Finset (ZImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * zSelected S n A) = ((pZ S n β A : ℝ) : ℂ) := by
  change LinearMap.trace ℂ _ (_ * CSSGibbs.selectedProjector _ _ _ (Finset.univ ×ˢ A)) = _
  rw [CSSGibbs.gibbs_rectangle_trace,CSSGibbs.sum_rowProbability,one_mul]
  rfl
end QEC.Coding.BDL26CoboundaryContainment
