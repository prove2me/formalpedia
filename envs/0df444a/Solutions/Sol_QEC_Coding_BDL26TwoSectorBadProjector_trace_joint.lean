-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.trace_joint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:22:38.263437+00:00
-- url     : https://prove2.me/submissions/54348478-c388-4721-a4f6-9533dae7f166

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Theorems.Thm_QEC_Coding_CSSGibbs_gibbs_rectangle_trace
import Theorems.Thm_QEC_Coding_CSSGibbs_rowProbability_compl


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TwoSectorBadProjector
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_24
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_25
namespace QEC.Coding.BDL26TwoSectorBadProjector
theorem _root_.solution (β : ℝ) (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * Pjoint S n BX BZ) =
      (((1-pX S n β BX)*(1-pZ S n β BZ) : ℝ) : ℂ) := by
  change LinearMap.trace ℂ _ (_ * CSSGibbs.selectedProjector _ _ _ (BXᶜ ×ˢ BZᶜ)) = _
  rw [CSSGibbs.gibbs_rectangle_trace, CSSGibbs.rowProbability_compl, CSSGibbs.rowProbability_compl]
  rfl
end QEC.Coding.BDL26TwoSectorBadProjector
