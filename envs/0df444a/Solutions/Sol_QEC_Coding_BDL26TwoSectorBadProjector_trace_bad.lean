-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.trace_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:28:13.782977+00:00
-- url     : https://prove2.me/submissions/8d679e9a-1cc9-467f-8498-6fd928c086fe

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_trace_joint

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
      ((gibbs S n β).toOperator * (1-Pjoint S n BX BZ)) =
      ((pX S n β BX+pZ S n β BZ-pX S n β BX*pZ S n β BZ : ℝ) : ℂ) := by
  rw [mul_sub, mul_one, map_sub, (gibbs S n β).trace_one, trace_joint]
  push_cast
  ring
end QEC.Coding.BDL26TwoSectorBadProjector
