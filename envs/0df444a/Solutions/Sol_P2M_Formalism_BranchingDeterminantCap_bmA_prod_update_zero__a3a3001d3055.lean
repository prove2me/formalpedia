-- Prove2me | solution 1 for P2M_Formalism_BranchingDeterminantCap_bmA_prod_update_zero__a3a3001d3055
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:30.141688+00:00
-- url     : https://prove2.me/submissions/efc60996-946d-4a2c-9798-858b7627f4d5

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_prod_update_sub
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {A : Type*} [Ring A]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {n : ℕ} (g : Fin n → A) (k : Fin n) :
    (List.ofFn (Function.update g k 0)).prod = 0 := by
  have := bmA_prod_update_sub g k 0 0
  rw [sub_self, sub_self] at this
  exact this
end Formalism.BranchingDeterminantCap
