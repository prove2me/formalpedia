-- Prove2me | solution 1 for PI.WeylForUWork.denom_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:29:40.827633+00:00
-- url     : https://prove2.me/submissions/f8232e94-06a2-4ea6-8c21-ad125a978ece

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaUnitary_NatWCastReal
import Theorems.Thm_PI_WeylForUWork_denom_range
import Theorems.Thm_PI_WeylForUWork_row_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForUWork
open Finset PI.UpqRep Formalism.BasicNotions
namespace PI.WeylForUWork
theorem _root_.solution (n : ℕ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ range n, ((i.factorial : ℕ) : ℝ) := by
  refine (Finset.prod_congr rfl (fun a _ => row_fin n a)).trans ?_
  exact (Fin.prod_univ_eq_prod_range (fun i : ℕ => ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ))) n).trans
    (denom_range n)
end PI.WeylForUWork
