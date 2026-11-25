-- Prove2me | solution 1 for PI.GTNum.abs_cBr_le_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:47:44.312139+00:00
-- url     : https://prove2.me/submissions/c208c2d0-b54b-489a-81d7-f4f43aabefbf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_NumMore
import Theorems.Thm_PI_GTNum_sg_le_top
import Theorems.Thm_PI_GTNum_mem_R_bounds_top
import Theorems.Thm_PI_GTNum_abs_prod_le_pow
import Theorems.Thm_PI_GTNum_abs_prod_le_prod
import Theorems.Thm_PI_GTNum_last_le_sg
import Theorems.Thm_PI_GTNum_prod_pow_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GTNum
open Formalism.BasicNotions PI Finset
variable {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
namespace PI.GTNum
theorem _root_.solution (hI : Interlace h lam sg) :
    |cBr h lam sg| ≤ (lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + (n : ℤ)) ^
      (n * ∑ i : Fin n, ((Rset h lam sg i).erase (sg.w i)).card) := by
  unfold cBr
  rw [← prod_pow_pow]
  refine abs_prod_le_prod _ _ _ (fun i _ => ?_)
  refine abs_prod_le_pow _ _ _ (fun v hv => ?_)
  have hc : ((lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + (n : ℤ)) ^ n) =
      (lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + (n : ℤ)) ^ (univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hc]
  refine abs_prod_le_pow _ _ _ (fun j _ => ?_)
  have hv' := mem_R_bounds_top h lam sg i v (Finset.mem_of_mem_erase hv)
  have hs1 := last_le_sg h lam sg hI j
  have hs2 := sg_le_top h lam sg hI j
  have hi := i.2
  have hj := j.2
  rw [abs_le]
  constructor <;> omega
end PI.GTNum
