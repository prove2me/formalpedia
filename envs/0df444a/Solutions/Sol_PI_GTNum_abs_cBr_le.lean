-- Prove2me | solution 1 for PI.GTNum.abs_cBr_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:14:06.325069+00:00
-- url     : https://prove2.me/submissions/36781ae6-3bd5-4145-a5e6-1cef8d46d082

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTCoefTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_GTCoefTopMain
import Theorems.Thm_PI_GTNum_abs_factor_le
import Theorems.Thm_PI_GTNum_abs_prod_le_pow
import Theorems.Thm_PI_GTNum_abs_prod_le_prod
import Theorems.Thm_PI_GTNum_last_le_sg
import Theorems.Thm_PI_GTNum_mem_R_bounds
import Theorems.Thm_PI_GTNum_prod_pow_pow
import Theorems.Thm_PI_GTNum_sg_le_first


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
namespace PI.GTNum
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (hn : 0 < n) (lam : DomWeight N) (sg : DomWeight n)
    (hI : Interlace h lam sg) :
    |cBr h lam sg| ≤ (2 * (sg.w ⟨0, hn⟩ - lam.w ⟨N - 1, by omega⟩) + (N : ℤ)) ^
      (n * ∑ i : Fin n, ((Rset h lam sg i).erase (sg.w i)).card) := by
  set B : ℤ := 2 * (sg.w ⟨0, hn⟩ - lam.w ⟨N - 1, by omega⟩) + (N : ℤ) with hB
  unfold cBr
  rw [← prod_pow_pow]
  refine abs_prod_le_prod _ _ _ (fun i _ => ?_)
  refine abs_prod_le_pow _ _ _ (fun v hv => ?_)
  have hc : (B ^ n) = B ^ (univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hc]
  refine abs_prod_le_pow _ _ _ (fun j _ => ?_)
  have hv' := mem_R_bounds h lam sg hI hn i v (Finset.mem_of_mem_erase hv)
  have hs1 := last_le_sg h lam sg hI j
  have hs2 := sg_le_first sg hn j
  have := abs_factor_le v (sg.w j) (lam.w ⟨N - 1, by omega⟩) (sg.w ⟨0, hn⟩) i.1 j.1 n i.2 j.2
    hv'.1 hv'.2 hs1 hs2
  have hN : ((n + 1 : ℕ) : ℤ) = (N : ℤ) := by rw [h]
  rw [hN] at this
  rw [hB]
  exact this
end PI.GTNum
