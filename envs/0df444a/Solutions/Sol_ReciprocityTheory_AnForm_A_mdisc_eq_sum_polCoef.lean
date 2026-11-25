-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_eq_sum_polCoef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:17.264489+00:00
-- url     : https://prove2.me/submissions/eb08fe1b-2785-4093-9141-907448bb8988

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_finsetSum_eq_sum_fun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mdisc A = (1 / (D.factorial : ℂ)) *
      ∑ r : Fin D → Fin D, polCoef r * (Matrix.of fun i => A (r i) i).det := by
  classical
  unfold mdisc polCoef
  congr 1
  simp_rw [det_finsetSum_eq_sum_fun, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun S _ => ?_
  split_ifs <;> ring
end ReciprocityTheory.AnForm.A
