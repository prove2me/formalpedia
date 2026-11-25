-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_cons_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:26:52.006899+00:00
-- url     : https://prove2.me/submissions/72b73242-a27c-484e-8c75-9306e5666b90

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_mdisc_cons_eq_sum__cdfc9455009b

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
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons A B) = ∑ j, ∑ k, A j k * mixedCof B j k := by
  exact mdisc_cons_eq_sum' A B
end ReciprocityTheory.AnForm.A
