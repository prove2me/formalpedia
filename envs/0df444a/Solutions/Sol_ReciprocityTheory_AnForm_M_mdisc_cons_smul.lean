-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.mdisc_cons_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:48.324802+00:00
-- url     : https://prove2.me/submissions/434765d7-b55a-4bc3-a7ea-0ed7c4319291

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_update_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Filter Topology
open scoped ContDiff ComplexOrder
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e : ℕ} (c : ℂ) (B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
    (F : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    mdisc (Fin.cons (c • B) F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) =
      c * mdisc (Fin.cons B F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) := by
  have := ReciprocityTheory.AnForm.A.mdisc_update_smul
    (Fin.cons B F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) 0 c B
  simpa only [Fin.update_cons_zero] using this
end ReciprocityTheory.AnForm.M
