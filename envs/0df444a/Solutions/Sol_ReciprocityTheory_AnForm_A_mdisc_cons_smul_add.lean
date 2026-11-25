-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_cons_smul_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:34.268954+00:00
-- url     : https://prove2.me/submissions/7bafd635-d932-4430-afdb-3373948f6117

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_eq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Filter Topology
open scoped ComplexOrder
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (c c' : ℂ) (A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons (c • A + c' • A') B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      c * mdisc (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
        c' * mdisc (Fin.cons A' B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  rw [mdisc_cons_eq_sum, mdisc_cons_eq_sum, mdisc_cons_eq_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring
end ReciprocityTheory.AnForm.A
