-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_maDens_cons_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:17.031531+00:00
-- url     : https://prove2.me/submissions/23129b74-df1b-4221-8072-377ab0182f2c

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_eq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {n : ℕ} (φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ)
    (y : Fin (n + 1) → ℂ) (h : hessC (φ 0) y = 0) : maDens φ y = 0 := by
  have hm : (fun k => hessC (φ k) y) =
      (Fin.cons (hessC (φ 0) y) (fun i : Fin n => hessC (φ i.succ) y) :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
    funext k; refine Fin.cases ?_ (fun i => ?_) k <;> simp
  simp only [maDens, hm, h, ReciprocityTheory.AnForm.A.mdisc_cons_eq_sum]
  simp
end ReciprocityTheory.AnForm.M
