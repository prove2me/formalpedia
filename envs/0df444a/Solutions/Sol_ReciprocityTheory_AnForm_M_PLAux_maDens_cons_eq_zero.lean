-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.maDens_cons_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:34:47.001838+00:00
-- url     : https://prove2.me/submissions/7f8df9a5-e5c2-4d80-9d87-a90fa81c7cc5

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_hessC_eq_zero_of_eventuallyEq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_eq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLAux
theorem _root_.solution {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℝ}
    {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} {y : Fin (n + 1) → ℂ} (h : f =ᶠ[𝓝 y] fun _ => 0) :
    maDens (Fin.cons f φ) y = 0 := by
  have hc : (fun k => hessC ((Fin.cons f φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) y) =
      Fin.cons (hessC f y) (fun k => hessC (φ k) y) := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k <;> simp
  unfold maDens
  rw [hc, ReciprocityTheory.AnForm.A.mdisc_cons_eq_sum, hessC_eq_zero_of_eventuallyEq_zero h]
  simp
end ReciprocityTheory.AnForm.M.PLAux
