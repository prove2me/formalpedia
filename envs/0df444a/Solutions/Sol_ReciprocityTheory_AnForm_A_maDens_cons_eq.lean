-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.maDens_cons_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:31.253801+00:00
-- url     : https://prove2.me/submissions/56ac7d9a-30d0-49da-b85a-935600bdbf23

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v : (Fin (n + 1) → ℂ) → ℝ)
    (z : Fin (n + 1) → ℂ) :
    maDens (Fin.cons v φ) z = ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
      (mdisc (Fin.cons (hessC v z) fun i => hessC (φ i) z)).re := by
  have e : (fun k => hessC ((Fin.cons v φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z) =
      Fin.cons (hessC v z) fun i => hessC (φ i) z := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  rw [maDens, e]
end ReciprocityTheory.AnForm.A
