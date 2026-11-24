-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_maDens_cons_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:34.142202+00:00
-- url     : https://prove2.me/submissions/1de25ebb-1d99-4218-87e9-b8fc99f168aa

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_hessC_congr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
private lemma maDens_congr_of_hessC_eq {D : ℕ} {F F' : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ k, hessC (F k) y = hessC (F' k) y) : maDens F y = maDens F' y := by
  unfold maDens
  simp only [h]
section Piece
variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))
end Piece
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {n : ℕ} {f g : (Fin (n + 1) → ℂ) → ℝ}
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) {y : Fin (n + 1) → ℂ} (h : f =ᶠ[𝓝 y] g) :
    maDens (Fin.cons f φ) y = maDens (Fin.cons g φ) y := by
  apply maDens_congr_of_hessC_eq
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa only [Fin.cons_zero] using st_hessC_congr h
  · simp only [Fin.cons_succ]
end ReciprocityTheory.AnForm.M
