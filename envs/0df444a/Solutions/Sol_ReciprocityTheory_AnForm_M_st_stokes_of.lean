-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_stokes_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:11:44.310803+00:00
-- url     : https://prove2.me/submissions/ee1607a5-93ce-471d-ac8d-615568fcbe73

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_ofFun
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntRsmul
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_byPartsSymm_of

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
open ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
section Leibniz
variable {D : ℕ}
end Leibniz
variable {e : ℕ} {X : Type} [TopologicalSpace X]
section Piece
variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))
end Piece
private theorem mInt_cons_const_eq_zero (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (c : ℝ) (g : X → ℝ) :
    mInt A (Fin.cons (LocPot.ofFun fun _ => c) Φ) g = 0 := by
  have hL : ∀ j y, locDens A (Fin.cons (LocPot.ofFun fun _ => c) Φ) j y =
      locDens A (Fin.cons ((LocPot.ofFun fun _ => c).rsmul 0) Φ) j y := by
    intro j y
    have hf : ∀ c' : ℝ, fderiv ℝ (fderiv ℝ (fun _ : Fin (e + 1) → ℂ => c')) y = 0 := by
      intro c'
      have h0 : fderiv ℝ (fun _ : Fin (e + 1) → ℂ => c') = fun _ => 0 :=
        funext fun x => fderiv_const_apply c'
      rw [h0]
      exact fderiv_const_apply _
    have hz : ∀ c' : ℝ, hessC (fun _ : Fin (e + 1) → ℂ => c') y = 0 := by
      intro c'
      funext a b
      simp only [hessC, hf c']
      simp
    simp only [locDens, maDens]
    congr 3
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [Fin.cons_zero, LocPot.ofFun, LocPot.rsmul, zero_mul]
      rw [hz c, hz 0]
    · simp
  have h := mIntRsmul A 0 (LocPot.ofFun fun _ => c) Φ
    (isPotential_ofFun A _ fun j => contDiffOn_const) hΦ g
  rw [zero_mul] at h
  rw [← h]
  simp only [mInt, integralWith, hL]
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (hP : PartsStatement) : StokesStatement := by
  intro e X _ _ _ A w hw Φ hΦ
  have h1 : A.Smooth (fun _ : X => (1 : ℝ)) := fun j => contDiffOn_const
  rw [st_byPartsSymm_of hP A (fun _ => 1) w h1 hw Φ hΦ]
  exact mInt_cons_const_eq_zero A Φ hΦ 1 w
end ReciprocityTheory.AnForm.M
