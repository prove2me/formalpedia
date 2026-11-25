-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessCof_hasDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:51.344821+00:00
-- url     : https://prove2.me/submissions/b2c99276-d687-4f68-a159-0718d38e68d2

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_eq_hessMat
import Theorems.Thm_ReciprocityTheory_AnForm_A_continuous_mdisc
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessCof_eq
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_multilinearMap_eq_mdisc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix
noncomputable section
private theorem exists_continuousMultilinearMap_eq_mdisc (D : ℕ) :
    ∃ Mc : ContinuousMultilinearMap ℝ (fun _ : Fin D => Fin D → Fin D → ℂ) ℂ,
      ∀ x : Fin D → Matrix (Fin D) (Fin D) ℂ, Mc x = mdisc x := by
  obtain ⟨M, hM⟩ := exists_multilinearMap_eq_mdisc (D := D)
  let Mr : MultilinearMap ℝ (fun _ : Fin D => Fin D → Fin D → ℂ) ℂ := M.restrictScalars ℝ
  have hMr : ∀ x : Fin D → Matrix (Fin D) (Fin D) ℂ, Mr x = mdisc x := fun x => congrFun hM x
  exact ⟨⟨Mr, by
    have : (⇑Mr : (Fin D → Fin D → Fin D → ℂ) → ℂ) = fun x => mdisc x := funext hMr
    show Continuous (⇑Mr)
    rw [this]
    exact continuous_mdisc⟩, hMr⟩
end
end ReciprocityTheory.AnForm.A
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ)
    (hφ : ∀ i, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (φ i))) z) (j k : Fin (n + 1)) :
    DifferentiableAt ℝ (fun y => hessCof φ y j k) z ∧ ∀ u,
      fderiv ℝ (fun y => hessCof φ y j k) z u = ∑ i, mdisc (Function.update
        (Fin.cons (Matrix.single j k 1) fun l => hessC (φ l) z) i.succ
          (hessMat (fderiv ℝ (fderiv ℝ (fderiv ℝ (φ i))) z u))) := by
  obtain ⟨Mc, hMc⟩ := exists_continuousMultilinearMap_eq_mdisc (n + 1)
  let Lℓ : BilinSp (n + 1) →ₗ[ℝ] (Fin (n + 1) → Fin (n + 1) → ℂ) := hessMat
  let L : BilinSp (n + 1) →L[ℝ] (Fin (n + 1) → Fin (n + 1) → ℂ) := LinearMap.toContinuousLinearMap Lℓ
  let g : (Fin (n + 1) → ℂ) → (Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℂ) :=
    fun y => Fin.cons (Matrix.single j k (1 : ℂ) : Fin (n + 1) → Fin (n + 1) → ℂ)
      fun l => L (fderiv ℝ (fderiv ℝ (φ l)) y)
  let g' : (Fin (n + 1) → ℂ) →L[ℝ] (Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℂ) :=
    ContinuousLinearMap.pi fun i =>
      Fin.cases 0 (fun l => L.comp (fderiv ℝ (fderiv ℝ (fderiv ℝ (φ l))) z)) i
  have hg : HasFDerivAt g g' z := by
    refine hasFDerivAt_pi.2 fun i => ?_
    refine Fin.cases ?_ (fun l => ?_) i
    · simp only [g, g', Fin.cons_zero, Fin.cases_zero]
      exact hasFDerivAt_const _ _
    · simp only [g, g', Fin.cons_succ, Fin.cases_succ]
      exact L.hasFDerivAt.comp z (hφ l).hasFDerivAt
  have hfun : (fun y => hessCof φ y j k) = fun y => Mc (g y) := by
    funext y
    rw [hessCof_eq, ← hMc]
    rfl
  have hD : HasFDerivAt (fun y => Mc (g y)) ((Mc.linearDeriv (g z)).comp g') z :=
    (Mc.hasFDerivAt (g z)).comp z hg
  rw [hfun]
  refine ⟨hD.differentiableAt, fun u => ?_⟩
  rw [hD.fderiv, ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply,
    Fin.sum_univ_succ]
  have h0 : g' u 0 = 0 := by simp [g']
  have hz : Mc (Function.update (g z) 0 (g' u 0)) = 0 := by
    rw [h0]
    exact Mc.toMultilinearMap.map_update_zero _ _
  rw [hz, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hMc]
  congr 1
  funext r
  by_cases hr : r = i.succ
  · rw [hr, Function.update_self, Function.update_self]
    simp only [g', ContinuousLinearMap.pi_apply, Fin.cases_succ, ContinuousLinearMap.comp_apply]
    rfl
  · rw [Function.update_of_ne hr, Function.update_of_ne hr]
    refine Fin.cases ?_ (fun l => ?_) r
    · rfl
    · simp only [g, Fin.cons_succ]
      rw [hessC_eq_hessMat]
      rfl
end ReciprocityTheory.AnForm.A
