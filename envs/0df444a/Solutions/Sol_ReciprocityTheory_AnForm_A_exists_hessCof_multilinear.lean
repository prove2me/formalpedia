-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.exists_hessCof_multilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:47.70229+00:00
-- url     : https://prove2.me/submissions/b1325154-6cea-4d6a-8fd0-0ba98f08356e

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
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
theorem _root_.solution (n : ℕ) (j k : Fin (n + 1)) :
    ∃ G : ContinuousMultilinearMap ℝ (fun _ : Fin n => BilinSp (n + 1)) ℂ,
      ∀ (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ),
        hessCof φ y j k = G (fun i => fderiv ℝ (fderiv ℝ (φ i)) y) := by
  obtain ⟨Mc, hMc⟩ := exists_continuousMultilinearMap_eq_mdisc (n + 1)
  let Lℓ : BilinSp (n + 1) →ₗ[ℝ] (Fin (n + 1) → Fin (n + 1) → ℂ) := hessMat
  let L : BilinSp (n + 1) →L[ℝ] (Fin (n + 1) → Fin (n + 1) → ℂ) := LinearMap.toContinuousLinearMap Lℓ
  refine ⟨(Mc.curryLeft (Matrix.single j k (1 : ℂ) : Fin (n + 1) → Fin (n + 1) → ℂ)).compContinuousLinearMap
    fun _ => L, fun φ y => ?_⟩
  rw [hessCof_eq, ← hMc]
  rfl
end ReciprocityTheory.AnForm.A
