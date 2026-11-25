-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_update_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:44.008503+00:00
-- url     : https://prove2.me/submissions/00ae405e-0ac2-46f6-97ec-d3c7d58d2ae2

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_multilinearMap_eq_mdisc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (q : Fin D)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    mdisc (Function.update A q X) =
      ∑ a, ∑ b, X a b * mdisc (Function.update A q (Matrix.single a b 1)) := by
  obtain ⟨M, hM⟩ := exists_multilinearMap_eq_mdisc (D := D)
  have hX : X = ∑ a, ∑ b, X a b • Matrix.single a b (1 : ℂ) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_eq_single i (fun c _ hc => by simp [hc]) (by simp),
      Finset.sum_eq_single j (fun c _ hc => by simp [hc]) (by simp)]
    simp
  have h : ∀ Y, mdisc (Function.update A q Y) = M.toLinearMap A q Y := fun Y => by
    rw [MultilinearMap.toLinearMap_apply, hM]
  rw [h]
  conv_lhs => rw [hX]
  simp only [map_sum, map_smul, smul_eq_mul]
  simp only [← h]
end ReciprocityTheory.AnForm.A
