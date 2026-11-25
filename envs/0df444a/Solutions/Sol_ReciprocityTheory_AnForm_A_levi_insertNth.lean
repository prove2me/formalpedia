-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.levi_insertNth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:12:21.654581+00:00
-- url     : https://prove2.me/submissions/0583394c-3e45-426b-b432-2865858de45f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Theorems.Thm_ReciprocityTheory_AnForm_A_insertNth_eq_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Laplacian Pointwise
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (j : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ)
    (hu : ContDiff ℝ 2 u) (w : Fin D → ℂ) (ζ : ℂ) :
    ReciprocityTheory.AnForm.levi u (Fin.insertNth j ζ w) (Pi.single j 1) =
      Δ (fun ζ' => u (Fin.insertNth j ζ' w)) ζ / 4 := by
  set A : ℂ →L[ℝ] (Fin (D + 1) → ℂ) := ContinuousLinearMap.single ℝ (fun _ : Fin (D + 1) => ℂ) j with hA
  set c : Fin (D + 1) → ℂ := Fin.insertNth j (0 : ℂ) w with hc
  have hAv : ∀ a : ℂ, A a = Pi.single j a := fun a => rfl
  have hf : (fun ζ' : ℂ => u (Fin.insertNth j ζ' w)) = (fun z => u (z + c)) ∘ A := by
    funext ζ'
    show u (Fin.insertNth j ζ' w) = u (A ζ' + c)
    rw [hAv, add_comm (Pi.single j ζ') c]
    exact congrArg u (insertNth_eq_add j w ζ')
  have huc : ContDiff ℝ 2 (fun z => u (z + c)) := hu.comp (contDiff_id.add contDiff_const)
  have hz : A ζ + c = Fin.insertNth j ζ w := by
    rw [hAv, add_comm (Pi.single j ζ) c]
    exact (insertNth_eq_add j w ζ).symm
  have h2 : ∀ a : ℂ, iteratedFDeriv ℝ 2 (fun ζ' : ℂ => u (Fin.insertNth j ζ' w)) ζ ![a, a] =
      fderiv ℝ (fderiv ℝ u) (Fin.insertNth j ζ w) (A a) (A a) := by
    intro a
    rw [hf, ContinuousLinearMap.iteratedFDeriv_comp_right A huc ζ (by norm_num),
      ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_right,
      iteratedFDeriv_two_apply, hz]
    simp
  have hΔ := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane
    (fun ζ' : ℂ => u (Fin.insertNth j ζ' w))) ζ
  rw [hΔ, h2, h2]
  have hAI : A Complex.I = Complex.I • (Pi.single j 1 : Fin (D + 1) → ℂ) := by
    rw [hAv]
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  rw [hAI, hAv]
  rfl
end ReciprocityTheory.AnForm.A
