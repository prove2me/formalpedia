-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetTerm_weight_window_dd35cc3747df
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:51.618801+00:00
-- url     : https://prove2.me/submissions/c1f9a138-c113-4fbe-b20c-e81233713bcd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StStokesOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StokesOffDiscriminantWindow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetTerm_window_8615461adc16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_sheet_congr_cfb570777011

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.StokesOffDiscriminant
variable {n D : ℕ}
open Classical
namespace GroundTheory.Heights₂.Heights.StokesOffDiscriminant
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    {s : (Fin D → ℂ) → Fin n → ℂ} {V : Set (Fin D → ℂ)} {W : Set (Fin n → ℂ)}
    (hsec : ∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : ∀ x ∈ zeroSet J ∩ W, A *ᵥ x ∈ V ∧ IsSheetAt J A x s) (f : (Fin n → ℂ) → ℝ)
    (hfW : tsupport f ⊆ W) (Ψ : Fin D → (Fin n → ℂ) → ℝ) (y : Fin D → ℂ) (x : Fin n → ℂ) :
    sheetTerm J A (fun x s' => f x * ReciprocityTheory.AnForm.maDens (fun k => Ψ k ∘ s') y) y x =
      if y ∈ V ∧ x = s y then f (s y) * ReciprocityTheory.AnForm.maDens (fun k => Ψ k ∘ s) y else 0 := by
  have hf0 : ∀ x, x ∉ W → f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hfW h)
  refine sheetTerm_window hsec hW ?_ ?_ ?_ x
  · rintro x s' rfl hs' hs
    rw [maDens_sheet_congr Ψ hs hs']
  · intro x s' _ _ hxW _
    rw [hf0 x hxW, zero_mul]
  · intro _ hyW
    rw [hf0 _ hyW, zero_mul]
end GroundTheory.Heights₂.Heights.StokesOffDiscriminant
