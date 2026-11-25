-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetTerm_cons_window_a573806b344c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:42.413877+00:00
-- url     : https://prove2.me/submissions/9f56206b-d462-4d26-ab53-a7b84e12b8fa

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_eq_zero_of_notMem_tsupport_2109f7bfe5df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_maDens_sheet_congr_cfb570777011
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_continuousAt_sheet_0a0c684fe6fd

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
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (D + 1)) (Fin n) ℂ} {s : (Fin (D + 1) → ℂ) → Fin n → ℂ}
    {V : Set (Fin (D + 1) → ℂ)} {W : Set (Fin n → ℂ)} (hV : IsOpen V)
    (hsd : DifferentiableOn ℂ s V) (hsec : ∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : ∀ x ∈ zeroSet J ∩ W, A *ᵥ x ∈ V ∧ IsSheetAt J A x s) (f G : (Fin n → ℂ) → ℝ)
    (hfW : tsupport f ⊆ W) (φ : Fin D → (Fin n → ℂ) → ℝ) (y : Fin (D + 1) → ℂ)
    (x : Fin n → ℂ) :
    sheetTerm J A (fun x s' => G x * ReciprocityTheory.AnForm.maDens (fun k => vecCons f φ k ∘ s') y) y x =
      if y ∈ V ∧ x = s y then G (s y) * ReciprocityTheory.AnForm.maDens (fun k => vecCons f φ k ∘ s) y
      else 0 := by
  refine sheetTerm_window hsec hW ?_ ?_ ?_ x
  · rintro x s' rfl hs' hs
    rw [maDens_sheet_congr (vecCons f φ) hs hs']
  · rintro x s' _ rfl hxW hs'
    have hx : s' (A *ᵥ x) = x := hs'.choose_spec.2.2.2.1
    rw [maDens_eq_zero_of_notMem_tsupport f φ (continuousAt_sheet hs')
      (by rw [hx]; exact fun h => hxW (hfW h)), mul_zero]
  · intro hyV hyW
    rw [maDens_eq_zero_of_notMem_tsupport f φ (hsd.continuousOn.continuousAt (hV.mem_nhds hyV))
      (fun h => hyW (hfW h)), mul_zero]
end GroundTheory.Heights₂.Heights.StokesOffDiscriminant
