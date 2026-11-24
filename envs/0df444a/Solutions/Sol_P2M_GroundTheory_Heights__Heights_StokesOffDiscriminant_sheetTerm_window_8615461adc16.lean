-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_sheetTerm_window_8615461adc16
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:45.574246+00:00
-- url     : https://prove2.me/submissions/35e8ce81-eb69-4fcf-8cba-c54c12b6d1b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StStokesOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StokesOffDiscriminantWindow

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
    {H : (Fin n → ℂ) → ((Fin D → ℂ) → Fin n → ℂ) → ℝ} {y : Fin D → ℂ}
    {s : (Fin D → ℂ) → Fin n → ℂ} {V : Set (Fin D → ℂ)} {W : Set (Fin n → ℂ)}
    (hsec : ∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : ∀ x ∈ zeroSet J ∩ W, A *ᵥ x ∈ V ∧ IsSheetAt J A x s)
    (h1 : ∀ x s', A *ᵥ x = y → IsSheetAt J A x s' → IsSheetAt J A x s → H x s' = H x s)
    (h2 : ∀ x s', x ∈ zeroSet J → A *ᵥ x = y → x ∉ W → IsSheetAt J A x s' → H x s' = 0)
    (h3 : y ∈ V → s y ∉ W → H (s y) s = 0) (x : Fin n → ℂ) :
    sheetTerm J A H y x = if y ∈ V ∧ x = s y then H (s y) s else 0 := by
  unfold sheetTerm
  by_cases hx : x ∈ fibre J A y
  · rw [Set.indicator_of_mem hx]
    obtain ⟨hxZ, hxy⟩ := hx
    by_cases hxW : x ∈ W
    · obtain ⟨hAV, hsx⟩ := hW x ⟨hxZ, hxW⟩
      have hxs : s (A *ᵥ x) = x := hsx.choose_spec.2.2.2.1
      have hyV : y ∈ V := hxy ▸ hAV
      have hx' : x = s y := by rw [← hxy, hxs]
      have hex : ∃ s', IsSheetAt J A x s' := ⟨s, hsx⟩
      rw [dif_pos hex, if_pos ⟨hyV, hx'⟩, h1 x _ hxy hex.choose_spec hsx, ← hx']
    · have h0 : (if h : ∃ s', IsSheetAt J A x s' then H x h.choose else 0) = 0 := by
        split_ifs with hex
        · exact h2 x _ hxZ hxy hxW hex.choose_spec
        · rfl
      rw [h0]
      split_ifs with hc
      · obtain ⟨hyV, rfl⟩ := hc
        exact (h3 hyV hxW).symm
      · rfl
  · rw [Set.indicator_of_notMem hx]
    split_ifs with hc
    · obtain ⟨hyV, rfl⟩ := hc
      exact absurd ⟨(hsec y hyV).2, (hsec y hyV).1⟩ hx
    · rfl
end GroundTheory.Heights₂.Heights.StokesOffDiscriminant
