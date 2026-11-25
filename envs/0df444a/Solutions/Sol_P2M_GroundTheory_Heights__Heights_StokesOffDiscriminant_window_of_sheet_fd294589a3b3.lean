-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_window_of_sheet_fd294589a3b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:19:33.952794+00:00
-- url     : https://prove2.me/submissions/833d3c69-e862-47e0-8c3b-1e3e2daf9a98

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
namespace GroundTheory.Heights₂.Heights.StokesOffDiscriminant
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin D) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin D → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) :
    ∃ (V : Set (Fin D → ℂ)) (W : Set (Fin n → ℂ)), IsOpen V ∧ IsOpen W ∧ x ∈ W ∧
      DifferentiableOn ℂ s V ∧ (∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
      ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ V ∧ IsSheetAt J A x' s := by
  obtain ⟨V, hV, hxV, hsd, hsx, hsec, N, hN, hNs⟩ := hs
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  refine ⟨V, interior N ∩ (fun z => A *ᵥ z) ⁻¹' V, hV, isOpen_interior.inter (hV.preimage hAc),
    ⟨mem_interior_iff_mem_nhds.2 hN, hxV⟩, hsd, hsec, ?_⟩
  rintro x' ⟨hx'Z, hx'N, hx'V⟩
  have hx's : s (A *ᵥ x') = x' := (hNs x' ⟨hx'Z, interior_subset hx'N⟩ hx'V).symm
  exact ⟨hx'V, V, hV, hx'V, hsd, hx's, hsec, interior N, isOpen_interior.mem_nhds hx'N,
    fun x'' hx'' hAx'' => hNs x'' ⟨hx''.1, interior_subset hx''.2⟩ hAx''⟩
end GroundTheory.Heights₂.Heights.StokesOffDiscriminant
