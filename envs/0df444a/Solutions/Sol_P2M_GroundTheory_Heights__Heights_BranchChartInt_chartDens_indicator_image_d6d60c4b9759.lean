-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BranchChartInt_chartDens_indicator_image_d6d60c4b9759
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:09.336847+00:00
-- url     : https://prove2.me/submissions/9351b093-1904-443c-959f-78677fbdbd22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchChartInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicFibreSumInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchSheetAE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchChartInt

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.BranchChartInt
open Classical
namespace GroundTheory.Heights₂.Heights.BranchChartInt
theorem _root_.solution {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {p : Fin n → ℂ} (γ : VarBranch J d p) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (y : Fin d → ℂ) :
    chartDens J A (γ.image.indicator g) φ y =
      ∑ᶠ t ∈ {t | t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius ∧ A *ᵥ γ.toFun t = y},
        (if h : ∃ s, IsSheetAt J A (γ.toFun t) s then
          g (γ.toFun t) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ γ.toFun t) else 0) := by
  set T : (Fin n → ℂ) → ℝ := fun x => if h : ∃ s, IsSheetAt J A x s then
      γ.image.indicator g x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y else 0 with hT
  have h1 : chartDens J A (γ.image.indicator g) φ y = ∑ᶠ x ∈ fibre J A y, T x := rfl
  have h2 : ∑ᶠ x ∈ fibre J A y, T x =
      ∑ᶠ x ∈ γ.toFun '' {t | t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius ∧ A *ᵥ γ.toFun t = y}, T x := by
    apply finsum_mem_inter_support_eq
    ext x
    simp only [Set.mem_inter_iff, Function.mem_support]
    constructor
    · rintro ⟨hx, hTx⟩
      have hxi : x ∈ γ.image := by
        by_contra hni
        apply hTx
        simp only [hT, Set.indicator_of_notMem hni, zero_mul, dite_eq_ite, ite_self]
      obtain ⟨t, ht, rfl⟩ := hxi
      exact ⟨⟨t, ⟨ht, hx.2⟩, rfl⟩, hTx⟩
    · rintro ⟨⟨t, ⟨ht, hty⟩, rfl⟩, hTx⟩
      exact ⟨⟨γ.mapsTo ht, hty⟩, hTx⟩
  rw [h1, h2, finsum_mem_image (γ.injOn.mono fun t ht => ht.1)]
  refine finsum_mem_congr rfl fun t ht => ?_
  have hti : γ.toFun t ∈ γ.image := ⟨t, ht.1, rfl⟩
  simp only [hT, Set.indicator_of_mem hti, ht.2]
end GroundTheory.Heights₂.Heights.BranchChartInt
