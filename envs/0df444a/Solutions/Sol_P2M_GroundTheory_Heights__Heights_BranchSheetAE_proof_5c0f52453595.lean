-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BranchSheetAE_proof_5c0f52453595
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:59:53.735937+00:00
-- url     : https://prove2.me/submissions/e9e53f8f-aa0e-40b4-9150-6fe0131eb813

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchSheetAE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRankDeficientFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscriminantSheetCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchSheetAE
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BranchSheetAE_volume_preimage_null_9a44d12a3b9a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_analyticOnNhd_det_jacC_ddf5e32b96d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_differentiableOn_mulVec_9d66d20ccb40
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_injective_iff_det_ne_zero_4dda9d931b27
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_jacC
import Theorems.Thm_ReciprocityTheory_AnForm_volume_zero_set_of_analyticOnNhd


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
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace BranchSheetAE
theorem _root_.solution (h₁ : IndefiniteRowSideFullHecke.ComplexSets.RankDeficientFibreInfinite.Statement)
    (h₂ : ComplexSets.FibreBound.Statement) (h₃ : DiscriminantSheetCover.Statement) :
    BranchSheetAE.Statement := by
  intro n d J A p γ hJ hdim hA
  set Δ := Metric.ball (0 : Fin d → ℂ) γ.radius with hΔ
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτdef
  have hΔo : IsOpen Δ := Metric.isOpen_ball
  have hτd : DifferentiableOn ℂ τ Δ := SheetOnlyNull.differentiableOn_mulVec A γ.differentiableOn
  have hdeta := SheetOnlyNull.analyticOnNhd_det_jacC hΔo hτd
  have hne : ∃ z ∈ Δ, (ReciprocityTheory.AnForm.A.jacC τ z).det ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨y, hy⟩ := h₁ d d Δ τ hΔo ⟨0, Metric.mem_ball_self γ.radius_pos⟩ hτd fun v hv hinj =>
      (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
        (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall v hv)
    have hinf : (γ.toFun '' {t | t ∈ Δ ∧ τ t = y}).Infinite :=
      (Set.infinite_image_iff (γ.injOn.mono fun t ht => ht.1)).2 hy
    refine hinf ((h₂ n d J A hJ hdim hA y).2.1.subset ?_)
    rintro _ ⟨t, ⟨htΔ, hty⟩, rfl⟩
    exact ⟨γ.mapsTo htΔ, hty⟩
  have hZ := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd hΔo (convex_ball _ _).isPreconnected
    hdeta hne
  obtain ⟨P, U, D, N, s, -, hUD, -, -, hnull, hfib⟩ := h₃ n d J A hJ hdim hA
  set G := Δ ∩ (fun t => (ReciprocityTheory.AnForm.A.jacC τ t).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G := hdeta.continuousOn.isOpen_inter_preimage hΔo isOpen_compl_singleton
  have hS := BranchSheetAE.volume_preimage_null hG (hτd.mono Set.inter_subset_left)
    (fun w hw => hw.2) hnull
  rw [ae_restrict_iff' hΔo.measurableSet, ae_iff]
  refine measure_mono_null ?_ (measure_union_null hZ hS)
  intro t ht
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at ht
  obtain ⟨htΔ, hno⟩ := ht
  by_cases hdt : (ReciprocityTheory.AnForm.A.jacC τ t).det = 0
  · exact Or.inl ⟨htΔ, hdt⟩
  refine Or.inr ⟨⟨htΔ, hdt⟩, fun hD => hno ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hD
  obtain ⟨hfibk, -, hsh⟩ := hfib k (τ t) ((hUD k).2.2.1 hk)
  have hmem : γ.toFun t ∈ fibre J A (τ t) := ⟨γ.mapsTo htΔ, rfl⟩
  rw [hfibk] at hmem
  obtain ⟨j, hj⟩ := hmem
  exact ⟨s k j, hj ▸ hsh j⟩
end BranchSheetAE
end GroundTheory.Heights₂.Heights
