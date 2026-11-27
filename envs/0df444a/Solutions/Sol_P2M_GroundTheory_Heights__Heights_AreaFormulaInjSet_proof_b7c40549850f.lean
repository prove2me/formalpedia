-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaFormulaInjSet_proof_b7c40549850f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:57:22.740778+00:00
-- url     : https://prove2.me/submissions/c18306a1-548d-46c5-811d-27060e95d28c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaInjSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjectionFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetImageAreaSetFrame
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaFormulaInjSet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hausdorffMeasure_image_eq_zero_of_not_injective_0e64433aadc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_eq_normDet_42419aa0db84


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
open MeasureTheory Module Set
open scoped ENNReal
namespace GroundTheory.Heights₂.Heights
namespace AreaFormulaInjSet
theorem _root_.solution (h : AreaFormulaLocal.Statement) : AreaFormulaInjSet.Statement := by
  classical
  intro E F _ _ _ _ _ _ _ _ _ _ k hk U A f hU hf hAU hA hinj
  set J : E → ℝ≥0∞ := fun x => ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) with hJdef
  change μH[(k : ℝ)] (f '' A) = ∫⁻ x in A, J x ∂(μH[(k : ℝ)])
  have hdiff : ∀ x ∈ U, HasFDerivAt f (fderiv ℝ f x) x := fun x hx =>
    ((hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)).hasFDerivAt

  set C : Set E := A ∩ fderiv ℝ f ⁻¹' {L : E →L[ℝ] F | Function.Injective L}ᶜ with hCdef
  have hCm : MeasurableSet C :=
    hA.inter (measurable_fderiv ℝ f ContinuousLinearMap.isOpen_injective.measurableSet.compl)
  have hJC : EqOn J (fun _ => 0) C := by
    intro x hx
    have hni : ¬ Function.Injective (fderiv ℝ f x : E →ₗ[ℝ] F) := hx.2
    have h0 : (fderiv ℝ f x : E →ₗ[ℝ] F).normDet = 0 :=
      LinearMap.normDet_eq_zero_iff_ker_ne_bot.2 fun hk0 => hni (LinearMap.ker_eq_bot.1 hk0)
    simp [hJdef, SheetImageAreaSet.areaJacobian_eq_normDet, h0]
  have hCnull : μH[(k : ℝ)] (f '' C) = 0 := by
    let e : (Fin k → ℝ) ≃L[ℝ] E := (finBasisOfFinrankEq ℝ E hk).equivFun.symm.toContinuousLinearEquiv
    have himg : f '' C = (f ∘ e) '' (e ⁻¹' C) := by
      rw [image_comp, image_preimage_eq _ e.surjective]
    have key := IndefiniteRowSideFullHecke.ComplexSets.hausdorffMeasure_image_eq_zero_of_not_injective (f := f ∘ e)
      (s := e ⁻¹' C) (f' := fun x => (fderiv ℝ f (e x)).comp (e : (Fin k → ℝ) →L[ℝ] E)) ?_ ?_
    · rw [himg]
      simpa using key
    · intro x hx
      exact ((hdiff (e x) (hAU hx.1)).comp x e.hasFDerivAt).hasFDerivWithinAt
    · intro x hx hinj'
      apply hx.2
      intro a c hac
      have h2 := @hinj' (e.symm a) (e.symm c) (by simpa using hac)
      simpa using congrArg e h2

  set R : Set E := A \ C with hRdef
  have hRm : MeasurableSet R := hA.diff hCm
  set G : Set (Set E) := {V | IsOpen V ∧ V ⊆ U ∧ ∀ B ⊆ V, MeasurableSet B →
    μH[(k : ℝ)] (f '' B) = ∫⁻ x in B, J x ∂(μH[(k : ℝ)])} with hGdef
  have hRG : R ⊆ ⋃₀ G := by
    intro x hx
    have hxinj : Function.Injective (fderiv ℝ f x) := by
      by_contra hn
      exact hx.2 ⟨hx.1, hn⟩
    obtain ⟨V, hVo, hxV, hVU, hV⟩ := h E F k hk U f x hU hf (hAU hx.1) hxinj
    exact ⟨V, ⟨hVo, hVU, hV⟩, hxV⟩
  obtain ⟨T, hTc, hTG, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable G fun V hV => hV.1
  have hG0 : (∅ : Set E) ∈ G := ⟨isOpen_empty, empty_subset _, fun B hB _ => by
    rw [subset_empty_iff.1 hB]
    simp⟩
  obtain ⟨V, hVeq⟩ := (hTc.insert ∅).exists_eq_range (insert_nonempty _ _)
  have hVG : ∀ n, V n ∈ G := by
    intro n
    have hn : V n ∈ insert ∅ T := by
      rw [hVeq]
      exact mem_range_self n
    rcases hn with h0 | hT
    · rw [h0]
      exact hG0
    · exact hTG hT
  have hRV : R ⊆ ⋃ n, V n := by
    intro x hx
    have hx' : x ∈ ⋃₀ T := by
      rw [hTU]
      exact hRG hx
    obtain ⟨W, hWT, hxW⟩ := hx'
    have hW : W ∈ range V := by
      rw [← hVeq]
      exact mem_insert_of_mem _ hWT
    obtain ⟨n, rfl⟩ := hW
    exact mem_iUnion.2 ⟨n, hxW⟩

  set B : ℕ → Set E := fun n => R ∩ disjointed V n with hBdef
  have hBm : ∀ n, MeasurableSet (B n) := fun n =>
    hRm.inter (MeasurableSet.disjointed (fun m => (hVG m).1.measurableSet) n)
  have hBd : Pairwise (Function.onFun Disjoint B) := fun m n hmn =>
    ((disjoint_disjointed V) hmn).mono inter_subset_right inter_subset_right
  have hBU : ⋃ n, B n = R := by
    rw [← inter_iUnion, iUnion_disjointed]
    exact inter_eq_left.2 hRV
  have hBV : ∀ n, B n ⊆ V n := fun n => inter_subset_right.trans (disjointed_subset V n)
  have hBA : ∀ n, B n ⊆ A := fun n => inter_subset_left.trans sdiff_subset
  have hR : μH[(k : ℝ)] (f '' R) = ∫⁻ x in R, J x ∂(μH[(k : ℝ)]) := by
    rw [← hBU, image_iUnion, measure_iUnion, lintegral_iUnion hBm hBd]
    · exact tsum_congr fun n => (hVG n).2.2 (B n) (hBV n) (hBm n)
    · intro m n hmn
      refine disjoint_left.2 ?_
      rintro _ ⟨a, ha, rfl⟩ ⟨c, hc, hca⟩
      obtain rfl := hinj (hBA n hc) (hBA m ha) hca
      exact disjoint_left.1 (hBd hmn) ha hc
    · intro n
      exact (hBm n).image_of_continuousOn_injOn
        (hf.continuousOn.mono ((hBV n).trans (hVG n).2.1)) (hinj.mono (hBA n))

  have hAC : A = R ∪ C := (sdiff_union_of_subset inter_subset_left).symm
  have himgA : μH[(k : ℝ)] (f '' A) = μH[(k : ℝ)] (f '' R) := by
    apply le_antisymm
    · calc μH[(k : ℝ)] (f '' A) = μH[(k : ℝ)] (f '' R ∪ f '' C) := by
            rw [← image_union, ← hAC]
        _ ≤ μH[(k : ℝ)] (f '' R) + μH[(k : ℝ)] (f '' C) := measure_union_le _ _
        _ = μH[(k : ℝ)] (f '' R) := by rw [hCnull, add_zero]
    · exact measure_mono (image_mono sdiff_subset)
  have hintA : ∫⁻ x in A, J x ∂(μH[(k : ℝ)]) = ∫⁻ x in R, J x ∂(μH[(k : ℝ)]) := by
    calc ∫⁻ x in A, J x ∂(μH[(k : ℝ)]) = ∫⁻ x in R ∪ C, J x ∂(μH[(k : ℝ)]) := by rw [← hAC]
      _ = ∫⁻ x in R, J x ∂(μH[(k : ℝ)]) + ∫⁻ x in C, J x ∂(μH[(k : ℝ)]) :=
          lintegral_union hCm disjoint_sdiff_left
      _ = ∫⁻ x in R, J x ∂(μH[(k : ℝ)]) := by
          rw [setLIntegral_congr_fun hCm hJC, lintegral_zero, add_zero]
  rw [himgA, hR, hintA]
end AreaFormulaInjSet
end GroundTheory.Heights₂.Heights
