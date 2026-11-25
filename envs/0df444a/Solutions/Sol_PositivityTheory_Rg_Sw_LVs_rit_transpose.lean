-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.rit_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:24:01.810913+00:00
-- url     : https://prove2.me/submissions/aa04e2f0-8722-406c-aec9-943dc8d74d03

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_rit_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_rit_contDiffOn
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_rit_law
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_snoc_rev
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_rit_snoc
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cont_on_K
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_gset_sub_dom
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_isOpen_dom
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_mul_mem_dom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (hI : InfInv) (F1 : M2 n → ℂ) (χ1 χ2 : M2 n → ℂ) (hF1 : ContDiffOn ℂ ∞ F1 (Dom n))
    (h1 : ∀ P x, InP P → x ∈ Dom n → F1 (P * x) = χ1 P * F1 x)
    (h12 : ∀ P, InP P → χ1 P * χ2 P = ((‖(P.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ))
    (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g) :
    ∀ (N : ℕ) (F2 : M2 n → ℂ), ContDiffOn ℂ ∞ F2 (Dom n) →
      (∀ P x, InP P → x ∈ Dom n → F2 (P * x) = χ2 P * F2 x) → ∀ (W : Fin N → M2 n), (∀ a b, W a * W b = 0) →
      ∫ k, rit F1 N W (ι k) * F2 (ι k) ∂μ = (-1) ^ N * ∫ k, F1 (ι k) * rit F2 N (fun i => W (Fin.rev i)) (ι k) ∂μ := by
  have hdom : ∀ k, ι k ∈ Dom n := fun k => gset_sub_dom ((hK (ι k)).2 ⟨k, rfl⟩).1
  have hint : ∀ g : Kg → ℂ, Continuous g → Integrable g μ := fun g hg => by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    exact Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall fun k => hC k trivial)
  have hUP : ∀ P x, InP P → x ∈ Dom n → P * x ∈ Dom n := fun P x hP hx => mul_mem_dom hP hx
  intro N
  induction N with
  | zero => intro F2 _ _ W _; simp [rit_zero]
  | succ N ih =>
    intro F2 hF2 h2 W hW
    set G := rit F1 N (fun i => W i.succ) with hGdef
    set F2' : M2 n → ℂ := fun y => fderiv ℂ F2 y (y * W 0) with hF2'def
    have hG : ContDiffOn ℂ ∞ G (Dom n) := rit_contDiffOn F1 _ isOpen_dom hF1 N _
    have hGlaw : ∀ P x, InP P → x ∈ Dom n → G (P * x) = χ1 P * G x :=
      rit_law F1 (Dom n) isOpen_dom hF1 χ1 hUP h1 N _
    have hF2'e : F2' = rit F2 1 (fun _ => W 0) := rfl
    have hF2' : ContDiffOn ℂ ∞ F2' (Dom n) := by rw [hF2'e]; exact rit_contDiffOn F2 _ isOpen_dom hF2 1 _
    have hF2'law : ∀ P x, InP P → x ∈ Dom n → F2' (P * x) = χ2 P * F2' x := by
      rw [hF2'e]; exact rit_law F2 (Dom n) isOpen_dom hF2 χ2 hUP h2 1 _
    have hlaw : ∀ p x, InG p → p.toBlocks₂₁ = 0 → InG x →
        G (p * x) * F2 (p * x) = ((‖(p.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) * (G x * F2 x) := by
      intro p x hp hp0 hx
      have hP : InP p := ⟨hp, hp0⟩
      rw [hGlaw p x hP (gset_sub_dom hx), h2 p x hP (gset_sub_dom hx), ← h12 p hP]
      ring
    have hInf := hI n G F2 (Dom n) isOpen_dom gset_sub_dom hG hF2 hlaw Kg μ ι hι hK (W 0)
    have hA : Continuous (fun k => rit F1 (N + 1) W (ι k) * F2 (ι k)) :=
      (cont_on_K _ (rit_contDiffOn F1 _ isOpen_dom hF1 (N + 1) W) Kg ι hι hdom).mul
        (cont_on_K _ hF2 Kg ι hι hdom)
    have hB : Continuous (fun k => G (ι k) * F2' (ι k)) :=
      (cont_on_K _ hG Kg ι hι hdom).mul (cont_on_K _ hF2' Kg ι hι hdom)
    have hsplit : (∫ k, rit F1 (N + 1) W (ι k) * F2 (ι k) ∂μ) + ∫ k, G (ι k) * F2' (ι k) ∂μ = 0 := by
      rw [← integral_add (hint _ hA) (hint _ hB)]
      exact hInf
    have hIH := ih F2' hF2' hF2'law (fun i => W i.succ) (fun a b => hW _ _)
    have hr : rit F2' N (fun i => W (Fin.rev i).succ) = rit F2 (N + 1) (fun i => W (Fin.rev i)) := by
      rw [hF2'def, rit_snoc F2 (W 0) N, snoc_rev]
    rw [hr] at hIH
    rw [pow_succ]
    linear_combination hsplit - hIH
end PositivityTheory.Rg.Sw.LVs
