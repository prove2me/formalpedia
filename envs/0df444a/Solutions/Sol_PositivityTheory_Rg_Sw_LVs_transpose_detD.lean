-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.transpose_detD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:24:20.772811+00:00
-- url     : https://prove2.me/submissions/c1007754-b860-42a6-b163-114695ce6a14

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IntegrableIteratedFDerivTranslate
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_detD_detD_comp
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_fin_append_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_gset_sub_dom
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_integrable_of_continuous_K
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_isOpen_dom
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_transpose


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (hI : InfInv) (F1 F2 : M2 n → ℂ) (χ1 χ2 : M2 n → ℂ) (hF1 : ContDiffOn ℂ ∞ F1 (Dom n))
    (hF2 : ContDiffOn ℂ ∞ F2 (Dom n)) (h1 : ∀ P x, InP P → x ∈ Dom n → F1 (P * x) = χ1 P * F1 x)
    (h2 : ∀ P x, InP P → x ∈ Dom n → F2 (P * x) = χ2 P * F2 x)
    (h12 : ∀ P, InP P → χ1 P * χ2 P = ((‖(P.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ))
    (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g)
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (WA : Matrix ιA ιA ℂ →L[ℂ] M2 n) (WB : Matrix ιB ιB ℂ →L[ℂ] M2 n)
    (hW : ∀ (T T' : Matrix ιA ιA ℂ) (S S' : Matrix ιB ιB ℂ), (WA T + WB S) * (WA T' + WB S') = 0) :
    ∫ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F1 (ι k + ι k * WA T + ι k * WB S))) * F2 (ι k) ∂μ =
      (-1) ^ (Fintype.card ιA + Fintype.card ιB) * ∫ k, F1 (ι k) * detD (fun T : Matrix ιA ιA ℂ =>
        detD (fun S : Matrix ιB ιB ℂ => F2 (ι k + ι k * WA T + ι k * WB S))) ∂μ := by
  classical
  have hιK : ∀ k, InK (ι k) := fun k => (hK (ι k)).2 ⟨k, rfl⟩
  have hιDom : ∀ k, ι k ∈ Dom n := fun k => gset_sub_dom (hιK k).1
  set N := Fintype.card ιA + Fintype.card ιB with hN
  let W : Equiv.Perm ιA → Equiv.Perm ιB → Fin N → M2 n := fun σ τ =>
    Fin.append (fun i => WA (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
      (fun i => WB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))
  have hWW : ∀ σ τ a b, W σ τ a * W σ τ b = 0 := by
    intro σ τ a b
    have hAA : ∀ T T' : Matrix ιA ιA ℂ, WA T * WA T' = 0 := fun T T' => by
      simpa only [map_zero, add_zero] using hW T T' 0 0
    have hAB : ∀ (T : Matrix ιA ιA ℂ) (S' : Matrix ιB ιB ℂ), WA T * WB S' = 0 := fun T S' => by
      simpa only [map_zero, add_zero, zero_add] using hW T 0 0 S'
    have hBA : ∀ (S : Matrix ιB ιB ℂ) (T' : Matrix ιA ιA ℂ), WB S * WA T' = 0 := fun S T' => by
      simpa only [map_zero, add_zero, zero_add] using hW 0 T' S 0
    have hBB : ∀ S S' : Matrix ιB ιB ℂ, WB S * WB S' = 0 := fun S S' => by
      simpa only [map_zero, zero_add] using hW 0 0 S S'
    refine Fin.addCases (fun i => ?_) (fun i => ?_) a <;> refine Fin.addCases (fun i' => ?_) (fun i' => ?_) b <;>
      simp only [W, Fin.append_left, Fin.append_right]
    · exact hAA _ _
    · exact hAB _ _
    · exact hBA _ _
    · exact hBB _ _
  have expand : ∀ (F : M2 n → ℂ), ContDiffOn ℂ ∞ F (Dom n) → ∀ k,
      detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (ι k + ι k * WA T + ι k * WB S))) =
      ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ N F (ι k) (fun i => ι k * W σ τ i) := by
    intro F hF k
    have e := detD_detD_comp F (Dom n) isOpen_dom hF (ι k) (hιDom k)
      ((LinearMap.mulLeft ℂ (ι k)).toContinuousLinearMap.comp WA) ((LinearMap.mulLeft ℂ (ι k)).toContinuousLinearMap.comp WB)
    refine e.trans (Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_)
    congr 2
    rw [fin_append_mul]
    rfl
  have hcontD : ∀ (F : M2 n → ℂ), ContDiffOn ℂ ∞ F (Dom n) → ∀ σ τ,
      Continuous (fun k => iteratedFDeriv ℂ N F (ι k) (fun i => ι k * W σ τ i)) := by
    intro F hF σ τ
    have h1 : ContinuousOn (iteratedFDeriv ℂ N F) (Dom n) :=
      (hF.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast le_top) isOpen_dom.uniqueDiffOn).congr
        (fun x hx => (iteratedFDerivWithin_of_isOpen N isOpen_dom hx).symm)
    have h2 : Continuous (fun k => iteratedFDeriv ℂ N F (ι k)) := h1.comp_continuous hι hιDom
    have h3 : Continuous (fun k => (fun i => ι k * W σ τ i : Fin N → M2 n)) :=
      continuous_pi fun i => hι.mul continuous_const
    exact h2.eval h3
  have hc1 : Continuous fun k => F1 (ι k) := hF1.continuousOn.comp_continuous hι hιDom
  have hc2 : Continuous fun k => F2 (ι k) := hF2.continuousOn.comp_continuous hι hιDom
  have hint1 : ∀ σ τ, Integrable (fun k => iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W σ τ i) * F2 (ι k)) μ :=
    fun σ τ => integrable_of_continuous_K μ ((hcontD F1 hF1 σ τ).mul hc2)
  have hint2 : ∀ σ τ, Integrable (fun k => F1 (ι k) * iteratedFDeriv ℂ N F2 (ι k) (fun i => ι k * W σ τ i)) μ :=
    fun σ τ => integrable_of_continuous_K μ (hc1.mul (hcontD F2 hF2 σ τ))
  have eL : (fun k => detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F1 (ι k + ι k * WA T + ι k * WB S))) * F2 (ι k)) =
      fun k => ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        (iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W σ τ i) * F2 (ι k)) := by
    funext k; rw [expand F1 hF1 k, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  have eR : (fun k => F1 (ι k) * detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F2 (ι k + ι k * WA T + ι k * WB S)))) =
      fun k => ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        (F1 (ι k) * iteratedFDeriv ℂ N F2 (ι k) (fun i => ι k * W σ τ i)) := by
    funext k; rw [expand F2 hF2 k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  rw [eL, eR, integral_finset_sum _ (fun σ _ => integrable_finset_sum _ (fun τ _ => (hint1 σ τ).const_mul _)),
    integral_finset_sum _ (fun σ _ => integrable_finset_sum _ (fun τ _ => (hint2 σ τ).const_mul _)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_finset_sum _ (fun τ _ => (hint1 σ τ).const_mul _),
    integral_finset_sum _ (fun τ _ => (hint2 σ τ).const_mul _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul, integral_const_mul,
    transpose hI F1 F2 χ1 χ2 hF1 hF2 h1 h2 h12 Kg μ ι hι hK N (W σ τ) (hWW σ τ)]
  ring
end PositivityTheory.Rg.Sw.LVs
