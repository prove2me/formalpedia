-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.spherical_detD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:10.442202+00:00
-- url     : https://prove2.me/submissions/dce52967-b473-43bb-9289-b48d5e4dd53a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IntegrableIteratedFDerivTranslate
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_integrable_iteratedFDeriv_translate
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_contDiff_mulLeft
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_continuousOn_iteratedFDeriv_translate
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_detD_detD_comp
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_detD_detD_mul_const
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_fin_append_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_isOpen_dom
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_isOpen_domK
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_iteratedFDeriv_left_mul


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
theorem _root_.solution (hHI : HolInt) (F : M2 n → ℂ) (hF : ContDiffOn ℂ ∞ F (Dom n))
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasure μ] [IsFiniteMeasureOnCompacts μ] (ι : Kg → M2 n) (hι : Continuous ι)
    (c : Kg → ℂ) (hc : Continuous c)
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (LA : M2 n → Matrix ιA ιA ℂ →L[ℂ] M2 n) (LB : M2 n → Matrix ιB ιB ℂ →L[ℂ] M2 n)
    (hLA : ∀ M x T, LA (M * x) T = M * LA x T) (hLB : ∀ M x S, LB (M * x) S = M * LB x S)
    (g : M2 n) (hg : ∀ k, ι k * g ∈ Dom n) :
    detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        ∫ k, F (ι k * (g + LA g T + LB g S)) * c k ∂μ)) =
      ∫ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F (ι k * g + LA (ι k * g) T + LB (ι k * g) S))) * c k ∂μ := by
  classical
  set Ω : Set (M2 n) := {x | ∀ k, ι k * x ∈ Dom n} with hΩ
  have hΩo : IsOpen Ω := isOpen_domK Kg ι hι
  have hsm : ∀ k, ContDiffOn ℂ ∞ (fun x => F (ι k * x) * c k) Ω := fun k =>
    (hF.comp (contDiff_mulLeft (ι k)).contDiffOn (fun x (hx : x ∈ Ω) => hx k)).mul contDiffOn_const
  have hH := hHI n Kg μ Ω (fun k x => F (ι k * x) * c k) hΩo
    (fun N => continuousOn_iteratedFDeriv_translate F (Dom n) isOpen_dom hF Kg ι hι c hc N) hsm
  have hgΩ : g ∈ Ω := hg
  have hAv : ContDiffOn ℂ ∞ (fun x => ∫ k, F (ι k * x) * c k ∂μ) Ω := hH.1
  have key : ∀ (N : ℕ) (v : Fin N → M2 n), iteratedFDeriv ℂ N (fun x => ∫ k, F (ι k * x) * c k ∂μ) g v =
      ∫ k, iteratedFDeriv ℂ N (fun x => F (ι k * x) * c k) g v ∂μ := fun N v => hH.2 N g v hgΩ
  have e0 : (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => ∫ k, F (ι k * (g + LA g T + LB g S)) * c k ∂μ))
      = fun T => detD (fun S => (fun x => ∫ k, F (ι k * x) * c k ∂μ) (g + LA g T + LB g S)) := rfl
  have hFc : ∀ k, ContDiffOn ℂ ∞ (fun y => F y * c k) (Dom n) := fun k => hF.mul contDiffOn_const
  have hk : ∀ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
      F (ι k * g + LA (ι k * g) T + LB (ι k * g) S))) * c k =
      ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) (fun x => F (ι k * x) * c k) g
          (Fin.append (fun i => LA g (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
            (fun i => LB g (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
    intro k
    rw [← detD_detD_mul_const F (Dom n) isOpen_dom hF (ι k * g) (hg k) (LA (ι k * g)) (LB (ι k * g)) (c k),
      detD_detD_comp (fun y => F y * c k) (Dom n) isOpen_dom (hFc k) (ι k * g) (hg k) _ _]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    congr 1
    rw [iteratedFDeriv_left_mul (fun y => F y * c k) (Dom n) isOpen_dom (hFc k) (ι k) g (hg k), fin_append_mul]
    simp only [hLA, hLB]
  have hint : ∀ (σ : Equiv.Perm ιA) (τ : Equiv.Perm ιB), Integrable (fun k =>
      iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) (fun x => F (ι k * x) * c k) g
          (Fin.append (fun i => LA g (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
            (fun i => LB g (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1)))) μ :=
    fun σ τ => integrable_iteratedFDeriv_translate F (Dom n) isOpen_dom hF μ ι hι c hc _ g hg _
  rw [e0, detD_detD_comp _ Ω hΩo hAv g hgΩ (LA g) (LB g), integral_congr_ae (Filter.Eventually.of_forall hk)]
  simp only [key]
  symm
  rw [integral_finset_sum _ (fun σ _ => integrable_finset_sum _ (fun τ _ => (hint σ τ).const_mul _))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_finset_sum _ (fun τ _ => (hint σ τ).const_mul _)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul]
end PositivityTheory.Rg.Sw.LVs
