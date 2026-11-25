-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.holInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:29.195662+00:00
-- url     : https://prove2.me/submissions/81168563-fdfd-4e9b-83fa-edfe99efc867

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_HasFDerivAtInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_Imports
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarDir
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivEqZeroOfVanish
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_nat_lt_infty
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolA_hasFDerivAt_int
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolA_integrable_of_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Filter Topology Set Metric Matrix
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs.HolB PositivityTheory.Rg.Sw.LVs.HolC
variable {n : ℕ}
private theorem contDiffOn_integral_and_iteratedFDeriv_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasure μ] {Ω : Set E} (F : Kg → E → ℂ) (hΩ : IsOpen Ω)
    (hcont : ∀ N : ℕ, ContinuousOn (fun y : Kg × E => iteratedFDeriv ℂ N (F y.1) y.2) (univ ×ˢ Ω))
    (hF : ∀ k, ContDiffOn ℂ ∞ (F k) Ω) :
    ContDiffOn ℂ ∞ (fun x => ∫ k, F k x ∂μ) Ω ∧ ∀ (N : ℕ) (x : E) (v : Fin N → E), x ∈ Ω →
      iteratedFDeriv ℂ N (fun x => ∫ k, F k x ∂μ) x v = ∫ k, iteratedFDeriv ℂ N (F k) x v ∂μ := by
  have hFd : ∀ k, ∀ x ∈ Ω, ContDiffAt ℂ ∞ (F k) x := fun k x hx =>
    (hF k).contDiffAt (hΩ.mem_nhds hx)
  have hA : ∀ N : ℕ, ∀ x ∈ Ω, HasFDerivAt (fun x => ∫ k, iteratedFDeriv ℂ N (F k) x ∂μ)
      (∫ k, fderiv ℂ (iteratedFDeriv ℂ N (F k)) x ∂μ) x := by
    intro N x hx
    refine HolA.hasFDerivAt_int hΩ (hcont N) ?_ ?_ hx
    · have e : (fun y : Kg × E => fderiv ℂ (iteratedFDeriv ℂ N (F y.1)) y.2) =
          fun y => continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ
            (iteratedFDeriv ℂ (N + 1) (F y.1) y.2) := by
        funext y
        rw [fderiv_iteratedFDeriv]
        rfl
      rw [e]
      exact (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ).continuous.comp_continuousOn
        (hcont (N + 1))
    · intro k x hx
      exact ((hFd k x hx).differentiableAt_iteratedFDeriv (by simpa using nat_lt_infty N)).hasFDerivAt
  have hB : ∀ N : ℕ, ∀ x ∈ Ω, iteratedFDeriv ℂ N (fun x => ∫ k, F k x ∂μ) x =
      ∫ k, iteratedFDeriv ℂ N (F k) x ∂μ := by
    intro N
    induction N with
    | zero =>
      intro x _
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℂ E ℂ).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
    | succ N ih =>
      intro x hx
      have hev : iteratedFDeriv ℂ N (fun x => ∫ k, F k x ∂μ) =ᶠ[𝓝 x]
          fun x => ∫ k, iteratedFDeriv ℂ N (F k) x ∂μ :=
        Filter.eventually_of_mem (hΩ.mem_nhds hx) ih
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hev.fderiv_eq, (hA N x hx).fderiv]
      exact ((continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ).symm.toContinuousLinearEquiv.integral_comp_comm
        (fun k => fderiv ℂ (iteratedFDeriv ℂ N (F k)) x)).symm
  have hD : ∀ m : ℕ, DifferentiableOn ℂ (fun x => iteratedFDerivWithin ℂ m (fun x => ∫ k, F k x ∂μ) Ω x) Ω :=
    fun m x hx => ((hA m x hx).differentiableAt.differentiableWithinAt).congr
      (fun y hy => (iteratedFDerivWithin_of_isOpen m hΩ hy).trans (hB m y hy))
      ((iteratedFDerivWithin_of_isOpen m hΩ hx).trans (hB m x hx))
  refine ⟨contDiffOn_of_continuousOn_differentiableOn (n := ⊤) (fun m _ => (hD m).continuousOn)
    (fun m _ => hD m), ?_⟩
  intro N x v hx
  rw [hB N x hx]
  have hint : Integrable (fun k => iteratedFDeriv ℂ N (F k) x) μ :=
    HolA.integrable_of_cont ((hcont N).comp_continuous (continuous_id.prodMk continuous_const)
      (fun k => ⟨mem_univ _, hx⟩))
  exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin N => E) ℂ v).integral_comp_comm hint).symm
end PositivityTheory.Rg.Sw.LVs
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Metric Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs.HolB PositivityTheory.Rg.Sw.LVs.HolC
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution : HolInt := by
  intro n Kg _ _ _ _ μ _ Ω F hΩ hcont hF
  exact contDiffOn_integral_and_iteratedFDeriv_integral μ F hΩ hcont hF
end PositivityTheory.Rg.Sw.LVs
