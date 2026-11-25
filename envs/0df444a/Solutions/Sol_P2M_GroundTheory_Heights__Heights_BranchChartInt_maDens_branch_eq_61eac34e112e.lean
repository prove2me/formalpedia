-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BranchChartInt_maDens_branch_eq_61eac34e112e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:50:38.356178+00:00
-- url     : https://prove2.me/submissions/a74a56ee-026a-433b-aea8-b2d432bc5954

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchChartInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicFibreSumInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchSheetAE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchChartInt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BranchChartInt_analyticOnNhd_of_differentiableOn_5a13dc7ae73c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BranchChartInt_differentiable_mulVec_82eea0bfd5ec
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_comp


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
namespace GroundTheory.Heights₂.Heights.BranchChartInt
theorem _root_.solution {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {p : Fin n → ℂ} (γ : VarBranch J d p) {φ : Fin d → (Fin n → ℂ) → ℝ}
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k)) {t : Fin d → ℂ} (ht : t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius)
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A (γ.toFun t) s) :
    ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t =
      ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (A *ᵥ γ.toFun t) *
        Complex.normSq (jacC (fun t => A *ᵥ γ.toFun t) t).det := by
  obtain ⟨U, hUo, hxU, hsd, hsx, -, V, hV, hVeq⟩ := hs
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτ
  have hτd : DifferentiableOn ℂ τ (Metric.ball 0 γ.radius) :=
    (differentiable_mulVec A).comp_differentiableOn γ.differentiableOn
  have hτa : AnalyticAt ℂ τ t := analyticOnNhd_of_differentiableOn Metric.isOpen_ball hτd t ht
  have hΔ : Metric.ball (0 : Fin d → ℂ) γ.radius ∈ 𝓝 t := Metric.isOpen_ball.mem_nhds ht
  have hγc : ContinuousAt γ.toFun t := γ.differentiableOn.continuousOn.continuousAt hΔ
  have hev : ∀ k, φ k ∘ γ.toFun =ᶠ[𝓝 t] (φ k ∘ s) ∘ τ := by
    intro k
    filter_upwards [hΔ, hγc.preimage_mem_nhds hV,
      hτa.continuousAt.preimage_mem_nhds (hUo.mem_nhds hxU)] with t' ht' hV' hU'
    simp only [Function.comp_apply]
    rw [← hVeq (γ.toFun t') ⟨γ.mapsTo ht', hV'⟩ hU']
  have hmd : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t =
      ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) t := by
    unfold ReciprocityTheory.AnForm.maDens
    congr 3
    funext k
    have h2 : fderiv ℝ (fderiv ℝ (φ k ∘ γ.toFun)) t = fderiv ℝ (fderiv ℝ ((φ k ∘ s) ∘ τ)) t :=
      ((hev k).fderiv (𝕜 := ℝ)).fderiv_eq
    unfold ReciprocityTheory.AnForm.hessC
    rw [h2]
  have hsa : AnalyticAt ℂ s (τ t) := analyticOnNhd_of_differentiableOn hUo hsd (τ t) hxU
  have hc : ∀ k, ContDiffAt ℝ 2 (φ k ∘ s) (τ t) := by
    intro k
    obtain ⟨O, hOo, hZO, hφO⟩ := hφ k
    have hmem : s (τ t) ∈ O := by
      rw [show s (τ t) = γ.toFun t from hsx]
      exact hZO (γ.mapsTo ht)
    exact ((hφO.contDiffAt (hOo.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top)).comp (τ t)
      (hsa.contDiffAt.restrict_scalars ℝ)
  rw [hmd]
  exact maDens_comp (fun k => φ k ∘ s) τ t hτa hc
end GroundTheory.Heights₂.Heights.BranchChartInt
