-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.isPshRsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:42.306582+00:00
-- url     : https://prove2.me/submissions/670099fe-0035-41f4-a27f-bfcb907b3842

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Theorems.Thm_ReciprocityTheory_AnForm_M_contDiffAt_of_isPotential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
section SlopeTestRemainingChoices
variable {e : ℕ} {X : Type} [TopologicalSpace X]
end SlopeTestRemainingChoices
private theorem eventually_contDiffAt_potential_chart_symm {e : ℕ} {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P) (x : X) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ (P.φ x ∘ (A.chart j).symm) z := by
  filter_upwards [((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds hy] with z hz
  exact contDiffAt_of_isPotential A P hP x j hz
private theorem differentiableAt_of_contDiffAt_infty {n : ℕ} {F : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ}
    (hF : ContDiffAt ℝ ∞ F y) : DifferentiableAt ℝ F y :=
  hF.differentiableAt (by simp)
private theorem differentiableAt_fderiv_of_contDiffAt_infty {n : ℕ} {F : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ}
    (hF : ContDiffAt ℝ ∞ F y) : DifferentiableAt ℝ (fderiv ℝ F) y :=
  (hF.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt (by simp)
private theorem fderiv_fderiv_const_mul {n : ℕ} {F : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ}
    (hF : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ F z) (c : ℝ) :
    fderiv ℝ (fderiv ℝ (fun z => c * F z)) y = c • fderiv ℝ (fderiv ℝ F) y := by
  have hev : fderiv ℝ (fun z => c * F z) =ᶠ[𝓝 y] fun z => c • fderiv ℝ F z := by
    filter_upwards [hF] with z hFz
    exact fderiv_const_mul (differentiableAt_of_contDiffAt_infty hFz) c
  rw [hev.fderiv_eq]
  exact fderiv_const_smul (differentiableAt_fderiv_of_contDiffAt_infty hF.self_of_nhds) c
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : IsPshRsmulStatement := by
  intro e X _ A c P hc hP hpP x j y hy w
  have hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x := hy
  have hp := hpP x j y hy' w
  have hrw : (P.rsmul c).φ x ∘ (A.chart j).symm = fun z => c * (P.φ x ∘ (A.chart j).symm) z := rfl
  rw [hrw]
  unfold ReciprocityTheory.AnForm.levi at hp ⊢
  rw [fderiv_fderiv_const_mul (eventually_contDiffAt_potential_chart_symm A P hP x j hy') c]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [show ∀ a b : ℝ, (c * a + c * b) / 4 = c * ((a + b) / 4) from fun a b => by ring]
  exact mul_nonneg hc hp
end ReciprocityTheory.AnForm.M
