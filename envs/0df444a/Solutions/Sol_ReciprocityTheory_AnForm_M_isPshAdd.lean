-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.isPshAdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:42.432853+00:00
-- url     : https://prove2.me/submissions/fe2ac731-ef91-48a1-ae4b-2ef1b43b9153

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
private theorem fderiv_fderiv_add' {n : ℕ} {F G : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ}
    (hF : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ F z) (hG : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ G z) :
    fderiv ℝ (fderiv ℝ (fun z => F z + G z)) y = fderiv ℝ (fderiv ℝ F) y + fderiv ℝ (fderiv ℝ G) y := by
  have hev : fderiv ℝ (fun z => F z + G z) =ᶠ[𝓝 y] fun z => fderiv ℝ F z + fderiv ℝ G z := by
    filter_upwards [hF, hG] with z hFz hGz
    exact fderiv_add (differentiableAt_of_contDiffAt_infty hFz) (differentiableAt_of_contDiffAt_infty hGz)
  rw [hev.fderiv_eq]
  exact fderiv_add (differentiableAt_fderiv_of_contDiffAt_infty hF.self_of_nhds)
    (differentiableAt_fderiv_of_contDiffAt_infty hG.self_of_nhds)
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : IsPshAddStatement := by
  intro e X _ A P Q hP hQ hpP hpQ x j y hy w
  have hy' : y ∈ (A.chart j).target ∧ (A.chart j).symm y ∈ P.U x ∩ Q.U x := hy
  have hyP : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x := ⟨hy'.1, hy'.2.1⟩
  have hyQ : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U x := ⟨hy'.1, hy'.2.2⟩
  have hp := hpP x j y hyP w
  have hq := hpQ x j y hyQ w
  have hrw : (P + Q).φ x ∘ (A.chart j).symm =
      fun z => (P.φ x ∘ (A.chart j).symm) z + (Q.φ x ∘ (A.chart j).symm) z := rfl
  rw [hrw]
  unfold ReciprocityTheory.AnForm.levi at hp hq ⊢
  rw [fderiv_fderiv_add' (eventually_contDiffAt_potential_chart_symm A P hP x j hyP)
    (eventually_contDiffAt_potential_chart_symm A Q hQ x j hyQ)]
  simp only [ContinuousLinearMap.add_apply]
  linarith
end ReciprocityTheory.AnForm.M
