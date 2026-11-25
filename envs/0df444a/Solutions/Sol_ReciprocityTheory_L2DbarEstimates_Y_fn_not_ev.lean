-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_not_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:25:45.328813+00:00
-- url     : https://prove2.me/submissions/9b2b05ce-20dc-4312-90b1-86bff757bfc5

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ImportsAlt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_of_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_eq_zero_of_eval
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_mem_Mset_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.L2DbarEstimates.Y.fn_hom_zero

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) {P : Y} (hP : P ∈ A.zeroSet s) :
    ¬ ∀ᶠ y in 𝓝 P, y ∉ A.Mset w0 s De := by
  intro H
  apply hF.De_ne
  set i := A.pick P with hi
  have hPs : P ∈ (A.chart i).source := A.mem_pick P
  set c := A.chart i P with hc
  have hct : c ∈ (A.chart i).target := (A.chart i).map_source hPs
  have hsymm : (A.chart i).symm c = P := (A.chart i).left_inv hPs
  obtain ⟨h0, -⟩ : A.IsSecOn L Set.univ w0 := hD.isSection_denom
  have hw : DifferentiableOn ℂ (fun v => w0 i ((A.chart i).symm v)) (A.chart i).target := by
    have := h0 i
    rwa [Set.preimage_univ, Set.inter_univ] at this
  have hs : ∀ k, DifferentiableOn ℂ (fun v => s k i ((A.chart i).symm v)) (A.chart i).target := by
    intro k
    obtain ⟨hk, -⟩ : A.IsSecOn L Set.univ (s k) := hD.sec_s k
    have := hk i
    rwa [Set.preimage_univ, Set.inter_univ] at this
  have hw0P : w0 i P ≠ 0 := hD.w0_ne P hP
  let U := (A.chart i).target ∩ (fun v => w0 i ((A.chart i).symm v)) ⁻¹' {0}ᶜ
  have hUo : IsOpen U := hw.continuousOn.isOpen_inter_preimage (A.chart i).open_target isOpen_compl_singleton
  have hcU : c ∈ U := ⟨hct, by
    show w0 i ((A.chart i).symm c) ≠ 0
    rw [hsymm]; exact hw0P⟩
  have hcd : ContDiffOn ℂ ∞ (A.zLoc w0 s i) U := by
    rw [contDiffOn_piLp]
    intro k
    have hk : DifferentiableOn ℂ (fun v => s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v)) U := by
      have hne : ∀ v ∈ U, w0 i ((A.chart i).symm v) ≠ 0 := fun v hv => hv.2
      intro v hv
      have h1 : DifferentiableWithinAt ℂ (fun v => s k i ((A.chart i).symm v)) U v :=
        ((hs k).mono Set.inter_subset_left) v hv
      have h2 : DifferentiableWithinAt ℂ (fun v => w0 i ((A.chart i).symm v)) U v :=
        (hw.mono Set.inter_subset_left) v hv
      have h3 : DifferentiableWithinAt ℂ
          (fun v => s k i ((A.chart i).symm v) * (w0 i ((A.chart i).symm v))⁻¹) U v :=
        h1.mul (h2.inv (hne v hv))
      simpa only [div_eq_mul_inv] using h3
    exact contDiffOn_of_differentiableOn n _ U hUo hk
  have hcda : ContDiffAt ℂ ∞ (A.zLoc w0 s i) c := hcd.contDiffAt (hUo.mem_nhds hcU)
  have hstr : HasStrictFDerivAt (A.zLoc w0 s i) (fderiv ℂ (A.zLoc w0 s i) c) c := by
    first
    | exact hcda.hasStrictFDerivAt (by simp)
    | exact hcda.hasStrictFDerivAt (by norm_num)
    | exact hcda.hasStrictFDerivAt (by exact_mod_cast le_top)
  have hdet : LinearMap.det (fderiv ℂ (A.zLoc w0 s i) c : V n →ₗ[ℂ] V n) ≠ 0 := hD.coord P hP
  let e : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero (fderiv ℂ (A.zLoc w0 s i) c : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv
  have hstrict : HasStrictFDerivAt (A.zLoc w0 s i) (e : V n →L[ℂ] V n) c :=
    hstr.congr_fderiv (by ext v; rfl)
  have H2 : ∀ᶠ v in 𝓝 c, (A.chart i).symm v ∉ A.Mset w0 s De := by
    have hm := (A.chart i).symm_map_nhds_eq hPs
    rw [← hm] at H
    exact H
  have H3 : ∀ᶠ v in 𝓝 c, MvPolynomial.eval (fun k => (A.zLoc w0 s i v) k) De = 0 := by
    filter_upwards [H2, hUo.mem_nhds hcU] with v hv hvU
    have hvs : (A.chart i).symm v ∈ (A.chart i).source := (A.chart i).map_target hvU.1
    have hw0v : w0 i ((A.chart i).symm v) ≠ 0 := hvU.2
    have h1 := (fn_mem_Mset_iff A hD hvs).not.mp hv
    rw [not_not, fn_hom_of_ne De hw0v] at h1
    have h2 := (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hw0v)
    simpa [WeightedAtlas.zLoc] using h2
  have H4 : ∀ᶠ z in 𝓝 (A.zLoc w0 s i c), MvPolynomial.eval (fun k => z k) De = 0 := by
    rw [← hstrict.map_nhds_eq_of_equiv]
    exact H3
  exact fn_eq_zero_of_eval De H4
end ReciprocityTheory.L2DbarEstimates.Y
