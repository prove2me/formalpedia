-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_compare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:03:54.857602+00:00
-- url     : https://prove2.me/submissions/eb6ba803-b063-477c-b598-f904e9afe8f9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_mem_coneOver_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_trans_fac
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_maDensity_eq_maDens
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_hessC_congr
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_contDiffAt_log__a466d063bccb
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_add_log_norm
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
variable {J : Type} [Fintype J] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J}
    (hsm : IsSmoothMetric m) {U U' : Set (Fin D → ℂ)} {γ γ' : (Fin D → ℂ) → J → ℂ}
    (h : IsParam P U γ) (hγ' : AnalyticOnNhd ℂ γ' U')
    {O' : Set (J → ℂ)} {q' : (J → ℂ) → Fin D → ℂ} (hO' : IsOpen O') (hq' : AnalyticOnNhd ℂ q' O')
    (hOP' : O' ∩ pts P = coneOver U' γ')
    (hsc' : ∀ z ∈ O', ∀ c : ℂ, c ≠ 0 → c • z ∈ O' ∧ q' (c • z) = q' z)
    (hqγ' : ∀ y ∈ U', q' (γ' y) = y) {y : Fin D → ℂ} (hy : y ∈ U) (hyO : γ y ∈ O') :
    maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y =
      maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ' w))) (q' (γ y)) *
        Complex.normSq (ReciprocityTheory.AnForm.A.jacC (q' ∘ γ) y).det := by
  classical
  obtain ⟨hU, hγ, hpts, -⟩ := h
  set τ : (Fin D → ℂ) → Fin D → ℂ := q' ∘ γ with hτdef
  set V := U ∩ γ ⁻¹' O' with hVdef
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU hO'
  have hyV : y ∈ V := ⟨hy, hyO⟩
  have hτan : AnalyticOnNhd ℂ τ V := fun w hw => (hq' (γ w) hw.2).comp (hγ w hw.1)
  have hfac : ∀ w ∈ V, τ w ∈ U' ∧ ∃ c : ℂ, c ≠ 0 ∧ γ w = c • γ' (τ w) := fun w hw =>
    adens_trans_fac hpts hOP' hsc' hqγ' hw.1 hw.2
  have hpts' : ∀ v ∈ U', γ' v ∈ pts P := fun v hv =>
    (hOP' ▸ adens_mem_coneOver_self hv : γ' v ∈ O' ∩ pts P).2
  have hτy : τ y ∈ U' := (hfac y hyV).1
  have hne : γ' (τ y) ≠ 0 := (hpts' _ hτy).1
  obtain ⟨i, hi⟩ : ∃ i, γ' (τ y) i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (funext hc)
  have hgτ : AnalyticAt ℂ (fun w => γ' (τ w)) y := (hγ' _ hτy).comp (hτan y hyV)
  have hgτi : AnalyticAt ℂ (fun w => γ' (τ w) i) y := analyticAt_pi_iff.1 hgτ i
  have hγi : AnalyticAt ℂ (fun w => γ w i) y := analyticAt_pi_iff.1 (hγ y hy) i
  set c : (Fin D → ℂ) → ℂ := fun w => γ w i / γ' (τ w) i with hcdef
  have hcan : AnalyticAt ℂ c y := hγi.div hgτi hi
  obtain ⟨c₀, hc₀, e₀⟩ := (hfac y hyV).2
  have hcy : c y ≠ 0 := by
    have : γ y i = c₀ * γ' (τ y) i := by rw [e₀]; rfl
    simp only [hcdef, this, mul_div_assoc, div_self hi, mul_one]
    exact hc₀
  set φ' : (Fin D → ℂ) → ℝ := fun w => Real.log (m.ρ (γ' w)) with hφ'def
  have hev : (fun w => Real.log (m.ρ (γ w))) =ᶠ[𝓝 y] fun w => φ' (τ w) + Real.log ‖c w‖ := by
    have h1 : ∀ᶠ w in 𝓝 y, w ∈ V := hV.mem_nhds hyV
    have h2 : ∀ᶠ w in 𝓝 y, γ' (τ w) i ≠ 0 := hgτi.continuousAt.eventually_ne hi
    filter_upwards [h1, h2] with w hw hwi
    obtain ⟨hτw, c₁, hc₁, e₁⟩ := hfac w hw
    have hcw : c w = c₁ := by
      have : γ w i = c₁ * γ' (τ w) i := by rw [e₁]; rfl
      simp only [hcdef, this, mul_div_assoc, div_self hwi, mul_one]
    have hne' : γ' (τ w) ≠ 0 := (hpts' _ hτw).1
    simp only [hφ'def]
    rw [hcw, e₁, m.smul, Real.log_mul (norm_ne_zero_iff.2 hc₁) (m.pos _ hne').ne', add_comm]
  have hφ'τ : ContDiffAt ℝ 2 (fun w => φ' (τ w)) y :=
    (adens_contDiffAt_logρ hsm hgτ (by simpa using hne))
  have hH : ReciprocityTheory.AnForm.hessC (fun w => Real.log (m.ρ (γ w))) y =
      ReciprocityTheory.AnForm.hessC (φ' ∘ τ) y := by
    rw [adens_hessC_congr hev]
    exact ReciprocityTheory.AnForm.A.hessC_add_log_norm _ c y hφ'τ hcan hcy
  have hcomp := ReciprocityTheory.AnForm.A.maDens_comp (fun _ : Fin D => φ') τ y (hτan y hyV)
    (fun _ => adens_contDiffAt_logρ hsm (hγ' _ hτy) hne)
  rw [adens_maDensity_eq_maDens, adens_maDensity_eq_maDens]
  change _ = ReciprocityTheory.AnForm.maDens (fun _ : Fin D => φ') (τ y) * _
  rw [← hcomp]
  unfold ReciprocityTheory.AnForm.maDens
  simp only [hH]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
