-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_density_compare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:12.276944+00:00
-- url     : https://prove2.me/submissions/da2508e9-90f7-4b21-b386-e22313e79572

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_mem_coneOver_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_smul_mem_coneOver
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_measurableSet_cut
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_lintegral_ofReal_indicator_one
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_jacC
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_restrictScalars_real
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


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
theorem _root_.solution {P : Ideal (MvPolynomial J ℤ)} {μ : Measure (J → ℂ)}
    {U U' : Set (Fin D → ℂ)} {γ γ' : (Fin D → ℂ) → J → ℂ} {ν ν' : (Fin D → ℂ) → ℝ}
    (h : IsParam P U γ) (hν : IsDensityFor μ U γ ν) (hU' : IsOpen U')
    (hγ' : AnalyticOnNhd ℂ γ' U') (hν' : IsDensityFor μ U' γ' ν')
    {O' : Set (J → ℂ)} {q' : (J → ℂ) → Fin D → ℂ} (hO' : IsOpen O') (hq' : AnalyticOnNhd ℂ q' O')
    (hOP' : O' ∩ pts P = coneOver U' γ')
    (hsc' : ∀ z ∈ O', ∀ c : ℂ, c ≠ 0 → c • z ∈ O' ∧ q' (c • z) = q' z)
    (hqγ' : ∀ y ∈ U', q' (γ' y) = y) {y : Fin D → ℂ} (hy : y ∈ U) (hyO : γ y ∈ O') :
    ν y = ν' (q' (γ y)) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC (q' ∘ γ) y).det := by
  classical
  obtain ⟨hU, hγ, hpts, O, q, hO, hq, hOP, hsc, hqγ⟩ := h
  set τ : (Fin D → ℂ) → Fin D → ℂ := q' ∘ γ with hτdef
  set V := U ∩ γ ⁻¹' O' with hVdef
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU hO'
  have hyV : y ∈ V := ⟨hy, hyO⟩
  have hτan : AnalyticOnNhd ℂ τ V := fun w hw => (hq' (γ w) hw.2).comp (hγ w hw.1)

  have hfac : ∀ w ∈ V, τ w ∈ U' ∧ ∃ c : ℂ, c ≠ 0 ∧ γ w = c • γ' (τ w) := by
    intro w hw
    have hm : γ w ∈ O' ∩ pts P := ⟨hw.2, hpts w hw.1⟩
    rw [hOP'] at hm
    obtain ⟨y', hy', c, hc, he⟩ := hm
    have hO'y : γ' y' ∈ O' := (hOP' ▸ adens_mem_coneOver_self hy' : γ' y' ∈ O' ∩ pts P).1
    have : τ w = y' := by
      simp only [hτdef, Function.comp, he, (hsc' _ hO'y c hc).2, hqγ' y' hy']
    exact ⟨this ▸ hy', c, hc, this ▸ he⟩
  have hγO : ∀ w ∈ U, γ w ∈ O := fun w hw => (hOP ▸ adens_mem_coneOver_self hw : γ w ∈ O ∩ pts P).1
  have hinj : Set.InjOn τ V := by
    intro w₁ h₁ w₂ h₂ he
    obtain ⟨-, c₁, hc₁, e₁⟩ := hfac w₁ h₁
    obtain ⟨-, c₂, hc₂, e₂⟩ := hfac w₂ h₂
    have : γ w₂ = (c₂ / c₁) • γ w₁ := by
      rw [e₂, e₁, he, smul_smul, div_mul_cancel₀ _ hc₁]
    have h2 := hqγ w₂ h₂.1
    rw [this, (hsc _ (hγO w₁ h₁.1) _ (div_ne_zero hc₂ hc₁)).2, hqγ w₁ h₁.1] at h2
    exact h2
  have hdet : ∀ w ∈ V, |(fderiv ℝ τ w).det| = Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ w).det := by
    intro w hw
    have hd : DifferentiableAt ℂ τ w := (hτan w hw).differentiableAt
    rw [hd.fderiv_restrictScalars ℝ]
    have : ((fderiv ℂ τ w).restrictScalars ℝ).det =
        Complex.normSq (LinearMap.det (fderiv ℂ τ w : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) :=
      ReciprocityTheory.AnForm.A.det_restrictScalars_real _
    rw [this, ← ReciprocityTheory.AnForm.A.det_jacC, abs_of_nonneg (Complex.normSq_nonneg _)]
  have hkey : ∀ A : Set (Fin D → ℂ), MeasurableSet A → A ⊆ V →
      ∫⁻ w in A, ENNReal.ofReal (ν w) =
        ∫⁻ w in A, ENNReal.ofReal (ν' (τ w) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ w).det) := by
    intro A hA hAV
    set S := {z | z ∈ O ∧ z ∈ pts P ∧ q z ∈ A} with hSdef
    have hSm : MeasurableSet S := adens_measurableSet_cut hO hq.continuousOn P hA
    set g : (J → ℂ) → ℝ := S.indicator (fun _ => 1) with hgdef
    have hgm : Measurable g := measurable_const.indicator hSm
    have hg0 : ∀ z, 0 ≤ g z := fun z => Set.indicator_nonneg (fun _ _ => zero_le_one) z
    have hSc : ∀ z, ∀ c : ℂ, c ≠ 0 → z ∈ S → c • z ∈ S := by
      rintro z c hc ⟨h1, h2, h3⟩
      have hz : z ∈ coneOver U γ := hOP ▸ ⟨h1, h2⟩
      have hcz : c • z ∈ O ∩ pts P := hOP ▸ adens_smul_mem_coneOver hz hc
      exact ⟨hcz.1, hcz.2, by rwa [(hsc z h1 c hc).2]⟩
    have hgdeg : IsDegZero g := by
      intro c z hc
      by_cases hz : z ∈ S
      · simp [hgdef, hz, hSc z c hc hz]
      · have : c • z ∉ S := fun h' => hz (by
          have := hSc _ c⁻¹ (inv_ne_zero hc) h'
          rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this)
        simp [hgdef, hz, this]
    have hSsub : S ⊆ coneOver U γ := fun z hz => hOP ▸ ⟨hz.1, hz.2.1⟩
    have hSsub' : S ⊆ coneOver U' γ' := by
      rintro z ⟨h1, h2, h3⟩
      have hz : z ∈ coneOver U γ := hOP ▸ ⟨h1, h2⟩
      obtain ⟨w, hw, c, hc, rfl⟩ := hz
      have hqw : q (c • γ w) = w := by rw [(hsc _ (hγO w hw) c hc).2, hqγ w hw]
      rw [hqw] at h3
      obtain ⟨hτU, c', hc', e⟩ := hfac w (hAV h3)
      exact ⟨τ w, hτU, c * c', mul_ne_zero hc hc', by rw [e, smul_smul]⟩
    have e1 := hν.2.2 g hgm hgdeg hg0
    have e2 := hν'.2.2 g hgm hgdeg hg0
    rw [adens_lintegral_ofReal_indicator_one _ hSm, Set.inter_eq_left.2 hSsub] at e1
    rw [adens_lintegral_ofReal_indicator_one _ hSm, Set.inter_eq_left.2 hSsub'] at e2
    have r1 : ∫⁻ w in U, ENNReal.ofReal (g (γ w) * ν w) = ∫⁻ w in A, ENNReal.ofReal (ν w) := by
      have : ∀ w ∈ U, ENNReal.ofReal (g (γ w) * ν w) =
          A.indicator (fun w => ENNReal.ofReal (ν w)) w := by
        intro w hw
        have hmem : γ w ∈ S ↔ w ∈ A := by
          constructor
          · rintro ⟨-, -, h3⟩; rwa [hqγ w hw] at h3
          · intro hwA; exact ⟨hγO w hw, hpts w hw, by rwa [hqγ w hw]⟩
        by_cases hwA : w ∈ A
        · simp [hgdef, hmem.2 hwA, hwA]
        · simp [hgdef, mt hmem.1 hwA, hwA]
      rw [setLIntegral_congr_fun hU.measurableSet this, lintegral_indicator hA,
        Measure.restrict_restrict hA, Set.inter_eq_left.2 (hAV.trans Set.inter_subset_left)]
    have hderiv : ∀ x ∈ A, HasFDerivWithinAt τ (fderiv ℝ τ x) A x := fun x hx =>
      ((hτan x (hAV hx)).differentiableAt.restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
    have hτA : MeasurableSet (τ '' A) :=
      measurable_image_of_fderivWithin hA hderiv (hinj.mono hAV)
    have hτsub : τ '' A ⊆ U' := by rintro _ ⟨w, hw, rfl⟩; exact (hfac w (hAV hw)).1
    have r2 : ∫⁻ y' in U', ENNReal.ofReal (g (γ' y') * ν' y') =
        ∫⁻ y' in τ '' A, ENNReal.ofReal (ν' y') := by
      have : ∀ y' ∈ U', ENNReal.ofReal (g (γ' y') * ν' y') =
          (τ '' A).indicator (fun y' => ENNReal.ofReal (ν' y')) y' := by
        intro y' hy'
        have hO'y : γ' y' ∈ O' := (hOP' ▸ adens_mem_coneOver_self hy' : γ' y' ∈ O' ∩ pts P).1
        have hmem : γ' y' ∈ S ↔ y' ∈ τ '' A := by
          constructor
          · rintro ⟨h1, h2, h3⟩
            have hz : γ' y' ∈ coneOver U γ := hOP ▸ ⟨h1, h2⟩
            obtain ⟨w, hw, c, hc, e⟩ := hz
            have hqw : q (γ' y') = w := by rw [e, (hsc _ (hγO w hw) c hc).2, hqγ w hw]
            refine ⟨w, hqw ▸ h3, ?_⟩
            have : γ w = c⁻¹ • γ' y' := by rw [e, smul_smul, inv_mul_cancel₀ hc, one_smul]
            show q' (γ w) = y'
            rw [this, (hsc' _ hO'y _ (inv_ne_zero hc)).2, hqγ' y' hy']
          · rintro ⟨w, hwA, rfl⟩
            obtain ⟨-, c, hc, e⟩ := hfac w (hAV hwA)
            have : γ' (τ w) = c⁻¹ • γ w := by rw [e, smul_smul, inv_mul_cancel₀ hc, one_smul]
            have hz : c⁻¹ • γ w ∈ O ∩ pts P :=
              hOP ▸ adens_smul_mem_coneOver (adens_mem_coneOver_self (hAV hwA).1) (inv_ne_zero hc)
            rw [this]
            exact ⟨hz.1, hz.2, by
              rwa [(hsc _ (hγO w (hAV hwA).1) _ (inv_ne_zero hc)).2, hqγ w (hAV hwA).1]⟩
        by_cases h' : y' ∈ τ '' A
        · simp [hgdef, hmem.2 h', h']
        · simp [hgdef, mt hmem.1 h', h']
      rw [setLIntegral_congr_fun hU'.measurableSet this, lintegral_indicator hτA,
        Measure.restrict_restrict hτA, Set.inter_eq_left.2 hτsub]
    have r3 := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA hderiv (hinj.mono hAV)
      (fun y' => ENNReal.ofReal (ν' y'))
    rw [← r1, ← e1, e2, r2, r3]
    refine setLIntegral_congr_fun hA (fun w hw => ?_)
    rw [hdet w (hAV hw), ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm]
  have hcontν : ContinuousOn (fun w => ENNReal.ofReal (ν w)) V :=
    ENNReal.continuous_ofReal.comp_continuousOn (hν.1.continuousOn.mono Set.inter_subset_left)
  have hτc : ContinuousOn τ V := hτan.continuousOn
  have hNc : ContinuousOn (fun w => Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ w).det) V := by
    have hf : ContinuousOn (fderiv ℂ τ) V := (hτan.fderiv).continuousOn
    have hj : ContinuousOn (fun w => ReciprocityTheory.AnForm.A.jacC τ w) V := by
      refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun k => ?_
      exact (continuous_apply a).comp_continuousOn
        ((ContinuousLinearMap.apply ℂ (Fin D → ℂ) (Pi.single k 1)).continuous.comp_continuousOn hf)
    exact Complex.continuous_normSq.comp_continuousOn ((continuous_id.matrix_det).comp_continuousOn hj)
  have hcont' : ContinuousOn
      (fun w => ENNReal.ofReal (ν' (τ w) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ w).det)) V := by
    refine ENNReal.continuous_ofReal.comp_continuousOn (ContinuousOn.mul ?_ hNc)
    exact hν'.1.continuousOn.comp hτc (fun w hw => (hfac w hw).1)
  have hae : (fun w => ENNReal.ofReal (ν w)) =ᵐ[volume.restrict V]
      (fun w => ENNReal.ofReal (ν' (τ w) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ w).det)) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ (hcontν.aemeasurable hV.measurableSet)
      (hcont'.aemeasurable hV.measurableSet) ?_
    intro s hs _
    rw [Measure.restrict_restrict hs]
    exact hkey _ (hs.inter hV.measurableSet) Set.inter_subset_right
  have := Measure.eqOn_open_of_ae_eq hae hV hcontν hcont' hyV
  simp only at this
  rwa [ENNReal.ofReal_eq_ofReal_iff (hν.2.1 y hy).le
    (mul_nonneg (hν'.2.1 _ (hfac y hyV).1).le (Complex.normSq_nonneg _))] at this
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
