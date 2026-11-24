-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.integrable_secFun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:43.684868+00:00
-- url     : https://prove2.me/submissions/0634976c-7ec4-49b8-a5d2-9421ac8b37da

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_continuous_secFun
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_secFun_smul


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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ} (hb : IsSecBasis x n b)
    (i j : Fin r) :
    Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt m n z : ℂ)) μ := by
  classical
  have hm : IsSmoothMetric m := hg.semipos.1
  have hρ : ContinuousOn m.ρ {0}ᶜ := hm.continuousOn.mono fun _ hz => hz
  haveI : IsProbabilityMeasure μ := hg.vol.1
  have hpts : ∀ᵐ z ∂μ, z ∈ pts (coordIdeal ℤ x) := by
    rw [ae_iff]
    exact hg.vol.2.1
  have hbound : ∀ k, ∃ C : ℝ, ∀ z : Ix κ → ℂ, z ≠ 0 → ‖secFun (b k) z‖ ^ 2 * wgt m n z ≤ C := by
    intro k
    have hdeg : ∀ (c : ℂ) (z : Ix κ → ℂ), c ≠ 0 →
        ‖secFun (b k) (c • z)‖ ^ 2 * wgt m n (c • z) = ‖secFun (b k) z‖ ^ 2 * wgt m n z := by
      intro c z hc
      have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
      have hpow : ‖c‖ ^ (2 * n) ≠ 0 := pow_ne_zero _ hn
      simp only [wgt]
      rw [secFun_smul (hb.1 k), m.smul, norm_mul, norm_pow, mul_pow, mul_pow (‖c‖), mul_inv, ← pow_mul]
      field_simp
      ring
    have hcont : ContinuousOn (fun z => ‖secFun (b k) z‖ ^ 2 * wgt m n z) {0}ᶜ := by
      refine ContinuousOn.mul ?_ ?_
      · exact ((continuous_secFun (b k)).norm.pow 2).continuousOn
      · exact ContinuousOn.inv₀ (hρ.pow _) fun z hz => pow_ne_zero _ (m.pos z hz).ne'
    have hS : IsCompact (Metric.sphere (0 : Ix κ → ℂ) 1) := isCompact_sphere 0 1
    have hSsub : Metric.sphere (0 : Ix κ → ℂ) 1 ⊆ {0}ᶜ := by
      intro z hz h0
      rw [Set.mem_singleton_iff] at h0
      rw [h0, mem_sphere_iff_norm, sub_zero, norm_zero] at hz
      exact zero_ne_one hz
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (hcont.mono hSsub)
    refine ⟨C, fun z hz => ?_⟩
    have hnz : ((‖z‖ : ℝ) : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast norm_ne_zero_iff.2 hz)
    have h1 := hdeg _ z hnz
    have hz1 : ((‖z‖ : ℝ) : ℂ)⁻¹ • z ∈ Metric.sphere (0 : Ix κ → ℂ) 1 := by
      rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]
    have h2 := hC _ hz1
    rw [← h1]
    exact (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at h2)
  obtain ⟨Ci, hCi⟩ := hbound i
  obtain ⟨Cj, hCj⟩ := hbound j
  have hρm : Measurable m.ρ := by
    have h := ContinuousOn.measurable_piecewise hρ
      (by rw [compl_compl]; exact continuousOn_singleton m.ρ 0)
      (measurableSet_singleton (0 : Ix κ → ℂ)).compl
    rwa [Set.piecewise_same] at h
  have hw : Measurable (wgt m n) := (hρm.pow_const _).inv
  have hF : Measurable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt m n z : ℂ)) :=
    ((Complex.continuous_conj.comp (continuous_secFun (b i))).mul (continuous_secFun (b j))).measurable.mul
      (Complex.measurable_ofReal.comp hw)
  refine Integrable.mono' (integrable_const ((Ci + Cj) / 2)) hF.aestronglyMeasurable ?_
  filter_upwards [hpts] with z hz
  have hz0 : z ≠ 0 := hz.1
  have hwz : 0 ≤ wgt m n z := inv_nonneg.2 (pow_nonneg (m.pos z hz0).le _)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hwz, Complex.norm_conj]
  have e1 := hCi z hz0
  have e2 := hCj z hz0
  nlinarith [mul_nonneg (sq_nonneg (‖secFun (b i) z‖ - ‖secFun (b j) z‖)) hwz]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
