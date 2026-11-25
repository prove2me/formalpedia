-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eq_zero_of_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:13:45.17239+00:00
-- url     : https://prove2.me/submissions/c1166c31-348a-47fa-9924-3c71742342b9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_exists_isParam


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
    (hg : IsGood D x m μ) {g : (Ix κ → ℂ) → ℝ} (hcont : ContinuousOn g {0}ᶜ) (hdeg : IsDegZero g)
    (hnn : ∀ z, 0 ≤ g z) (hae : g =ᵐ[μ] 0) {z₀ : Ix κ → ℂ} (hz₀ : z₀ ∈ pts (coordIdeal ℤ x)) :
    g z₀ = 0 := by
  obtain ⟨ρ₀, γ, hρ₀, hpar, hγ0⟩ := exists_isParam hg hz₀
  obtain ⟨ν, hν, hνpos, hint⟩ := hg.vol.2.2 _ γ hpar
  have hmeas : Measurable g := measurable_of_continuousOn_compl_singleton 0 hcont
  have h1 := hint g hmeas hdeg hnn
  have h0 : ∫⁻ z in coneOver (Metric.ball 0 ρ₀) γ, ENNReal.ofReal (g z) ∂μ = 0 := by
    rw [lintegral_congr_ae (g := fun _ => 0)]
    · simp
    · exact ae_restrict_of_ae (hae.mono fun z hz => by simp [hz])
  rw [h0] at h1
  set U := Metric.ball (0 : Fin D → ℂ) ρ₀ with hUdef
  have hγc : ContinuousOn γ U := hpar.2.1.continuousOn
  have hγne : Set.MapsTo γ U ({0}ᶜ : Set (Ix κ → ℂ)) := fun y hy => (hpar.2.2.1 y hy).1
  have hφc : ContinuousOn (fun y => g (γ y) * ν y) U := (hcont.comp hγc hγne).mul hν.continuousOn
  have hU0 : (0 : Fin D → ℂ) ∈ U := Metric.mem_ball_self hρ₀
  by_contra hne
  have hpos : 0 < g (γ 0) * ν 0 := by
    rw [hγ0]
    exact mul_pos (lt_of_le_of_ne (hnn _) (Ne.symm hne)) (hνpos 0 hU0)
  have hev : ∀ᶠ y in nhds (0 : Fin D → ℂ), 0 < g (γ y) * ν y :=
    (hφc.continuousAt (Metric.isOpen_ball.mem_nhds hU0)).eventually (lt_mem_nhds hpos)
  obtain ⟨V, hVsub, hVo, hV0⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem hev (Metric.isOpen_ball.mem_nhds hU0))
  have hae2 := (lintegral_eq_zero_iff' (hφc.aemeasurable measurableSet_ball).ennreal_ofReal).mp h1.symm
  have hae3 : ∀ᵐ y ∂(volume : Measure (Fin D → ℂ)), y ∈ U → ENNReal.ofReal (g (γ y) * ν y) = 0 :=
    (ae_restrict_iff' measurableSet_ball).mp (hae2.mono fun y hy => by simpa using hy)
  have hnull : (volume : Measure (Fin D → ℂ)) V = 0 := by
    refine measure_mono_null (fun y hy => ?_) (ae_iff.mp hae3)
    obtain ⟨hy1, hy2⟩ := hVsub hy
    exact fun h => (ENNReal.ofReal_pos.mpr hy1).ne' (h hy2)
  exact hVo.measure_ne_zero volume ⟨0, hV0⟩ hnull
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
