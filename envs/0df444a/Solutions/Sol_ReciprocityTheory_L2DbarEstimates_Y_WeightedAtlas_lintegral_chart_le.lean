-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.lintegral_chart_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:23.844984+00:00
-- url     : https://prove2.me/submissions/31aeacca-5710-4dc6-94e5-5b4260e0cec9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution (A : WeightedAtlas n Y ι La) (i : ι) (y0 : Y) {W : Set (V n)}
    (hW : IsOpen W) (hWt : W ⊆ (A.chart i).target) (c : ℝ≥0∞)
    (hc : ∀ v ∈ W, ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) ≤ c)
    (ψ : V n → ℝ≥0∞) (hψ : Continuous ψ) :
    ∫⁻ x in (A.chart i).source ∩ A.chart i ⁻¹' W, ψ (A.chart i x) ∂A.mu ≤
      c * ∫⁻ v in W, ψ v := by
  classical
  set e := A.chart i
  set U := e.source ∩ e ⁻¹' W with hUdef
  have hUo : IsOpen U := e.isOpen_inter_preimage hW
  have hUm : MeasurableSet U := hUo.measurableSet
  set φ : V n → Y := W.piecewise e.symm (fun _ => y0) with hφdef
  have hφ : Measurable φ :=
    ContinuousOn.measurable_piecewise (e.continuousOn_symm.mono hWt) continuousOn_const
      hW.measurableSet
  have himg : ∀ B : Set Y, e '' (B ∩ U) = φ ⁻¹' B ∩ W := by
    intro B
    ext v
    constructor
    · rintro ⟨x, ⟨hxB, hxs, hxW⟩, rfl⟩
      refine ⟨?_, hxW⟩
      show φ (e x) ∈ B
      rw [show φ (e x) = e.symm (e x) from Set.piecewise_eq_of_mem _ _ _ hxW, e.left_inv hxs]
      exact hxB
    · rintro ⟨hvB, hvW⟩
      rw [Set.mem_preimage, show φ v = e.symm v from Set.piecewise_eq_of_mem _ _ _ hvW] at hvB
      have hvt := hWt hvW
      refine ⟨e.symm v, ⟨hvB, e.map_target hvt, ?_⟩, e.right_inv hvt⟩
      show e (e.symm v) ∈ W
      rwa [e.right_inv hvt]
  set ν : Measure (V n) := c • (volume.restrict W)
  have hle : A.mu.restrict U ≤ Measure.map φ ν := by
    rw [Measure.le_iff]
    intro B hB
    rw [Measure.restrict_apply hB, Measure.map_apply hφ hB,
      A.mu_chart i (B ∩ U) (hB.inter hUm) (Set.inter_subset_right.trans Set.inter_subset_left),
      himg B]
    have hm : MeasurableSet (φ ⁻¹' B ∩ W) := (hφ hB).inter hW.measurableSet
    calc ∫⁻ v in φ ⁻¹' B ∩ W, ENNReal.ofReal (Real.exp (A.ph A.kap i (e.symm v)))
        ≤ ∫⁻ _ in φ ⁻¹' B ∩ W, c := setLIntegral_mono' hm (fun v hv => hc v hv.2)
      _ = ν (φ ⁻¹' B) := by
        rw [setLIntegral_const, Measure.smul_apply, Measure.restrict_apply (hφ hB), smul_eq_mul,
          mul_comm]
  set Φ : Y → ℝ≥0∞ := U.piecewise (fun x => ψ (e x)) (fun _ => 0) with hΦdef
  have hΦ : Measurable Φ :=
    ContinuousOn.measurable_piecewise (hψ.comp_continuousOn (e.continuousOn.mono
      Set.inter_subset_left)) continuousOn_const hUm
  calc ∫⁻ x in U, ψ (e x) ∂A.mu = ∫⁻ x in U, Φ x ∂A.mu :=
        setLIntegral_congr_fun hUm (fun x hx => by simp [Φ, Set.piecewise_eq_of_mem _ _ _ hx])
    _ ≤ ∫⁻ x, Φ x ∂(Measure.map φ ν) := lintegral_mono' hle le_rfl
    _ = ∫⁻ v, Φ (φ v) ∂ν := lintegral_map hΦ hφ
    _ = c * ∫⁻ v in W, Φ (φ v) := lintegral_smul_measure _ _
    _ = c * ∫⁻ v in W, ψ v := by
        congr 1
        refine setLIntegral_congr_fun hW.measurableSet (fun v hv => ?_)
        have hvt := hWt hv
        have hU : e.symm v ∈ U := ⟨e.map_target hvt, by
          show e (e.symm v) ∈ W
          rwa [e.right_inv hvt]⟩
        simp only [φ, Φ, Set.piecewise_eq_of_mem _ _ _ hv, Set.piecewise_eq_of_mem _ _ _ hU,
          e.right_inv hvt]
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
