-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.vanishing_order_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:50:21.35786+00:00
-- url     : https://prove2.me/submissions/a957ee9a-0eec-4347-92ef-972467f32207

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_VanishingOrderTransfer
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_differentiableAt_localCoordinates
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_localCoordinates_eq_zmap
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ratio_pow_chart_independent
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_sub_isBigO_of_det_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (A : WeightedAtlas n Y ι La) (L : La) (m : ℕ) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (Nsec : ι → Y → ℂ)
    (hw : A.IsSec L w0) (hs : ∀ k, A.IsSec L (s k)) (hN : A.IsSec (m • L) Nsec)
    (y : Y) (hy0 : w0 (A.pick y) y ≠ 0)
    (hdet : (fderiv ℂ (A.zLoc w0 s (A.pick y)) (A.chart (A.pick y) y)).det ≠ 0)
    (hvan : A.VanishOrd Nsec y (m + 1))
    {T : Type*} [TopologicalSpace T] (j : T → Y) (hj : Continuous j)
    (e : OpenPartialHomeomorph T (V n)) (he : Set.EqOn (fun t => A.zmap w0 s (j t)) e e.source)
    (t0 : T) (ht0 : t0 ∈ e.source) (hjt0 : j t0 = y) :
    ∃ C : ℝ, ∀ᶠ v in 𝓝 (e t0),
      ‖(fun t => Nsec (A.pick (j t)) (j t) / w0 (A.pick (j t)) (j t) ^ m) (e.symm v)‖ ≤
        C * ‖v - e t0‖ ^ (m + 1) := by
  set p := A.pick y with hp
  set c := A.chart p with hc
  set v0 := e t0 with hv0def
  have hy : y ∈ c.source := A.mem_pick y
  have hv0 : v0 ∈ e.target := e.map_source ht0
  have hsymm0 : e.symm v0 = t0 := e.left_inv ht0
  have hte : Tendsto (fun v => j (e.symm v)) (𝓝 v0) (𝓝 y) := by
    have h := (hj.continuousAt (x := e.symm v0)).tendsto.comp (e.continuousAt_symm hv0).tendsto
    rw [hsymm0, hjt0] at h
    exact h
  let φ := fun v => c (j (e.symm v))
  have htφ : Tendsto φ (𝓝 v0) (𝓝 (c y)) := (c.continuousAt hy).tendsto.comp hte
  have hev : ∀ᶠ v in 𝓝 v0, v ∈ e.target ∧ j (e.symm v) ∈ c.source :=
    (e.open_target.eventually_mem hv0).and (hte.eventually (c.open_source.eventually_mem hy))
  have hzφ : ∀ᶠ v in 𝓝 v0, A.zLoc w0 s p (φ v) = v := hev.mono fun v hv => by
    rw [localCoordinates_eq_zmap A L w0 s hw hs p _ hv.2]
    have := he (e.map_target hv.1)
    simp only at this
    rw [this, e.right_inv hv.1]
  have hUeq : ∀ᶠ v in 𝓝 v0,
      Nsec p (c.symm (φ v)) * (w0 p (c.symm (φ v)) ^ m)⁻¹ =
      (fun t => Nsec (A.pick (j t)) (j t) / w0 (A.pick (j t)) (j t) ^ m) (e.symm v) :=
    hev.mono fun v hv => by
      simp only [φ, c.left_inv hv.2]
      rw [ratio_pow_chart_independent A L m Nsec w0 hN hw (A.pick (j (e.symm v))) p _ (A.mem_pick _) hv.2,
        div_eq_mul_inv]
  have hN' : (fun w => Nsec p (c.symm w)) =O[𝓝 (c y)] (fun w => ‖w - c y‖ ^ (m + 1)) := by
    obtain ⟨C, hC⟩ := hvan
    exact IsBigO.of_bound C (hC.mono fun w hw => by rw [norm_pow, norm_norm]; exact hw)
  have hw0c : ContinuousAt (fun w => w0 p (c.symm w)) (c y) := by
    have := hw.1 p
    simp only [Set.preimage_univ, Set.inter_univ] at this
    exact (this.differentiableAt (c.open_target.mem_nhds (c.map_source hy))).continuousAt
  have hinv : (fun w => (w0 p (c.symm w) ^ m)⁻¹) =O[𝓝 (c y)] (fun _ => (1 : ℝ)) := by
    have : ContinuousAt (fun w => (w0 p (c.symm w) ^ m)⁻¹) (c y) :=
      (hw0c.pow m).inv₀ (by
        show w0 p (c.symm (c y)) ^ m ≠ 0
        rw [c.left_inv hy]; exact pow_ne_zero _ hy0)
    exact this.tendsto.isBigO_one ℝ
  have hG := (hN'.mul hinv).comp_tendsto htφ
  have hlow : (fun v => φ v - c y) =O[𝓝 v0] (fun v => v - v0) := by
    have hd := differentiableAt_localCoordinates A L w0 s hw hs p y hy hy0
    have h1 := (sub_isBigO_of_det_ne_zero hd.hasFDerivAt hdet).comp_tendsto htφ
    have hq0 : A.zLoc w0 s p (c y) = v0 := by
      rw [localCoordinates_eq_zmap A L w0 s hw hs p y hy, ← hjt0]; exact he ht0
    refine h1.congr' (Eventually.of_forall fun v => rfl) (hzφ.mono fun v hv => ?_)
    simp only [Function.comp_apply, hv]
    exact congrArg (v - ·) hq0
  have hfin : (fun v => Nsec p (c.symm (φ v)) * (w0 p (c.symm (φ v)) ^ m)⁻¹) =O[𝓝 v0]
      (fun v => ‖v - v0‖ ^ (m + 1)) := by
    refine hG.trans ?_
    have := hlow.norm_norm.pow (m + 1)
    exact this.congr_left (fun v => by simp [φ])
  obtain ⟨C, hC⟩ := isBigO_iff.1 (hfin.congr' hUeq EventuallyEq.rfl)
  refine ⟨C, hC.mono fun v hv => ?_⟩
  rwa [norm_pow, norm_norm] at hv
end ReciprocityTheory.L2DbarEstimates.Y
