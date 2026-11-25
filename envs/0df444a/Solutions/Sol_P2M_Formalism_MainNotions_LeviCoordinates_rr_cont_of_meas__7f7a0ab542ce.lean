-- Prove2me | solution 1 for P2M_Formalism_MainNotions_LeviCoordinates_rr_cont_of_meas__7f7a0ab542ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:31:09.786799+00:00
-- url     : https://prove2.me/submissions/eba41114-ea75-481b-817f-79938d6b592e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrdStronglyMeasurable
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrd_ae_zero
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrd_vec_tendsto
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrd_inner_vec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Filter Topology Set TopologicalSpace
open scoped InnerProductSpace
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H]
variable {π : G → (H →L[ℂ] H)}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution [SigmaFinite μ] [IsLocallyFiniteMeasure μ] (hμ : μ ≠ 0)
    (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1) (hiso : ∀ g x, ‖π g x‖ = ‖x‖)
    (hmeas : ∀ x y, StronglyMeasurable fun g => ⟪x, π g y⟫_ℂ) (x : H) : Continuous fun g => π g x := by
  let W : Submodule ℂ H :=
    { carrier := {w | Tendsto (fun h => π h w) (𝓝 1) (𝓝 w)}
      add_mem' := fun {a b} ha hb => by
        have ha' : Tendsto (fun h => π h a) (𝓝 1) (𝓝 a) := ha
        have hb' : Tendsto (fun h => π h b) (𝓝 1) (𝓝 b) := hb
        exact (ha'.add hb').congr fun h => (map_add (π h) a b).symm
      zero_mem' := by
        show Tendsto (fun h => π h 0) (𝓝 1) (𝓝 0)
        simp only [map_zero]
        exact tendsto_const_nhds
      smul_mem' := fun c {w} hw => by
        have hw' : Tendsto (fun h => π h w) (𝓝 1) (𝓝 w) := hw
        exact (hw'.const_smul c).congr fun h => (map_smul (π h) c w).symm }
  have memW : ∀ w, w ∈ W ↔ Tendsto (fun h => π h w) (𝓝 1) (𝓝 w) := fun w => Iff.rfl
  have hclosed : IsClosed (W : Set H) := by
    refine isClosed_of_closure_subset fun w hw => ?_
    rw [SetLike.mem_coe, memW, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨w', hw', hd⟩ := Metric.mem_closure_iff.1 hw (ε / 3) (by positivity)
    rw [SetLike.mem_coe, memW, Metric.tendsto_nhds] at hw'
    filter_upwards [hw' (ε / 3) (by positivity)] with h hh
    have e1 : dist (π h w) (π h w') = dist w w' := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, hiso]
    calc dist (π h w) w ≤ dist (π h w) (π h w') + dist (π h w') w' + dist w' w := dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by rw [e1, dist_comm w' w]; linarith
      _ = ε := by ring
  have hperp : W.orthogonal = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    have hae : ∀ v : H, ∀ᵐ g ∂μ, ⟪u, π g v⟫_ℂ = 0 := by
      intro v
      have hz := rrd_ae_zero (μ := μ) (fun g => ⟪u, π g v⟫_ℂ) (hmeas u v)
        (‖u‖ * ‖v‖) (fun g => ?_) (fun f hc hf => ?_)
      · filter_upwards [hz] with g hg
        simpa using hg
      · calc ‖⟪u, π g v⟫_ℂ‖ ≤ ‖u‖ * ‖π g v‖ := norm_inner_le_norm _ _
          _ = ‖u‖ * ‖v‖ := by rw [hiso]
      · show ∫ g, f g * ⟪u, π g v⟫_ℂ ∂μ = 0
        rw [← rrd_inner_vec hiso hmeas hf u v]
        have hw : rrd_vec μ π f v ∈ W :=
          (memW _).2 (rrd_vec_tendsto hmul hiso hmeas hc hf v)
        first
        | exact Submodule.inner_left_of_mem_orthogonal hw hu
        | exact (Submodule.mem_orthogonal' W u).1 hu _ hw
        | exact inner_eq_zero_symm.1 ((Submodule.mem_orthogonal W u).1 hu _ hw)
    have hall : ∀ᵐ g ∂μ, ∀ n : ℕ, ⟪u, π g (denseSeq H n)⟫_ℂ = 0 := ae_all_iff.2 fun n => hae _
    haveI : (ae μ).NeBot := ae_neBot.2 hμ
    obtain ⟨g, hg⟩ := hall.exists
    have hzero : ∀ y : H, ⟪u, π g y⟫_ℂ = 0 := fun y =>
      (denseRange_denseSeq H).induction_on y
        (isClosed_eq (continuous_const.inner (π g).continuous) continuous_const) hg
    have e : π g ∘L π g⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
    have e2 : π g (π g⁻¹ u) = u := by
      have := congrArg (fun T : H →L[ℂ] H => T u) e
      simpa using this
    have hu' : ⟪u, u⟫_ℂ = 0 := by
      have := hzero (π g⁻¹ u)
      rwa [e2] at this
    exact inner_self_eq_zero.1 hu'
  have htc : W.topologicalClosure = ⊤ := by
    first
    | exact Submodule.topologicalClosure_eq_top_iff.2 hperp
    | exact (Submodule.topologicalClosure_eq_top_iff W).2 hperp
  have hx : ∀ x : H, Tendsto (fun h => π h x) (𝓝 1) (𝓝 x) := by
    intro x
    have h1 : x ∈ W.topologicalClosure := by
      rw [htc]
      exact Submodule.mem_top
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, hclosed.closure_eq, SetLike.mem_coe] at h1
    exact (memW x).1 h1
  refine continuous_iff_continuousAt.2 fun g0 => ?_
  have t1 : Tendsto (fun g => g0⁻¹ * g) (𝓝 g0) (𝓝 1) := by
    simpa using (continuous_mul_left g0⁻¹).tendsto g0
  have t2 := ((π g0).continuous.tendsto x).comp ((hx x).comp t1)
  refine t2.congr fun g => ?_
  have e : π g = π g0 ∘L π (g0⁻¹ * g) := by rw [← hmul, mul_inv_cancel_left]
  simp only [Function.comp_apply, e, ContinuousLinearMap.comp_apply]
end Formalism.MainNotions.LeviCoordinates
