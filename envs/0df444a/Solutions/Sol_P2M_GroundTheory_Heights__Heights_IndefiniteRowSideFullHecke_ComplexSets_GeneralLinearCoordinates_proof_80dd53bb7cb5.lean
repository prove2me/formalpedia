-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GeneralLinearCoordinates_proof_80dd53bb7cb5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:34.890321+00:00
-- url     : https://prove2.me/submissions/ff111402-1cd8-4d6e-8f17-ec860320e8b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermGeneralCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermGeneralCoordinates
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_lastCoord_ne_zero_of_mem_nhds_f89c61425edb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GeneralLinearCoordinates
theorem _root_.solution : GeneralLinearCoordinates.Statement := by
  classical
  intro σ _ f hf hnz
  obtain ⟨r, hr, hfr⟩ := hf.exists_ball_analyticOnNhd

  obtain ⟨w, hwb, hfw⟩ : ∃ w ∈ Metric.ball (0 : Option σ → ℂ) r, f w ≠ 0 := by
    by_contra h
    push Not at h
    exact hnz (Filter.mem_of_superset (Metric.ball_mem_nhds _ hr) fun x hx => h x hx)
  have hUopen : IsOpen (Metric.ball (0 : Option σ → ℂ) r ∩ f ⁻¹' {z | z ≠ 0}) :=
    hfr.continuousOn.isOpen_inter_preimage Metric.isOpen_ball isOpen_ne
  obtain ⟨v, ⟨hvb, hfv⟩, hvt⟩ := exists_lastCoord_ne_zero_of_mem_nhds (hUopen.mem_nhds ⟨hwb, hfw⟩)
  replace hfv : f v ≠ 0 := hfv

  let e : Option σ → ℂ := Pi.single none 1
  let L : (Option σ → ℂ) →ₗ[ℂ] (Option σ → ℂ) :=
    LinearMap.id + (LinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) none).smulRight (v - e)
  have hL : ∀ x, L x = x + x none • (v - e) := fun x => rfl
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : (L x) none = 0 := by rw [hx]; rfl
    have hnone : x none = 0 := by
      rw [hL] at h1
      simp [e] at h1
      have h2 : x none * v none = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h2).resolve_right hvt
    rw [hL, hnone, zero_smul, add_zero] at hx
    exact hx
  let A : (Option σ → ℂ) ≃L[ℂ] (Option σ → ℂ) :=
    (LinearEquiv.ofInjectiveEndo L hLinj).toContinuousLinearEquiv
  have hA : ∀ t : ℂ, A (pointWithLast 0 t) = t • v := by
    intro t
    show L (pointWithLast 0 t) = t • v
    rw [hL]
    funext o
    cases o with
    | none => simp [pointWithLast, e]; ring
    | some i => simp [pointWithLast, e]
  refine ⟨A, ?_⟩
  have hfun : (fun t => f (A (pointWithLast 0 t))) = fun t : ℂ => f (t • v) := by
    funext t; rw [hA]
  rw [hfun]

  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr fun h => hvt (by rw [h]; rfl)
  have hvr : ‖v‖ < r := by simpa using hvb
  set R := r / ‖v‖
  have hR1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, norm_one]
    exact (one_lt_div hv0).mpr hvr
  have hR0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self (lt_trans one_pos
    ((one_lt_div hv0).mpr hvr))
  have han : AnalyticOnNhd ℂ (fun t : ℂ => f (t • v)) (Metric.ball (0 : ℂ) R) := by
    intro t ht
    have htv : t • v ∈ Metric.ball (0 : Option σ → ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul]
      rw [Metric.mem_ball, dist_zero_right] at ht
      calc ‖t‖ * ‖v‖ < R * ‖v‖ := mul_lt_mul_of_pos_right ht hv0
        _ = r := div_mul_cancel₀ r hv0.ne'
    have hs : AnalyticAt ℂ (fun s : ℂ => s • v) t := analyticAt_id.smul analyticAt_const
    show AnalyticAt ℂ (f ∘ fun s : ℂ => s • v) t
    exact AnalyticAt.comp (f := fun s : ℂ => s • v) (x := t) (hfr _ htv) hs
  have hnot : ¬ (∀ᶠ t in 𝓝 (0 : ℂ), f (t • v) = 0) := by
    intro h
    have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hR0 h hR1
    simp at this
    exact hfv this
  have hne : analyticOrderAt (fun t : ℂ => f (t • v)) 0 ≠ ⊤ := fun h =>
    hnot (analyticOrderAt_eq_top.mp h)
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hne
  exact ⟨d, hd.symm⟩
end GeneralLinearCoordinates
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
