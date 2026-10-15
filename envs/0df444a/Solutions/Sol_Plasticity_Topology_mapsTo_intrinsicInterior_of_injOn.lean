-- Prove2me | solution 1 for Plasticity.Topology.mapsTo_intrinsicInterior_of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:40:52.893446+00:00
-- url     : https://prove2.me/submissions/f31ba8e4-a4fb-471b-bbcf-119d944581e3

import Theorems.Thm_Plasticity_Topology_mem_intrinsicInterior_iff_ball
import Theorems.Thm_Plasticity_Topology_isOpen_image_of_injOn_of_finrank_eq
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.LocallyConvex.HahnBanach

namespace Sol_Plasticity_Topology_mapsTo_intrinsicInterior_of_injOn

end Sol_Plasticity_Topology_mapsTo_intrinsicInterior_of_injOn

open Set Metric in
theorem solution {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (D : Set E) (C : Set E')
    (hD : FiniteDimensional ℝ (vectorSpan ℝ D)) (hC : FiniteDimensional ℝ (vectorSpan ℝ C))
    (hdim : Module.finrank ℝ (vectorSpan ℝ D) = Module.finrank ℝ (vectorSpan ℝ C))
    (f : E → E') (hf : ContinuousOn f D) (hinj : Set.InjOn f D) (hmaps : Set.MapsTo f D C) :
    Set.MapsTo f (intrinsicInterior ℝ D) (intrinsicInterior ℝ C) := by
  intro x hx
  have hxD : x ∈ D := intrinsicInterior_subset hx
  have hfxC : f x ∈ C := hmaps hxD
  obtain ⟨ε, hε, hball⟩ := (Plasticity.Topology.mem_intrinsicInterior_iff_ball D x).1 hx
  obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional (vectorSpan ℝ C)
  let g : vectorSpan ℝ D → vectorSpan ℝ C := fun w => P (f (x + w) - f x)
  have hgD : ∀ w : vectorSpan ℝ D, ‖w‖ < ε → x + (w : E) ∈ D := fun w hw => hball w w.2 hw
  have hgval : ∀ w : vectorSpan ℝ D, ‖w‖ < ε → (g w : E') = f (x + w) - f x := by
    intro w hw
    have hmem : f (x + w) - f x ∈ vectorSpan ℝ C := vsub_mem_vectorSpan ℝ (hmaps (hgD w hw)) hfxC
    have h1 := hP ⟨_, hmem⟩
    simp only [g]
    rw [h1]
  have hcont : ContinuousOn g (ball 0 ε) := by
    apply P.continuous.comp_continuousOn
    apply ContinuousOn.sub _ continuousOn_const
    refine hf.comp (continuous_const.add continuous_subtype_val).continuousOn ?_
    intro w hw
    exact hgD w (mem_ball_zero_iff.mp hw)
  have hginj : InjOn g (ball 0 ε) := by
    intro w₁ h₁ w₂ h₂ h
    have h' : (g w₁ : E') = g w₂ := by rw [h]
    rw [hgval w₁ (mem_ball_zero_iff.mp h₁), hgval w₂ (mem_ball_zero_iff.mp h₂)] at h'
    have h3 := hinj (hgD w₁ (mem_ball_zero_iff.mp h₁)) (hgD w₂ (mem_ball_zero_iff.mp h₂))
      (sub_left_injective h')
    exact Subtype.ext (add_left_cancel h3)
  have hopen := Plasticity.Topology.isOpen_image_of_injOn_of_finrank_eq hdim (ball 0 ε) isOpen_ball g hcont hginj
  have h0 : (0 : vectorSpan ℝ C) ∈ g '' ball 0 ε := by
    refine ⟨0, mem_ball_self hε, ?_⟩
    apply Subtype.ext
    rw [hgval 0 (by simpa using hε)]
    simp
  obtain ⟨ε', hε', hsub⟩ := Metric.isOpen_iff.mp hopen 0 h0
  rw [Plasticity.Topology.mem_intrinsicInterior_iff_ball C (f x)]
  refine ⟨ε', hε', fun v hv hvε => ?_⟩
  obtain ⟨w, hw, hgw⟩ := hsub (show (⟨v, hv⟩ : vectorSpan ℝ C) ∈ ball 0 ε' by simpa using hvε)
  have h1 := hgval w (mem_ball_zero_iff.mp hw)
  rw [hgw] at h1
  simp only at h1
  rw [h1, add_sub_cancel]
  exact hmaps (hgD w (mem_ball_zero_iff.mp hw))
