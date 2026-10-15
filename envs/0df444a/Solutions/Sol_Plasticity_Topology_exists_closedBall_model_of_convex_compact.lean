-- Prove2me | solution 1 for Plasticity.Topology.exists_closedBall_model_of_convex_compact
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:40:11.256026+00:00
-- url     : https://prove2.me/submissions/f25f379f-f8f0-4b21-b650-2d70c5dceec3

import Theorems.Thm_Plasticity_Topology_mem_intrinsicInterior_iff_ball
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.LocallyConvex.HahnBanach

namespace Sol_Plasticity_Topology_exists_closedBall_model_of_convex_compact

open Set Metric Topology

lemma frontier_eq_sdiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
    (hC : IsClosed C) : intrinsicFrontier ℝ C = C \ intrinsicInterior ℝ C := by
  have hcl : intrinsicClosure ℝ C = C :=
    Subset.antisymm (intrinsicClosure_subset_closure.trans hC.closure_subset)
      subset_intrinsicClosure
  rw [← intrinsicClosure_sdiff_intrinsicInterior, hcl]

lemma ri_nonempty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
    (hconv : Convex ℝ C) (hne : C.Nonempty) [FiniteDimensional ℝ (vectorSpan ℝ C)] :
    (intrinsicInterior ℝ C).Nonempty := by
  obtain ⟨c, hc⟩ := hne
  set W := vectorSpan ℝ C
  let ι : W →ᵃⁱ[ℝ] E :=
    (AffineIsometryEquiv.vaddConst ℝ c).toAffineIsometry.comp W.subtypeₗᵢ.toAffineIsometry
  have hι : ∀ w : W, ι w = (w : E) + c := fun w => rfl
  have himg : ι '' (ι ⁻¹' C) = C := by
    apply image_preimage_eq_of_subset
    intro y hy
    refine ⟨⟨y - c, vsub_mem_vectorSpan ℝ hy hc⟩, ?_⟩
    simp [hι]
  have hconv' : Convex ℝ (ι ⁻¹' C) := hconv.affine_preimage ι.toAffineMap
  have hne' : (ι ⁻¹' C).Nonempty := ⟨0, by simp [hι, hc]⟩
  obtain ⟨w, hw⟩ := Set.Nonempty.intrinsicInterior hconv' hne'
  refine ⟨ι w, ?_⟩
  rw [← himg, AffineIsometry.intrinsicInterior_image]
  exact mem_image_of_mem _ hw

end Sol_Plasticity_Topology_exists_closedBall_model_of_convex_compact

open Set Metric Topology in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E)
    (hcpt : IsCompact C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hfin : FiniteDimensional ℝ (vectorSpan ℝ C)) :
    ∃ φ : vectorSpan ℝ C → E, ∃ ψ : E → vectorSpan ℝ C, Continuous φ ∧ Continuous ψ ∧
      (∀ z : vectorSpan ℝ C, ‖z‖ ≤ 1 →
        φ z ∈ C ∧ ψ (φ z) = z ∧ (φ z ∈ intrinsicFrontier ℝ C ↔ ‖z‖ = 1)) ∧
      ∀ y ∈ C, ‖ψ y‖ ≤ 1 ∧ φ (ψ y) = y := by
  have := hfin
  set W := vectorSpan ℝ C with hW
  have hCcl : IsClosed C := hcpt.isClosed
  obtain ⟨c₀, hc₀⟩ := Sol_Plasticity_Topology_exists_closedBall_model_of_convex_compact.ri_nonempty hconv hne
  have hc₀C : c₀ ∈ C := intrinsicInterior_subset hc₀
  obtain ⟨ε, hε, hball⟩ := (Plasticity.Topology.mem_intrinsicInterior_iff_ball C c₀).1 hc₀
  set C₀ : Set W := {w | (w : E) + c₀ ∈ C} with hC₀
  have hC₀conv : Convex ℝ C₀ := by
    have h1 : C₀ = W.subtype ⁻¹' ((fun x => c₀ + x) ⁻¹' C) := by
      ext w
      simp [C₀, add_comm]
    rw [h1]
    exact (hconv.translate_preimage_right c₀).linear_preimage W.subtype
  have hC₀cl : IsClosed C₀ := hCcl.preimage (continuous_subtype_val.add continuous_const)
  have hC₀bdd : Bornology.IsBounded C₀ := by
    obtain ⟨R, hR⟩ := hcpt.isBounded.subset_closedBall 0
    refine (isBounded_closedBall (x := (0 : W)) (r := R + ‖c₀‖)).subset ?_
    intro w hw
    have h1 := hR hw
    rw [mem_closedBall_zero_iff] at h1 ⊢
    calc ‖w‖ = ‖((w : E) + c₀) - c₀‖ := by simp
      _ ≤ ‖(w : E) + c₀‖ + ‖c₀‖ := norm_sub_le _ _
      _ ≤ R + ‖c₀‖ := by linarith
  have hC₀nhds : C₀ ∈ 𝓝 (0 : W) := by
    rw [Metric.mem_nhds_iff]
    refine ⟨ε, hε, fun w hw => ?_⟩
    have h1 := hball (w : E) w.2 (by simpa using hw)
    show (w : E) + c₀ ∈ C
    rwa [add_comm]
  have hint : ∀ w ∈ C₀, (w ∈ interior C₀ ↔ (w : E) + c₀ ∈ intrinsicInterior ℝ C) := by
    intro w hw
    rw [Plasticity.Topology.mem_intrinsicInterior_iff_ball C _, mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    constructor
    · rintro ⟨δ, hδ, hsub⟩
      refine ⟨δ, hδ, fun v hv hvδ => ?_⟩
      have h1 := hsub (show (w + ⟨v, hv⟩ : W) ∈ ball w δ by simpa [dist_eq_norm] using hvδ)
      have h2 : ((w + ⟨v, hv⟩ : W) : E) + c₀ = (w : E) + c₀ + v := by
        push_cast; abel
      rw [← h2]
      exact h1
    · rintro ⟨δ, hδ, h⟩
      refine ⟨δ, hδ, fun w' hw' => ?_⟩
      have h1 := h ((w' : E) - w) (Submodule.sub_mem _ w'.2 w.2)
        (by rw [mem_ball, dist_eq_norm] at hw'; simpa using hw')
      show (w' : E) + c₀ ∈ C
      convert h1 using 1
      abel
  have hbC₀ := NormedSpace.isVonNBounded_of_isBounded ℝ hC₀bdd
  have hbB := NormedSpace.isVonNBounded_ball ℝ W 1
  let h : W ≃ₜ W := gaugeRescaleHomeomorph C₀ (ball (0 : W) 1) hC₀conv hC₀nhds hbC₀
    (convex_ball 0 1) (ball_mem_nhds 0 one_pos) hbB
  have hh_int : h '' interior C₀ = ball 0 1 := by
    rw [image_gaugeRescaleHomeomorph_interior, isOpen_ball.interior_eq]
  have hh_cl : h '' C₀ = closedBall 0 1 := by
    have h1 := image_gaugeRescaleHomeomorph_closure hC₀conv hC₀nhds hbC₀ (convex_ball (0 : W) 1)
      (ball_mem_nhds 0 one_pos) hbB
    rwa [hC₀cl.closure_eq, closure_ball _ one_ne_zero] at h1
  obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional W
  refine ⟨fun z => (h.symm z : E) + c₀, fun y => h (P (y - c₀)), ?_, ?_, ?_, ?_⟩
  · exact (continuous_subtype_val.comp h.symm.continuous).add continuous_const
  · exact h.continuous.comp (P.continuous.comp (continuous_id.sub continuous_const))
  · intro z hz
    have hz' : z ∈ closedBall (0 : W) 1 := mem_closedBall_zero_iff.mpr hz
    have hsym : h.symm z ∈ C₀ := by
      rw [← hh_cl] at hz'
      obtain ⟨w, hw, rfl⟩ := hz'
      simpa using hw
    refine ⟨hsym, ?_, ?_⟩
    · simp [hP]
    · rw [Sol_Plasticity_Topology_exists_closedBall_model_of_convex_compact.frontier_eq_sdiff hCcl, mem_sdiff, ← hint _ hsym]
      constructor
      · rintro ⟨-, hni⟩
        by_contra hne1
        apply hni
        have h2 : z ∈ ball (0 : W) 1 := mem_ball_zero_iff.mpr (lt_of_le_of_ne hz hne1)
        rw [← hh_int] at h2
        obtain ⟨w, hw, hwz⟩ := h2
        rw [← hwz]
        simpa using hw
      · intro h1
        refine ⟨hsym, fun hi => ?_⟩
        have h2 : h (h.symm z) ∈ ball (0 : W) 1 := by
          rw [← hh_int]
          exact mem_image_of_mem _ hi
        rw [Homeomorph.apply_symm_apply, mem_ball_zero_iff, h1] at h2
        exact lt_irrefl _ h2
  · intro y hy
    have hyW : y - c₀ ∈ W := vsub_mem_vectorSpan ℝ hy hc₀C
    have hPy : P (y - c₀) = ⟨y - c₀, hyW⟩ := hP ⟨y - c₀, hyW⟩
    have hmem : (⟨y - c₀, hyW⟩ : W) ∈ C₀ := by
      show (y - c₀) + c₀ ∈ C
      simpa using hy
    refine ⟨?_, ?_⟩
    · have h1 : h ⟨y - c₀, hyW⟩ ∈ closedBall (0 : W) 1 := by
        rw [← hh_cl]
        exact mem_image_of_mem _ hmem
      simpa [hPy] using h1
    · simp [hPy]
