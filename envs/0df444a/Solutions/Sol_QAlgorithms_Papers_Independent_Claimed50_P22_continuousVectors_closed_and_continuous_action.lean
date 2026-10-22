-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P22.continuousVectors_closed_and_continuous_action
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:19:44.708244+00:00
-- url     : https://prove2.me/submissions/7900328d-9f0f-46b2-9480-66f10654475f

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22
open QAlgorithms.Papers.Independent.Claimed50.P22

open Set Filter Topology

universe u v w z

section BanachRepresentations

variable {K : Type u} [RCLike K]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {V : Type w} [NormedAddCommGroup V] [NormedSpace K V]

theorem g67f2_loc (pi : G →* (V ≃L[K] V)) (U : Set G) (hU : U ∈ 𝓝 (1 : G)) (C : ℝ)
    (hC : ∀ g ∈ U, ‖(pi g).toContinuousLinearMap‖ ≤ C) (g0 : G) :
    ∀ᶠ g in 𝓝 g0, ∀ x : V, ‖pi g x‖ ≤ ‖(pi g0).toContinuousLinearMap‖ * C * ‖x‖ := by
  have hmem : {g : G | g0⁻¹ * g ∈ U} ∈ 𝓝 g0 := by
    have hc : ContinuousAt (fun g : G => g0⁻¹ * g) g0 :=
      (continuous_const.mul continuous_id).continuousAt
    have : U ∈ 𝓝 (g0⁻¹ * g0) := by rw [inv_mul_cancel]; exact hU
    exact hc.preimage_mem_nhds this
  filter_upwards [hmem] with g hg x
  have he : pi g x = pi g0 (pi (g0⁻¹ * g) x) := by
    conv_lhs => rw [show g = g0 * (g0⁻¹ * g) by group]
    rw [map_mul]; rfl
  rw [he]
  have h1 : ‖pi g0 (pi (g0⁻¹ * g) x)‖ ≤ ‖(pi g0).toContinuousLinearMap‖ * ‖pi (g0⁻¹ * g) x‖ :=
    (pi g0).toContinuousLinearMap.le_opNorm _
  have h2 : ‖pi (g0⁻¹ * g) x‖ ≤ C * ‖x‖ :=
    ((pi (g0⁻¹ * g)).toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hC _ hg) (norm_nonneg _))
  calc _ ≤ _ := h1
    _ ≤ ‖(pi g0).toContinuousLinearMap‖ * (C * ‖x‖) := by gcongr
    _ = _ := by ring

theorem solution [CompleteSpace V]
    (pi : G →* (V ≃L[K] V)) (hBound : LocallyBoundedRepresentation pi) :
    IsClosed (ContinuousVectors pi) ∧
    (∀ g : G, ∀ v ∈ ContinuousVectors pi, pi g v ∈ ContinuousVectors pi) ∧
    Continuous (fun p : G × {v : V // v ∈ ContinuousVectors pi} => pi p.1 p.2.val) ∧
    (∃ U : Set G, U ∈ 𝓝 (1 : G) ∧ ∃ C : ℝ, 0 < C ∧
      ∀ g ∈ U, ∀ v ∈ ContinuousVectors pi, ‖pi g v‖ ≤ C * ‖v‖) := by
  obtain ⟨U, hU, C, hC0, hC⟩ := hBound
  have hloc := g67f2_loc pi U hU C hC
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- closedness
    rw [← closure_subset_iff_isClosed]
    intro v hv
    show Continuous (fun g : G => pi g v)
    rw [continuous_iff_continuousAt]
    intro g0
    set B := ‖(pi g0).toContinuousLinearMap‖ * C
    set A0 := ‖(pi g0).toContinuousLinearMap‖
    have hB : 0 ≤ B := by positivity
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    have hD : 0 < 3 * (B + A0 + 1) := by positivity
    obtain ⟨w, hw, hvw⟩ := Metric.mem_closure_iff.mp hv (ε / (3 * (B + A0 + 1))) (by positivity)
    have hwc : Continuous (fun g : G => pi g w) := hw
    have hev := Metric.tendsto_nhds.mp (hwc.tendsto g0) (ε / 3) (by positivity)
    filter_upwards [hev, hloc g0] with g hg1 hg2
    rw [dist_eq_norm] at hg1 hvw ⊢
    have e : pi g v - pi g0 v = pi g (v - w) + (pi g w - pi g0 w) + pi g0 (w - v) := by
      simp only [map_sub]; abel
    have h3 : ‖pi g0 (w - v)‖ ≤ A0 * ‖v - w‖ := by
      have := (pi g0).toContinuousLinearMap.le_opNorm (w - v)
      rw [norm_sub_rev w v] at this
      exact this
    have h4 := hg2 (v - w)
    have h5 : (B + A0 + 1) * ‖v - w‖ < ε / 3 := by
      rw [lt_div_iff₀ hD] at hvw
      have : 0 < B + A0 + 1 := by positivity
      nlinarith
    calc ‖pi g v - pi g0 v‖ ≤ ‖pi g (v - w)‖ + ‖pi g w - pi g0 w‖ + ‖pi g0 (w - v)‖ := by
          rw [e]; exact norm_add₃_le
      _ < ε := by nlinarith [norm_nonneg (v - w)]
  · intro g v hv
    show Continuous (fun h : G => pi h (pi g v))
    have : (fun h : G => pi h (pi g v)) = fun h => pi (h * g) v := by
      funext h; rw [map_mul]; rfl
    rw [this]
    exact (hv : Continuous fun g => pi g v).comp (continuous_id.mul continuous_const)
  · rw [continuous_iff_continuousAt]
    rintro ⟨g0, w0, hw0⟩
    set B := ‖(pi g0).toContinuousLinearMap‖ * C
    have hB : 0 ≤ B := by positivity
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    have hwc : Continuous (fun g : G => pi g w0) := hw0
    have hev1 := (continuous_fst.tendsto (g0, (⟨w0, hw0⟩ : {v : V // v ∈ ContinuousVectors pi}))).eventually
      (Metric.tendsto_nhds.mp (hwc.tendsto g0) (ε / 2) (by positivity))
    have hev2 := (continuous_fst.tendsto (g0, (⟨w0, hw0⟩ : {v : V // v ∈ ContinuousVectors pi}))).eventually
      (hloc g0)
    have hev3 := (continuous_subtype_val.comp continuous_snd).tendsto
      (g0, (⟨w0, hw0⟩ : {v : V // v ∈ ContinuousVectors pi}))
    have hev3' := Metric.tendsto_nhds.mp hev3 (ε / (2 * (B + 1))) (by positivity)
    filter_upwards [hev1, hev2, hev3'] with p h1 h2 h3
    simp only [Function.comp] at h1 h2 h3 ⊢
    rw [dist_eq_norm] at h1 h3 ⊢
    have e : pi p.1 p.2.val - pi g0 w0 = pi p.1 (p.2.val - w0) + (pi p.1 w0 - pi g0 w0) := by
      simp only [map_sub]; abel
    have h4 := h2 (p.2.val - w0)
    have h5 : (B + 1) * ‖p.2.val - w0‖ < ε / 2 := by
      have hD : 0 < 2 * (B + 1) := by positivity
      rw [lt_div_iff₀ hD] at h3
      nlinarith
    calc ‖pi p.1 p.2.val - pi g0 w0‖ ≤ ‖pi p.1 (p.2.val - w0)‖ + ‖pi p.1 w0 - pi g0 w0‖ := by
          rw [e]; exact norm_add_le _ _
      _ < ε := by nlinarith [norm_nonneg (p.2.val - w0)]
  · refine ⟨U, hU, C, hC0, fun g hg v _ => ?_⟩
    exact ((pi g).toContinuousLinearMap.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hC g hg) (norm_nonneg _))

end BanachRepresentations
