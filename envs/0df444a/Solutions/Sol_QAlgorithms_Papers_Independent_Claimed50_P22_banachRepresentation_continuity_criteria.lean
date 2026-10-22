-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P22.banachRepresentation_continuity_criteria
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:20:30.31731+00:00
-- url     : https://prove2.me/submissions/58f8d37a-8a93-45b9-8da4-6ebed582f235

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

theorem g67f2_joint (pi : G →* (V ≃L[K] V)) (hB : LocallyBoundedRepresentation pi)
    (hs : ∀ v : V, Continuous (fun g : G => pi g v)) :
    Continuous (fun p : G × V => pi p.1 p.2) := by
  obtain ⟨U, hU, C, hC0, hC⟩ := hB
  have hloc := g67f2_loc pi U hU C hC
  rw [continuous_iff_continuousAt]
  rintro ⟨g0, w0⟩
  set B := ‖(pi g0).toContinuousLinearMap‖ * C
  have hB : 0 ≤ B := by positivity
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hev1 := (continuous_fst.tendsto (g0, w0)).eventually
    (Metric.tendsto_nhds.mp ((hs w0).tendsto g0) (ε / 2) (by positivity))
  have hev2 := (continuous_fst.tendsto (g0, w0)).eventually (hloc g0)
  have hev3' := Metric.tendsto_nhds.mp (continuous_snd.tendsto (g0, w0)) (ε / (2 * (B + 1)))
    (by positivity)
  filter_upwards [hev1, hev2, hev3'] with p h1 h2 h3
  rw [dist_eq_norm] at h1 h3 ⊢
  have e : pi p.1 p.2 - pi g0 w0 = pi p.1 (p.2 - w0) + (pi p.1 w0 - pi g0 w0) := by
    simp only [map_sub]; abel
  have h4 := h2 (p.2 - w0)
  have h5 : (B + 1) * ‖p.2 - w0‖ < ε / 2 := by
    have hD : 0 < 2 * (B + 1) := by positivity
    rw [lt_div_iff₀ hD] at h3
    nlinarith
  calc ‖pi p.1 p.2 - pi g0 w0‖ ≤ ‖pi p.1 (p.2 - w0)‖ + ‖pi p.1 w0 - pi g0 w0‖ := by
        rw [e]; exact norm_add_le _ _
    _ < ε := by nlinarith [norm_nonneg (p.2 - w0)]

theorem g67f2_lb_of_joint (pi : G →* (V ≃L[K] V))
    (hc : Continuous (fun p : G × V => pi p.1 p.2)) : LocallyBoundedRepresentation pi := by
  have hS : (fun p : G × V => pi p.1 p.2) ⁻¹' Metric.ball 0 1 ∈ 𝓝 ((1 : G), (0 : V)) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using Metric.ball_mem_nhds (0 : V) one_pos
  obtain ⟨U, hU, W, hW, hUW⟩ := mem_nhds_prod_iff.mp hS
  obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.mp hW
  obtain ⟨k, hk⟩ := @NontriviallyNormedField.non_trivial K _
  refine ⟨U, hU, ‖k‖ / δ, by positivity, fun g hg => ?_⟩
  apply ContinuousLinearMap.opNorm_le_of_shell hδ (by positivity) hk
  intro x hx1 hx2
  have hxW : x ∈ W := hδW (mem_ball_zero_iff.mpr hx2)
  have h1 : ‖pi g x‖ < 1 := by
    have := hUW (Set.mk_mem_prod hg hxW)
    simpa using this
  have hk0 : 0 < ‖k‖ := by linarith
  have h2 : 1 ≤ ‖k‖ / δ * ‖x‖ := by
    rw [div_le_iff₀ hk0] at hx1
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    linarith
  show ‖pi g x‖ ≤ ‖k‖ / δ * ‖x‖
  linarith

theorem solution [CompleteSpace V]
    (pi : G →* (V ≃L[K] V)) :
    ((Continuous (fun p : G × V => pi p.1 p.2)) ↔
      (∀ v : V, ContinuousAt (fun p : G × V => pi p.1 p.2) (1, v))) ∧
    ((Continuous (fun p : G × V => pi p.1 p.2)) ↔
      (LocallyBoundedRepresentation pi ∧
        ∀ v : V, Continuous (fun g : G => pi g v))) ∧
    (TopologicalSpace.MetrizableSpace G →
      ((Continuous (fun p : G × V => pi p.1 p.2)) ↔
        (∀ v : V, Continuous (fun g : G => pi g v)))) := by
  have hstrong : Continuous (fun p : G × V => pi p.1 p.2) →
      ∀ v : V, Continuous (fun g : G => pi g v) := fun hc v =>
    hc.comp (continuous_id.prodMk continuous_const)
  refine ⟨⟨fun hc v => hc.continuousAt, fun hat => ?_⟩,
    ⟨fun hc => ⟨g67f2_lb_of_joint pi hc, hstrong hc⟩, fun h => g67f2_joint pi h.1 h.2⟩,
    fun hmet => ⟨hstrong, fun hs => ?_⟩⟩
  · rw [continuous_iff_continuousAt]
    rintro ⟨g0, v0⟩
    have heq : (fun p : G × V => pi p.1 p.2) =
        fun p : G × V => pi g0 (pi (g0⁻¹ * p.1) p.2) := by
      funext p
      show pi p.1 p.2 = pi g0 (pi (g0⁻¹ * p.1) p.2)
      have key : pi (g0 * (g0⁻¹ * p.1)) p.2 = pi g0 (pi (g0⁻¹ * p.1) p.2) := by
        rw [map_mul pi g0 (g0⁻¹ * p.1)]; rfl
      rw [← key, mul_inv_cancel_left]
    rw [heq]
    have hφ : ContinuousAt (fun p : G × V => (g0⁻¹ * p.1, p.2)) (g0, v0) :=
      ((continuous_const.mul continuous_fst).prodMk continuous_snd).continuousAt
    have h1 : ContinuousAt (fun p : G × V => pi (g0⁻¹ * p.1) p.2) (g0, v0) :=
      ContinuousAt.comp_of_eq (hat v0) hφ (by simp)
    exact (pi g0).continuous.continuousAt.comp h1
  · apply g67f2_joint pi _ hs
    haveI := hmet
    by_contra hnot
    simp only [LocallyBoundedRepresentation, not_exists, not_and, not_forall, not_le] at hnot
    obtain ⟨s, hsb⟩ := (𝓝 (1 : G)).exists_antitone_basis
    have hch : ∀ n : ℕ, ∃ g ∈ s n, ((n : ℝ) + 1) < ‖(pi g).toContinuousLinearMap‖ := by
      intro n
      obtain ⟨g, hg, hlt⟩ := hnot (s n) (hsb.mem n) ((n : ℝ) + 1) (by positivity)
      exact ⟨g, hg, hlt⟩
    choose g hgs hgn using hch
    have hgt : Tendsto g atTop (𝓝 1) := hsb.tendsto hgs
    obtain ⟨C', hC'⟩ := banach_steinhaus (g := fun n => (pi (g n)).toContinuousLinearMap)
      (fun v => by
        have ht : Tendsto (fun n => pi (g n) v) atTop (𝓝 (pi 1 v)) :=
          ((hs v).tendsto 1).comp hgt
        obtain ⟨C, hC⟩ := ht.norm.bddAbove_range
        exact ⟨C, fun n => hC ⟨n, rfl⟩⟩)
    have h1 := hgn (⌈C'⌉₊)
    have h2 := hC' (⌈C'⌉₊)
    have h3 := Nat.le_ceil C'
    linarith
