-- Prove2me | solution 1 for RobinsonNSIFT.Implicit.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:02:55.7805+00:00
-- url     : https://prove2.me/submissions/447e6204-10e5-4f38-bea9-6fcfc1f1b703

import Mathlib
import Definitions.Def_RobinsonNSIFT_Implicit_Basic

set_option autoImplicit false
open Set Filter Topology Metric
open scoped NNReal
open RobinsonNSIFT.Implicit

theorem rob_lemma_3_1 {X Y : Type*} [MetricSpace X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Ω : Set X) (hΩ : IsOpen Ω) (f h : X → Y) (η : ℝ≥0) (hh : LipschitzOnWith η h Ω)
    (x₀ : X) (hx₀ : x₀ ∈ Ω) (y₀ : Y) (hfx₀ : f x₀ = y₀) (α δ : ℝ)
    (hδ : ExpansionAtLeast f Ω δ)
    (h1 : closedBall y₀ α ⊆ f '' Ω)
    (h2 : (η : ℝ) < δ)
    (h3 : closedBall x₀ (α / δ) ⊆ Ω)
    (h4 : 0 ≤ (1 - η / δ) * α - ‖h x₀‖) :
    closedBall y₀ ((1 - η / δ) * α - ‖h x₀‖) ⊆ (f + h) '' closedBall x₀ (α / δ) ∧
      ExpansionAtLeast (f + h) Ω (δ - η) ∧ 0 < δ - η := by
  have hη0 : (0 : ℝ) ≤ η := η.coe_nonneg
  have hδpos : 0 < δ := lt_of_le_of_lt hη0 h2
  haveI : Nonempty X := ⟨x₀⟩
  have hα0 : 0 ≤ α / δ := by
    have hpos : 0 < 1 - η / δ := by
      have := (div_lt_one hδpos).mpr h2
      linarith
    have : 0 ≤ α := by
      by_contra hneg
      push_neg at hneg
      nlinarith [norm_nonneg (h x₀), mul_neg_of_pos_of_neg hpos hneg]
    positivity
  refine ⟨?_, ?_, by linarith⟩
  · intro y hy
    rw [mem_closedBall] at hy
    set B : Set X := closedBall x₀ (α / δ) with hB
    set g : X → X := fun x => Function.invFunOn f Ω (y - h x) with hg
    -- key facts
    have hzmem : ∀ x ∈ B, y - h x ∈ closedBall y₀ α := by
      intro x hxB
      rw [mem_closedBall] at hxB ⊢
      have hxΩ : x ∈ Ω := h3 hxB
      have hlip := hh.dist_le_mul x hxΩ x₀ hx₀
      have e1 : dist (y - h x) y₀ ≤ dist y y₀ + dist (h x) (h x₀) + ‖h x₀‖ := by
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
        have : y - h x - y₀ = (y - y₀) - (h x - h x₀) - h x₀ := by abel
        rw [this]
        calc ‖(y - y₀) - (h x - h x₀) - h x₀‖ ≤ ‖(y - y₀) - (h x - h x₀)‖ + ‖h x₀‖ := norm_sub_le _ _
          _ ≤ ‖y - y₀‖ + ‖h x - h x₀‖ + ‖h x₀‖ := by gcongr; exact norm_sub_le _ _
      have e2 : (η : ℝ) * dist x x₀ ≤ η * (α / δ) := mul_le_mul_of_nonneg_left hxB hη0
      have e3 : (η : ℝ) * (α / δ) = η / δ * α := by ring
      nlinarith
    have hgx : ∀ x ∈ B, g x ∈ Ω ∧ f (g x) = y - h x := by
      intro x hxB
      obtain ⟨a, ha, hfa⟩ := h1 (hzmem x hxB)
      exact Function.invFunOn_pos ⟨a, ha, hfa⟩
    have hmaps : Set.MapsTo g B B := by
      intro x hxB
      obtain ⟨hgΩ, hgf⟩ := hgx x hxB
      have := hδ _ hgΩ x₀ hx₀
      rw [hgf, hfx₀] at this
      have h5 : dist (y - h x) y₀ ≤ α := mem_closedBall.mp (hzmem x hxB)
      rw [hB, mem_closedBall, le_div_iff₀ hδpos]
      linarith
    have hK : ((Real.toNNReal ((η : ℝ) / δ) : ℝ≥0) : ℝ) = η / δ :=
      Real.coe_toNNReal _ (div_nonneg hη0 hδpos.le)
    have hKlt : Real.toNNReal ((η : ℝ) / δ) < 1 := by
      rw [← NNReal.coe_lt_coe, hK]
      simpa using (div_lt_one hδpos).mpr h2
    have hcontr : ContractingWith (Real.toNNReal ((η : ℝ) / δ)) (hmaps.restrict g B B) := by
      refine ⟨hKlt, LipschitzWith.of_dist_le_mul fun x x' => ?_⟩
      obtain ⟨hgΩ, hgf⟩ := hgx x.1 x.2
      obtain ⟨hgΩ', hgf'⟩ := hgx x'.1 x'.2
      have := hδ _ hgΩ _ hgΩ'
      rw [hgf, hgf'] at this
      have e1 : dist (y - h x.1) (y - h x'.1) = dist (h x.1) (h x'.1) := by
        exact dist_sub_left _ _ _
      have e2 := hh.dist_le_mul x.1 (h3 x.2) x'.1 (h3 x'.2)
      rw [hK]
      simp only [MapsTo.restrict, Subtype.dist_eq]
      show dist (g x.1) (g x'.1) ≤ η / δ * dist x.1 x'.1
      rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]
      nlinarith
    have hBc : IsComplete B := (isClosed_closedBall).isComplete
    obtain ⟨x, hxB, hfix, -⟩ := hcontr.exists_fixedPoint' hBc hmaps (x := x₀)
      (mem_closedBall_self hα0) (edist_ne_top _ _)
    refine ⟨x, hxB, ?_⟩
    obtain ⟨-, hgf⟩ := hgx x hxB
    have : g x = x := hfix
    rw [this] at hgf
    simp only [Pi.add_apply, hgf]
    abel
  · intro x₁ hx₁ x₂ hx₂
    have := hδ x₁ hx₁ x₂ hx₂
    have e2 := hh.dist_le_mul x₁ hx₁ x₂ hx₂
    have e3 : dist (f x₁) (f x₂) ≤ dist ((f + h) x₁) ((f + h) x₂) + dist (h x₁) (h x₂) := by
      simp only [Pi.add_apply]
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
      calc ‖f x₁ - f x₂‖ = ‖(f x₁ + h x₁ - (f x₂ + h x₂)) - (h x₁ - h x₂)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    nlinarith

theorem rob_eq_3_1_3_2 {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (x₀ : X) (y₀ : Y) (Ξ : Set X) (H : Set Y) (hΞ : Ξ ∈ 𝓝 x₀) (hH : H ∈ 𝓝 y₀)
    (F : X → Y → Z) (hF₀ : F x₀ y₀ = 0) (f : X → Z) (hf₀ : f x₀ = 0)
    (ha : StronglyApproxInX f F x₀ y₀)
    (φ : ℝ≥0) (hb : ∀ x ∈ Ξ, LipschitzOnWith φ (F x) H)
    (hc : f '' Ξ ∈ 𝓝 (0 : Z))
    (d₀ : ℝ) (hd₀ : 0 < d₀) (hd : ExpansionAtLeast f Ξ d₀) :
    ∀ ε : ℝ, 0 < ε → ε < d₀ → ∃ α > (0 : ℝ), ∃ κ > (0 : ℝ), ∃ V ∈ 𝓝 y₀, V ⊆ H ∧
      closedBall x₀ (α / d₀) ⊆ Ξ ∧
      ∀ y ∈ V, ExpansionAtLeast (fun x => F x y) (closedBall x₀ (α / d₀)) (d₀ - ε) ∧
        closedBall (0 : Z) ((1 - ε / d₀) * α - ‖F x₀ y‖) ⊆
          (fun x => F x y) '' closedBall x₀ (α / d₀) ∧
        κ ≤ (1 - ε / d₀) * α - ‖F x₀ y‖ := by
  intro ε hε hεd
  obtain ⟨U, hU, V₁, hV₁, hUV⟩ := ha ε hε
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hΞ hU)
  obtain ⟨r₂', hr₂', hr₂sub⟩ := Metric.mem_nhds_iff.mp hc
  set r₂ : ℝ := r₂' / 2 with hr₂
  have hr₂pos : 0 < r₂ := by positivity
  set α : ℝ := min (d₀ * r / 2) r₂ with hα
  have hαpos : 0 < α := lt_min (by positivity) hr₂pos
  have hα1 : α ≤ d₀ * r / 2 := min_le_left _ _
  have hα2 : α ≤ r₂ := min_le_right _ _
  have hαd : α / d₀ ≤ r / 2 := by
    rw [div_le_iff₀ hd₀]; linarith
  have hεd0 : 0 < 1 - ε / d₀ := by
    have := (div_lt_one hd₀).mpr hεd
    linarith
  set Ω : Set X := ball x₀ r with hΩ
  have hΩΞ : Ω ⊆ Ξ := fun x hx => (hrsub hx).1
  have hΩU : Ω ⊆ U := fun x hx => (hrsub hx).2
  have hx₀Ω : x₀ ∈ Ω := mem_ball_self hr
  have hx₀Ξ : x₀ ∈ Ξ := hΩΞ hx₀Ω
  have hball : closedBall x₀ (α / d₀) ⊆ Ω := by
    intro x hx
    rw [mem_closedBall] at hx
    rw [hΩ, mem_ball]
    linarith
  have hfΩ : closedBall (0 : Z) α ⊆ f '' Ω := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    have hz' : z ∈ f '' Ξ := hr₂sub (by rw [mem_ball, dist_zero_right]; linarith)
    obtain ⟨a, haΞ, rfl⟩ := hz'
    refine ⟨a, ?_, rfl⟩
    have := hd a haΞ x₀ hx₀Ξ
    rw [hf₀, dist_zero_right] at this
    have h5 : dist a x₀ ≤ α / d₀ := by rw [le_div_iff₀ hd₀]; linarith
    rw [hΩ, mem_ball]
    linarith
  -- the neighbourhood in y
  set ρ : ℝ := (1 - ε / d₀) * α / (2 * (φ + 1)) with hρ
  have hρpos : 0 < ρ := by positivity
  refine ⟨α, hαpos, (1 - ε / d₀) * α / 2, by positivity,
    V₁ ∩ H ∩ ball y₀ ρ, inter_mem (inter_mem hV₁ hH) (ball_mem_nhds y₀ hρpos),
    fun y hy => hy.1.2, fun x hx => hΩΞ (hball hx), ?_⟩
  intro y hy
  obtain ⟨⟨hyV, hyH⟩, hyρ⟩ := hy
  -- Lipschitz bound for h
  set h : X → Z := fun x => F x y - f x with hh
  have hhΩ : LipschitzOnWith ε.toNNReal h Ω := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' => ?_
    have := hUV x (hΩU hx) x' (hΩU hx') y hyV
    rw [dist_eq_norm, dist_eq_norm]
    simpa [hh, Real.coe_toNNReal _ hε.le] using this
  have hfh : (f + h) = fun x => F x y := by
    funext x; simp [hh]
  have hhx₀ : ‖h x₀‖ = ‖F x₀ y‖ := by simp [hh, hf₀]
  have hexp : ExpansionAtLeast f Ω d₀ := fun x₁ hx₁ x₂ hx₂ => hd x₁ (hΩΞ hx₁) x₂ (hΩΞ hx₂)
  have hFy : ‖F x₀ y‖ ≤ φ * ρ := by
    have := (hb x₀ hx₀Ξ).dist_le_mul y hyH y₀ (mem_of_mem_nhds hH)
    rw [hF₀, dist_zero_right] at this
    have hd2 : dist y y₀ ≤ ρ := (mem_ball.mp hyρ).le
    calc ‖F x₀ y‖ ≤ φ * dist y y₀ := this
      _ ≤ φ * ρ := mul_le_mul_of_nonneg_left hd2 φ.coe_nonneg
  have hφρ : (φ : ℝ) * ρ ≤ (1 - ε / d₀) * α / 2 := by
    rw [hρ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0:ℝ) ≤ (1 - ε / d₀) * α := by positivity
    nlinarith [φ.coe_nonneg]
  have hT : 0 < (1 - ε / d₀) * α := by positivity
  have h4 : 0 ≤ (1 - (ε.toNNReal : ℝ) / d₀) * α - ‖h x₀‖ := by
    rw [Real.coe_toNNReal _ hε.le, hhx₀]; linarith
  obtain ⟨hcov, hexp', -⟩ := rob_lemma_3_1 Ω isOpen_ball f h ε.toNNReal hhΩ x₀ hx₀Ω 0 hf₀ α d₀ hexp
    hfΩ (by rw [Real.coe_toNNReal _ hε.le]; exact hεd)
    hball h4
  rw [hfh, Real.coe_toNNReal _ hε.le, hhx₀] at hcov
  rw [hfh, Real.coe_toNNReal _ hε.le] at hexp'
  refine ⟨fun x₁ hx₁ x₂ hx₂ => hexp' x₁ (hball hx₁) x₂ (hball hx₂), hcov, ?_⟩
  linarith

theorem solution {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (x₀ : X) (y₀ : Y) (Ξ : Set X) (H : Set Y) (hΞ : Ξ ∈ 𝓝 x₀) (hH : H ∈ 𝓝 y₀)
    (F : X → Y → Z) (hF₀ : F x₀ y₀ = 0) (f : X → Z) (hf₀ : f x₀ = 0)
    (ha : StronglyApproxInX f F x₀ y₀)
    (φ : ℝ≥0) (hb : ∀ x ∈ Ξ, LipschitzOnWith φ (F x) H)
    (hc : f '' Ξ ∈ 𝓝 (0 : Z))
    (d₀ : ℝ) (hd₀ : 0 < d₀) (hd : ExpansionAtLeast f Ξ d₀)
    (lam : ℝ≥0) (hlam : (φ : ℝ) / d₀ < lam) :
    ∃ U ∈ 𝓝 x₀, ∃ V ∈ 𝓝 y₀, U ⊆ Ξ ∧ V ⊆ H ∧ ∃ x : Y → X, Set.MapsTo x V U ∧
      x y₀ = x₀ ∧ LipschitzOnWith lam x V ∧
      ∀ y ∈ V, F (x y) y = 0 ∧ ∀ x' ∈ U, F x' y = 0 → x' = x y := by
  have hφ0 : (0 : ℝ) ≤ φ := φ.coe_nonneg
  have hlam0 : (0 : ℝ) < lam := lt_of_le_of_lt (div_nonneg hφ0 hd₀.le) hlam
  have hlamd : (φ : ℝ) < lam * d₀ := by
    rw [div_lt_iff₀ hd₀] at hlam; exact hlam
  set ε : ℝ := (lam * d₀ - φ) / (2 * lam) with hε
  have hε0 : 0 < ε := by rw [hε]; apply div_pos <;> linarith
  have hεd : ε < d₀ := by
    rw [hε, div_lt_iff₀ (by linarith)]; nlinarith
  have hde : (φ : ℝ) ≤ lam * (d₀ - ε) := by
    have : lam * (d₀ - ε) = (lam * d₀ + φ) / 2 := by
      rw [hε]; field_simp; ring
    rw [this]; linarith
  have hde0 : 0 < d₀ - ε := by linarith
  obtain ⟨α, hα, κ, hκ, V, hV, hVH, hball, hmain⟩ :=
    rob_eq_3_1_3_2 x₀ y₀ Ξ H hΞ hH F hF₀ f hf₀ ha φ hb hc d₀ hd₀ hd ε hε0 hεd
  set U : Set X := closedBall x₀ (α / d₀) with hU
  have hUn : U ∈ 𝓝 x₀ := closedBall_mem_nhds _ (by positivity)
  have hex : ∀ y ∈ V, ∃ x' ∈ U, F x' y = 0 := by
    intro y hy
    obtain ⟨-, hcov, hθ⟩ := hmain y hy
    have : (0 : Z) ∈ closedBall (0 : Z) ((1 - ε / d₀) * α - ‖F x₀ y‖) := by
      rw [mem_closedBall, dist_self]; linarith
    obtain ⟨x', hx', hFx'⟩ := hcov this
    exact ⟨x', hx', hFx'⟩
  have hinj : ∀ y ∈ V, ∀ x₁ ∈ U, ∀ x₂ ∈ U, F x₁ y = 0 → F x₂ y = 0 → x₁ = x₂ := by
    intro y hy x₁ hx₁ x₂ hx₂ h1 h2
    have := (hmain y hy).1 x₁ hx₁ x₂ hx₂
    simp only [h1, h2, dist_self] at this
    have : dist x₁ x₂ ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      nlinarith [mul_pos hde0 hcon]
    exact dist_le_zero.mp this
  classical
  let xf : Y → X := fun y => if h : y ∈ V then Classical.choose (hex y h) else x₀
  have hxf : ∀ y (h : y ∈ V), xf y ∈ U ∧ F (xf y) y = 0 := by
    intro y h
    have := Classical.choose_spec (hex y h)
    simpa [xf, h] using this
  have hy₀V : y₀ ∈ V := mem_of_mem_nhds hV
  have hx₀U : x₀ ∈ U := mem_closedBall_self (by positivity)
  refine ⟨U, hUn, V, hV, fun x hx => (hball hx), hVH, xf, fun y hy => (hxf y hy).1, ?_, ?_, ?_⟩
  · exact (hinj y₀ hy₀V _ (hxf y₀ hy₀V).1 _ hx₀U (hxf y₀ hy₀V).2 hF₀)
  · refine LipschitzOnWith.of_dist_le_mul fun y₁ hy₁ y₂ hy₂ => ?_
    obtain ⟨hx1, hf1⟩ := hxf y₁ hy₁
    obtain ⟨hx2, hf2⟩ := hxf y₂ hy₂
    have h1 := (hmain y₁ hy₁).1 _ hx1 _ hx2
    have h2 := (hb _ (hball hx2)).dist_le_mul y₂ (hVH hy₂) y₁ (hVH hy₁)
    beta_reduce at h1
    rw [hf1] at h1
    rw [hf2] at h2
    have h5 : (d₀ - ε) * dist (xf y₁) (xf y₂) ≤ φ * dist y₂ y₁ := by
      linarith
    have h6 : (d₀ - ε) * dist (xf y₁) (xf y₂) ≤ (d₀ - ε) * (lam * dist y₁ y₂) := by
      calc (d₀ - ε) * dist (xf y₁) (xf y₂) ≤ φ * dist y₂ y₁ := h5
        _ ≤ lam * (d₀ - ε) * dist y₁ y₂ := by
          rw [dist_comm y₂ y₁]; exact mul_le_mul_of_nonneg_right hde dist_nonneg
        _ = (d₀ - ε) * (lam * dist y₁ y₂) := by ring
    exact le_of_mul_le_mul_left h6 hde0
  · intro y hy
    refine ⟨(hxf y hy).2, fun x' hx' hFx' => ?_⟩
    exact hinj y hy x' hx' _ (hxf y hy).1 hFx' (hxf y hy).2
