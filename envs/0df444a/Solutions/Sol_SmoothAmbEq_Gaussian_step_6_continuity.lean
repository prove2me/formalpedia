-- Prove2me | solution 1 for SmoothAmbEq.Gaussian.step_6_continuity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T20:03:01.419803+00:00
-- url     : https://prove2.me/submissions/14bac30e-48d0-412e-ac44-6a2376245aaf

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate
import Theorems.Thm_SmoothAmbEq_Gaussian_lemma_C_1

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace SmoothAmbS6Aux

open SmoothAmbEq.Gaussian

/-- Every set of the (unaugmented) shifted Brownian filtration is null-measurable, hence a
function adapted to it is a.e.-measurable for the ambient σ-algebra. -/
lemma aem_of_shift {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianReal W P) (t : ℝ) (v : ℝ≥0) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable[shiftFiltration W t v] f P) : AEMeasurable f P := by
  obtain ⟨g, hg, hfg⟩ := hf
  have hle : ∀ A, MeasurableSet[shiftFiltration W t v] A → NullMeasurableSet A P := by
    have h0 : shiftFiltration W t v ≤
        (show MeasurableSpace Ω from NullMeasurableSpace.instMeasurableSpace (μ := P)) := by
      unfold shiftFiltration
      refine iSup₂_le fun u _ => ?_
      rw [MeasurableSpace.comap_le_iff_le_map]
      intro B hB
      have hae : AEMeasurable (shiftBM W t u) P := by
        unfold shiftBM
        exact (hW.aemeasurable _).sub (hW.aemeasurable _)
      exact hae.nullMeasurable hB
    intro A hA
    exact h0 A hA
  have hgn : NullMeasurable g P := by
    intro B hB
    exact hle _ (hg.measurable hB)
  exact (hgn.aemeasurable).congr hfg.symm

/-- Bound on the quadratic form `f^z(s, β)` by `A + B β²`. -/
lemma fz_le (c : Coeffs) (z s β Bd : ℝ) (hBd : 0 ≤ Bd)
    (h1 : |c.m₁ s| ≤ Bd) (h2 : |c.m₂ s| ≤ Bd) (h3 : |c.m₃ s| ≤ Bd) (h4 : |c.m₄ s| ≤ Bd)
    (h5 : |c.m₅ s| ≤ Bd) (h6 : |c.m₆ s| ≤ Bd) :
    fz c z s β ≤ Bd * (z ^ 2 + 2 * |z| + 2) + (Bd * (1 + |z|) + 1) * β ^ 2 := by
  unfold fz
  have hb : |β| ≤ (1 + β ^ 2) / 2 := by
    nlinarith [sq_nonneg (|β| - 1), sq_abs β, abs_nonneg β]
  have t1 : 1 / 2 * c.m₁ s * β ^ 2 ≤ 1 / 2 * Bd * β ^ 2 := by
    have := (abs_le.1 h1).2
    nlinarith [sq_nonneg β]
  have t2 : c.m₂ s * β * z ≤ Bd * |z| * ((1 + β ^ 2) / 2) := by
    have e : c.m₂ s * β * z ≤ |c.m₂ s| * |β| * |z| := by
      have := le_abs_self (c.m₂ s * β * z)
      rw [abs_mul, abs_mul] at this; exact this
    have : |c.m₂ s| * |β| * |z| ≤ Bd * ((1 + β ^ 2) / 2) * |z| :=
      mul_le_mul_of_nonneg_right (mul_le_mul h2 hb (abs_nonneg _) hBd) (abs_nonneg _)
    nlinarith
  have t3 : 1 / 2 * c.m₃ s * z ^ 2 ≤ 1 / 2 * Bd * z ^ 2 := by
    have := (abs_le.1 h3).2
    nlinarith [sq_nonneg z]
  have t4 : c.m₄ s * β ≤ Bd * ((1 + β ^ 2) / 2) := by
    have e : c.m₄ s * β ≤ |c.m₄ s| * |β| := by
      have := le_abs_self (c.m₄ s * β); rw [abs_mul] at this; exact this
    have : |c.m₄ s| * |β| ≤ Bd * ((1 + β ^ 2) / 2) := mul_le_mul h4 hb (abs_nonneg _) hBd
    linarith
  have t5 : c.m₅ s * z ≤ Bd * |z| := by
    have e : c.m₅ s * z ≤ |c.m₅ s| * |z| := by
      have := le_abs_self (c.m₅ s * z); rw [abs_mul] at this; exact this
    have : |c.m₅ s| * |z| ≤ Bd * |z| := mul_le_mul_of_nonneg_right h5 (abs_nonneg _)
    linarith
  have t6 : c.m₆ s ≤ Bd := (abs_le.1 h6).2
  have hz : 0 ≤ |z| := abs_nonneg z
  have hβ2 : 0 ≤ β ^ 2 := sq_nonneg β
  nlinarith [mul_nonneg hBd hz, mul_nonneg (mul_nonneg hBd hz) hβ2]

/-- `|g^z|^p ≤ k^{-p}(½ e^{-2p k e X} + ½ e^{2p f})`. -/
lemma gz_rpow_le (M : Model) (c : Coeffs) (z s X b p : ℝ) :
    |gz M c z s X b| ^ p ≤ (1 / M.k) ^ p *
      (1 / 2 * Real.exp (-(2 * p) * M.k * Real.exp (M.r * (M.T - s)) * X)
        + 1 / 2 * Real.exp ((2 * p) * fz c z s b)) := by
  have hk := M.hk
  have habs : |gz M c z s X b| = 1 / M.k * Real.exp (-M.k * Real.exp (M.r * (M.T - s)) * X
      + fz c z s b) := by
    unfold gz
    rw [abs_mul, abs_neg, abs_of_pos (by positivity), abs_of_pos (Real.exp_pos _)]
  rw [habs, Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  set a := -M.k * Real.exp (M.r * (M.T - s)) * X
  set f := fz c z s b
  have e1 : (a + f) * p = p * a + p * f := by ring
  have e2 : -(2 * p) * M.k * Real.exp (M.r * (M.T - s)) * X = 2 * (p * a) := by
    simp only [a]; ring
  rw [e1, e2, Real.exp_add]
  have h2 : Real.exp (2 * (p * a)) = Real.exp (p * a) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  have h3 : Real.exp (2 * p * f) = Real.exp (p * f) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [h2, h3]
  nlinarith [sq_nonneg (Real.exp (p * a) - Real.exp (p * f))]

/-- Tail inequality: for `y ≥ K/2 > 0` and `p > 1`, `y ≤ y^p / (K/2)^{p-1}`. -/
lemma tail_le {y K p : ℝ} (hK : 0 < K) (hy : K / 2 ≤ y) (hp : 1 < p) :
    y ≤ y ^ p / (K / 2) ^ (p - 1) := by
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  rw [le_div_iff₀ (by positivity)]
  have : (K / 2) ^ (p - 1) ≤ y ^ (p - 1) :=
    Real.rpow_le_rpow (by positivity) hy (by linarith)
  calc y * (K / 2) ^ (p - 1) ≤ y * y ^ (p - 1) := mul_le_mul_of_nonneg_left this hy0.le
    _ = y ^ p := by
      rw [← Real.rpow_one_add' hy0.le (by linarith)]
      congr 1; ring

lemma integ_of_lint {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ}
    (hf : AEMeasurable f P) (hpos : ∀ ω, 0 ≤ f ω) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) ≤ ENNReal.ofReal C) :
    Integrable f P ∧ ∫ ω, f ω ∂P ≤ C := by
  have hint : Integrable f P := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hpos)]
    exact lt_of_le_of_lt hC ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hpos) hf.aestronglyMeasurable]
  calc (∫⁻ ω, ENNReal.ofReal (f ω) ∂P).toReal ≤ (ENNReal.ofReal C).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hC
    _ = C := ENNReal.toReal_ofReal hC0

lemma aem_beta {Ω : Type*} [MeasurableSpace Ω] (M : Model) (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (z t β u : ℝ) :
    AEMeasurable (fun ω => betaZ M W z t β u ω) P := by
  have h1 := hW.aemeasurable u.toNNReal
  have h2 := hW.aemeasurable t.toNNReal
  unfold betaZ
  fun_prop

lemma meas_gz (M : Model) (c : Coeffs) (z s : ℝ) :
    Measurable (fun q : ℝ × ℝ => gz M c z s q.1 q.2) := by
  unfold gz fz
  fun_prop

lemma bdd_on {f : ℝ → ℝ} {T : ℝ} (hf : ContinuousOn f (Icc 0 T)) :
    ∃ B, 0 ≤ B ∧ ∀ s ∈ Icc 0 T, |f s| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine ⟨max B 0, le_max_right _ _, fun s hs => ?_⟩
  have := hB s hs
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- Pointwise splitting used for uniform integrability. -/
lemma split_le {y y₀ K p : ℝ} (hK : 0 < K) (hK2 : 2 * |y₀| ≤ K) (hp : 1 < p) :
    |y - y₀| ≤ min |y - y₀| K + 2 * (|y| ^ p / (K / 2) ^ (p - 1)) := by
  have hnn : 0 ≤ |y| ^ p / (K / 2) ^ (p - 1) := by positivity
  by_cases hD : |y - y₀| ≤ K
  · rw [min_eq_left hD]; linarith
  · push_neg at hD
    have hy : K / 2 ≤ |y| := by
      have := abs_sub_abs_le_abs_sub y y₀
      have h2 : |y - y₀| ≤ |y| + |y₀| := abs_sub _ _
      linarith
    have ht := tail_le hK hy hp
    have h2 : |y - y₀| ≤ |y| + |y₀| := abs_sub _ _
    have hmin : 0 ≤ min |y - y₀| K := le_min (abs_nonneg _) hK.le
    linarith

/-- Pathwise right-continuity of `h ↦ g^z(t+h, X_{t+h}, β^z_{t+h})` at `0`. -/
lemma conv_path {Ω : Type*} (M : Model) (c : Coeffs) (W : ℝ≥0 → Ω → ℝ) (X : ℝ → Ω → ℝ)
    (z t x β : ℝ) (ω : Ω) (ht0 : 0 ≤ t) (htT : t < M.T)
    (hm : ∀ f ∈ [c.m₁, c.m₂, c.m₃, c.m₄, c.m₅, c.m₆], ContinuousOn f (Icc 0 M.T))
    (hXc : ContinuousOn (fun s => X s ω) (Icc t M.T)) (hXt : X t ω = x)
    (hWc : Continuous (fun s => W s ω)) :
    Tendsto (fun h => gz M c z (t + h) (X (t + h) ω) (betaZ M W z t β (t + h) ω))
      (𝓝[>] 0) (𝓝 (gz M c z t x β)) := by
  have hσ := M.hσ; have hσ₀ := M.hσ₀
  have hsub : Icc t M.T ⊆ Icc 0 M.T := Icc_subset_Icc_left ht0
  have h1 := (hm c.m₁ (by simp)).mono hsub
  have h2 := (hm c.m₂ (by simp)).mono hsub
  have h3 := (hm c.m₃ (by simp)).mono hsub
  have h4 := (hm c.m₄ (by simp)).mono hsub
  have h5 := (hm c.m₅ (by simp)).mono hsub
  have h6 := (hm c.m₆ (by simp)).mono hsub
  have hζ : ContinuousOn M.ζ (Icc t M.T) := by
    unfold Model.ζ
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro u hu
    have : 0 ≤ u := ht0.trans hu.1
    positivity
  have hWr : Continuous (fun u : ℝ => W u.toNNReal ω) := hWc.comp continuous_real_toNNReal
  have hb : ContinuousOn (fun u => betaZ M W z t β u ω) (Icc t M.T) := by
    unfold betaZ
    apply hζ.mul
    exact (by fun_prop : Continuous fun u : ℝ =>
      β / M.ζ t + z * (u - t) / M.σ ^ 2 + (W u.toNNReal ω - W t.toNNReal ω) / M.σ).continuousOn
  have hF : ContinuousOn (fun s => gz M c z s (X s ω) (betaZ M W z t β s ω)) (Icc t M.T) := by
    unfold gz fz
    fun_prop
  have hbt : betaZ M W z t β t ω = β := by
    have hz : M.ζ t ≠ 0 := by
      unfold Model.ζ
      have : 0 < M.σ ^ 2 + t * M.σ₀ ^ 2 := by positivity
      positivity
    simp only [betaZ, sub_self, mul_zero, zero_div, add_zero]
    field_simp
  have hcw := (hF t ⟨le_rfl, htT.le⟩).tendsto
  simp only [hXt, hbt] at hcw
  have hmap : Tendsto (fun h : ℝ => t + h) (𝓝[>] 0) (𝓝[Icc t M.T] t) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 (t + 0)) :=
        tendsto_const_nhds.add tendsto_id
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · have : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo 0 (M.T - t) :=
        Ioo_mem_nhdsGT (by linarith)
      filter_upwards [this] with h hh
      exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  exact hcw.comp hmap

end SmoothAmbS6Aux

open SmoothAmbEq.Gaussian SmoothAmbS6Aux

theorem solution (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : max a (1 - 1 / 2 * (M.σ ^ 2 / (M.σ₀ ^ 2 * M.T))) < M.α) (c : Coeffs)
    (hc : SolvesODE510 M c) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P)
    (π : Strategy) (hπ : Admissible M P W π) (t : ℝ) (ht : t ∈ Ico 0 M.T) (x β z : ℝ)
    (X : ℝ → Ω → ℝ) (hX : IsInsideWealth M P W π z t x β X) :
    (∀ᶠ h in 𝓝[>] (0 : ℝ), Integrable
      (fun ω => gz M c z (t + h) (X (t + h) ω) (betaZ M W z t β (t + h) ω)) P) ∧
    Tendsto (fun h => ∫ ω, gz M c z (t + h) (X (t + h) ω) (betaZ M W z t β (t + h) ω) ∂P)
      (𝓝[>] 0) (𝓝 (gz M c z t x β)) := by
  have hk := M.hk
  have ht0 : 0 ≤ t := ht.1
  have htT : t < M.T := ht.2
  -- continuity and boundedness of the coefficients
  obtain ⟨-, hd1, hd2, hd3, hd4, hd5, hd6, -⟩ := hc
  have hm : ∀ f ∈ [c.m₁, c.m₂, c.m₃, c.m₄, c.m₅, c.m₆], ContinuousOn f (Icc 0 M.T) := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fun s hs => (hd1 s hs).continuousWithinAt
    · exact fun s hs => (hd2 s hs).continuousWithinAt
    · exact fun s hs => (hd3 s hs).continuousWithinAt
    · exact fun s hs => (hd4 s hs).continuousWithinAt
    · exact fun s hs => (hd5 s hs).continuousWithinAt
    · exact fun s hs => (hd6 s hs).continuousWithinAt
  obtain ⟨B1, hB1, hb1⟩ := bdd_on (hm c.m₁ (by simp))
  obtain ⟨B2, hB2, hb2⟩ := bdd_on (hm c.m₂ (by simp))
  obtain ⟨B3, hB3, hb3⟩ := bdd_on (hm c.m₃ (by simp))
  obtain ⟨B4, hB4, hb4⟩ := bdd_on (hm c.m₄ (by simp))
  obtain ⟨B5, hB5, hb5⟩ := bdd_on (hm c.m₅ (by simp))
  obtain ⟨B6, hB6, hb6⟩ := bdd_on (hm c.m₆ (by simp))
  set Bd := B1 + B2 + B3 + B4 + B5 + B6 with hBd
  have hBd0 : 0 ≤ Bd := by positivity
  set A := Bd * (z ^ 2 + 2 * |z| + 2) with hA
  set B := Bd * (1 + |z|) + 1 with hB
  have hB0 : 0 < B := by positivity
  have hfz : ∀ s ∈ Icc 0 M.T, ∀ b : ℝ, fz c z s b ≤ A + B * b ^ 2 := by
    intro s hs b
    exact fz_le c z s b Bd hBd0 (by linarith [hb1 s hs]) (by linarith [hb2 s hs])
      (by linarith [hb3 s hs]) (by linarith [hb4 s hs]) (by linarith [hb5 s hs])
      (by linarith [hb6 s hs])
  -- admissibility (5.4) and Lemma C.1 (C.4)
  obtain ⟨δ, hδ, tt, htt, C1, hC1, hadm⟩ := hπ.2 t ht x β 1 one_pos 3 (by norm_num)
  set p := δ / 2 with hp
  have hp1 : 1 < p := by rw [hp]; linarith
  obtain ⟨h₁, hh₁, HC1⟩ := lemma_C_1 M (δ * B) (by positivity) 1 one_pos
  have hC4 := (HC1 P W hW t ht β z).2
  set K2 := Real.sqrt 2 * Real.exp (1 * z ^ 2 + 3 * (δ * B) * M.σ₀ ^ 4 * (M.ζ M.T ^ 2)⁻¹ * β ^ 2)
    with hK2
  set Mtot := (1 / M.k) ^ p * (1 / 2 * (C1 * Real.exp (1 * z ^ 2)) + 1 / 2 * (Real.exp (δ * A) * K2))
    with hMtot
  have hMtot0 : 0 ≤ Mtot := by positivity
  set h₀ := min (tt - t) (min h₁ (M.T - t)) with hh₀
  have hh₀0 : 0 < h₀ := lt_min (by linarith [htt.1]) (lt_min hh₁ (by linarith))
  -- measurability
  obtain ⟨hadapt, hXcont, -, I, hI, hXeq⟩ := id hX
  have aemX : ∀ s ∈ Icc t M.T, AEMeasurable (X s) P := fun s hs =>
    aem_of_shift P W hW t _ (X s) (hadapt s hs)
  set Y : ℝ → Ω → ℝ := fun h ω => gz M c z (t + h) (X (t + h) ω) (betaZ M W z t β (t + h) ω)
    with hY
  have hrange : ∀ h ∈ Ioo 0 h₀, t + h ∈ Icc t M.T ∧ t + h ∈ Icc 0 M.T ∧ t + h ∈ Icc t tt ∧
      t + h ∈ Ico t (min (t + h₁) M.T) := by
    intro h hh
    have a1 : h < tt - t := lt_of_lt_of_le hh.2 (min_le_left _ _)
    have a2 : h < h₁ := lt_of_lt_of_le hh.2 ((min_le_right _ _).trans (min_le_left _ _))
    have a3 : h < M.T - t := lt_of_lt_of_le hh.2 ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨⟨by linarith [hh.1], by linarith⟩, ⟨by linarith [hh.1], by linarith⟩,
      ⟨by linarith [hh.1], by linarith⟩, ⟨by linarith [hh.1], lt_min (by linarith) (by linarith)⟩⟩
  have aemY : ∀ h ∈ Ioo 0 h₀, AEMeasurable (Y h) P := by
    intro h hh
    exact (meas_gz M c z (t + h)).comp_aemeasurable
      ((aemX _ (hrange h hh).1).prodMk (aem_beta M P W hW z t β (t + h)))
  -- the L^p bound
  have hLp : ∀ h ∈ Ioo 0 h₀, Integrable (fun ω => |Y h ω| ^ p) P ∧
      ∫ ω, |Y h ω| ^ p ∂P ≤ Mtot := by
    intro h hh
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hrange h hh
    set s := t + h
    have hE1 := (hadm z X hX s hs3).1
    have hE2 := hC4 s hs4
    have aXs := aemX s hs1
    have aBs := aem_beta M P W hW z t β s
    obtain ⟨IU, hU⟩ := integ_of_lint (P := P)
      (f := fun ω => Real.exp (-δ * M.k * Real.exp (M.r * (M.T - s)) * X s ω))
      ((by fun_prop : Measurable fun y : ℝ => Real.exp (-δ * M.k * Real.exp (M.r * (M.T - s)) * y)).comp_aemeasurable aXs)
      (fun _ => (Real.exp_pos _).le) (by positivity) hE1
    obtain ⟨IV, hV⟩ := integ_of_lint (P := P)
      (f := fun ω => Real.exp (δ * B * (betaZ M W z t β s ω) ^ 2))
      ((by fun_prop : Measurable fun y : ℝ => Real.exp (δ * B * y ^ 2)).comp_aemeasurable aBs)
      (fun _ => (Real.exp_pos _).le) (by positivity) hE2
    set Φ : Ω → ℝ := fun ω => (1 / M.k) ^ p * (1 / 2 * Real.exp (-δ * M.k * Real.exp (M.r * (M.T - s)) * X s ω)
      + 1 / 2 * (Real.exp (δ * A) * Real.exp (δ * B * (betaZ M W z t β s ω) ^ 2))) with hΦ
    have IΦ : Integrable Φ P :=
      ((IU.const_mul (1 / 2)).add ((IV.const_mul (Real.exp (δ * A))).const_mul (1 / 2))).const_mul _
    have hΦint : ∫ ω, Φ ω ∂P ≤ Mtot := by
      rw [hΦ, integral_const_mul, integral_add (IU.const_mul _) ((IV.const_mul _).const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul, hMtot]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := mul_le_mul_of_nonneg_left hV (Real.exp_pos (δ * A)).le
      linarith
    have hpt : ∀ ω, |Y h ω| ^ p ≤ Φ ω := by
      intro ω
      refine (gz_rpow_le M c z s (X s ω) (betaZ M W z t β s ω) p).trans ?_
      simp only [hΦ]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have e1 : -(2 * p) * M.k * Real.exp (M.r * (M.T - s)) * X s ω
          = -δ * M.k * Real.exp (M.r * (M.T - s)) * X s ω := by rw [hp]; ring
      rw [e1]
      have e2 : Real.exp (δ * A) * Real.exp (δ * B * (betaZ M W z t β s ω) ^ 2)
          = Real.exp (2 * p * (A + B * (betaZ M W z t β s ω) ^ 2)) := by
        rw [← Real.exp_add]; congr 1; rw [hp]; ring
      rw [e2]
      have := hfz s hs2 (betaZ M W z t β s ω)
      have : Real.exp (2 * p * fz c z s (betaZ M W z t β s ω))
          ≤ Real.exp (2 * p * (A + B * (betaZ M W z t β s ω) ^ 2)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left this (by linarith))
      linarith
    have aY := aemY h hh
    have IYp : Integrable (fun ω => |Y h ω| ^ p) P := by
      refine IΦ.mono' ?_ (ae_of_all _ fun ω => ?_)
      · exact (aY.norm.pow_const p).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt ω
    refine ⟨IYp, ?_⟩
    exact (integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity) IΦ (ae_of_all _ hpt)).trans hΦint
  have IY : ∀ h ∈ Ioo 0 h₀, Integrable (Y h) P := by
    intro h hh
    refine ((integrable_const (1 : ℝ)).add (hLp h hh).1).mono' (aemY h hh).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    by_cases h1 : |Y h ω| ≤ 1
    · have : 0 ≤ |Y h ω| ^ p := by positivity
      simp only [Pi.add_apply]; linarith
    · push Not at h1
      have := Real.self_le_rpow_of_one_le h1.le hp1.le
      simp only [Pi.add_apply]; linarith
  have hevent : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo 0 h₀ := Ioo_mem_nhdsGT hh₀0
  refine ⟨hevent.mono IY, ?_⟩
  -- the start: `X_t = x` a.s.
  have hI0 : ∀ᵐ ω ∂P, I 0 ω = 0 := by
    obtain ⟨an, -, -, -, hconv⟩ := hI.2 0
    have hzero : (fun n => EthierKurtz.itoStepSum (shiftBM W t) 0 n (an n)) =
        fun _ _ => (0 : ℝ) := by
      funext n ω
      simp [EthierKurtz.itoStepSum]
    rw [hzero] at hconv
    have h0 : TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop (fun _ => (0 : ℝ)) :=
      tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
        (ae_of_all _ fun _ => tendsto_const_nhds)
    exact tendstoInMeasure_ae_unique hconv h0
  have hXt : ∀ᵐ ω ∂P, X t ω = x := by
    filter_upwards [hXeq t ⟨le_rfl, htT.le⟩, hI0] with ω hω hω0
    rw [hω]
    simp [hω0]
  set y₀ := gz M c z t x β with hy₀
  have hae : ∀ᵐ ω ∂P, Tendsto (fun h => Y h ω) (𝓝[>] 0) (𝓝 y₀) := by
    filter_upwards [hXcont, hXt, hW.cont] with ω h1 h2 h3
    exact conv_path M c W X z t x β ω ht0 htT hm h1 h2 h3
  -- uniform integrability argument
  rw [Metric.tendsto_nhds]
  intro η hη
  -- choose the truncation level `K`
  have hpow : Tendsto (fun K : ℝ => (K / 2) ^ (p - 1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp (tendsto_id.atTop_div_const (by norm_num))
  obtain ⟨K, hK1, hK2⟩ := ((hpow.eventually_gt_atTop (4 * Mtot / η)).and
    (eventually_ge_atTop (2 * |y₀| + 1))).exists
  have hKpos : 0 < K := by linarith [abs_nonneg y₀]
  have hK2' : 2 * |y₀| ≤ K := by linarith
  have hKp : 0 < (K / 2) ^ (p - 1) := by positivity
  have htail : 2 * Mtot / (K / 2) ^ (p - 1) < η / 2 := by
    rw [div_lt_iff₀ hKp]
    rw [div_lt_iff₀ hη] at hK1
    nlinarith
  -- dominated convergence for the truncated part
  have hdom : Tendsto (fun h => ∫ ω, min |Y h ω - y₀| K ∂P) (𝓝[>] 0) (𝓝 (∫ _ω : Ω, (0 : ℝ) ∂P)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => K)
    · filter_upwards [hevent] with h hh
      exact (((aemY h hh).sub_const y₀).abs.min aemeasurable_const).aestronglyMeasurable
    · filter_upwards [hevent] with h hh
      refine ae_of_all _ fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg _) hKpos.le)]
      exact min_le_right _ _
    · exact integrable_const K
    · filter_upwards [hae] with ω hω
      have hc : Continuous (fun y : ℝ => min |y - y₀| K) := by fun_prop
      have := (hc.tendsto y₀).comp hω
      simp only [sub_self, abs_zero, min_eq_left hKpos.le] at this
      exact this
  rw [integral_zero] at hdom
  have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∫ ω, min |Y h ω - y₀| K ∂P < η / 2 :=
    hdom (Iio_mem_nhds (by linarith))
  filter_upwards [hevent, hsmall] with h hh hs
  have IYh := IY h hh
  obtain ⟨IYp, hYp⟩ := hLp h hh
  have Imin : Integrable (fun ω => min |Y h ω - y₀| K) P := by
    refine (integrable_const K).mono' (((aemY h hh).sub_const y₀).abs.min aemeasurable_const).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg _) hKpos.le)]
    exact min_le_right _ _
  rw [Real.dist_eq]
  have e1 : (∫ ω, Y h ω ∂P) - y₀ = ∫ ω, (Y h ω - y₀) ∂P := by
    rw [integral_sub IYh (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [e1]
  calc |∫ ω, (Y h ω - y₀) ∂P| ≤ ∫ ω, |Y h ω - y₀| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (min |Y h ω - y₀| K + 2 * (|Y h ω| ^ p / (K / 2) ^ (p - 1))) ∂P := by
        apply integral_mono (IYh.sub (integrable_const _)).abs
          (Imin.add ((IYp.div_const _).const_mul _))
        intro ω
        exact split_le hKpos hK2' hp1
    _ = ∫ ω, min |Y h ω - y₀| K ∂P + 2 * ((∫ ω, |Y h ω| ^ p ∂P) / (K / 2) ^ (p - 1)) := by
        rw [integral_add Imin ((IYp.div_const _).const_mul _), integral_const_mul, integral_div]
    _ < η / 2 + η / 2 := by
        have : 2 * ((∫ ω, |Y h ω| ^ p ∂P) / (K / 2) ^ (p - 1)) ≤ 2 * Mtot / (K / 2) ^ (p - 1) := by
          rw [mul_div_assoc]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact div_le_div_of_nonneg_right hYp hKp.le
        linarith
    _ = η := by ring
