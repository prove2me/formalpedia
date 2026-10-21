-- Prove2me | solution 1 for SaddleSplit.Async.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T16:21:47.739207+00:00
-- url     : https://prove2.me/submissions/0c8e2644-4b5f-4369-af0a-81280c87146a

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence

open SaddleSplit.Async DouglasRachfordPPA.GenDR

theorem ss_exists_weak_subseq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (u : ℕ → E) (M : ℝ) (hM : ∀ k, ‖u k‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : E, WeakTendsto (u ∘ φ) w := by
  set V : Submodule ℝ E := (Submodule.span ℝ (Set.range u)).topologicalClosure with hV
  have hsep : TopologicalSpace.IsSeparable (V : Set E) := by
    rw [hV, Submodule.topologicalClosure_coe]
    exact (Set.countable_range u).isSeparable.span.closure
  haveI : TopologicalSpace.SeparableSpace V := hsep.separableSpace
  haveI : CompleteSpace V := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hmem : ∀ k, u k ∈ V := fun k =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨k, rfl⟩)
  let xs : ℕ → V := fun k => ⟨u k, hmem k⟩
  let g : ℕ → WeakDual ℝ V := fun k => StrongDual.toWeakDual (innerSL ℝ (xs k))
  have hg : ∀ k, g k ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ V) M := by
    intro k
    simp only [Set.mem_preimage, g]
    rw [StrongDual.toStrongDual_toWeakDual]
    have h : ‖(innerSL ℝ (xs k) : StrongDual ℝ V)‖ ≤ M := by
      rw [innerSL_apply_norm]; exact hM k
    exact mem_closedBall_zero_iff.mpr h
  obtain ⟨a, -, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℝ V 0 M hg
  refine ⟨φ, hφ, ((toDual ℝ V).symm (WeakDual.toStrongDual a) : E), fun y => ?_⟩
  have hev : ∀ v : V, Tendsto (fun k => (g (φ k)) v) atTop (𝓝 (a v)) := fun v =>
    ((WeakDual.eval_continuous v).tendsto a).comp hlim
  set py : V := V.orthogonalProjectionOnto y
  have hpy : ∀ v : V, ⟪(v : E), y⟫_ℝ = ⟪v, py⟫_ℝ := by
    intro v
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have h1 := hev py
  simp only [g, StrongDual.toWeakDual_apply, innerSL_apply_apply] at h1
  have e1 : (fun k => ⟪(u ∘ φ) k, y⟫_ℝ) = fun k => ⟪(xs (φ k) : V), py⟫_ℝ := by
    funext k; exact hpy (xs (φ k))
  rw [e1, hpy]
  rw [toDual_symm_apply]
  exact h1

theorem ss_opial_seq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : ℕ → E) (w1 w2 : E) (φ ψ : ℕ → ℕ) (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (h1 : WeakTendsto (x ∘ φ) w1) (h2 : WeakTendsto (x ∘ ψ) w2)
    (hc1 : ∃ d, Tendsto (fun k => ‖x k - w1‖) atTop (𝓝 d))
    (hc2 : ∃ d, Tendsto (fun k => ‖x k - w2‖) atTop (𝓝 d)) : w1 = w2 := by
  obtain ⟨d1, hd1⟩ := hc1
  obtain ⟨d2, hd2⟩ := hc2
  set v := w1 - w2 with hv
  have hg : Tendsto (fun k => ‖x k - w2‖ ^ 2 - ‖x k - w1‖ ^ 2) atTop (𝓝 (d2 ^ 2 - d1 ^ 2)) :=
    (hd2.pow 2).sub (hd1.pow 2)
  have hid : ∀ k, ‖x k - w2‖ ^ 2 - ‖x k - w1‖ ^ 2 =
      2 * ⟪x k, v⟫_ℝ - 2 * ⟪w1, v⟫_ℝ + ‖v‖ ^ 2 := by
    intro k
    have e : x k - w2 = (x k - w1) + v := by rw [hv]; abel
    rw [e, norm_add_sq_real, inner_sub_left]; ring
  simp only [hid] at hg
  have g1 : Tendsto (fun k => 2 * ⟪x (φ k), v⟫_ℝ - 2 * ⟪w1, v⟫_ℝ + ‖v‖ ^ 2) atTop
      (𝓝 (2 * ⟪w1, v⟫_ℝ - 2 * ⟪w1, v⟫_ℝ + ‖v‖ ^ 2)) :=
    (((h1 v).const_mul 2).sub tendsto_const_nhds).add tendsto_const_nhds
  have g2 : Tendsto (fun k => 2 * ⟪x (ψ k), v⟫_ℝ - 2 * ⟪w1, v⟫_ℝ + ‖v‖ ^ 2) atTop
      (𝓝 (2 * ⟪w2, v⟫_ℝ - 2 * ⟪w1, v⟫_ℝ + ‖v‖ ^ 2)) :=
    (((h2 v).const_mul 2).sub tendsto_const_nhds).add tendsto_const_nhds
  have e1 := tendsto_nhds_unique g1 (hg.comp hφ.tendsto_atTop)
  have e2 := tendsto_nhds_unique g2 (hg.comp hψ.tendsto_atTop)
  have e3 : ⟪w2, v⟫_ℝ - ⟪w1, v⟫_ℝ = -‖v‖ ^ 2 := by
    rw [← inner_sub_left, ← real_inner_self_eq_norm_sq, hv, ← inner_neg_left, neg_sub]
  have : ‖v‖ ^ 2 = 0 := by nlinarith
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  rw [norm_eq_zero, hv, sub_eq_zero] at this
  exact this

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Z : Set E) (hZne : Z.Nonempty) (hZcl : IsClosed Z) (hZcv : Convex ℝ Z)
    (ε : ℝ) (hε : ε ∈ Set.Ioo 0 1)
    (x t : ℕ → E) (η Δ lam : ℕ → ℝ) (hrun : IsFejerHalfspaceRun Z ε x t η Δ lam) :
    (∀ z ∈ Z, ∀ n, ‖x (n + 1) - z‖ ≤ ‖x n - z‖) ∧
    Summable (fun n => ‖x (n + 1) - x n‖ ^ 2) ∧
    ((∀ (y : E) (k : ℕ → ℕ), StrictMono k → WeakTendsto (x ∘ k) y → y ∈ Z) →
      ∃ z ∈ Z, WeakTendsto x z) := by
  obtain ⟨hε0, hε1⟩ := hε
  obtain ⟨z0, hz0⟩ := hZne
  -- the key descent inequality
  have key : ∀ z ∈ Z, ∀ n, ε * ‖x (n + 1) - x n‖ ^ 2 ≤
      (2 - ε) * (‖x n - z‖ ^ 2 - ‖x (n + 1) - z‖ ^ 2) := by
    intro z hz n
    obtain ⟨hZH, hΔ, hpos, hnpos⟩ := hrun n
    by_cases hΔ0 : 0 < Δ n
    · obtain ⟨⟨hl1, hl2⟩, hx⟩ := hpos hΔ0
      have ht : t n ≠ 0 := by
        intro h0
        have := hZH hz0
        simp only [Set.mem_setOf_eq, h0, inner_zero_right] at this
        rw [hΔ, h0, inner_zero_right] at hΔ0
        linarith
      have hτ : 0 < ‖t n‖ ^ 2 := by positivity
      set c := lam n * Δ n / ‖t n‖ ^ 2 with hc
      have hc0 : 0 ≤ c := by
        rw [hc]; exact div_nonneg (mul_nonneg (by linarith) hΔ0.le) hτ.le
      have hcτ : c * ‖t n‖ ^ 2 = lam n * Δ n := by rw [hc]; field_simp
      have hd : x (n + 1) - x n = -(c • t n) := by rw [hx]; abel
      have hs : Δ n ≤ ⟪x n - z, t n⟫_ℝ := by
        have := hZH hz
        simp only [Set.mem_setOf_eq] at this
        rw [inner_sub_left, hΔ]; linarith
      have hD : ‖x (n + 1) - x n‖ ^ 2 = c ^ 2 * ‖t n‖ ^ 2 := by
        rw [hd, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have hB : ‖x (n + 1) - z‖ ^ 2 = ‖x n - z‖ ^ 2 - 2 * c * ⟪x n - z, t n⟫_ℝ
          + c ^ 2 * ‖t n‖ ^ 2 := by
        have e : x (n + 1) - z = (x n - z) + -(c • t n) := by rw [← hd]; abel
        rw [e, norm_add_sq_real, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul,
          mul_pow, Real.norm_eq_abs, sq_abs]
        ring
      rw [hD, hB]
      have h1 : c * ⟪x n - z, t n⟫_ℝ ≥ c * Δ n := mul_le_mul_of_nonneg_left hs hc0
      have h2 : c ^ 2 * ‖t n‖ ^ 2 = lam n * (c * Δ n) := by rw [sq, mul_assoc, hcτ]; ring
      have h3 : 0 ≤ c * Δ n := mul_nonneg hc0 hΔ0.le
      have h4 : lam n * (c * Δ n) ≤ (2 - ε) * (c * Δ n) := mul_le_mul_of_nonneg_right hl2 h3
      nlinarith
    · have hx := hnpos (not_lt.1 hΔ0)
      rw [hx, sub_self, norm_zero]
      simp
  have fejer : ∀ z ∈ Z, ∀ n, ‖x (n + 1) - z‖ ≤ ‖x n - z‖ := by
    intro z hz n
    have := key z hz n
    have h0 : 0 ≤ ε * ‖x (n + 1) - x n‖ ^ 2 := by positivity
    have h5 : ‖x (n + 1) - z‖ ^ 2 ≤ ‖x n - z‖ ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h5
  refine ⟨fejer, ?_, ?_⟩
  · -- summability via telescoping
    apply summable_of_sum_range_le (c := (2 - ε) / ε * ‖x 0 - z0‖ ^ 2)
    · intro n; positivity
    · intro N
      have htel : ∀ N, ε * ∑ n ∈ Finset.range N, ‖x (n + 1) - x n‖ ^ 2 ≤
          (2 - ε) * (‖x 0 - z0‖ ^ 2 - ‖x N - z0‖ ^ 2) := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          rw [Finset.sum_range_succ, mul_add]
          have := key z0 hz0 N
          nlinarith
      have h := htel N
      rw [div_mul_eq_mul_div, le_div_iff₀ hε0]
      have : 0 ≤ (2 - ε) * ‖x N - z0‖ ^ 2 := by
        have : 0 < 2 - ε := by linarith
        positivity
      nlinarith
  · intro hclus
    have hbd : ∀ n, ‖x n‖ ≤ ‖x 0 - z0‖ + ‖z0‖ := by
      have hmono : ∀ n, ‖x n - z0‖ ≤ ‖x 0 - z0‖ := by
        intro n
        induction n with
        | zero => exact le_rfl
        | succ n ih => exact (fejer z0 hz0 n).trans ih
      intro n
      calc ‖x n‖ = ‖(x n - z0) + z0‖ := by rw [sub_add_cancel]
        _ ≤ ‖x n - z0‖ + ‖z0‖ := norm_add_le _ _
        _ ≤ _ := by linarith [hmono n]
    have hconv : ∀ z ∈ Z, ∃ d, Tendsto (fun k => ‖x k - z‖) atTop (𝓝 d) := by
      intro z hz
      have hanti : Antitone (fun k => ‖x k - z‖) := antitone_nat_of_succ_le (fejer z hz)
      exact ⟨_, tendsto_atTop_ciInf hanti ⟨0, by rintro _ ⟨k, rfl⟩; exact norm_nonneg _⟩⟩
    obtain ⟨φ, hφ, w, hw⟩ := ss_exists_weak_subseq x _ hbd
    have hwZ := hclus w φ hφ hw
    refine ⟨w, hwZ, fun y => ?_⟩
    by_contra hnt
    rw [not_tendsto_iff_exists_frequently_notMem] at hnt
    obtain ⟨s, hs, hfreq⟩ := hnt
    obtain ⟨ψ, hψ, hψs⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨χ, hχ, w', hw'⟩ := ss_exists_weak_subseq (x ∘ ψ) _ (fun n => hbd (ψ n))
    have hmono' : StrictMono (ψ ∘ χ) := hψ.comp hχ
    have hw'Z := hclus w' (ψ ∘ χ) hmono' hw'
    have heq := ss_opial_seq x w w' φ (ψ ∘ χ) hφ hmono' hw hw' (hconv w hwZ) (hconv w' hw'Z)
    subst heq
    have hl := hw' y
    obtain ⟨k, hk⟩ := (hl.eventually hs).exists
    exact hψs (χ k) hk
