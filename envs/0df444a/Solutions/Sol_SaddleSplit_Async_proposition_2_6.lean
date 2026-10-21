-- Prove2me | solution 1 for SaddleSplit.Async.proposition_2_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T16:46:11.92913+00:00
-- url     : https://prove2.me/submissions/aeaec298-6d4f-44d8-ae2e-902c462c5587

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting
import Theorems.Thm_SaddleSplit_Async_lemma_A_4
import Theorems.Thm_SaddleSplit_Async_proposition_2_5
import Theorems.Thm_SaddleSplit_Async_proposition_2_2_i_ii

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

/-- zeros of a maximally monotone operator: `x ∈ zer T` iff `⟪x, w⟫ ≤ ⟪u, w⟫` on the graph. -/
theorem ss26_mem_zer_of {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E → Set E) (hT : IsMaximalMonotone T) (x : E)
    (h : ∀ u w, w ∈ T u → ⟪x, w⟫_ℝ ≤ ⟪u, w⟫_ℝ) : x ∈ zer T := by
  classical
  let T' : E → Set E := fun u => T u ∪ {w | u = x ∧ w = 0}
  have hmon : IsMonotoneOp T' := by
    intro a b u v hu hv
    rcases hu with hu | ⟨rfl, rfl⟩ <;> rcases hv with hv | ⟨rfl, rfl⟩
    · exact hT.1 _ _ _ _ hu hv
    · have := h a u hu
      rw [sub_zero, inner_sub_left]; linarith
    · have := h b v hv
      rw [zero_sub, inner_neg_right, inner_sub_left]; linarith
    · simp
  have heq := hT.2 T' hmon (fun u w hw => Or.inl hw)
  have : (0 : E) ∈ T' x := Or.inr ⟨rfl, rfl⟩
  rw [heq] at this
  exact this

/-- weakly convergent sequences are bounded (uniform boundedness). -/
theorem ss26_weak_bdd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : ℕ → E) (w : E) (hu : WeakTendsto u w) : ∃ C, ∀ n, ‖u n‖ ≤ C := by
  have hpt : ∀ y : E, ∃ C, ∀ n, ‖(innerSL ℝ (u n)) y‖ ≤ C := by
    intro y
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ (hu y)).exists_norm_le
    exact ⟨C, fun n => by simpa [innerSL_apply_apply] using hC _ ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hpt
  exact ⟨C, fun n => by simpa [innerSL_apply_norm] using hC n⟩

theorem solution {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]
    (prob : Problem H G) (hprob : prob.Hyp) (hzer : (zer (saddleOp prob)).Nonempty)
    (α : ℝ) (hα : IsLeast (Set.range prob.αc ∪ Set.range prob.βc ∪ Set.range prob.δc) α)
    (ε : ℝ) (hε : ε ∈ Set.Ioo 0 1)
    (x p ps q t : ℕ → XSpace H G) (Δ lam : ℕ → ℝ)
    (hrun : IsOuterApproxRun prob α ε x p ps q t Δ lam) :
    (∀ z ∈ zer (saddleOp prob), ∀ n, ‖x (n + 1) - z‖ ≤ ‖x n - z‖) ∧
    Summable (fun n => ‖x (n + 1) - x n‖ ^ 2) ∧
    (Bornology.IsBounded (Set.range t) → ∀ δ > 0, ∀ᶠ n in atTop, Δ n ≤ δ) ∧
    (WeakTendsto (fun n => x n - p n) 0 → Tendsto (fun n => p n - q n) atTop (𝓝 0) →
      Tendsto t atTop (𝓝 0) → ∃ z ∈ zer (saddleOp prob), WeakTendsto x z) := by
  obtain ⟨hSeq, hMmax, hCα⟩ := proposition_2_5 prob hprob
  obtain ⟨hCco, hhalf⟩ := hCα α hα
  obtain ⟨hSmax, hZcl, hZcv⟩ := proposition_2_2_i_ii prob hprob
  have hα0 : 0 < α := by
    rcases hα.1 with (⟨i, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩
    · exact (hprob.1 i).2.1
    · exact (hprob.2.1 k).2.1
    · exact (hprob.2.2.1 k).2.1
  set Z := zer (saddleOp prob)
  set η : ℕ → ℝ := fun n => (4 * α)⁻¹ * ‖p n - q n‖ ^ 2 + ⟪p n, t n⟫_ℝ
  have hfr : IsFejerHalfspaceRun Z ε x t η Δ lam := by
    intro n
    obtain ⟨hps, ht, hΔ, hpos, hnpos⟩ := hrun n
    refine ⟨fun X hX => ?_, ?_, hpos, hnpos⟩
    · have := hhalf (p n) (ps n) (q n) hps hX
      simp only [Set.mem_ofPred_eq] at this ⊢
      rw [← ht, inner_sub_left] at this
      simp only [η]; linarith
    · rw [hΔ, inner_sub_left]; simp only [η]; ring
  obtain ⟨hF, hS, hW⟩ := lemma_A_4 Z hzer hZcl hZcv ε hε x t η Δ lam hfr
  refine ⟨hF, hS, ?_, ?_⟩
  · -- (iii)
    intro hb δ hδ
    obtain ⟨μ, hμ⟩ := hb.exists_norm_le
    have hμ' : ∀ n, ‖t n‖ ≤ μ := fun n => hμ _ ⟨n, rfl⟩
    have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ' 0)
    have hd : Tendsto (fun n => ‖x (n + 1) - x n‖) atTop (𝓝 0) := by
      have h3 := hS.tendsto_atTop_zero.sqrt
      simpa [Real.sqrt_sq (norm_nonneg _)] using h3
    have hbound : ∀ n, Δ n ≤ ε⁻¹ * μ * ‖x (n + 1) - x n‖ := by
      intro n
      obtain ⟨-, -, hΔ, hpos, hnpos⟩ := hrun n
      by_cases h0 : 0 < Δ n
      · obtain ⟨⟨hl1, hl2⟩, hx⟩ := hpos h0
        have htn : t n ≠ 0 := by
          intro h
          rw [hΔ, h, inner_zero_right, zero_sub] at h0
          have : 0 ≤ (4 * α)⁻¹ * ‖p n - q n‖ ^ 2 := by positivity
          linarith
        have hτ : 0 < ‖t n‖ := norm_pos_iff.2 htn
        have hl0 : 0 < lam n := by linarith [hε.1]
        have hdx : ‖x (n + 1) - x n‖ = lam n * Δ n / ‖t n‖ := by
          rw [hx, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)]
          field_simp
        rw [hdx]
        have e : ε⁻¹ * μ * (lam n * Δ n / ‖t n‖) = (μ / ‖t n‖) * (lam n / ε) * Δ n := by
          field_simp
        rw [e]
        have h1 : 1 ≤ μ / ‖t n‖ := by rw [le_div_iff₀ hτ]; linarith [hμ' n]
        have h2 : 1 ≤ lam n / ε := by rw [le_div_iff₀ hε.1]; linarith
        have h3 : 1 ≤ (μ / ‖t n‖) * (lam n / ε) := by nlinarith
        nlinarith
      · push Not at h0
        have : 0 ≤ ε⁻¹ * μ * ‖x (n + 1) - x n‖ := by
          have := hε.1; positivity
        linarith
    have hlim : Tendsto (fun n => ε⁻¹ * μ * ‖x (n + 1) - x n‖) atTop (𝓝 0) := by
      simpa using hd.const_mul (ε⁻¹ * μ)
    filter_upwards [(hlim.eventually (gt_mem_nhds hδ))] with n hn
    exact (hbound n).trans hn.le
  · -- (iv)
    intro hxp hpq ht0
    apply hW
    intro y k hk hxk
    -- p_{k n} ⇀ y
    have hpk : WeakTendsto (p ∘ k) y := by
      intro z
      have h1 := hxk z
      have h2 := (hxp z).comp hk.tendsto_atTop
      simp only [inner_zero_left] at h2
      have := h1.sub h2
      simp only [Function.comp_apply, sub_zero] at this ⊢
      refine this.congr fun n => ?_
      rw [inner_sub_left]; ring
    -- w_n = ps_n + C p_n ∈ 𝓢 p_n and w_n → 0
    set w : ℕ → XSpace H G := fun n => ps n + opC prob (p n)
    have hwS : ∀ n, w n ∈ saddleOp prob (p n) := by
      intro n; rw [hSeq]; exact ⟨ps n, (hrun n).1, rfl⟩
    have hCL : ∀ X Y : XSpace H G, ‖opC prob X - opC prob Y‖ ≤ α⁻¹ * ‖X - Y‖ := by
      intro X Y
      have hc := hCco X Y
      have hcs := real_inner_le_norm (opC prob X - opC prob Y) (X - Y)
      by_cases h0 : ‖opC prob X - opC prob Y‖ = 0
      · rw [h0]; positivity
      · have hp : 0 < ‖opC prob X - opC prob Y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
        rw [le_inv_mul_iff₀ hα0]
        nlinarith
    have hw0 : Tendsto w atTop (𝓝 0) := by
      have hwle : ∀ n, ‖w n‖ ≤ ‖t n‖ + α⁻¹ * ‖p n - q n‖ := by
        intro n
        have e : w n = t n + (opC prob (p n) - opC prob (q n)) := by
          simp only [w, (hrun n).2.1]; abel
        rw [e]
        exact (norm_add_le _ _).trans (by linarith [hCL (p n) (q n)])
      have hr : Tendsto (fun n => ‖t n‖ + α⁻¹ * ‖p n - q n‖) atTop (𝓝 0) := by
        have h1 := (tendsto_zero_iff_norm_tendsto_zero.1 ht0)
        have h2 := (tendsto_zero_iff_norm_tendsto_zero.1 hpq).const_mul α⁻¹
        simpa using h1.add h2
      exact tendsto_zero_iff_norm_tendsto_zero.2
        (squeeze_zero (fun n => norm_nonneg _) hwle hr)
    -- boundedness of p ∘ k
    obtain ⟨z0, hz0⟩ := hzer
    obtain ⟨Cd, hCd⟩ := ss26_weak_bdd _ _ hxp
    have hxb : ∀ n, ‖x n‖ ≤ ‖x 0 - z0‖ + ‖z0‖ := by
      have hmono : ∀ n, ‖x n - z0‖ ≤ ‖x 0 - z0‖ := by
        intro n
        induction n with
        | zero => exact le_rfl
        | succ n ih => exact (hF z0 hz0 n).trans ih
      intro n
      calc ‖x n‖ = ‖(x n - z0) + z0‖ := by rw [sub_add_cancel]
        _ ≤ ‖x n - z0‖ + ‖z0‖ := norm_add_le _ _
        _ ≤ _ := by linarith [hmono n]
    have hpb : ∀ n, ‖p n‖ ≤ ‖x 0 - z0‖ + ‖z0‖ + Cd := by
      intro n
      calc ‖p n‖ = ‖x n - (x n - p n)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x n‖ + ‖x n - p n‖ := norm_sub_le _ _
        _ ≤ _ := by linarith [hxb n, hCd n]
    -- demiclosedness
    apply ss26_mem_zer_of _ hSmax y
    intro u us hu
    have hmon : ∀ n, 0 ≤ ⟪p (k n) - u, w (k n) - us⟫_ℝ := fun n =>
      hSmax.1 _ _ _ _ (hwS (k n)) hu
    -- ⟪p_{kn} - u, w_{kn}⟫ → 0
    have hA : Tendsto (fun n => ⟪p (k n) - u, w (k n)⟫_ℝ) atTop (𝓝 0) := by
      have hwk := hw0.comp hk.tendsto_atTop
      have hb : ∀ n, |⟪p (k n) - u, w (k n)⟫_ℝ| ≤ (‖x 0 - z0‖ + ‖z0‖ + Cd + ‖u‖) * ‖w (k n)‖ := by
        intro n
        refine (abs_real_inner_le_norm _ _).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by linarith [hpb (k n)])
      have hr : Tendsto (fun n => (‖x 0 - z0‖ + ‖z0‖ + Cd + ‖u‖) * ‖w (k n)‖) atTop (𝓝 0) := by
        simpa using ((tendsto_zero_iff_norm_tendsto_zero.1 hwk).const_mul
          (‖x 0 - z0‖ + ‖z0‖ + Cd + ‖u‖))
      exact squeeze_zero_norm' (Eventually.of_forall fun n => by
        rw [Real.norm_eq_abs]; exact hb n) hr
    have hB : Tendsto (fun n => ⟪p (k n) - u, us⟫_ℝ) atTop (𝓝 ⟪y - u, us⟫_ℝ) := by
      have := (hpk us).sub (tendsto_const_nhds (x := ⟪u, us⟫_ℝ))
      simp only [Function.comp_apply] at this
      refine (this.congr fun n => ?_).trans (le_of_eq (by rw [inner_sub_left]))
      rw [inner_sub_left]
    have hlim : Tendsto (fun n => ⟪p (k n) - u, w (k n) - us⟫_ℝ) atTop (𝓝 (0 - ⟪y - u, us⟫_ℝ)) := by
      refine (hA.sub hB).congr fun n => ?_
      rw [inner_sub_right]
    have := ge_of_tendsto' hlim hmon
    rw [inner_sub_left] at this
    linarith
