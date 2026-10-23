-- Prove2me | solution 1 for WaitTimePricing.Existence.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T09:33:32.273886+00:00
-- url     : https://prove2.me/submissions/ec5009ad-81f8-4ebc-a075-5feda02a40d5

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1
import Theorems.Thm_WaitTimePricing_Existence_lemma_2
import Theorems.Thm_WaitTimePricing_Existence_proposition_5
import Theorems.Thm_WaitTimePricing_Existence_lemma_6

open Set Filter WaitTimePricing.Existence

theorem solution (M : Model) (hM : M.Standing) (obj : Objective) :
    (∀ w ∈ Icc 0 (wbar M + M.C),
      Tendsto (fun j : ℕ => VgN M obj (gbar M obj) (2 ^ j) w) atTop (nhds (Vbar M obj w))) ∧
    TendstoUniformlyOn (fun j : ℕ => VgN M obj (gbar M obj) (2 ^ j)) (Vbar M obj) atTop
      (Icc 0 (wbar M + M.C)) ∧
    ConcaveOn ℝ (Icc 0 (wbar M + M.C)) (Vbar M obj) ∧
    AntitoneOn (Vbar M obj) (Icc 0 (wbar M + M.C)) ∧
    ∀ x ∈ Icc 0 (wbar M + M.C), ∀ y ∈ Icc 0 (wbar M + M.C),
      |Vbar M obj x - Vbar M obj y| ≤ gbar M obj * |x - y| := by
  have hw0 : 0 ≤ wbar M := Real.sSup_nonneg (fun x hx => le_of_lt hx.1)
  have hC := hM.C_pos
  obtain ⟨h5a, -, -, h5d⟩ := proposition_5 M hM obj
  have h6 := lemma_6 M hM obj
  set I := Icc 0 (wbar M + M.C) with hI
  set gb := gbar M obj with hgb
  set F : ℕ → ℝ → ℝ := fun j => VgN M obj gb (2 ^ j) with hF
  -- ḡ ≥ 0
  have hg0 : 0 ≤ gb := ge_of_tendsto h5d (eventually_atTop.2 ⟨1, fun j hj => h5a j hj⟩)
  -- V(w̄) = 0
  have hstep : ∀ (g : ℝ) (N k : ℕ), VStep M obj g N k (wbar M) = 0 := by
    intro g N k
    induction k with
    | zero => show -(wbar M - wbar M) * g = 0; ring
    | succ k ih =>
      have hg : grid M N (N - k) ≤ wbar M := by
        unfold grid
        rcases Nat.eq_zero_or_pos N with h | h
        · subst h; simp [hw0]
        · have hN : (0:ℝ) < N := by exact_mod_cast h
          have h1 : ((N - k : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N k
          calc ((N - k : ℕ) : ℝ) * (wbar M / N) ≤ N * (wbar M / N) :=
                mul_le_mul_of_nonneg_right h1 (div_nonneg hw0 hN.le)
            _ = wbar M := by field_simp
      show (if grid M N (N - (k + 1)) ≤ wbar M ∧ wbar M < grid M N (N - k) then _ else _) = _
      rw [if_neg (fun h => absurd (lt_of_lt_of_le h.2 hg) (lt_irrefl _)), ih]
  have hwI : wbar M ∈ I := ⟨hw0, by linarith⟩
  -- antitone in j
  have hanti : ∀ w ∈ I, Antitone (fun j => F j w) := by
    intro w hw
    apply antitone_nat_of_succ_le
    intro j
    have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
    show VgN M obj gb (2 ^ (j + 1)) w ≤ VgN M obj gb (2 ^ j) w
    rw [this]; exact (lemma_2 M hM obj gb hg0 (2 ^ j) Nat.one_le_two_pow w hw).1
  -- lower bound
  have hlow1 : ∀ j, 1 ≤ j → ∀ w ∈ I, -(gb * (wbar M + M.C)) ≤ F j w := by
    intro j hj w hw
    have h : |F j w - F j (wbar M)| ≤ gb * |w - wbar M| := (h6 j hj).2.2 w hw (wbar M) hwI
    have hz : F j (wbar M) = 0 := hstep _ _ _
    rw [hz, sub_zero] at h
    have h2 : |w - wbar M| ≤ wbar M + M.C := by
      rw [abs_le]; constructor <;> linarith [hw.1, hw.2]
    have h3 := le_trans h (mul_le_mul_of_nonneg_left h2 hg0)
    linarith [neg_abs_le (F j w)]
  have hlow : ∀ j, ∀ w ∈ I, -(gb * (wbar M + M.C)) ≤ F j w := by
    intro j w hw
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; exact le_trans (hlow1 1 le_rfl w hw) (hanti w hw (Nat.zero_le 1))
    · exact hlow1 j h w hw
  -- pointwise limit
  have hlim : ∀ w ∈ I, Tendsto (fun j => F j w) atTop (nhds (Vbar M obj w)) := by
    intro w hw
    have ht := tendsto_atTop_ciInf (hanti w hw) ⟨_, by rintro _ ⟨j, rfl⟩; exact hlow j w hw⟩
    have : Vbar M obj w = ⨅ j, F j w := ht.limUnder_eq
    rw [this]; exact ht
  have ev1 : ∀ᶠ j in (atTop : Filter ℕ), 1 ≤ j := eventually_atTop.2 ⟨1, fun _ h => h⟩
  -- Lipschitz
  have hlip : ∀ x ∈ I, ∀ y ∈ I, |Vbar M obj x - Vbar M obj y| ≤ gb * |x - y| := by
    intro x hx y hy
    have ht : Tendsto (fun j => |F j x - F j y|) atTop (nhds |Vbar M obj x - Vbar M obj y|) :=
      ((hlim x hx).sub (hlim y hy)).abs
    exact le_of_tendsto ht (ev1.mono fun j hj => (h6 j hj).2.2 x hx y hy)
  have hcontV : ContinuousOn (Vbar M obj) I := by
    apply (LipschitzOnWith.continuousOn (K := gb.toNNReal))
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hg0]; exact hlip x hx y hy
  have hcontF : ∀ j, 1 ≤ j → ContinuousOn (F j) I := by
    intro j hj
    apply (LipschitzOnWith.continuousOn (K := gb.toNNReal))
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hg0]; exact (h6 j hj).2.2 x hx y hy
  refine ⟨hlim, ?_, ?_, ?_, hlip⟩
  · -- Dini on the shifted sequence
    have hD : TendstoUniformlyOn (fun j => F (j + 1)) (Vbar M obj) atTop I :=
      Antitone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
        (fun j => hcontF (j + 1) (Nat.succ_le_succ (Nat.zero_le j)))
        (fun x hx a b hab => hanti x hx (Nat.succ_le_succ hab)) hcontV
        (fun x hx => (hlim x hx).comp (tendsto_add_atTop_nat 1))
    rw [Metric.tendstoUniformlyOn_iff] at hD ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hD ε hε)
    refine eventually_atTop.2 ⟨N + 1, fun n hn => ?_⟩
    have := hN (n - 1) (by omega)
    rwa [Nat.sub_add_cancel (by omega)] at this
  · refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
    have hz : a • x + b • y ∈ I := convex_Icc _ _ hx hy ha hb hab
    have ht1 : Tendsto (fun j => a • F j x + b • F j y) atTop
        (nhds (a • Vbar M obj x + b • Vbar M obj y)) :=
      ((hlim x hx).const_smul a).add ((hlim y hy).const_smul b)
    exact le_of_tendsto_of_tendsto ht1 (hlim _ hz)
      (ev1.mono fun j hj => (h6 j hj).2.1.2 hx hy ha hb hab)
  · intro x hx y hy hxy
    exact le_of_tendsto_of_tendsto (hlim y hy) (hlim x hx)
      (ev1.mono fun j hj => (h6 j hj).1 hx hy hxy)
