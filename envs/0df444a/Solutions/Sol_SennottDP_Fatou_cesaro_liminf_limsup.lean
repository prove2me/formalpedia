-- Prove2me | solution 1 for SennottDP.Fatou.cesaro_liminf_limsup
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T16:53:28.911588+00:00
-- url     : https://prove2.me/submissions/641697d7-7dc7-4fb1-be50-0c49f3baa0e2

import Mathlib

open Filter Topology in
lemma cesaro_limsup_le_970b (u w : ℕ → ℝ)
    (hw : ∀ n, 1 ≤ n → w n = ∑ k ∈ Finset.range n, u k) :
    limsup (fun n => ((w n / n : ℝ) : EReal)) atTop ≤ limsup (fun n => (u n : EReal)) atTop := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  refine le_trans ?_ hr2.le
  have hev : ∀ᶠ n in atTop, (u n : EReal) < r := eventually_lt_of_limsup_lt hr1
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  set D : ℝ := ∑ k ∈ Finset.range N, u k - N * r with hD
  have hle : ∀ᶠ n in atTop, ((w n / n : ℝ) : EReal) ≤ ((r + D / n : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop (N + 1)] with n hn
    rw [EReal.coe_le_coe_iff]
    have hn1 : 1 ≤ n := by omega
    have hNn : N ≤ n := by omega
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [hw n hn1, ← Finset.sum_range_add_sum_Ico _ hNn]
    have hsum : ∑ k ∈ Finset.Ico N n, u k ≤ ∑ k ∈ Finset.Ico N n, r :=
      Finset.sum_le_sum (fun k hk => (EReal.coe_lt_coe_iff.1 (hN k (Finset.mem_Ico.1 hk).1)).le)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hNn] at hsum
    rw [div_le_iff₀ hpos]
    have h2 : (r + D / n) * n = r * n + D := by field_simp
    rw [h2, hD]
    linarith
  calc limsup (fun n => ((w n / n : ℝ) : EReal)) atTop
      ≤ limsup (fun n : ℕ => ((r + D / n : ℝ) : EReal)) atTop := limsup_le_limsup hle
    _ = r := by
      apply Tendsto.limsup_eq
      have ht : Tendsto (fun n : ℕ => r + D / (n : ℝ)) atTop (𝓝 r) := by
        have := (tendsto_const_div_atTop_nhds_zero_nat D).const_add r
        simpa using this
      exact (continuous_coe_real_ereal.tendsto r).comp ht

open Filter Topology in
theorem solution (u w : ℕ → ℝ)
    (hw : ∀ n, 1 ≤ n → w n = ∑ k ∈ Finset.range n, u k) :
    liminf (fun n => (u n : EReal)) atTop ≤ liminf (fun n => ((w n / n : ℝ) : EReal)) atTop ∧
    liminf (fun n => ((w n / n : ℝ) : EReal)) atTop ≤
      limsup (fun n => ((w n / n : ℝ) : EReal)) atTop ∧
    limsup (fun n => ((w n / n : ℝ) : EReal)) atTop ≤ limsup (fun n => (u n : EReal)) atTop := by
  refine ⟨?_, liminf_le_limsup, cesaro_limsup_le_970b u w hw⟩
  have h := cesaro_limsup_le_970b (fun n => -u n) (fun n => -w n)
    (by intro n hn; rw [hw n hn, Finset.sum_neg_distrib])
  have e1 : (fun n : ℕ => (((-w n) / n : ℝ) : EReal)) = -(fun n => ((w n / n : ℝ) : EReal)) := by
    funext n; simp [neg_div]
  have e2 : (fun n : ℕ => ((-u n : ℝ) : EReal)) = -(fun n => (u n : EReal)) := by
    funext n; simp
  rw [e1, e2, EReal.limsup_neg, EReal.limsup_neg, EReal.neg_le_neg_iff] at h
  exact h
