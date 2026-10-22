-- Prove2me | solution 1 for ProcessingNetworks.ProportionalFairness.entropy_lyapunov_drift_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:54:17.398789+00:00
-- url     : https://prove2.me/submissions/6595dd3d-8ac0-4f6d-ab59-b89948cb4a43

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedFluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedCore



namespace ProcessingNetworks.ProportionalFairness

open Filter Topology

lemma pf_coe_sum {L : ℕ} (g : Fin L → ℝ) : ((∑ k, g k : ℝ) : EReal) = ∑ k, ((g k : ℝ) : EReal) :=
  map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) g Finset.univ

noncomputable def pfRv {L : ℕ} (y x : Fin L → ℝ) : ℝ := ∑ k, y k * Real.log (x k)

lemma pf_f_eq_Rv {L : ℕ} (y x : Fin L → ℝ) (h : ∀ k, y k ≠ 0 → x k ≠ 0) :
    f y x = ((pfRv y x : ℝ) : EReal) := by
  unfold f pfRv
  rw [pf_coe_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : y k = 0
  · simp [hk]
  · rw [extLog, if_neg (h k hk)]
    exact (EReal.coe_mul _ _).symm

lemma pf_f_eq_bot {L : ℕ} (y x : Fin L → ℝ) (k : Fin L) (hk : 0 < y k) (hx : x k = 0) :
    f y x = ⊥ := by
  unfold f
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), extLog, if_pos hx,
    EReal.coe_mul_bot_of_pos hk, EReal.bot_add]

lemma pf_dom_bound {L : ℕ} {S : Set (Fin L → ℝ)} (hdom : IsPFDomain S) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x ∈ S, ∀ k, |x k| ≤ B := by
  obtain ⟨r, hr⟩ := hdom.1.subset_closedBall 0
  refine ⟨max r 1, le_max_right _ _, fun x hx k => ?_⟩
  have h1 := hr hx
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have := norm_le_pi_norm x k
  rw [Real.norm_eq_abs] at this
  linarith [le_max_left r 1]

lemma pf_log_le_B {B x : ℝ} (hB : 1 ≤ B) (hx : |x| ≤ B) : Real.log x ≤ B := by
  rcases eq_or_ne x 0 with h | h
  · simp [h]; linarith
  · rw [← Real.log_abs]
    have := Real.log_le_sub_one_of_pos (abs_pos.mpr h)
    linarith

lemma pf_exists_max {L : ℕ} {S : Set (Fin L → ℝ)} (hdom : IsPFDomain S) (y : Fin L → ℝ)
    (hy : ∀ k, 0 ≤ y k) : ∃ x, IsPFMaximizer S y x := by
  obtain ⟨B, hB1, hB⟩ := pf_dom_bound hdom
  obtain ⟨p, hpS, hp⟩ := hdom.2.2.2.2
  set Y := ∑ k, y k with hY
  set V0 := pfRv y p with hV0
  have hev : ∀ k, ∀ᶠ δ in 𝓝[>] (0:ℝ), δ < p k ∧ (0 < y k → y k * Real.log δ + Y * B < V0) := by
    intro k
    refine (Filter.Tendsto.eventually_lt_const (hp k)
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)).and ?_
    by_cases hk : 0 < y k
    · have : Tendsto (fun δ => y k * Real.log δ + Y * B) (𝓝[>] 0) atBot :=
        tendsto_atBot_add_const_right _ _ (Real.tendsto_log_nhdsGT_zero.const_mul_atBot hk)
      exact (this.eventually (eventually_lt_atBot V0)).mono fun δ h _ => h
    · exact Eventually.of_forall fun δ h => absurd h hk
  obtain ⟨δ, hδall, hδpos⟩ := ((eventually_all.2 hev).and self_mem_nhdsWithin).exists
  have hδpos' : 0 < δ := hδpos
  set K : Set (Fin L → ℝ) := S ∩ ⋂ k, {x | 0 < y k → δ ≤ |x k|} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded (hdom.2.1.inter (isClosed_iInter fun k => ?_))
      (hdom.1.subset Set.inter_subset_left)
    by_cases hk : 0 < y k
    · simp only [hk, true_implies]
      exact isClosed_le continuous_const (continuous_apply k).abs
    · simp only [hk, false_implies, Set.ofPred_true]
      exact isClosed_univ
  have hpK : p ∈ K := ⟨hpS, Set.mem_iInter.2 fun k _ => by
    rw [abs_of_pos (hp k)]; exact (hδall k).1.le⟩
  have hne : ∀ x ∈ K, ∀ k, y k ≠ 0 → x k ≠ 0 := by
    intro x hx k hk h0
    have := (Set.mem_iInter.1 hx.2 k) (lt_of_le_of_ne (hy k) (Ne.symm hk))
    rw [h0, abs_zero] at this
    linarith
  have hcont : ContinuousOn (pfRv y) K := by
    unfold pfRv
    refine continuousOn_finsetSum _ fun k _ => ?_
    by_cases hk : y k = 0
    · simp only [hk, zero_mul]; exact continuousOn_const
    · exact continuousOn_const.mul (ContinuousOn.log (continuous_apply k).continuousOn
        fun x hx => hne x hx k hk)
  obtain ⟨x0, hx0K, hx0max⟩ := hKc.exists_isMaxOn ⟨p, hpK⟩ hcont
  refine ⟨x0, hx0K.1, fun w hw => ?_⟩
  rw [pf_f_eq_Rv y x0 (hne x0 hx0K)]
  by_cases hw0 : ∃ k, 0 < y k ∧ w k = 0
  · obtain ⟨k, hk, hk0⟩ := hw0
    rw [pf_f_eq_bot y w k hk hk0]; exact bot_le
  push_neg at hw0
  rw [pf_f_eq_Rv y w (fun k hk => hw0 k (lt_of_le_of_ne (hy k) (Ne.symm hk))),
    EReal.coe_le_coe_iff]
  by_cases hwK : w ∈ K
  · exact hx0max hwK
  · have : ∃ k, 0 < y k ∧ |w k| < δ := by
      by_contra hc
      push_neg at hc
      exact hwK ⟨hw, Set.mem_iInter.2 fun k hk => hc k hk⟩
    obtain ⟨k, hk, hwk⟩ := this
    have hwk0 : w k ≠ 0 := hw0 k hk
    have h1 : pfRv y w ≤ y k * Real.log (w k) + Y * B := by
      unfold pfRv
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hY, Finset.sum_mul]
      have : ∑ j ∈ Finset.univ.erase k, y j * Real.log (w j) ≤ ∑ j, y j * B := by
        refine (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (pf_log_le_B hB1 (hB w hw j)) (hy j)).trans ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun j _ _ => mul_nonneg (hy j) (by linarith)
      linarith
    have h2 : y k * Real.log (w k) < y k * Real.log δ := by
      apply mul_lt_mul_of_pos_left _ hk
      rw [← Real.log_abs]
      exact Real.log_lt_log (abs_pos.2 hwk0) hwk
    have h3 := (hδall k).2 hk
    have h4 : V0 ≤ pfRv y x0 := hx0max hpK
    linarith

lemma pf_max_ne_zero {L : ℕ} {S : Set (Fin L → ℝ)} (hdom : IsPFDomain S) (y : Fin L → ℝ)
    (x : Fin L → ℝ) (hx : IsPFMaximizer S y x) (k : Fin L) (hk : 0 < y k) : x k ≠ 0 := by
  obtain ⟨p, hpS, hp⟩ := hdom.2.2.2.2
  intro h0
  have h1 := hx.2 p hpS
  rw [pf_f_eq_bot y x k hk h0, pf_f_eq_Rv y p (fun j _ => (hp j).ne')] at h1
  exact EReal.coe_ne_bot _ (le_bot_iff.mp h1)



open Classical in
noncomputable def pfXm {L : ℕ} (S : Set (Fin L → ℝ)) (z : Fin L → ℝ) : Fin L → ℝ :=
  if h : ∃ x, IsPFMaximizer S z x then Classical.choose h else 0

lemma pf_psi_eq {L : ℕ} (S : Set (Fin L → ℝ)) (z : Fin L → ℝ) (ℓ : Fin L) (h : 0 < z ℓ) :
    psi S z ℓ = pfXm S z ℓ := by
  simp only [psi, if_pos h, pfXm]
  split_ifs <;> rfl

lemma pf_xm_max {L : ℕ} {S : Set (Fin L → ℝ)} (hdom : IsPFDomain S) (z : Fin L → ℝ)
    (hz : ∀ k, 0 ≤ z k) : IsPFMaximizer S z (pfXm S z) := by
  have h := pf_exists_max hdom z hz
  simp only [pfXm, dif_pos h]
  exact Classical.choose_spec h


/-- `d log(d/α) - d + α ≥ 0` for `d ≥ 0`, `α > 0`. -/
lemma dr_h_nonneg {d α : ℝ} (hd : 0 ≤ d) (hα : 0 < α) :
    0 ≤ d * Real.log (d / α) - d + α := by
  rcases hd.eq_or_lt with h | h
  · subst h; simp; exact hα.le
  · have := Real.one_sub_inv_le_log_of_pos (div_pos h hα)
    rw [inv_div] at this
    have h2 : d * (1 - α / d) ≤ d * Real.log (d / α) := mul_le_mul_of_nonneg_left this h.le
    have h3 : d * (1 - α / d) = d - α := by field_simp
    linarith

/-- per-source log-sum step. -/
lemma dr_logsum_term {p dk αk a α : ℝ} (hp : 0 ≤ p) (hdk : 0 ≤ dk) (hαk : 0 < αk)
    (ha : 0 < a) (hα : 0 < α) :
    p * dk * Real.log (a / α) + p * dk - a * (p * αk) / α ≤ p * dk * Real.log (dk / αk) := by
  rcases hp.eq_or_lt with h | h
  · subst h; simp
  rcases hdk.eq_or_lt with h2 | h2
  · subst h2; simp; positivity
  have key : dk * Real.log (a / α) + dk - a * αk / α ≤ dk * Real.log (dk / αk) := by
    have hl := Real.one_sub_inv_le_log_of_pos (show 0 < (dk / αk) / (a / α) by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at hl
    have h4 : dk * (1 - ((dk / αk) / (a / α))⁻¹) ≤ dk * (Real.log (dk / αk) - Real.log (a / α)) :=
      mul_le_mul_of_nonneg_left hl h2.le
    have h5 : dk * (1 - ((dk / αk) / (a / α))⁻¹) = dk - a * αk / α := by
      field_simp
    linarith
  have := mul_le_mul_of_nonneg_left key h.le
  calc p * dk * Real.log (a / α) + p * dk - a * (p * αk) / α
      = p * (dk * Real.log (a / α) + dk - a * αk / α) := by ring
    _ ≤ p * (dk * Real.log (dk / αk)) := this
    _ = p * dk * Real.log (dk / αk) := by ring

lemma dr_logsum {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (lam alpha d : Fin I → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hα : ∀ i, 0 < alpha i)
    (hd : ∀ i, 0 ≤ d i) (i : Fin I) (halpha : alpha i = lam i + ∑ k, P k i * alpha k) :
    (lam i + ∑ k, P k i * d k) * Real.log ((lam i + ∑ k, P k i * d k) / alpha i) ≤
      ∑ k, P k i * d k * Real.log (d k / alpha k) := by
  set a := lam i + ∑ k, P k i * d k with ha
  have hsum : 0 ≤ ∑ k, P k i * d k := Finset.sum_nonneg fun k _ => mul_nonneg (hP k i) (hd k)
  have ha0 : 0 ≤ a := add_nonneg (hlam i) hsum
  rcases ha0.eq_or_lt with h | h
  · rw [← h]; simp
    apply Finset.sum_nonneg
    intro k _
    have h1 : lam i = 0 := by linarith [hlam i]
    have h2 : ∑ k, P k i * d k = 0 := by linarith
    have h3 : P k i * d k = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (hP k i) (hd k))).1 h2 k
        (Finset.mem_univ k)
    rw [h3]; simp
  · have hterm : ∀ k, P k i * d k * Real.log (a / alpha i) + P k i * d k
        - a * (P k i * alpha k) / alpha i ≤ P k i * d k * Real.log (d k / alpha k) :=
      fun k => dr_logsum_term (hP k i) (hd k) (hα k) h (hα i)
    have hs := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hterm k
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
    rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.mul_sum] at hs
    have hext : lam i * Real.log (a / alpha i) + lam i - a * lam i / alpha i ≤ 0 := by
      have := Real.log_le_sub_one_of_pos (div_pos h (hα i))
      have h2 : lam i * Real.log (a / alpha i) ≤ lam i * (a / alpha i - 1) :=
        mul_le_mul_of_nonneg_left this (hlam i)
      have h3 : lam i * (a / alpha i - 1) = a * lam i / alpha i - lam i := by ring
      linarith
    have hαi := hα i
    have e1 : a * (lam i + ∑ k, P k i * alpha k) / alpha i = a := by
      rw [← halpha]; field_simp
    have : a * Real.log (a / alpha i) = (lam i * Real.log (a / alpha i) + lam i
        - a * lam i / alpha i) + ((∑ k, P k i * d k) * Real.log (a / alpha i)
        + ∑ k, P k i * d k - a * (∑ k, P k i * alpha k) / alpha i) := by
      have : a * lam i / alpha i + a * (∑ k, P k i * alpha k) / alpha i = a := by
        have e2 := e1; rw [mul_add, add_div] at e2; exact e2
      rw [ha]; linarith
    linarith

/-- The key inequality: drift plus the "B" term is nonpositive. -/
lemma dr_key {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hProw : ∀ i, ∑ j, P i j ≤ 1)
    (lam alpha d : Fin I → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hα : ∀ i, 0 < alpha i)
    (hd : ∀ i, 0 ≤ d i) (halpha : ∀ i, alpha i = lam i + ∑ k, P k i * alpha k)
    (hd0 : ∀ i, d i = 0 → lam i + ∑ k, P k i * d k = 0) :
    ∑ i, (lam i + ∑ k, P k i * d k - d i) * Real.log (d i / alpha i) +
      ∑ i, ((lam i + ∑ k, P k i * d k) * Real.log ((lam i + ∑ k, P k i * d k) / d i)
        - (lam i + ∑ k, P k i * d k) + d i) ≤ 0 := by
  set a : Fin I → ℝ := fun i => lam i + ∑ k, P k i * d k with ha
  have ha0 : ∀ i, 0 ≤ a i := fun i =>
    add_nonneg (hlam i) (Finset.sum_nonneg fun k _ => mul_nonneg (hP k i) (hd k))
  -- pointwise identity
  have hpt : ∀ i, (a i - d i) * Real.log (d i / alpha i) +
      (a i * Real.log (a i / d i) - a i + d i) =
      a i * Real.log (a i / alpha i) - d i * Real.log (d i / alpha i) - (a i - d i) := by
    intro i
    rcases (hd i).eq_or_lt with h | h
    · have : a i = 0 := hd0 i h.symm
      rw [this, ← h]; simp
    rcases (ha0 i).eq_or_lt with h2 | h2
    · rw [← h2]; simp
    rw [Real.log_div h2.ne' h.ne', Real.log_div h.ne' (hα i).ne',
      Real.log_div h2.ne' (hα i).ne']
    ring
  have hsum1 : ∑ i, (a i - d i) * Real.log (d i / alpha i) +
      ∑ i, (a i * Real.log (a i / d i) - a i + d i) =
      ∑ i, a i * Real.log (a i / alpha i) - ∑ i, d i * Real.log (d i / alpha i)
        - ∑ i, (a i - d i) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => hpt i
  show ∑ i, (a i - d i) * Real.log (d i / alpha i) +
      ∑ i, (a i * Real.log (a i / d i) - a i + d i) ≤ 0
  rw [hsum1]
  have hls : ∑ i, a i * Real.log (a i / alpha i) ≤
      ∑ i, ∑ k, P k i * d k * Real.log (d k / alpha k) :=
    Finset.sum_le_sum fun i _ => dr_logsum P hP lam alpha d hlam hα hd i (halpha i)
  rw [Finset.sum_comm] at hls
  have hswap : ∑ k, ∑ i, P k i * d k * Real.log (d k / alpha k) =
      ∑ k, (∑ i, P k i) * (d k * Real.log (d k / alpha k)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hswap] at hls
  have hA : ∑ i, (a i - d i) = ∑ k, (1 - ∑ i, P k i) * (alpha k - d k) := by
    have e1 : ∑ i, a i = ∑ i, lam i + ∑ k, (∑ i, P k i) * d k := by
      simp only [a, Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul]
    have e2 : ∑ i, lam i = ∑ k, (1 - ∑ i, P k i) * alpha k := by
      have : ∑ i, lam i = ∑ i, alpha i - ∑ k, (∑ i, P k i) * alpha k := by
        have : ∑ i, alpha i = ∑ i, lam i + ∑ k, (∑ i, P k i) * alpha k := by
          conv_lhs => rw [Finset.sum_congr rfl fun i _ => halpha i]
          rw [Finset.sum_add_distrib, Finset.sum_comm]
          congr 1
          exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul]
        linarith
      rw [this, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [Finset.sum_sub_distrib, e1, e2]
    have : ∑ k, (1 - ∑ i, P k i) * (alpha k - d k) =
        ∑ k, (1 - ∑ i, P k i) * alpha k + ∑ k, (∑ i, P k i) * d k - ∑ k, d k := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    linarith
  rw [hA]
  have hfin : ∑ k, (∑ i, P k i) * (d k * Real.log (d k / alpha k)) -
      ∑ k, d k * Real.log (d k / alpha k) - ∑ k, (1 - ∑ i, P k i) * (alpha k - d k) =
      - ∑ k, (1 - ∑ i, P k i) * (d k * Real.log (d k / alpha k) - d k + alpha k) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hnn : 0 ≤ ∑ k, (1 - ∑ i, P k i) * (d k * Real.log (d k / alpha k) - d k + alpha k) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (by linarith [hProw k]) (dr_h_nonneg (hd k) (hα k))
  linarith

/-- lower bound on a single B-term. -/
lemma dr_b_lower {a d c D : ℝ} (ha : 0 ≤ a) (hd : 0 < d) (hc : 0 < c) (hcd : a ≤ d - c)
    (hD : d ≤ D) :
    c ^ 2 / (4 * D) ≤ a * Real.log (a / d) - a + d := by
  have hDpos : 0 < D := lt_of_lt_of_le hd hD
  have hmain : (d - a) ^ 2 / (4 * d) ≤ a * Real.log (a / d) - a + d := by
    rcases ha.eq_or_lt with h | h
    · rw [← h]; simp
      rw [div_le_iff₀ (by positivity)]; nlinarith
    · set u := a / d with hu
      have hu0 : 0 < u := div_pos h hd
      have hu1 : u ≤ 1 := by rw [hu, div_le_one hd]; linarith
      have hsq : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
      have hlog : Real.log u = 2 * Real.log (Real.sqrt u) := by
        rw [Real.log_sqrt hu0.le]; ring
      have h1 := Real.one_sub_inv_le_log_of_pos hsq
      -- u log u ≥ 2u - 2√u
      have hss : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
      have h2 : u * Real.log u ≥ 2 * u - 2 * Real.sqrt u := by
        rw [hlog]
        have : u * (1 - (Real.sqrt u)⁻¹) = u - Real.sqrt u := by
          field_simp; nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h1 hu0.le]
      -- h(u) ≥ (1 - √u)^2 ≥ (1-u)^2/4
      have hsq1 : Real.sqrt u ≤ 1 := by
        rw [← hss] at hu1; nlinarith
      have h3 : u * Real.log u - u + 1 ≥ (1 - u) ^ 2 / 4 := by
        have : (1 - u) = (1 - Real.sqrt u) * (1 + Real.sqrt u) := by nlinarith
        have h4 : (1 - u) ^ 2 ≤ 4 * (1 - Real.sqrt u) ^ 2 := by
          rw [this]; nlinarith [sq_nonneg (1 - Real.sqrt u)]
        nlinarith
      have hal : a * Real.log (a / d) - a + d = d * (u * Real.log u - u + 1) := by
        rw [hu]; field_simp
      rw [hal]
      have : (d - a) ^ 2 / (4 * d) = d * ((1 - u) ^ 2 / 4) := by
        rw [hu]; field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left h3 hd.le
  refine le_trans ?_ hmain
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : c ≤ d - a := by linarith
  have h5 : c ^ 2 ≤ (d - a) ^ 2 := by nlinarith
  nlinarith

/-- each B-term is nonnegative. -/
lemma dr_b_nonneg {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hd0 : d = 0 → a = 0) :
    0 ≤ a * Real.log (a / d) - a + d := by
  rcases hd.eq_or_lt with h | h
  · rw [hd0 h.symm, ← h]; simp
  rcases ha.eq_or_lt with h2 | h2
  · rw [← h2]; simp; exact h.le
  have := Real.one_sub_inv_le_log_of_pos (div_pos h2 h)
  rw [inv_div] at this
  have h3 : a * (1 - d / a) ≤ a * Real.log (a / d) := mul_le_mul_of_nonneg_left this h2.le
  have h4 : a * (1 - d / a) = a - d := by field_simp
  linarith



lemma dr_pow_nonneg {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) (hP : ∀ i j, 0 ≤ P i j) :
    ∀ n i j, 0 ≤ (P ^ n) i j := by
  intro n
  induction n with
  | zero => intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (hP k j)

lemma dr_pow_rowsum {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hProw : ∀ i, ∑ j, P i j ≤ 1) : ∀ n i, ∑ j, (P ^ n) i j ≤ 1 := by
  intro n
  induction n with
  | zero => intro i; simp [Matrix.one_apply]
  | succ n ih =>
    intro i
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    calc ∑ k, ∑ j, (P ^ n) i k * P k j = ∑ k, (P ^ n) i k * ∑ j, P k j := by
          refine Finset.sum_congr rfl fun k _ => ?_; rw [Finset.mul_sum]
      _ ≤ ∑ k, (P ^ n) i k * 1 :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hProw k) (dr_pow_nonneg P hP n i k)
      _ ≤ 1 := by simpa using ih i

lemma dr_pow_le_one {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hProw : ∀ i, ∑ j, P i j ≤ 1) (n : ℕ) (i j : Fin I) : (P ^ n) i j ≤ 1 :=
  le_trans (Finset.single_le_sum (f := fun j => (P ^ n) i j)
    (fun j _ => dr_pow_nonneg P hP n i j) (Finset.mem_univ j)) (dr_pow_rowsum P hP hProw n i)

lemma dr_iter {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hProw : ∀ i, ∑ j, P i j ≤ 1) (e : Fin I → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (H : ∀ i, e i ≤ ∑ k, P k i * e k + c) :
    ∀ (n : ℕ) (i : Fin I), e i ≤ ∑ j, (P ^ n) j i * e j + c * (n : ℝ) * (I : ℝ) := by
  intro n
  induction n with
  | zero => intro i; simp [Matrix.one_apply]
  | succ n ih =>
    intro i
    have h1 := ih i
    have h2 : ∑ j, (P ^ n) j i * e j ≤ ∑ j, (P ^ n) j i * (∑ k, P k j * e k + c) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (H j) (dr_pow_nonneg P hP n j i)
    have h3 : ∑ j, (P ^ n) j i * (∑ k, P k j * e k + c) =
        ∑ k, (P ^ (n + 1)) k i * e k + c * ∑ j, (P ^ n) j i := by
      simp only [mul_add, Finset.sum_add_distrib, pow_succ', Matrix.mul_apply, Finset.sum_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
      · exact Finset.sum_congr rfl fun j _ => by ring
    have h4 : ∑ j, (P ^ n) j i ≤ I := by
      calc ∑ j, (P ^ n) j i ≤ ∑ j : Fin I, (1 : ℝ) :=
            Finset.sum_le_sum fun j _ => dr_pow_le_one P hP hProw n j i
        _ = I := by simp
    have h5 : c * ∑ j, (P ^ n) j i ≤ c * I := mul_le_mul_of_nonneg_left h4 hc
    push_cast
    nlinarith

lemma dr_flow {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hProw : ∀ i, ∑ j, P i j ≤ 1) (hI : 0 < I) (n0 : ℕ)
    (hn0 : ∀ j i, (P ^ n0) j i ≤ 1 / (2 * I)) (e : Fin I → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (H : ∀ i, e i ≤ ∑ k, P k i * e k + c) (i0 : Fin I) (hi0 : 0 ≤ e i0) :
    e i0 ≤ 2 * c * n0 * I := by
  obtain ⟨im, _, him⟩ := Finset.exists_max_image Finset.univ e ⟨i0, Finset.mem_univ _⟩
  have hE : 0 ≤ e im := le_trans hi0 (him i0 (Finset.mem_univ _))
  have h1 := dr_iter P hP hProw e c hc H n0 im
  have h2 : ∑ j, (P ^ n0) j im * e j ≤ ∑ j : Fin I, (1 / (2 * I)) * e im :=
    Finset.sum_le_sum fun j _ => le_trans
      (mul_le_mul_of_nonneg_left (him j (Finset.mem_univ _)) (dr_pow_nonneg P hP n0 j im))
      (mul_le_mul_of_nonneg_right (hn0 j im) hE)
  have h3 : ∑ j : Fin I, (1 / (2 * I)) * e im = e im / 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (I : ℝ) ≠ 0 := by positivity
    field_simp
  have h4 : e im ≤ 2 * c * n0 * I := by linarith
  exact le_trans (him i0 (Finset.mem_univ _)) h4

/-- First-order optimality condition for a PF maximizer. -/
lemma dr_foc {L : ℕ} {S : Set (Fin L → ℝ)} (hdom : IsPFDomain S) (y : Fin L → ℝ)
    (hy : ∀ k, 0 ≤ y k) (x : Fin L → ℝ) (hx : IsPFMaximizer S y x)
    (hxpos : ∀ k, 0 < y k → 0 < x k) (p : Fin L → ℝ) (hpS : p ∈ S) (hp : ∀ k, 0 ≤ p k) :
    ∑ k, y k * (p k / x k) ≤ ∑ k, y k := by
  set g : ℝ → ℝ := fun s => ∑ k, y k * ((p k - x k) / ((1 - s) * x k + s * p k)) with hg
  have hcoe : ∀ (v : Fin L → ℝ), (∀ k, y k ≠ 0 → v k ≠ 0) →
      f y v = ((∑ k, y k * Real.log (v k) : ℝ) : EReal) := by
    intro v hv
    unfold f
    rw [pf_coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : y k = 0
    · simp [hk]
    · show (y k : EReal) * extLog (v k) = ((y k * Real.log (v k) : ℝ) : EReal)
      rw [extLog, if_neg (hv k hk)]
      exact (EReal.coe_mul _ _).symm
  have hneg : ∀ s ∈ Set.Ioo (0:ℝ) 1, g s ≤ 0 := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    set w : Fin L → ℝ := fun k => (1 - s) * x k + s * p k with hw
    have hwS : w ∈ S := by
      have := hdom.2.2.1 hx.1 hpS (by linarith : (0:ℝ) ≤ 1 - s) hs0.le (by ring)
      convert this using 1
      funext k; simp [w, smul_eq_mul]
    have hwpos : ∀ k, 0 < y k → 0 < w k := fun k hk => by
      have := hxpos k hk; have := hp k; simp only [w]; nlinarith
    have hle : ∑ k, y k * Real.log (w k) ≤ ∑ k, y k * Real.log (x k) := by
      have := hx.2 w hwS
      rwa [hcoe w (fun k hk => (hwpos k (lt_of_le_of_ne (hy k) (Ne.symm hk))).ne'),
        hcoe x (fun k hk => (hxpos k (lt_of_le_of_ne (hy k) (Ne.symm hk))).ne'),
        EReal.coe_le_coe_iff] at this
    have hterm : ∀ k, y k * (s * ((p k - x k) / w k)) ≤
        y k * Real.log (w k) - y k * Real.log (x k) := by
      intro k
      rcases (hy k).eq_or_lt with h | h
      · simp [← h]
      · have hw' := hwpos k h; have hx' := hxpos k h
        rw [← mul_sub, ← Real.log_div hw'.ne' hx'.ne']
        apply mul_le_mul_of_nonneg_left _ h.le
        have := Real.one_sub_inv_le_log_of_pos (div_pos hw' hx')
        rw [inv_div] at this
        have e : s * ((p k - x k) / w k) = 1 - x k / w k := by
          field_simp; simp only [w]; ring
        rw [e]; exact this
    have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hterm k
    rw [Finset.sum_sub_distrib] at hsum
    have : s * g s ≤ 0 := by
      simp only [hg, Finset.mul_sum]
      have : ∑ k, s * (y k * ((p k - x k) / ((1 - s) * x k + s * p k))) =
          ∑ k, y k * (s * ((p k - x k) / w k)) :=
        Finset.sum_congr rfl fun k _ => by simp only [w]; ring
      rw [this]; linarith
    by_contra hpos
    push Not at hpos
    nlinarith [mul_pos hs0 hpos]
  have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), g s ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs using hneg s hs
  have htend : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 (g 0)) := by
    have : ∀ k, ContinuousAt (fun s : ℝ => y k * ((p k - x k) / ((1 - s) * x k + s * p k))) 0 := by
      intro k
      rcases (hy k).eq_or_lt with h | h
      · simp [← h]; exact continuousAt_const
      · refine continuousAt_const.mul (continuousAt_const.div ?_ ?_)
        · fun_prop
        · simp; exact (hxpos k h).ne'
    exact tendsto_finsetSum _ fun k _ => (this k).tendsto.mono_left nhdsWithin_le_nhds
  have h0 : g 0 ≤ 0 := le_of_tendsto htend hev
  have : g 0 = ∑ k, y k * (p k / x k) - ∑ k, y k := by
    simp only [hg, sub_zero, one_mul, zero_mul, add_zero]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases (hy k).eq_or_lt with h | h
    · simp [← h]
    · have hx' := (hxpos k h).ne'
      rw [sub_div, div_self hx']; ring
  linarith


theorem entropy_drift_core {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0))
    (alpha : Fin I → ℝ) (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i)
    (hload : ∃ a ∈ dat.TildeAllocSet,
      ∀ ℓ, groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ < a ℓ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (Ah Dh Th Zh : ℝ → Fin I → ℝ), IsPFFluidModelSolution dat Ah Dh Th Zh →
        ∀ t : ℝ, 0 < t → RegularPoint Ah Dh Th Zh t → Zh t ≠ 0 →
          ∑ i, deriv (fun s => Zh s i) t * Real.log (deriv (fun s => Dh s i) t / alpha i) ≤ -ε := by
  rcases Nat.eq_zero_or_pos I with hI0 | hI
  · subst hI0
    exact ⟨1, one_pos, fun Ah Dh Th Zh _ t _ _ hZ => (hZ (funext fun i => i.elim0)).elim⟩
  have halpha' : ∀ i, alpha i = dat.lam i + ∑ k, dat.P k i * alpha k := fun i =>
    congrFun halpha i
  obtain ⟨a, haS, ha⟩ := hload
  obtain ⟨B, hB1, hB⟩ := pf_dom_bound hdom
  set ρ : Fin L → ℝ := groupAggregate dat.grp (fun i => alpha i * dat.m i) with hρ
  have hρnn : ∀ ℓ, 0 ≤ ρ ℓ := fun ℓ =>
    Finset.sum_nonneg fun i _ => (mul_pos (hα i) (dat.hm i)).le
  have hapos : ∀ ℓ, 0 < a ℓ := fun ℓ => lt_of_le_of_lt (hρnn ℓ) (ha ℓ)
  have haB : ∀ ℓ, a ℓ ≤ B := fun ℓ => le_trans (le_abs_self _) (hB a haS ℓ)
  obtain ⟨δ, hδ, hδpos⟩ : ∃ δ : ℝ, (∀ ℓ, δ ≤ a ℓ - ρ ℓ) ∧ 0 < δ := by
    have hev : ∀ ℓ, ∀ᶠ δ in 𝓝[>] (0:ℝ), δ ≤ a ℓ - ρ ℓ := fun ℓ =>
      eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds (by linarith [ha ℓ]))
    exact ((eventually_all.2 hev).and self_mem_nhdsWithin).exists
  have hδpos' : (0:ℝ) < δ := hδpos
  have hδB : δ ≤ B := by
    have := hδ (dat.grp ⟨0, hI⟩)
    linarith [hρnn (dat.grp ⟨0, hI⟩), haB (dat.grp ⟨0, hI⟩)]
  set θ : ℝ := 1 - δ / (2 * B) with hθ
  have hBpos : 0 < B := by linarith
  have hθ0 : 0 < θ := by
    have : δ / (2 * B) < 1 := by rw [div_lt_one (by positivity)]; linarith
    simp only [θ]; linarith
  have hθ1 : θ < 1 := by
    have : 0 < δ / (2 * B) := by positivity
    simp only [θ]; linarith
  have hρθ : ∀ ℓ, ρ ℓ ≤ θ * a ℓ := by
    intro ℓ
    have h1 : δ * a ℓ / (2 * B) ≤ δ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [haB ℓ, hapos ℓ]
    have h2 : θ * a ℓ = a ℓ - δ * a ℓ / (2 * B) := by simp only [θ]; ring
    linarith [hδ ℓ]
  obtain ⟨αm, hαm, hαmpos⟩ : ∃ αm : ℝ, (∀ i, αm ≤ alpha i) ∧ 0 < αm := by
    have hev : ∀ i, ∀ᶠ δ in 𝓝[>] (0:ℝ), δ ≤ alpha i := fun i =>
      eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds (hα i))
    exact ((eventually_all.2 hev).and self_mem_nhdsWithin).exists
  have hαmpos' : (0:ℝ) < αm := hαmpos
  obtain ⟨mm, hmm, hmmpos⟩ : ∃ mm : ℝ, (∀ i, mm ≤ dat.m i) ∧ 0 < mm := by
    have hev : ∀ i, ∀ᶠ δ in 𝓝[>] (0:ℝ), δ ≤ dat.m i := fun i =>
      eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds (dat.hm i))
    exact ((eventually_all.2 hev).and self_mem_nhdsWithin).exists
  have hmmpos' : (0:ℝ) < mm := hmmpos
  obtain ⟨n0, hn0, hn0pos⟩ : ∃ n0 : ℕ, (∀ j i, (dat.P ^ n0) j i ≤ 1 / (2 * I)) ∧ 1 ≤ n0 := by
    have hev : ∀ j i, ∀ᶠ n in atTop, (dat.P ^ n) j i ≤ 1 / (2 * I) := fun j i =>
      (hP_transient j i).eventually (eventually_le_nhds (by positivity))
    exact ((eventually_all.2 fun j => eventually_all.2 (hev j)).and (eventually_ge_atTop 1)).exists
  have hn0pos' : (0:ℝ) < n0 := by exact_mod_cast hn0pos
  have hIpos' : (0:ℝ) < I := by exact_mod_cast hI
  set R : ℝ := 1 / θ with hR
  have hR1 : 1 < R := one_lt_one_div hθ0 hθ1
  set c0 : ℝ := (R - 1) * αm / (4 * n0 * I) with hc0
  have hc0pos : 0 < c0 := div_pos (mul_pos (by linarith) hαmpos) (by positivity)
  set Dm : ℝ := B / mm with hDm
  have hDmpos : 0 < Dm := div_pos hBpos hmmpos
  refine ⟨c0 ^ 2 / (4 * Dm), by positivity, ?_⟩
  intro Ah Dh Th Zh hsol t ht hreg hZne
  obtain ⟨hZeq, hZnn, hAeq, hDeq, ⟨hT0, hTmono, _⟩, hTd⟩ := hsol
  obtain ⟨hAd, hDd, hTd', hZd⟩ := hreg
  set Z : Fin I → ℝ := Zh t with hZ
  set Y : Fin L → ℝ := groupAggregate dat.grp Z with hY
  set d : Fin I → ℝ := fun i => deriv (fun s => Dh s i) t with hd
  set zd : Fin I → ℝ := fun i => deriv (fun s => Zh s i) t with hzd
  set av : Fin I → ℝ := fun i => dat.lam i + ∑ k, dat.P k i * d k with hav
  have hDi : ∀ i, DifferentiableAt ℝ (fun s => Dh s i) t := fun i => differentiableAt_pi.1 hDd i
  -- F1
  have hF1 : ∀ i, zd i = av i - d i := by
    intro i
    have hs : HasDerivAt (fun s => ∑ k, dat.P k i * Dh s k) (∑ k, dat.P k i * d k) t :=
      HasDerivAt.fun_sum fun k _ => (hDi k).hasDerivAt.const_mul _
    have hl : HasDerivAt (fun s => dat.lam i * s) (dat.lam i * 1) t :=
      (hasDerivAt_id' t).const_mul _
    have h1 : HasDerivAt (fun s => Zh 0 i + (dat.lam i * s + ∑ k, dat.P k i * Dh s k) - Dh s i)
        (0 + (dat.lam i * 1 + ∑ k, dat.P k i * d k) - d i) t :=
      ((hasDerivAt_const t (Zh 0 i)).add (hl.add hs)).sub (hDi i).hasDerivAt
    have h2 : (fun s => Zh s i) =ᶠ[𝓝 t]
        fun s => Zh 0 i + (dat.lam i * s + ∑ k, dat.P k i * Dh s k) - Dh s i := by
      filter_upwards [lt_mem_nhds ht] with s hs
      rw [congrFun (hZeq s hs.le) i, hAeq s hs.le i]
    show deriv (fun s => Zh s i) t = _
    rw [(h1.congr_of_eventuallyEq h2).deriv]; simp only [av]; ring
  -- F2
  have hF2 : ∀ i, Z i = 0 → zd i = 0 := by
    intro i hi
    apply IsLocalMin.deriv_eq_zero
    filter_upwards [lt_mem_nhds ht] with s hs
    show Zh t i ≤ Zh s i
    rw [show Zh t i = 0 from hi]; exact hZnn s hs.le i
  -- F3
  have hF3 : ∀ i, 0 < Z i →
      d i = psi dat.TildeAllocSet Y (dat.grp i) * Z i / Y (dat.grp i) / dat.m i := by
    intro i hi
    have hd := (hTd t ht i hi).div_const (dat.m i)
    have := hd.congr_of_eventuallyEq (f₁ := fun s => Dh s i)
      (by filter_upwards [lt_mem_nhds ht] with s hs; exact hDeq s hs.le i)
    exact this.deriv
  -- F4
  have hF4 : ∀ i, 0 ≤ d i := by
    intro i
    have hmono : Monotone (fun u => Th u i) := fun x y hxy => hTmono hxy i
    have heq : (fun s => Dh s i) =ᶠ[𝓝 t] fun s => Th s i / dat.m i := by
      filter_upwards [lt_mem_nhds ht] with s hs; exact hDeq s hs.le i
    show 0 ≤ deriv (fun s => Dh s i) t
    rw [heq.deriv_eq, deriv_div_const]
    exact div_nonneg hmono.deriv_nonneg (dat.hm i).le
  have hYnn : ∀ ℓ, 0 ≤ Y ℓ := fun ℓ => Finset.sum_nonneg fun i _ => hZnn t ht.le i
  set xm : Fin L → ℝ := pfXm dat.TildeAllocSet Y with hxm
  have hxmmax : IsPFMaximizer dat.TildeAllocSet Y xm := pf_xm_max hdom Y hYnn
  have hZY : ∀ i, Z i ≤ Y (dat.grp i) := fun i =>
    Finset.single_le_sum (f := fun j => Z j) (fun j _ => hZnn t ht.le j)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
  have hxmpos : ∀ ℓ, 0 < Y ℓ → 0 < xm ℓ := by
    intro ℓ hℓ
    have : ∃ i, dat.grp i = ℓ ∧ 0 < Z i := by
      by_contra hc
      push Not at hc
      have : Y ℓ ≤ 0 := Finset.sum_nonpos fun i hi => hc i (Finset.mem_filter.1 hi).2
      linarith
    obtain ⟨i, rfl, hi⟩ := this
    have hne : xm (dat.grp i) ≠ 0 := pf_max_ne_zero hdom _ _ hxmmax _ hℓ
    have h4 := hF4 i
    rw [hF3 i hi, pf_psi_eq _ _ _ hℓ] at h4
    rcases lt_or_gt_of_ne hne with h | h
    · exfalso
      have : xm (dat.grp i) * Z i / Y (dat.grp i) / dat.m i < 0 :=
        div_neg_of_neg_of_pos (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h hi) hℓ) (dat.hm i)
      linarith
    · exact h
  have hF5 : ∀ i, 0 < Z i → 0 < psi dat.TildeAllocSet Y (dat.grp i) := fun i hi => by
    have hℓ := lt_of_lt_of_le hi (hZY i)
    rw [pf_psi_eq _ _ _ hℓ]; exact hxmpos _ hℓ
  have hdpos : ∀ i, 0 < Z i → 0 < d i := fun i hi => by
    rw [hF3 i hi]
    exact div_pos (div_pos (mul_pos (hF5 i hi) hi) (lt_of_lt_of_le hi (hZY i))) (dat.hm i)
  have hdle : ∀ i, 0 < Z i → d i ≤ Dm := by
    intro i hi
    rw [hF3 i hi]
    have hℓ := lt_of_lt_of_le hi (hZY i)
    rw [pf_psi_eq _ _ _ hℓ]
    have hx : xm (dat.grp i) ≤ B := le_trans (le_abs_self _) (hB xm hxmmax.1 _)
    have h1 : xm (dat.grp i) * Z i / Y (dat.grp i) ≤ xm (dat.grp i) := by
      rw [div_le_iff₀ hℓ]; exact mul_le_mul_of_nonneg_left (hZY i) (hxmpos _ hℓ).le
    calc xm (dat.grp i) * Z i / Y (dat.grp i) / dat.m i ≤ B / dat.m i :=
          div_le_div_of_nonneg_right (h1.trans hx) (dat.hm i).le
      _ ≤ B / mm := div_le_div_of_nonneg_left hBpos.le hmmpos (hmm i)
  -- PF step: some class has d i ≥ R * alpha i
  have hfoc := dr_foc hdom Y hYnn xm hxmmax hxmpos a haS (fun ℓ => (hapos ℓ).le)
  have hsum1 : ∑ ℓ, Y ℓ * (ρ ℓ / xm ℓ) ≤ θ * ∑ ℓ, Y ℓ := by
    have : ∀ ℓ, Y ℓ * (ρ ℓ / xm ℓ) ≤ θ * (Y ℓ * (a ℓ / xm ℓ)) := by
      intro ℓ
      rcases (hYnn ℓ).eq_or_lt with h | h
      · rw [← h]; simp
      · have hx := hxmpos ℓ h
        have : ρ ℓ / xm ℓ ≤ θ * (a ℓ / xm ℓ) := by
          rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (hρθ ℓ) hx.le
        calc Y ℓ * (ρ ℓ / xm ℓ) ≤ Y ℓ * (θ * (a ℓ / xm ℓ)) :=
              mul_le_mul_of_nonneg_left this h.le
          _ = θ * (Y ℓ * (a ℓ / xm ℓ)) := by ring
    calc ∑ ℓ, Y ℓ * (ρ ℓ / xm ℓ) ≤ ∑ ℓ, θ * (Y ℓ * (a ℓ / xm ℓ)) :=
          Finset.sum_le_sum fun ℓ _ => this ℓ
      _ = θ * ∑ ℓ, Y ℓ * (a ℓ / xm ℓ) := by rw [Finset.mul_sum]
      _ ≤ θ * ∑ ℓ, Y ℓ := mul_le_mul_of_nonneg_left hfoc hθ0.le
  set g : Fin I → ℝ := fun i => alpha i * dat.m i * (Y (dat.grp i) / xm (dat.grp i)) with hg
  have hsum2 : ∑ ℓ, Y ℓ * (ρ ℓ / xm ℓ) = ∑ i, g i := by
    rw [← Finset.sum_fiberwise Finset.univ dat.grp g]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [hρ, groupAggregate, g, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]; ring
  have hsum3 : ∑ ℓ, Y ℓ = ∑ i, Z i := by
    rw [← Finset.sum_fiberwise Finset.univ dat.grp Z]
    rfl
  have hgnn : ∀ i, 0 ≤ g i := by
    intro i
    simp only [g]
    rcases (hYnn (dat.grp i)).eq_or_lt with h | h
    · rw [← h]; simp
    · exact mul_nonneg (mul_pos (hα i) (dat.hm i)).le (div_pos h (hxmpos _ h)).le
  have hgZ : ∀ i, 0 < Z i → g i = Z i * alpha i / d i := by
    intro i hi
    have hℓ := lt_of_lt_of_le hi (hZY i)
    rw [hF3 i hi, pf_psi_eq _ _ _ hℓ, ← hxm]
    simp only [g]
    have := hxmpos _ hℓ
    have := dat.hm i
    field_simp
  obtain ⟨i0, hi0⟩ : ∃ i, 0 < Z i := by
    by_contra hc
    push Not at hc
    exact hZne (funext fun i => le_antisymm (hc i) (hZnn t ht.le i))
  obtain ⟨is, hZis, hdis⟩ : ∃ i, 0 < Z i ∧ R * alpha i ≤ d i := by
    by_contra hc
    push Not at hc
    have hlt : ∀ i, θ * Z i ≤ g i := by
      intro i
      rcases (hZnn t ht.le i).eq_or_lt with h | h
      · rw [show Z i = 0 from h.symm]; simp; exact hgnn i
      · rw [hgZ i h]
        have hdi := hdpos i h
        have h2 := hc i h
        rw [hR, div_mul_eq_mul_div, one_mul, lt_div_iff₀ hθ0] at h2
        rw [le_div_iff₀ hdi]; nlinarith [mul_lt_mul_of_pos_left h2 h]
    have hstrict : θ * Z i0 < g i0 := by
      rw [hgZ i0 hi0]
      have hdi := hdpos i0 hi0
      have h2 := hc i0 hi0
      rw [hR, div_mul_eq_mul_div, one_mul, lt_div_iff₀ hθ0] at h2
      rw [lt_div_iff₀ hdi]; nlinarith [mul_lt_mul_of_pos_left h2 hi0]
    have : ∑ i, θ * Z i < ∑ i, g i :=
      Finset.sum_lt_sum (fun i _ => hlt i) ⟨i0, Finset.mem_univ _, hstrict⟩
    rw [← Finset.mul_sum, ← hsum3, ← hsum2] at this
    linarith
  -- flow step: some class has zd k < -c0
  set e : Fin I → ℝ := fun i => d i - alpha i with he
  obtain ⟨k, hk⟩ : ∃ k, zd k < -c0 := by
    by_contra hc
    push Not at hc
    have H : ∀ i, e i ≤ ∑ j, dat.P j i * e j + c0 := by
      intro i
      have h1 := hc i
      rw [hF1 i] at h1
      have h2 : av i - d i = ∑ j, dat.P j i * e j - e i := by
        simp only [av, e, mul_sub, Finset.sum_sub_distrib]
        linarith [halpha' i]
      linarith
    have := dr_flow dat.P hP_nonneg hP_rowsum hI n0 hn0 e c0 hc0pos.le H is
      (by simp only [e]; nlinarith [hα is])
    have h3 : (R - 1) * αm ≤ e is := by
      simp only [e]; nlinarith [hαm is, hα is]
    have h4 : 2 * c0 * n0 * I = (R - 1) * αm / 2 := by
      simp only [c0]; field_simp; ring
    rw [h4] at this
    linarith [mul_pos (by linarith : (0:ℝ) < R - 1) hαmpos']
  have hZk : 0 < Z k := by
    rcases (hZnn t ht.le k).eq_or_lt with h | h
    · exfalso; have := hF2 k h.symm; linarith
    · exact h
  have hdk := hdpos k hZk
  have havnn : ∀ i, 0 ≤ av i := fun i =>
    add_nonneg (hlam i) (Finset.sum_nonneg fun j _ => mul_nonneg (hP_nonneg j i) (hF4 j))
  have hd0 : ∀ i, d i = 0 → av i = 0 := by
    intro i hi
    have hZi : Z i = 0 := by
      rcases (hZnn t ht.le i).eq_or_lt with h | h
      · exact h.symm
      · exfalso; have := hdpos i h; linarith
    have := hF2 i hZi
    rw [hF1 i] at this; linarith
  have hkey := dr_key dat.P hP_nonneg hP_rowsum dat.lam alpha d hlam hα hF4 halpha' hd0
  have hbk : c0 ^ 2 / (4 * Dm) ≤ av k * Real.log (av k / d k) - av k + d k :=
    dr_b_lower (havnn k) hdk hc0pos (by linarith [hF1 k]) (hdle k hZk)
  have hbsum : av k * Real.log (av k / d k) - av k + d k ≤
      ∑ i, (av i * Real.log (av i / d i) - av i + d i) :=
    Finset.single_le_sum (f := fun i => av i * Real.log (av i / d i) - av i + d i)
      (fun i _ => dr_b_nonneg (havnn i) (hF4 i) (hd0 i)) (Finset.mem_univ k)
  have hS : ∑ i, zd i * Real.log (d i / alpha i) = ∑ i, (av i - d i) * Real.log (d i / alpha i) :=
    Finset.sum_congr rfl fun i _ => by rw [hF1 i]
  have hfinal : ∑ i, zd i * Real.log (d i / alpha i) ≤ -(c0 ^ 2 / (4 * Dm)) := by
    rw [hS]; linarith
  exact hfinal

end ProcessingNetworks.ProportionalFairness

open ProcessingNetworks.ProportionalFairness


theorem solution
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0))
    (alpha : Fin I → ℝ) (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i)
    (hload : ∃ a ∈ dat.TildeAllocSet,
      ∀ ℓ, groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ < a ℓ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (Ah Dh Th Zh : ℝ → Fin I → ℝ), IsPFFluidModelSolution dat Ah Dh Th Zh →
        ∀ t : ℝ, 0 < t → RegularPoint Ah Dh Th Zh t → Zh t ≠ 0 →
          ∑ i, deriv (fun s => Zh s i) t * Real.log (deriv (fun s => Dh s i) t / alpha i) ≤ -ε := by
  exact entropy_drift_core dat hdom hlam hP_nonneg hP_rowsum hP_transient alpha halpha hα hload
