-- Prove2me | solution 1 for ProcessingNetworks.ProportionalFairness.entropy_lyapunov_dini_bound_regular
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T21:41:25.146256+00:00
-- url     : https://prove2.me/submissions/9baa3675-9266-4a14-a94f-336f1e321051

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_FluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_EntropyLyapunov



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

lemma pf_kkt {L : ℕ} {S : Set (Fin L → ℝ)} (hdom : IsPFDomain S) (y : Fin L → ℝ)
    (hy : ∀ k, 0 ≤ y k) (a : Fin L → ℝ) (ha : IsPFMaximizer S y a)
    (hapos : ∀ k, 0 < y k → 0 < a k) (p : Fin L → ℝ) (hpS : p ∈ S) (hp : ∀ k, 0 < p k)
    (ℓ : Fin L) (hℓ : 0 < y ℓ) :
    y ℓ * p ℓ / (2 * ∑ k, y k) ≤ a ℓ := by
  set Y := ∑ k, y k with hY
  have hyℓY : y ℓ ≤ Y := Finset.single_le_sum (fun k _ => hy k) (Finset.mem_univ ℓ)
  have hYpos : 0 < Y := lt_of_lt_of_le hℓ hyℓY
  set s := y ℓ / (4 * Y) with hs
  have hs0 : 0 < s := by positivity
  have hs4 : s * (4 * Y) = y ℓ := by rw [hs]; field_simp
  have hs1 : s ≤ 1 / 4 := by nlinarith
  set w : Fin L → ℝ := fun k => (1 - s) * a k + s * p k with hw
  have hwS : w ∈ S := by
    have := hdom.2.2.1 ha.1 hpS (by linarith : (0:ℝ) ≤ 1 - s) hs0.le (by ring)
    convert this using 1
    funext k; simp [w, smul_eq_mul]
  have hwpos : ∀ k, 0 < y k → 0 < w k := fun k hk => by
    have := hapos k hk; have := hp k; simp only [w]; nlinarith
  have hle : pfRv y w ≤ pfRv y a := by
    have := ha.2 w hwS
    rwa [pf_f_eq_Rv y w (fun k hk => (hwpos k (lt_of_le_of_ne (hy k) (Ne.symm hk))).ne'),
      pf_f_eq_Rv y a (fun k hk => (hapos k (lt_of_le_of_ne (hy k) (Ne.symm hk))).ne'),
      EReal.coe_le_coe_iff] at this
  have hterm : ∀ k, y k * (1 - a k / w k) ≤ y k * Real.log (w k) - y k * Real.log (a k) := by
    intro k
    rcases (hy k).eq_or_lt with h | h
    · simp [← h]
    · have hw' := hwpos k h; have ha' := hapos k h
      rw [← mul_sub, ← Real.log_div hw'.ne' ha'.ne']
      apply mul_le_mul_of_nonneg_left _ h.le
      have := Real.one_sub_inv_le_log_of_pos (div_pos hw' ha')
      rwa [inv_div] at this
  have hsum : ∑ k, y k * (1 - a k / w k) ≤ 0 := by
    have := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hterm k
    rw [Finset.sum_sub_distrib] at this
    simp only [pfRv] at hle; linarith
  have hlow : ∀ k, -(y k * (s / (1 - s))) ≤ y k * (1 - a k / w k) := by
    intro k
    rcases (hy k).eq_or_lt with h | h
    · simp [← h]
    · have hw' := hwpos k h; have ha' := hapos k h
      have : a k / w k - 1 ≤ s / (1 - s) := by
        rw [div_sub_one hw'.ne', div_le_div_iff₀ hw' (by linarith)]
        simp only [w]; nlinarith [hp k]
      nlinarith
  have hsplit := Finset.add_sum_erase Finset.univ (fun k => y k * (1 - a k / w k)) (Finset.mem_univ ℓ)
  have hrest : -((Y - y ℓ) * (s / (1 - s))) ≤ ∑ k ∈ Finset.univ.erase ℓ, y k * (1 - a k / w k) := by
    have h1 := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ.erase ℓ) => hlow k
    have h2 : ∑ k ∈ Finset.univ.erase ℓ, -(y k * (s / (1 - s))) = -((Y - y ℓ) * (s / (1 - s))) := by
      rw [Finset.sum_neg_distrib, ← Finset.sum_mul, Finset.sum_erase_eq_sub (Finset.mem_univ ℓ)]
    linarith
  have hmain : y ℓ * (1 - a ℓ / w ℓ) ≤ (Y - y ℓ) * (s / (1 - s)) := by
    linarith
  have hwℓ := hwpos ℓ hℓ
  have haℓ := hapos ℓ hℓ
  have h1s : 0 < 1 - s := by linarith
  have key : y ℓ * (w ℓ - a ℓ) * (1 - s) ≤ (Y - y ℓ) * s * w ℓ := by
    have e : y ℓ * (1 - a ℓ / w ℓ) = y ℓ * (w ℓ - a ℓ) / w ℓ := by field_simp
    rw [e, div_le_iff₀ hwℓ] at hmain
    rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ h1s] at hmain
    linarith
  have key2 : y ℓ * (p ℓ - a ℓ) * (1 - s) ≤ (Y - y ℓ) * w ℓ := by
    have : w ℓ - a ℓ = s * (p ℓ - a ℓ) := by simp only [w]; ring
    rw [this] at key
    have : s * (y ℓ * (p ℓ - a ℓ) * (1 - s)) ≤ s * ((Y - y ℓ) * w ℓ) := by nlinarith
    exact le_of_mul_le_mul_left this hs0
  rw [div_le_iff₀ (by positivity)]
  by_contra hlt
  push_neg at hlt
  simp only [w] at key2
  have hp' := hp ℓ
  -- multiply key2 by 4Y
  have k3 : y ℓ * (p ℓ - a ℓ) * (4 * Y - y ℓ) ≤ (Y - y ℓ) * ((4 * Y - y ℓ) * a ℓ + y ℓ * p ℓ) := by
    have e1 : (1 - s) * (4 * Y) = 4 * Y - y ℓ := by nlinarith
    have := mul_le_mul_of_nonneg_right key2 (by positivity : (0:ℝ) ≤ 4 * Y)
    nlinarith
  nlinarith [mul_pos hYpos hp', mul_pos hℓ hp', mul_lt_mul_of_pos_left hlt (by linarith : (0:ℝ) < 4 * Y - y ℓ)]

lemma pf_limit_eq {L : ℕ} {S : Set (Fin L → ℝ)} (hdom : IsPFDomain S)
    (y : ℕ → Fin L → ℝ) (y0 : Fin L → ℝ) (hy : Tendsto y atTop (𝓝 y0))
    (hy0 : ∀ k, 0 ≤ y0 k) (x : ℕ → Fin L → ℝ)
    (hx : ∀ᶠ n in atTop, IsPFMaximizer S (y n) (x n) ∧ (∀ k, 0 ≤ y n k) ∧
      ∀ k, 0 < y n k → 0 < x n k)
    (xs : Fin L → ℝ) (hxs : Tendsto x atTop (𝓝 xs))
    (hc : ∀ k, 0 < y0 k → ∃ c, 0 < c ∧ ∀ᶠ n in atTop, c ≤ x n k)
    (a : Fin L → ℝ) (ha : IsPFMaximizer S y0 a) (hapos : ∀ k, 0 < y0 k → 0 < a k) :
    ∀ ℓ, 0 < y0 ℓ → xs ℓ = a ℓ := by
  obtain ⟨B, hB1, hB⟩ := pf_dom_bound hdom
  obtain ⟨p, hpS, hp⟩ := hdom.2.2.2.2
  have hxsS : xs ∈ S := hdom.2.1.mem_of_tendsto hxs (hx.mono fun n h => h.1.1)
  have hcoord : ∀ k, Tendsto (fun n => x n k) atTop (𝓝 (xs k)) := fun k =>
    ((continuous_apply k).tendsto xs).comp hxs
  have hycoord : ∀ k, Tendsto (fun n => y n k) atTop (𝓝 (y0 k)) := fun k =>
    ((continuous_apply k).tendsto y0).comp hy
  have hxspos : ∀ k, 0 < y0 k → 0 < xs k := fun k hk => by
    obtain ⟨c, hc0, hcev⟩ := hc k hk
    exact lt_of_lt_of_le hc0 (ge_of_tendsto (hcoord k) hcev)
  have step1 : ∀ w ∈ S, (∀ k, w k ≠ 0) → pfRv y0 w ≤ pfRv y0 xs := by
    intro w hwS hw0
    have h1 : Tendsto (fun n => pfRv (y n) w) atTop (𝓝 (pfRv y0 w)) := by
      unfold pfRv; exact tendsto_finsetSum _ fun k _ => (hycoord k).mul_const _
    have hR : pfRv y0 xs = ∑ k, if 0 < y0 k then y0 k * Real.log (xs k) else y0 k * B := by
      unfold pfRv; refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs with hk
      · rfl
      · have : y0 k = 0 := le_antisymm (not_lt.1 hk) (hy0 k); simp [this]
    have h2 : Tendsto (fun n => ∑ k, if 0 < y0 k then y n k * Real.log (x n k) else y n k * B)
        atTop (𝓝 (pfRv y0 xs)) := by
      rw [hR]
      refine tendsto_finsetSum _ fun k _ => ?_
      by_cases hk : 0 < y0 k
      · simp only [if_pos hk]
        exact (hycoord k).mul ((Real.continuousAt_log (hxspos k hk).ne').tendsto.comp (hcoord k))
      · simp only [if_neg hk]
        exact (hycoord k).mul_const B
    refine le_of_tendsto_of_tendsto h1 h2 ?_
    filter_upwards [hx] with n ⟨hmax, hyn, hxpos⟩
    have e1 := hmax.2 w hwS
    rw [pf_f_eq_Rv _ _ (fun k _ => hw0 k),
      pf_f_eq_Rv _ _ (fun k hk => (hxpos k (lt_of_le_of_ne (hyn k) (Ne.symm hk))).ne'),
      EReal.coe_le_coe_iff] at e1
    refine e1.trans (Finset.sum_le_sum fun k _ => ?_)
    split_ifs with hk
    · exact le_rfl
    · rcases (hyn k).eq_or_lt with h | h
      · simp [← h]
      · exact mul_le_mul_of_nonneg_left (pf_log_le_B hB1 (hB _ hmax.1 k)) h.le
  have step2 : pfRv y0 a ≤ pfRv y0 xs := by
    set w : ℝ → Fin L → ℝ := fun ε k => (1 - ε) * a k + ε * p k with hw
    have hwt : ∀ k, Tendsto (fun ε => w ε k) (𝓝[>] (0:ℝ)) (𝓝 (a k)) := by
      intro k
      have : Tendsto (fun ε : ℝ => (1 - ε) * a k + ε * p k) (𝓝 0)
          (𝓝 ((1 - 0) * a k + 0 * p k)) :=
        (((continuous_const.sub continuous_id).mul continuous_const).add
          (continuous_id.mul continuous_const)).tendsto 0
      simp only [sub_zero, one_mul, zero_mul, add_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    have hlim : Tendsto (fun ε => pfRv y0 (w ε)) (𝓝[>] 0) (𝓝 (pfRv y0 a)) := by
      unfold pfRv
      refine tendsto_finsetSum _ fun k _ => ?_
      rcases (hy0 k).eq_or_lt with h | h
      · simp [← h]
      · exact ((Real.continuousAt_log (hapos k h).ne').tendsto.comp (hwt k)).const_mul _
    have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), w ε ∈ S ∧ ∀ k, w ε k ≠ 0 := by
      have hk : ∀ k, ∀ᶠ ε in 𝓝[>] (0:ℝ), w ε k ≠ 0 := by
        intro k
        rcases eq_or_ne (a k) 0 with h | h
        · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
          simp only [w, h, mul_zero, zero_add]; exact (mul_pos hε (hp k)).ne'
        · exact (hwt k).eventually_ne h
      have hS : ∀ᶠ ε in 𝓝[>] (0:ℝ), w ε ∈ S := by
        have h1 : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < 1 :=
          Filter.Tendsto.eventually_lt_const one_pos
            (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
        filter_upwards [self_mem_nhdsWithin, h1] with ε (hε : 0 < ε) hε1
        have := hdom.2.2.1 ha.1 hpS (by linarith : (0:ℝ) ≤ 1 - ε) hε.le (by ring)
        convert this using 1; funext k; simp [w, smul_eq_mul]
      exact hS.and (eventually_all.2 hk)
    refine le_of_tendsto hlim ?_
    filter_upwards [hev] with ε ⟨hS, h0⟩
    exact step1 _ hS h0
  intro ℓ hℓ
  by_contra hne
  set mid : Fin L → ℝ := fun k => (1/2) * a k + (1/2) * xs k with hmid
  have hmidS : mid ∈ S := by
    have := hdom.2.2.1 ha.1 hxsS (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num)
    convert this using 1; funext k; simp [mid, smul_eq_mul]
  have hmidpos : ∀ k, 0 < y0 k → 0 < mid k := fun k hk => by
    simp only [mid]; linarith [hapos k hk, hxspos k hk]
  have hle : pfRv y0 mid ≤ pfRv y0 a := by
    have := ha.2 mid hmidS
    rwa [pf_f_eq_Rv _ _ (fun k hk => (hmidpos k (lt_of_le_of_ne (hy0 k) (Ne.symm hk))).ne'),
      pf_f_eq_Rv _ _ (fun k hk => (hapos k (lt_of_le_of_ne (hy0 k) (Ne.symm hk))).ne'),
      EReal.coe_le_coe_iff] at this
  have hlt : (pfRv y0 a + pfRv y0 xs) / 2 < pfRv y0 mid := by
    have : (pfRv y0 a + pfRv y0 xs) / 2 =
        ∑ k, y0 k * ((1/2) * Real.log (a k) + (1/2) * Real.log (xs k)) := by
      unfold pfRv; rw [← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]; unfold pfRv
    refine Finset.sum_lt_sum (fun k _ => ?_) ⟨ℓ, Finset.mem_univ _, ?_⟩
    · rcases (hy0 k).eq_or_lt with h | h
      · simp [← h]
      · apply mul_le_mul_of_nonneg_left _ h.le
        have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 (hapos k h))
          (Set.mem_Ioi.2 (hxspos k h)) (by norm_num : (0:ℝ) ≤ 1/2)
          (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
        simpa [smul_eq_mul, mid] using this
    · apply mul_lt_mul_of_pos_left _ hℓ
      have := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.2 (hapos ℓ hℓ))
        (Set.mem_Ioi.2 (hxspos ℓ hℓ)) (fun h => hne h.symm) (by norm_num : (0:ℝ) < 1/2)
        (by norm_num : (0:ℝ) < 1/2) (by norm_num)
      simpa [smul_eq_mul, mid] using this
  linarith

lemma pf_seq_conv {L : ℕ} {S : Set (Fin L → ℝ)} (hdom : IsPFDomain S)
    (y : ℕ → Fin L → ℝ) (y0 : Fin L → ℝ) (hy : Tendsto y atTop (𝓝 y0))
    (hy0 : ∀ k, 0 ≤ y0 k) (x : ℕ → Fin L → ℝ)
    (hx : ∀ᶠ n in atTop, IsPFMaximizer S (y n) (x n) ∧ (∀ k, 0 ≤ y n k) ∧
      ∀ k, 0 < y n k → 0 < x n k)
    (hc : ∀ k, 0 < y0 k → ∃ c, 0 < c ∧ ∀ᶠ n in atTop, c ≤ x n k)
    (a : Fin L → ℝ) (ha : IsPFMaximizer S y0 a) (hapos : ∀ k, 0 < y0 k → 0 < a k)
    (ℓ : Fin L) (hℓ : 0 < y0 ℓ) : Tendsto (fun n => x n ℓ) atTop (𝓝 (a ℓ)) := by
  classical
  have hK : IsCompact S := Metric.isCompact_of_isClosed_isBounded hdom.2.1 hdom.1
  obtain ⟨p, hpS, -⟩ := hdom.2.2.2.2
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  set x' : ℕ → Fin L → ℝ := fun n => if x (ns n) ∈ S then x (ns n) else p with hx'
  obtain ⟨xs, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := x') (fun n => by
    simp only [x']; split_ifs with h
    · exact h
    · exact hpS)
  refine ⟨φ, ?_⟩
  have hnsφ : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hxe := hnsφ.eventually hx
  have heq : ∀ᶠ n in atTop, x' (φ n) = x (ns (φ n)) :=
    hxe.mono fun n h => by simp only [x', if_pos h.1.1]
  have hlim2 : Tendsto (fun n => x (ns (φ n))) atTop (𝓝 xs) := hlim.congr' heq
  have := pf_limit_eq hdom (fun n => y (ns (φ n))) y0 (hy.comp hnsφ) hy0
    (fun n => x (ns (φ n))) hxe xs hlim2
    (fun k hk => by
      obtain ⟨c, hc0, hcev⟩ := hc k hk
      exact ⟨c, hc0, hnsφ.eventually hcev⟩) a ha hapos ℓ hℓ
  rw [← this]
  exact ((continuous_apply ℓ).tendsto xs).comp hlim2

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

lemma pf_T_cont {I L : ℕ} {dat : PFUnitaryNetworkData I L} {Ah Dh Th Zh : ℝ → Fin I → ℝ}
    (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) (k : Fin I) (t0 : ℝ) (ht0 : 0 ≤ t0) :
    ContinuousWithinAt (fun t => Th t k) (Set.Ici 0) t0 := by
  obtain ⟨Kc, hKc⟩ := hsol.2.2.2.2.1.2.2
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε / (|Kc| + 1), by positivity, fun {t} ht hdist => ?_⟩
  have ht' : 0 ≤ t := ht
  rw [Real.dist_eq] at hdist ⊢
  have key : |Th t k - Th t0 k| ≤ |Kc| * |t - t0| := by
    rcases le_total t0 t with h | h
    · have := hKc t0 t ht0 h k
      rw [abs_of_nonneg (sub_nonneg.2 h)]
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sub_nonneg.2 h))
    · have := hKc t t0 ht' h k
      rw [abs_sub_comm, abs_sub_comm t t0, abs_of_nonneg (sub_nonneg.2 h)]
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sub_nonneg.2 h))
  calc |Th t k - Th t0 k| ≤ |Kc| * |t - t0| := key
    _ ≤ |Kc| * (ε / (|Kc| + 1)) := mul_le_mul_of_nonneg_left hdist.le (abs_nonneg _)
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [abs_nonneg Kc]

lemma pf_Z_cont {I L : ℕ} {dat : PFUnitaryNetworkData I L} {Ah Dh Th Zh : ℝ → Fin I → ℝ}
    (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) (i : Fin I) (t0 : ℝ) (ht0 : 0 ≤ t0) :
    ContinuousWithinAt (fun t => Zh t i) (Set.Ici 0) t0 := by
  have hform : ∀ t, 0 ≤ t → Zh t i = Zh 0 i + (dat.lam i * t +
      ∑ k, dat.P k i * (Th t k / dat.m k)) - Th t i / dat.m i := by
    intro t ht
    have := congrFun (hsol.1 t ht) i
    rw [this, hsol.2.2.1 t ht i, hsol.2.2.2.1 t ht i]
    have hs : ∑ k, dat.P k i * Dh t k = ∑ k, dat.P k i * (Th t k / dat.m k) :=
      Finset.sum_congr rfl fun k _ => by rw [hsol.2.2.2.1 t ht k]
    rw [hs]
  have hc : ContinuousWithinAt (fun t => Zh 0 i + (dat.lam i * t +
      ∑ k, dat.P k i * (Th t k / dat.m k)) - Th t i / dat.m i) (Set.Ici 0) t0 := by
    refine (continuousWithinAt_const.add ((continuousWithinAt_const.mul continuousWithinAt_id).add
      ?_)).sub ((pf_T_cont hsol i t0 ht0).div_const _)
    exact tendsto_finsetSum _ fun k _ =>
      (continuousWithinAt_const.mul ((pf_T_cont hsol k t0 ht0).div_const _))
  exact hc.congr (fun t ht => hform t ht) (hform t0 ht0)

lemma pf_Y_cont {I L : ℕ} {dat : PFUnitaryNetworkData I L} {Ah Dh Th Zh : ℝ → Fin I → ℝ}
    (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) (t0 : ℝ) (ht0 : 0 ≤ t0) :
    ContinuousWithinAt (fun t => groupAggregate dat.grp (Zh t)) (Set.Ici 0) t0 := by
  rw [continuousWithinAt_pi]
  intro ℓ
  unfold groupAggregate
  exact tendsto_finsetSum _ fun i _ => pf_Z_cont hsol i t0 ht0

lemma pf_Y_nonneg {I L : ℕ} {dat : PFUnitaryNetworkData I L} {Ah Dh Th Zh : ℝ → Fin I → ℝ}
    (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) (t : ℝ) (ht : 0 ≤ t) (ℓ : Fin L) :
    0 ≤ groupAggregate dat.grp (Zh t) ℓ :=
  Finset.sum_nonneg fun i _ => hsol.2.1 t ht i

lemma pf_Z_le_Y {I L : ℕ} {dat : PFUnitaryNetworkData I L} {Ah Dh Th Zh : ℝ → Fin I → ℝ}
    (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) (t : ℝ) (ht : 0 ≤ t) (i : Fin I) :
    Zh t i ≤ groupAggregate dat.grp (Zh t) (dat.grp i) :=
  Finset.single_le_sum (f := fun j => Zh t j) (fun j _ => hsol.2.1 t ht j)
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)

lemma pf_xm_pos {I L : ℕ} {dat : PFUnitaryNetworkData I L} {Ah Dh Th Zh : ℝ → Fin I → ℝ}
    (hdom : IsPFDomain dat.TildeAllocSet)
    (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) (t : ℝ) (ht : 0 < t) (ℓ : Fin L)
    (hℓ : 0 < groupAggregate dat.grp (Zh t) ℓ) :
    0 < pfXm dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) ℓ := by
  have : ∃ i, dat.grp i = ℓ ∧ 0 < Zh t i := by
    by_contra hc
    push_neg at hc
    have : groupAggregate dat.grp (Zh t) ℓ ≤ 0 :=
      Finset.sum_nonpos fun i hi => hc i (Finset.mem_filter.1 hi).2
    linarith
  obtain ⟨i, rfl, hi⟩ := this
  have hd := hsol.2.2.2.2.2 t ht i hi
  have hmono : Monotone (fun u => Th u i) := fun a b hab => hsol.2.2.2.2.1.2.1 hab i
  have h0 := hmono.deriv_nonneg (x := t)
  rw [hd.deriv] at h0
  have hY := hℓ
  rw [← pf_psi_eq _ _ _ hℓ]
  have hne : psi dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) (dat.grp i) ≠ 0 := by
    rw [pf_psi_eq _ _ _ hℓ]
    exact pf_max_ne_zero hdom _ _ (pf_xm_max hdom _ (pf_Y_nonneg hsol t ht.le)) _ hℓ
  rcases lt_or_gt_of_ne hne with h | h
  · exfalso
    have : psi dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) (dat.grp i) * Zh t i /
        groupAggregate dat.grp (Zh t) (dat.grp i) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h hi) hY
    linarith
  · exact h

lemma pf_derivWithin_D {I L : ℕ} {dat : PFUnitaryNetworkData I L}
    {Ah Dh Th Zh : ℝ → Fin I → ℝ}
    (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) (t : ℝ) (ht : 0 < t) (i : Fin I)
    (hi : 0 < Zh t i) :
    derivWithin (fun s => Dh s i) (Set.Ici t) t =
      psi dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) (dat.grp i) * Zh t i /
        groupAggregate dat.grp (Zh t) (dat.grp i) / dat.m i := by
  have hd := (hsol.2.2.2.2.2 t ht i hi).div_const (dat.m i)
  have hd2 := hd.hasDerivWithinAt (s := Set.Ici t)
  have hd3 : HasDerivWithinAt (fun s => Dh s i) _ (Set.Ici t) t :=
    hd2.congr (fun s hs => hsol.2.2.2.1 s (le_trans ht.le hs) i) (hsol.2.2.2.1 t ht.le i)
  exact hd3.derivWithin (uniqueDiffWithinAt_Ici t)

lemma pf_psi_cont {I L : ℕ} {dat : PFUnitaryNetworkData I L} {Ah Dh Th Zh : ℝ → Fin I → ℝ}
    (hdom : IsPFDomain dat.TildeAllocSet)
    (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) (t0 : ℝ) (ht0 : 0 < t0) (ℓ : Fin L)
    (hℓ : 0 < groupAggregate dat.grp (Zh t0) ℓ) :
    ContinuousWithinAt (fun t => psi dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) ℓ)
      (Set.Ioi 0) t0 := by
  obtain ⟨p, hpS, hp⟩ := hdom.2.2.2.2
  have hYc : ContinuousWithinAt (fun t => groupAggregate dat.grp (Zh t)) (Set.Ioi 0) t0 :=
    (pf_Y_cont hsol t0 ht0.le).mono Set.Ioi_subset_Ici_self
  unfold ContinuousWithinAt
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  obtain ⟨hu1, hu2⟩ := tendsto_nhdsWithin_iff.1 hu
  have hYu : Tendsto (fun n => groupAggregate dat.grp (Zh (u n))) atTop
      (𝓝 (groupAggregate dat.grp (Zh t0))) := hYc.tendsto.comp hu
  have hYk : ∀ k, Tendsto (fun n => groupAggregate dat.grp (Zh (u n)) k) atTop
      (𝓝 (groupAggregate dat.grp (Zh t0) k)) := fun k =>
    ((continuous_apply k).tendsto _).comp hYu
  have hsum : Tendsto (fun n => ∑ k, groupAggregate dat.grp (Zh (u n)) k) atTop
      (𝓝 (∑ k, groupAggregate dat.grp (Zh t0) k)) := tendsto_finsetSum _ fun k _ => hYk k
  have hconv := pf_seq_conv hdom (fun n => groupAggregate dat.grp (Zh (u n)))
    (groupAggregate dat.grp (Zh t0)) hYu (pf_Y_nonneg hsol t0 ht0.le)
    (fun n => pfXm dat.TildeAllocSet (groupAggregate dat.grp (Zh (u n))))
    (hu2.mono fun n hn => ⟨pf_xm_max hdom _ (pf_Y_nonneg hsol _ (le_of_lt hn)),
      pf_Y_nonneg hsol _ (le_of_lt hn), fun k hk => pf_xm_pos hdom hsol _ hn k hk⟩)
    ?_ (pfXm dat.TildeAllocSet (groupAggregate dat.grp (Zh t0)))
    (pf_xm_max hdom _ (pf_Y_nonneg hsol t0 ht0.le))
    (fun k hk => pf_xm_pos hdom hsol t0 ht0 k hk) ℓ hℓ
  · show Tendsto (fun n => psi dat.TildeAllocSet (groupAggregate dat.grp (Zh (u n))) ℓ) atTop
      (𝓝 (psi dat.TildeAllocSet (groupAggregate dat.grp (Zh t0)) ℓ))
    rw [pf_psi_eq _ _ _ hℓ]
    refine hconv.congr' ?_
    filter_upwards [(hYk ℓ).eventually_const_lt hℓ] with n hn
    exact (pf_psi_eq _ _ _ hn).symm
  · intro k hk
    have hSg0 : 0 ≤ ∑ j, groupAggregate dat.grp (Zh t0) j :=
      Finset.sum_nonneg fun j _ => pf_Y_nonneg hsol t0 ht0.le j
    refine ⟨groupAggregate dat.grp (Zh t0) k * p k /
      (4 * (∑ j, groupAggregate dat.grp (Zh t0) j + 1)),
      div_pos (mul_pos hk (hp k)) (by linarith), ?_⟩
    filter_upwards [hu2, (hYk k).eventually_const_lt (half_lt_self hk),
      hsum.eventually_lt_const (lt_add_one _)] with n hn h1 h2
    have hn' : (0:ℝ) ≤ u n := le_of_lt hn
    have hYn : 0 < groupAggregate dat.grp (Zh (u n)) k := lt_trans (half_pos hk) h1
    have hkkt := pf_kkt hdom _ (pf_Y_nonneg hsol _ hn') _
      (pf_xm_max hdom _ (pf_Y_nonneg hsol _ hn')) (fun j hj => pf_xm_pos hdom hsol _ hn j hj)
      p hpS hp k hYn
    refine le_trans ?_ hkkt
    have hSgpos : 0 < ∑ j, groupAggregate dat.grp (Zh (u n)) j :=
      lt_of_lt_of_le hYn (Finset.single_le_sum (fun j _ => pf_Y_nonneg hsol _ hn' j)
        (Finset.mem_univ k))
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    have e1 : groupAggregate dat.grp (Zh t0) k * ∑ j, groupAggregate dat.grp (Zh (u n)) j ≤
        (2 * groupAggregate dat.grp (Zh (u n)) k) *
          (∑ j, groupAggregate dat.grp (Zh t0) j + 1) :=
      mul_le_mul (by linarith) h2.le hSgpos.le (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left e1 (hp k).le]

theorem entropy_cont_core {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (alpha : Fin I → ℝ)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (hα : ∀ i, 0 < alpha i) :
    ContinuousOn (phi Dh Zh alpha) (Set.Ioi 0) := by
  obtain ⟨B, hB1, hB⟩ := pf_dom_bound hdom
  obtain ⟨p, hpS, hp⟩ := hdom.2.2.2.2
  have hterm : ∀ i, ∀ t, 0 < t → (if Zh t i = 0 then 0 else Zh t i *
      Real.log (derivWithin (fun s => Dh s i) (Set.Ici t) t / alpha i)) =
      Zh t i * Real.log (psi dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) (dat.grp i) *
        Zh t i / groupAggregate dat.grp (Zh t) (dat.grp i) / dat.m i / alpha i) := by
    intro i t ht
    split_ifs with h
    · rw [h, zero_mul]
    · rw [pf_derivWithin_D hsol t ht i (lt_of_le_of_ne (hsol.2.1 t ht.le i) (Ne.symm h))]
  unfold phi
  refine continuousOn_finsetSum _ fun i _ => ?_
  intro t0 ht0
  have ht0' : 0 < t0 := ht0
  refine ContinuousWithinAt.congr ?_ (fun t ht => hterm i t ht) (hterm i t0 ht0')
  have hZc : ContinuousWithinAt (fun t => Zh t i) (Set.Ioi 0) t0 :=
    (pf_Z_cont hsol i t0 ht0'.le).mono Set.Ioi_subset_Ici_self
  have hYc' : ContinuousWithinAt (fun t => groupAggregate dat.grp (Zh t)) (Set.Ioi 0) t0 :=
    (pf_Y_cont hsol t0 ht0'.le).mono Set.Ioi_subset_Ici_self
  have hYc : ContinuousWithinAt (fun t => groupAggregate dat.grp (Zh t) (dat.grp i))
      (Set.Ioi 0) t0 := ((continuous_apply _).continuousAt.comp_continuousWithinAt hYc')
  have hmi := dat.hm i
  rcases (hsol.2.1 t0 ht0'.le i).eq_or_lt with hz | hz
  · set Sg0 := ∑ j, groupAggregate dat.grp (Zh t0) j with hSg0def
    have hsumc : Tendsto (fun t => ∑ j, groupAggregate dat.grp (Zh t) j) (𝓝[Set.Ioi 0] t0)
        (𝓝 Sg0) := tendsto_finsetSum _ fun j _ => ((continuous_apply j).tendsto _).comp hYc'
    have hSg0 : 0 ≤ Sg0 := Finset.sum_nonneg fun j _ => pf_Y_nonneg hsol t0 ht0'.le j
    set κ := p (dat.grp i) / (2 * (Sg0 + 1) * dat.m i) with hκ
    have hκpos : 0 < κ := div_pos (hp _) (by positivity)
    have hL : Tendsto (fun t => Zh t i * Real.log (Zh t i) + Zh t i * Real.log (κ / alpha i))
        (𝓝[Set.Ioi 0] t0)
        (𝓝 (Zh t0 i * Real.log (Zh t0 i) + Zh t0 i * Real.log (κ / alpha i))) :=
      ((Real.continuous_mul_log.continuousAt.comp_continuousWithinAt hZc).add
        (hZc.mul_const _))
    have hU : Tendsto (fun t => Zh t i * Real.log (B / dat.m i / alpha i))
        (𝓝[Set.Ioi 0] t0) (𝓝 (Zh t0 i * Real.log (B / dat.m i / alpha i))) :=
      hZc.mul_const _
    rw [← hz] at hL hU
    simp only [zero_mul, Real.log_zero, add_zero] at hL hU
    show Tendsto _ (𝓝[Set.Ioi 0] t0) (𝓝 (Zh t0 i * _))
    rw [← hz, zero_mul]
    have hev : ∀ᶠ t in 𝓝[Set.Ioi 0] t0,
        Zh t i * Real.log (Zh t i) + Zh t i * Real.log (κ / alpha i) ≤
          Zh t i * Real.log (psi dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) (dat.grp i) *
            Zh t i / groupAggregate dat.grp (Zh t) (dat.grp i) / dat.m i / alpha i) ∧
        Zh t i * Real.log (psi dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) (dat.grp i) *
            Zh t i / groupAggregate dat.grp (Zh t) (dat.grp i) / dat.m i / alpha i) ≤
          Zh t i * Real.log (B / dat.m i / alpha i) := by
      filter_upwards [self_mem_nhdsWithin, hsumc.eventually_lt_const (lt_add_one Sg0)] with t
        (ht : 0 < t) hSg
      by_cases hZt : Zh t i = 0
      · simp [hZt]
      have hZp : 0 < Zh t i := lt_of_le_of_ne (hsol.2.1 t ht.le i) (Ne.symm hZt)
      have hYp : 0 < groupAggregate dat.grp (Zh t) (dat.grp i) :=
        lt_of_lt_of_le hZp (pf_Z_le_Y hsol t ht.le i)
      have hZY := pf_Z_le_Y hsol t ht.le i
      have hxm := pf_xm_pos hdom hsol t ht _ hYp
      rw [pf_psi_eq _ _ _ hYp]
      have hmax := pf_xm_max hdom _ (pf_Y_nonneg hsol t ht.le)
      have hxB : pfXm dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) (dat.grp i) ≤ B :=
        (le_abs_self _).trans (hB _ hmax.1 _)
      have hkkt := pf_kkt hdom _ (pf_Y_nonneg hsol t ht.le) _ hmax
        (fun j hj => pf_xm_pos hdom hsol t ht j hj) p hpS hp _ hYp
      have hSgpos : 0 < ∑ j, groupAggregate dat.grp (Zh t) j :=
        lt_of_lt_of_le hYp (Finset.single_le_sum (fun j _ => pf_Y_nonneg hsol t ht.le j)
          (Finset.mem_univ _))
      set X := pfXm dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) (dat.grp i)
      set Yl := groupAggregate dat.grp (Zh t) (dat.grp i)
      set Sgt := ∑ j, groupAggregate dat.grp (Zh t) j
      set Z := Zh t i
      have hαi := hα i
      have hg : 0 < X * Z / Yl / dat.m i / alpha i := by positivity
      constructor
      · have hlow : κ * Z / alpha i ≤ X * Z / Yl / dat.m i / alpha i := by
          apply div_le_div_of_nonneg_right _ hαi.le
          rw [hκ, div_mul_eq_mul_div, div_div, div_le_div_iff₀ (by positivity)
            (by positivity)]
          have e2 : Yl * p (dat.grp i) ≤ X * (2 * Sgt) := by
            rwa [div_le_iff₀ (by positivity)] at hkkt
          have e3 : 2 * Sgt ≤ 2 * (Sg0 + 1) := by linarith
          have e4 : Yl * p (dat.grp i) ≤ X * (2 * (Sg0 + 1)) :=
            e2.trans (mul_le_mul_of_nonneg_left e3 hxm.le)
          have e5 := mul_le_mul_of_nonneg_left e4 (by positivity : (0:ℝ) ≤ Z * dat.m i)
          nlinarith
        have hlog := Real.log_le_log (by positivity) hlow
        have e6 : Real.log (κ * Z / alpha i) = Real.log Z + Real.log (κ / alpha i) := by
          rw [mul_comm κ Z, mul_div_assoc, Real.log_mul hZp.ne' (by positivity)]
        rw [e6] at hlog
        nlinarith
      · have hup : X * Z / Yl / dat.m i / alpha i ≤ B / dat.m i / alpha i := by
          apply div_le_div_of_nonneg_right _ hαi.le
          apply div_le_div_of_nonneg_right _ hmi.le
          rw [div_le_iff₀ hYp]
          nlinarith
        have hlog := Real.log_le_log hg hup
        nlinarith
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU (hev.mono fun t h => h.1)
      (hev.mono fun t h => h.2)
  · have hYpos : 0 < groupAggregate dat.grp (Zh t0) (dat.grp i) :=
      lt_of_lt_of_le hz (pf_Z_le_Y hsol t0 ht0'.le i)
    have hpsic := pf_psi_cont hdom hsol t0 ht0' (dat.grp i) hYpos
    have hgc : ContinuousWithinAt (fun t => psi dat.TildeAllocSet (groupAggregate dat.grp (Zh t))
        (dat.grp i) * Zh t i / groupAggregate dat.grp (Zh t) (dat.grp i) / dat.m i / alpha i)
        (Set.Ioi 0) t0 :=
      (((hpsic.mul hZc).div hYc hYpos.ne').div_const (dat.m i)).div_const (alpha i)
    have hgpos : 0 < psi dat.TildeAllocSet (groupAggregate dat.grp (Zh t0)) (dat.grp i) *
        Zh t0 i / groupAggregate dat.grp (Zh t0) (dat.grp i) / dat.m i / alpha i := by
      have := pf_xm_pos hdom hsol t0 ht0' _ hYpos
      rw [← pf_psi_eq _ _ _ hYpos] at this
      have := hα i
      positivity
    exact hZc.mul (hgc.log hgpos.ne')

noncomputable def pfG {I L : ℕ} (dat : PFUnitaryNetworkData I L) (Zh : ℝ → Fin I → ℝ) (i : Fin I)
    (u : ℝ) : ℝ :=
  psi dat.TildeAllocSet (groupAggregate dat.grp (Zh u)) (dat.grp i) * Zh u i /
    groupAggregate dat.grp (Zh u) (dat.grp i) / dat.m i

lemma pf_G_pos {I L : ℕ} {dat : PFUnitaryNetworkData I L} {Ah Dh Th Zh : ℝ → Fin I → ℝ}
    (hdom : IsPFDomain dat.TildeAllocSet)
    (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) (i : Fin I) (u : ℝ) (hu : 0 < u)
    (hz : 0 < Zh u i) : 0 < pfG dat Zh i u := by
  have hYp : 0 < groupAggregate dat.grp (Zh u) (dat.grp i) :=
    lt_of_lt_of_le hz (pf_Z_le_Y hsol u hu.le i)
  have := pf_xm_pos hdom hsol u hu _ hYp
  rw [← pf_psi_eq _ _ _ hYp] at this
  have := dat.hm i
  unfold pfG
  positivity

lemma pf_G_le {I L : ℕ} {dat : PFUnitaryNetworkData I L} {Ah Dh Th Zh : ℝ → Fin I → ℝ}
    (hdom : IsPFDomain dat.TildeAllocSet)
    (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) (B : ℝ)
    (hB : ∀ x ∈ dat.TildeAllocSet, ∀ k, |x k| ≤ B) (i : Fin I) (u : ℝ) (hu : 0 < u)
    (hz : 0 < Zh u i) : pfG dat Zh i u ≤ B / dat.m i := by
  have hYp : 0 < groupAggregate dat.grp (Zh u) (dat.grp i) :=
    lt_of_lt_of_le hz (pf_Z_le_Y hsol u hu.le i)
  have hZY := pf_Z_le_Y hsol u hu.le i
  have hxm := pf_xm_pos hdom hsol u hu _ hYp
  have hmax := pf_xm_max hdom _ (pf_Y_nonneg hsol u hu.le)
  have hxB : pfXm dat.TildeAllocSet (groupAggregate dat.grp (Zh u)) (dat.grp i) ≤ B :=
    (le_abs_self _).trans (hB _ hmax.1 _)
  unfold pfG
  rw [pf_psi_eq _ _ _ hYp]
  apply div_le_div_of_nonneg_right _ (dat.hm i).le
  rw [div_le_iff₀ hYp]
  nlinarith

lemma pf_G_cont {I L : ℕ} {dat : PFUnitaryNetworkData I L} {Ah Dh Th Zh : ℝ → Fin I → ℝ}
    (hdom : IsPFDomain dat.TildeAllocSet)
    (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) (i : Fin I) (t0 : ℝ) (ht0 : 0 < t0)
    (hz : 0 < Zh t0 i) : ContinuousWithinAt (pfG dat Zh i) (Set.Ioi 0) t0 := by
  have hZc : ContinuousWithinAt (fun t => Zh t i) (Set.Ioi 0) t0 :=
    (pf_Z_cont hsol i t0 ht0.le).mono Set.Ioi_subset_Ici_self
  have hYc' : ContinuousWithinAt (fun t => groupAggregate dat.grp (Zh t)) (Set.Ioi 0) t0 :=
    (pf_Y_cont hsol t0 ht0.le).mono Set.Ioi_subset_Ici_self
  have hYc : ContinuousWithinAt (fun t => groupAggregate dat.grp (Zh t) (dat.grp i))
      (Set.Ioi 0) t0 := ((continuous_apply _).continuousAt.comp_continuousWithinAt hYc')
  have hYpos : 0 < groupAggregate dat.grp (Zh t0) (dat.grp i) :=
    lt_of_lt_of_le hz (pf_Z_le_Y hsol t0 ht0.le i)
  have hpsic := pf_psi_cont hdom hsol t0 ht0 (dat.grp i) hYpos
  exact ((hpsic.mul hZc).div hYc hYpos.ne').div_const (dat.m i)

lemma pf_fiber {I L : ℕ} (grp : Fin I → Fin L) (z : Fin I → ℝ) (c : Fin L → ℝ) :
    ∑ i, z i * c (grp i) = ∑ ℓ, groupAggregate grp z ℓ * c ℓ := by
  rw [← Finset.sum_fiberwise Finset.univ grp (fun i => z i * c (grp i))]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  unfold groupAggregate
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]

lemma pf_exists_pos {I L : ℕ} (grp : Fin I → Fin L) (z : Fin I → ℝ) (ℓ : Fin L)
    (h : 0 < groupAggregate grp z ℓ) : ∃ i, grp i = ℓ ∧ 0 < z i := by
  by_contra hc
  push_neg at hc
  have : groupAggregate grp z ℓ ≤ 0 :=
    Finset.sum_nonpos fun i hi => hc i (Finset.mem_filter.1 hi).2
  linarith

lemma pf_opt {I L : ℕ} {dat : PFUnitaryNetworkData I L} {Ah Dh Th Zh : ℝ → Fin I → ℝ}
    (hdom : IsPFDomain dat.TildeAllocSet)
    (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (hpos : ∀ i, 0 < Zh t i → 0 < Zh s i) :
    ∑ i, Zh t i * Real.log (pfG dat Zh i s) ≤ ∑ i, Zh t i * Real.log (pfG dat Zh i t) := by
  set S := dat.TildeAllocSet
  have hdecomp : ∀ u, 0 < u → (∀ i, 0 < Zh t i → 0 < Zh u i) →
      ∑ i, Zh t i * Real.log (pfG dat Zh i u) =
        pfRv (groupAggregate dat.grp (Zh t)) (pfXm S (groupAggregate dat.grp (Zh u))) +
        ∑ i, Zh t i * (Real.log (Zh u i) - Real.log (groupAggregate dat.grp (Zh u) (dat.grp i)))
        - ∑ i, Zh t i * Real.log (dat.m i) := by
    intro u hu hposu
    have e1 : ∀ i, Zh t i * Real.log (pfG dat Zh i u) =
        Zh t i * Real.log (pfXm S (groupAggregate dat.grp (Zh u)) (dat.grp i)) +
        Zh t i * (Real.log (Zh u i) - Real.log (groupAggregate dat.grp (Zh u) (dat.grp i)))
        - Zh t i * Real.log (dat.m i) := by
      intro i
      rcases (hsol.2.1 t ht.le i).eq_or_lt with h | h
      · simp [← h]
      · have hzu := hposu i h
        have hYp : 0 < groupAggregate dat.grp (Zh u) (dat.grp i) :=
          lt_of_lt_of_le hzu (pf_Z_le_Y hsol u hu.le i)
        have hxm := pf_xm_pos hdom hsol u hu _ hYp
        unfold pfG
        rw [pf_psi_eq _ _ _ hYp, Real.log_div (by have := dat.hm i; positivity) (dat.hm i).ne',
          Real.log_div (by positivity) hYp.ne', Real.log_mul hxm.ne' hzu.ne']
        ring
    rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    congr 2
    unfold pfRv
    exact pf_fiber dat.grp (Zh t) (fun ℓ => Real.log (pfXm S (groupAggregate dat.grp (Zh u)) ℓ))
  rw [hdecomp s hs hpos, hdecomp t ht (fun i h => h)]
  -- PF part
  have hYt := pf_Y_nonneg hsol t ht.le
  have hmaxt := pf_xm_max hdom _ hYt
  have hmaxs := pf_xm_max hdom _ (pf_Y_nonneg hsol s hs.le)
  have hPF : pfRv (groupAggregate dat.grp (Zh t)) (pfXm S (groupAggregate dat.grp (Zh s))) ≤
      pfRv (groupAggregate dat.grp (Zh t)) (pfXm S (groupAggregate dat.grp (Zh t))) := by
    have := hmaxt.2 _ hmaxs.1
    have hsupp : ∀ ℓ, 0 < groupAggregate dat.grp (Zh t) ℓ →
        0 < groupAggregate dat.grp (Zh s) ℓ := by
      intro ℓ hℓ
      obtain ⟨i, rfl, hi⟩ := pf_exists_pos dat.grp (Zh t) _ hℓ
      exact lt_of_lt_of_le (hpos i hi) (pf_Z_le_Y hsol s hs.le i)
    rwa [pf_f_eq_Rv _ _ (fun ℓ hℓ => (pf_xm_pos hdom hsol s hs ℓ
        (hsupp ℓ (lt_of_le_of_ne (hYt ℓ) (Ne.symm hℓ)))).ne'),
      pf_f_eq_Rv _ _ (fun ℓ hℓ => (pf_xm_pos hdom hsol t ht ℓ
        (lt_of_le_of_ne (hYt ℓ) (Ne.symm hℓ))).ne'), EReal.coe_le_coe_iff] at this
  -- Gibbs part
  have hG : ∑ i, Zh t i * (Real.log (Zh s i) - Real.log (groupAggregate dat.grp (Zh s) (dat.grp i)))
      ≤ ∑ i, Zh t i * (Real.log (Zh t i) - Real.log (groupAggregate dat.grp (Zh t) (dat.grp i))) := by
    have hterm : ∀ i, Zh t i * (Real.log (Zh s i) -
        Real.log (groupAggregate dat.grp (Zh s) (dat.grp i))) -
        Zh t i * (Real.log (Zh t i) - Real.log (groupAggregate dat.grp (Zh t) (dat.grp i))) ≤
        Zh s i * (groupAggregate dat.grp (Zh t) (dat.grp i) /
          groupAggregate dat.grp (Zh s) (dat.grp i)) - Zh t i := by
      intro i
      have hYs := pf_Y_nonneg hsol s hs.le (dat.grp i)
      rcases (hsol.2.1 t ht.le i).eq_or_lt with h | h
      · rw [← h]; simp only [zero_mul, sub_zero]
        exact mul_nonneg (hsol.2.1 s hs.le i) (div_nonneg (hYt _) hYs)
      · have hzs := hpos i h
        have hYsp : 0 < groupAggregate dat.grp (Zh s) (dat.grp i) :=
          lt_of_lt_of_le hzs (pf_Z_le_Y hsol s hs.le i)
        have hYtp : 0 < groupAggregate dat.grp (Zh t) (dat.grp i) :=
          lt_of_lt_of_le h (pf_Z_le_Y hsol t ht.le i)
        set a := Zh s i; set b := groupAggregate dat.grp (Zh s) (dat.grp i)
        set c := Zh t i; set d := groupAggregate dat.grp (Zh t) (dat.grp i)
        have hq : 0 < a * d / (b * c) := by positivity
        have hl := Real.log_le_sub_one_of_pos hq
        rw [Real.log_div (by positivity) (by positivity), Real.log_mul hzs.ne' hYtp.ne',
          Real.log_mul hYsp.ne' h.ne'] at hl
        have e : c * (a * d / (b * c) - 1) = a * (d / b) - c := by field_simp
        have := mul_le_mul_of_nonneg_left hl h.le
        rw [e] at this
        nlinarith
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsum
    have h1 := pf_fiber dat.grp (Zh s) (fun ℓ => groupAggregate dat.grp (Zh t) ℓ /
      groupAggregate dat.grp (Zh s) ℓ)
    have h2 := pf_fiber dat.grp (Zh t) (fun _ => (1:ℝ))
    simp only [mul_one] at h2
    have h3 : ∑ ℓ, groupAggregate dat.grp (Zh s) ℓ * (groupAggregate dat.grp (Zh t) ℓ /
        groupAggregate dat.grp (Zh s) ℓ) ≤ ∑ ℓ, groupAggregate dat.grp (Zh t) ℓ := by
      refine Finset.sum_le_sum fun ℓ _ => ?_
      rcases (pf_Y_nonneg hsol s hs.le ℓ).eq_or_lt with h | h
      · rw [← h, zero_mul]; exact hYt ℓ
      · rw [mul_div_cancel₀ _ h.ne']
    linarith
  linarith

lemma pf_phi_eq {I L : ℕ} {dat : PFUnitaryNetworkData I L} {Ah Dh Th Zh : ℝ → Fin I → ℝ}
    (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh) (alpha : Fin I → ℝ) (u : ℝ) (hu : 0 < u) :
    phi Dh Zh alpha u = ∑ i, Zh u i * Real.log (pfG dat Zh i u / alpha i) := by
  unfold phi
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [h, zero_mul]
  · rw [pf_derivWithin_D hsol u hu i (lt_of_le_of_ne (hsol.2.1 u hu.le i) (Ne.symm h))]
    rfl

theorem dini_regular_core {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (alpha : Fin I → ℝ)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (hα : ∀ i, 0 < alpha i) (t : ℝ) (ht : 0 < t) (hreg : RegularPoint Ah Dh Th Zh t) :
    diniUpperRight (phi Dh Zh alpha) t ≤
      ((∑ i, deriv (fun s => Zh s i) t * Real.log (deriv (fun s => Dh s i) t / alpha i) : ℝ) :
        EReal) := by
  obtain ⟨B, hB1, hB⟩ := pf_dom_bound hdom
  have hZd : ∀ i, HasDerivAt (fun s => Zh s i) (deriv (fun s => Zh s i) t) t := fun i =>
    (differentiableAt_pi.1 hreg.2.2.2 i).hasDerivAt
  have hZ0 : ∀ i, Zh t i = 0 → deriv (fun s => Zh s i) t = 0 := by
    intro i h
    apply IsLocalMin.deriv_eq_zero
    filter_upwards [lt_mem_nhds ht] with s hs
    rw [h]; exact hsol.2.1 s hs.le i
  have hDd : ∀ i, 0 < Zh t i → deriv (fun s => Dh s i) t = pfG dat Zh i t := by
    intro i h
    have hd := (hsol.2.2.2.2.2 t ht i h).div_const (dat.m i)
    have hd2 : HasDerivAt (fun s => Dh s i) _ t := hd.congr_of_eventuallyEq
      (by filter_upwards [lt_mem_nhds ht] with s hs; exact hsol.2.2.2.1 s hs.le i)
    exact hd2.deriv
  set Cp : Fin I → ℝ := fun i => max 0 (Real.log (B / dat.m i / alpha i)) with hCp
  set W : Fin I → ℝ → ℝ := fun i h =>
    if 0 < Zh t i then Real.log (pfG dat Zh i (t + h) / alpha i) else Cp i with hW
  set Lim : ℝ := ∑ i, deriv (fun s => Zh s i) t *
    (if 0 < Zh t i then Real.log (pfG dat Zh i t / alpha i) else Cp i) with hLim
  have hLimEq : Lim = ∑ i, deriv (fun s => Zh s i) t *
      Real.log (deriv (fun s => Dh s i) t / alpha i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rw [hDd i h]
    · have : Zh t i = 0 := le_antisymm (not_lt.1 h) (hsol.2.1 t ht.le i)
      rw [hZ0 i this, zero_mul, zero_mul]
  have hshift : Tendsto (fun h : ℝ => t + h) (𝓝[>] 0) (𝓝[Set.Ioi 0] t) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 (t + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      rw [add_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      exact show 0 < t + h by linarith
  have hF : Tendsto (fun h => ∑ i, (h⁻¹ * (Zh (t + h) i - Zh t i)) * W i h) (𝓝[>] 0)
      (𝓝 Lim) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    refine ((hZd i).tendsto_slope_zero_right).mul ?_
    by_cases h : 0 < Zh t i
    · simp only [W, if_pos h]
      have hg := (pf_G_cont hdom hsol i t ht h).tendsto.comp hshift
      exact (hg.div_const (alpha i)).log (div_pos (pf_G_pos hdom hsol i t ht h) (hα i)).ne'
    · simp only [W, if_neg h]
      exact tendsto_const_nhds
  have hZcont : ∀ i, Tendsto (fun h : ℝ => Zh (t + h) i) (𝓝[>] 0) (𝓝 (Zh t i)) := fun i =>
    (hZd i).continuousAt.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa using (continuous_const.add continuous_id).tendsto (0:ℝ) (f := fun h : ℝ => t + h)))
  have hposev : ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ i, 0 < Zh t i → 0 < Zh (t + h) i := by
    rw [eventually_all]
    intro i
    by_cases h : 0 < Zh t i
    · exact ((hZcont i).eventually_const_lt h).mono fun _ hh _ => hh
    · exact Eventually.of_forall fun _ h' => absurd h' h
  have hev : ∀ᶠ h in 𝓝[>] (0:ℝ), (phi Dh Zh alpha (t + h) - phi Dh Zh alpha t) / h ≤
      ∑ i, (h⁻¹ * (Zh (t + h) i - Zh t i)) * W i h := by
    filter_upwards [self_mem_nhdsWithin, hposev] with h (hh : 0 < h) hpos
    have hth : 0 < t + h := by linarith
    rw [pf_phi_eq hsol alpha _ hth, pf_phi_eq hsol alpha _ ht, div_eq_inv_mul]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hh.le)
    have hopt := pf_opt hdom hsol t (t + h) ht hth hpos
    have hper : ∀ i, Zh (t + h) i * Real.log (pfG dat Zh i (t + h) / alpha i) -
        Zh t i * Real.log (pfG dat Zh i t / alpha i) ≤
        (Zh (t + h) i - Zh t i) * W i h +
        (Zh t i * Real.log (pfG dat Zh i (t + h)) - Zh t i * Real.log (pfG dat Zh i t)) := by
      intro i
      by_cases hi : 0 < Zh t i
      · simp only [W, if_pos hi]
        have h1 := pf_G_pos hdom hsol i t ht hi
        have h2 := pf_G_pos hdom hsol i (t + h) hth (hpos i hi)
        rw [Real.log_div h1.ne' (hα i).ne', Real.log_div h2.ne' (hα i).ne']
        ring_nf; exact le_rfl
      · simp only [W, if_neg hi]
        have h0 : Zh t i = 0 := le_antisymm (not_lt.1 hi) (hsol.2.1 t ht.le i)
        rw [h0]
        simp only [zero_mul, sub_zero, add_zero]
        rcases (hsol.2.1 (t + h) hth.le i).eq_or_lt with hz | hz
        · rw [← hz]; simp
        · apply mul_le_mul_of_nonneg_left _ hz.le
          have hg := pf_G_pos hdom hsol i (t + h) hth hz
          have hgl := pf_G_le hdom hsol B hB i (t + h) hth hz
          refine le_trans ?_ (le_max_right _ _)
          exact Real.log_le_log (div_pos hg (hα i))
            (div_le_div_of_nonneg_right hgl (hα i).le)
    have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hper i
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
    linarith
  unfold diniUpperRight
  calc Filter.limsup (fun h : ℝ => (((phi Dh Zh alpha (t + h) - phi Dh Zh alpha t) / h : ℝ) :
        EReal)) (𝓝[>] 0)
      ≤ Filter.limsup (fun h : ℝ => ((∑ i, (h⁻¹ * (Zh (t + h) i - Zh t i)) * W i h : ℝ) :
        EReal)) (𝓝[>] 0) :=
        Filter.limsup_le_limsup (hev.mono fun h hh => EReal.coe_le_coe_iff.2 hh)
    _ = (Lim : EReal) := (EReal.tendsto_coe.2 hF).limsup_eq
    _ = _ := by rw [hLimEq]

end ProcessingNetworks.ProportionalFairness

open ProcessingNetworks.ProportionalFairness


theorem solution
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0)) (alpha : Fin I → ℝ)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i)
    (t : ℝ) (ht : 0 < t) (hreg : RegularPoint Ah Dh Th Zh t) :
    diniUpperRight (phi Dh Zh alpha) t ≤
      ((∑ i, deriv (fun s => Zh s i) t * Real.log (deriv (fun s => Dh s i) t / alpha i) : ℝ) :
        EReal) := by
  exact dini_regular_core dat hdom alpha Ah Dh Th Zh hsol hα t ht hreg
