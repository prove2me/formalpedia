-- Prove2me | solution 1 for SennottDP.ChainASM.atas_excess_to_finite_set_conforming
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:26:46.559539+00:00
-- url     : https://prove2.me/submissions/1da8bed3-3b4d-42da-b595-b1ac16e8f212

import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical


namespace SennottDP.ChainASM

lemma sdp_fatou_tsum {α : Type*} (f : ℕ → α → ℝ≥0∞) (g : α → ℝ≥0∞)
    (h : ∀ j, Tendsto (fun N => f N j) atTop (𝓝 (g j))) :
    ∑' j, g j ≤ liminf (fun N => ∑' j, f N j) atTop := by
  let _ : MeasurableSpace α := ⊤
  have := MeasureTheory.lintegral_liminf_le (μ := MeasureTheory.Measure.count) (f := f)
    (u := atTop) (fun n => measurable_from_top)
  simp only [MeasureTheory.lintegral_count] at this
  calc ∑' j, g j = ∑' j, liminf (fun N => f N j) atTop := by
        congr 1; ext j; exact ((h j).liminf_eq).symm
  _ ≤ _ := this

lemma sdp_split {α : Type*} (w a : α → ℝ≥0∞) (ha : ∀ j, a j ≤ 1) :
    ∑' j, w j * a j + ∑' j, w j * (1 - a j) = ∑' j, w j := by
  rw [← ENNReal.tsum_add]
  congr 1; ext j
  rw [← mul_add, add_tsub_cancel_of_le (ha j), mul_one]

lemma sdp_wlim {α : Type*} (w : ℕ → α → ℝ≥0∞) (w0 : α → ℝ≥0∞) (a : ℕ → α → ℝ≥0∞)
    (a0 : α → ℝ≥0∞) (hw : ∀ j, Tendsto (fun N => w N j) atTop (𝓝 (w0 j)))
    (ha : ∀ j, Tendsto (fun N => a N j) atTop (𝓝 (a0 j)))
    (hw1 : ∀ᶠ N in atTop, ∑' j, w N j = 1) (hw01 : ∑' j, w0 j = 1)
    (ha1 : ∀ N j, a N j ≤ 1) :
    Tendsto (fun N => ∑' j, w N j * a N j) atTop (𝓝 (∑' j, w0 j * a0 j)) := by
  have ha01 : ∀ j, a0 j ≤ 1 := fun j =>
    le_of_tendsto' (ha j) (fun N => ha1 N j)
  have hw0le : ∀ j, w0 j ≤ 1 := fun j => hw01 ▸ ENNReal.le_tsum j
  have hx := sdp_fatou_tsum (fun N j => w N j * a N j) (fun j => w0 j * a0 j)
    (fun j => ENNReal.Tendsto.mul (hw j) (Or.inr (ne_top_of_le_ne_top ENNReal.one_ne_top (ha01 j)))
      (ha j) (Or.inr (ne_top_of_le_ne_top ENNReal.one_ne_top (hw0le j))))
  have hy := sdp_fatou_tsum (fun N j => w N j * (1 - a N j)) (fun j => w0 j * (1 - a0 j))
    (fun j => ENNReal.Tendsto.mul (hw j) (Or.inr (by
        exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self))
      (ENNReal.Tendsto.sub tendsto_const_nhds (ha j) (Or.inl ENNReal.one_ne_top))
      (Or.inr (ne_top_of_le_ne_top ENNReal.one_ne_top (hw0le j))))
  have hs0 := sdp_split w0 a0 ha01
  rw [hw01] at hs0
  have hsN : ∀ᶠ N in atTop, ∑' j, w N j * a N j + ∑' j, w N j * (1 - a N j) = 1 := by
    filter_upwards [hw1] with N hN
    rw [sdp_split (w N) (a N) (ha1 N), hN]
  set x0 := ∑' j, w0 j * a0 j
  set y0 := ∑' j, w0 j * (1 - a0 j)
  refine tendsto_order.2 ⟨fun b hb => eventually_lt_of_lt_liminf (lt_of_lt_of_le hb hx), ?_⟩
  intro b hb
  by_cases hb1 : 1 < b
  · filter_upwards [hsN] with N hN
    refine lt_of_le_of_lt ?_ hb1
    rw [← hN]; exact le_self_add
  · push Not at hb1
    have hbt : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hb1
    have hy0t : y0 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hs0 ▸ le_add_self)
    have hc : 1 - b < y0 := by
      by_contra hcon
      push Not at hcon
      have : x0 + y0 < b + y0 := ENNReal.add_lt_add_right hy0t hb
      have h2 : b + y0 ≤ b + (1 - b) := add_le_add le_rfl hcon
      rw [add_tsub_cancel_of_le hb1, ← hs0] at h2
      exact lt_irrefl _ (lt_of_lt_of_le this h2)
    filter_upwards [hsN, eventually_lt_of_lt_liminf (lt_of_lt_of_le hc hy)] with N hN hyN
    by_contra hcon
    push Not at hcon
    have h1 : b + (1 - b) < b + ∑' j, w N j * (1 - a N j) := ENNReal.add_lt_add_left hbt hyN
    have h2 : b + ∑' j, w N j * (1 - a N j) ≤ 1 := by
      exact le_trans (add_le_add hcon le_rfl) hN.le
    rw [add_tsub_cancel_of_le hb1] at h1
    exact lt_irrefl _ (lt_of_lt_of_le h1 h2)


lemma sdp_taboo_le_one {S : Type*} (Γ : MC S) (G : Set S) :
    ∀ t i k, Γ.tabooProb G t i k ≤ 1 := by
  have h1 : ∀ i k, Γ.P i k ≤ 1 := fun i k => (Γ.P_sum i) ▸ ENNReal.le_tsum k
  have : ∀ t i k, Γ.tabooProb G (t + 1) i k ≤ 1 := by
    intro t
    induction t with
    | zero => intro i k; simpa [MC.tabooProb] using h1 i k
    | succ t ih =>
      intro i k
      rw [MC.tabooProb]
      calc (∑' j, if j ∈ G then 0 else Γ.P i j * Γ.tabooProb G (t + 1) j k)
          ≤ ∑' j, Γ.P i j := by
            refine ENNReal.tsum_le_tsum fun j => ?_
            split_ifs
            · exact bot_le
            · exact le_trans (mul_le_mul_right (ih j k) _) (by rw [mul_one])
        _ = 1 := Γ.P_sum i
  intro t i k
  cases t with
  | zero => simp only [MC.tabooProb]; split_ifs <;> simp
  | succ t => exact this t i k

lemma sdp_ev_mem {S : Type*} {Γ : MC S} (AS : ApproxSeq Γ) (i : S) :
    ∀ᶠ N in atTop, AS.N₀ ≤ N ∧ i ∈ AS.SN N := by
  obtain ⟨N1, h1, h2⟩ := AS.SN_cover i
  filter_upwards [eventually_ge_atTop N1] with N hN
  exact ⟨le_trans h1 hN, AS.SN_mono N1 N h1 hN h2⟩

lemma sdp_tabooN_le_one {S : Type*} {Γ : MC S} (AS : ApproxSeq Γ) (G : Set S) (t N : ℕ)
    (i k : S) : AS.tabooProbN G t N i k ≤ 1 := by
  unfold ApproxSeq.tabooProbN
  split_ifs with h
  · exact sdp_taboo_le_one _ _ _ _ _
  · exact bot_le

lemma sdp_tabooN_step {S : Type*} {Γ : MC S} (AS : ApproxSeq Γ) (G : Set S) (t N : ℕ)
    (i k : S) (h : AS.N₀ ≤ N ∧ i ∈ AS.SN N ∧ k ∈ AS.SN N) :
    AS.tabooProbN G (t + 2) N i k = ∑' j, (if j ∈ AS.SN N then AS.PN N i j else 0) *
      (if j ∈ G then 0 else AS.tabooProbN G (t + 1) N j k) := by
  unfold ApproxSeq.tabooProbN
  rw [dif_pos h, MC.tabooProb]
  rw [← tsum_subtype_eq_of_support_subset (s := (AS.SN N : Set S))]
  · refine tsum_congr fun j => ?_
    have hj : (j : S) ∈ AS.SN N := j.2
    simp only [Set.mem_preimage, hj, if_true]
    split_ifs with h3 h4
    · simp
    · simp [ApproxSeq.chain]
    · exact absurd ⟨h.1, trivial, h.2.2⟩ h4
  · intro j hj
    by_contra hc
    exact hj (by simp only [Finset.mem_coe] at hc; simp [hc])

lemma sdp_tabooN_one {S : Type*} {Γ : MC S} (AS : ApproxSeq Γ) (G : Set S) (N : ℕ)
    (i k : S) (h : AS.N₀ ≤ N ∧ i ∈ AS.SN N ∧ k ∈ AS.SN N) :
    AS.tabooProbN G 1 N i k = AS.PN N i k := by
  unfold ApproxSeq.tabooProbN
  rw [dif_pos h]; simp [MC.tabooProb, ApproxSeq.chain]

lemma sdp_taboo_tendsto {S : Type*} {Γ : MC S} (AS : ApproxSeq Γ) (G : Set S) :
    ∀ t : ℕ, ∀ i k : S, Tendsto (fun N => AS.tabooProbN G (t + 1) N i k) atTop
      (𝓝 (Γ.tabooProb G (t + 1) i k)) := by
  intro t
  induction t with
  | zero =>
    intro i k
    refine (AS.PN_tendsto i k).congr' ?_
    filter_upwards [sdp_ev_mem AS i, sdp_ev_mem AS k] with N h1 h2
    exact (sdp_tabooN_one AS G N i k ⟨h1.1, h1.2, h2.2⟩).symm
  | succ t ih =>
    intro i k
    have hw : ∀ j, Tendsto (fun N => if j ∈ AS.SN N then AS.PN N i j else 0) atTop
        (𝓝 (Γ.P i j)) := by
      intro j
      refine (AS.PN_tendsto i j).congr' ?_
      filter_upwards [sdp_ev_mem AS j] with N h1
      simp [h1.2]
    have ha : ∀ j, Tendsto (fun N => if j ∈ G then 0 else AS.tabooProbN G (t + 1) N j k) atTop
        (𝓝 (if j ∈ G then 0 else Γ.tabooProb G (t + 1) j k)) := by
      intro j
      by_cases hj : j ∈ G
      · simp [hj]
      · simpa [hj] using ih j k
    have hw1 : ∀ᶠ N in atTop, ∑' j, (if j ∈ AS.SN N then AS.PN N i j else 0) = 1 := by
      filter_upwards [sdp_ev_mem AS i] with N h1
      rw [tsum_eq_sum (s := AS.SN N) (fun j hj => by simp [hj])]
      rw [← AS.PN_sum N h1.1 i h1.2]
      exact Finset.sum_congr rfl fun j hj => by simp [hj]
    have := sdp_wlim _ _ _ _ hw ha hw1 (Γ.P_sum i) (fun N j => by
      split_ifs
      · exact bot_le
      · exact sdp_tabooN_le_one AS G _ _ _ _)
    have e : Γ.tabooProb G (t + 1 + 1) i k =
        ∑' j, Γ.P i j * (if j ∈ G then 0 else Γ.tabooProb G (t + 1) j k) := by
      rw [show t + 1 + 1 = t + 2 from rfl, MC.tabooProb]
      refine tsum_congr fun j => ?_
      split_ifs <;> simp
    rw [e]
    refine this.congr' ?_
    filter_upwards [sdp_ev_mem AS i, sdp_ev_mem AS k] with N h1 h2
    exact (sdp_tabooN_step AS G t N i k ⟨h1.1, h1.2, h2.2⟩).symm


noncomputable def sdpAvN {S : Type*} {Γ : MC S} (AS : ApproxSeq Γ) (G : Set S) (t N : ℕ)
    (i k : S) : ℝ≥0∞ :=
  if h : AS.N₀ ≤ N ∧ i ∈ AS.SN N ∧ k ∈ AS.SN N then
    (AS.chain N h.1).avoidProb (Subtype.val ⁻¹' G) t ⟨i, h.2.1⟩ ⟨k, h.2.2⟩ else 0

lemma sdp_avN_tendsto {S : Type*} {Γ : MC S} (AS : ApproxSeq Γ) (G : Set S) (t : ℕ)
    (i k : S) : Tendsto (fun N => sdpAvN AS G t N i k) atTop (𝓝 (Γ.avoidProb G t i k)) := by
  have hev : ∀ᶠ N in atTop, sdpAvN AS G t N i k = (if t = 0 then (if i = k then 1 else 0)
      else if k ∈ G then 0 else AS.tabooProbN G t N i k) := by
    filter_upwards [sdp_ev_mem AS i, sdp_ev_mem AS k] with N h1 h2
    have h : AS.N₀ ≤ N ∧ i ∈ AS.SN N ∧ k ∈ AS.SN N := ⟨h1.1, h1.2, h2.2⟩
    unfold sdpAvN ApproxSeq.tabooProbN
    rw [dif_pos h, dif_pos h]
    simp [MC.avoidProb]
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  unfold MC.avoidProb
  rcases t with _ | s
  · simp
  · simp only [Nat.add_one_ne_zero, if_false]
    by_cases hk : k ∈ G
    · simp [hk]
    · simpa [hk] using sdp_taboo_tendsto AS G s i k

lemma sdp_visitsN_eq {S : Type*} {Γ : MC S} (AS : ApproxSeq Γ) (G : Set S) (N : ℕ)
    (i k : S) : AS.visitsN G N i k = ∑' t, sdpAvN AS G t N i k := by
  unfold ApproxSeq.visitsN sdpAvN MC.visits
  split_ifs <;> simp

lemma sdp_inner_eq {S : Type*} {Γ : MC S} (AS : ApproxSeq Γ) (G : Set S) (t N : ℕ)
    (i : S) (h : AS.N₀ ≤ N ∧ i ∈ AS.SN N) (c : S → ℝ≥0∞) :
    ∑' k : AS.SN N, (AS.chain N h.1).avoidProb (Subtype.val ⁻¹' G) t ⟨i, h.2⟩ k * c k.1 =
      ∑' k, sdpAvN AS G t N i k * c k := by
  rw [← tsum_subtype_eq_of_support_subset (s := (AS.SN N : Set S))]
  · refine tsum_congr fun j => ?_
    have hj : (j : S) ∈ AS.SN N := j.2
    unfold sdpAvN
    rw [dif_pos ⟨h.1, h.2, hj⟩]
  · intro j hj
    by_contra hc
    simp only [Finset.mem_coe] at hc
    apply hj
    show sdpAvN AS G t N i j * c j = 0
    unfold sdpAvN
    rw [dif_neg (fun h' => hc h'.2.2)]; simp

lemma sdp_meanPassageN_eq {S : Type*} {Γ : MC S} (AS : ApproxSeq Γ) (G : Set S) (N : ℕ)
    (i : S) : AS.meanPassageN G N i = ∑' t, ∑' k, sdpAvN AS G t N i k * 1 := by
  unfold ApproxSeq.meanPassageN MC.meanPassage
  split_ifs with h
  · refine tsum_congr fun t => ?_
    rw [← sdp_inner_eq AS G t N i h (fun _ => 1)]
    simp
  · symm
    refine ENNReal.tsum_eq_zero.2 fun t => ENNReal.tsum_eq_zero.2 fun k => ?_
    unfold sdpAvN
    rw [dif_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]; simp

lemma sdp_passageCostN_eq {S : Type*} {Γ : MC S} (AS : ApproxSeq Γ) (G : Set S) (N : ℕ)
    (i : S) : AS.passageCostN G N i = ∑' t, ∑' k, sdpAvN AS G t N i k * (Γ.C k : ℝ≥0∞) := by
  unfold ApproxSeq.passageCostN MC.passageCost
  split_ifs with h
  · refine tsum_congr fun t => ?_
    rw [← sdp_inner_eq AS G t N i h (fun k => (Γ.C k : ℝ≥0∞))]
    rfl
  · symm
    refine ENNReal.tsum_eq_zero.2 fun t => ENNReal.tsum_eq_zero.2 fun k => ?_
    unfold sdpAvN
    rw [dif_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]; simp

lemma sdp_double_liminf {S : Type*} {Γ : MC S} (AS : ApproxSeq Γ) (G : Set S) (i : S)
    (c : S → ℝ≥0∞) (hc : ∀ k, c k ≠ ⊤) :
    ∑' t, ∑' k, Γ.avoidProb G t i k * c k ≤
      liminf (fun N => ∑' t, ∑' k, sdpAvN AS G t N i k * c k) atTop := by
  have := sdp_fatou_tsum (fun N (p : ℕ × S) => sdpAvN AS G p.1 N i p.2 * c p.2)
    (fun p => Γ.avoidProb G p.1 i p.2 * c p.2)
    (fun p => ENNReal.Tendsto.mul_const (sdp_avN_tendsto AS G p.1 i p.2) (Or.inr (hc p.2)))
  rw [← ENNReal.tsum_prod (f := fun t k => Γ.avoidProb G t i k * c k)]
  refine le_trans this (le_of_eq ?_)
  congr 1; ext N
  exact ENNReal.tsum_prod (f := fun t k => sdpAvN AS G t N i k * c k)

lemma sdp_visits_G {S : Type*} (Γ : MC S) (G : Set S) (i k : S) (hk : k ∈ G) :
    Γ.visits G i k = if i = k then 1 else 0 := by
  unfold MC.visits
  rw [tsum_eq_single 0]
  · simp [MC.avoidProb]
  · intro t ht
    simp [MC.avoidProb, ht, hk]

theorem as_taboo_visits_passage_limits_core {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (AS : ApproxSeq Γ) (G : Finset S) (hG : G.Nonempty) :
    (∀ i k : S, ∀ t : ℕ, 1 ≤ t →
      Tendsto (fun N => AS.tabooProbN (↑G : Set S) t N i k) atTop
        (𝓝 (Γ.tabooProb (↑G : Set S) t i k))) ∧
    (∀ k ∈ G, ∀ i : S, Γ.visits (↑G : Set S) i k = (if i = k then 1 else 0) ∧
      ∀ᶠ N in atTop, AS.visitsN (↑G : Set S) N i k = Γ.visits (↑G : Set S) i k) ∧
    (∀ i k : S, Γ.visits (↑G : Set S) i k ≤
      liminf (fun N => AS.visitsN (↑G : Set S) N i k) atTop) ∧
    (∀ i : S, Γ.meanPassage (↑G : Set S) i ≤
      liminf (fun N => AS.meanPassageN (↑G : Set S) N i) atTop) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i k t ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    exact sdp_taboo_tendsto AS _ s i k
  · intro k hk i
    have hkG : k ∈ (↑G : Set S) := hk
    refine ⟨sdp_visits_G Γ _ i k hkG, ?_⟩
    filter_upwards [sdp_ev_mem AS i, sdp_ev_mem AS k] with N h1 h2
    have h : AS.N₀ ≤ N ∧ i ∈ AS.SN N ∧ k ∈ AS.SN N := ⟨h1.1, h1.2, h2.2⟩
    unfold ApproxSeq.visitsN
    rw [dif_pos h, sdp_visits_G _ _ _ _ (by simpa using hkG), sdp_visits_G Γ _ i k hkG]
    simp
  · intro i k
    unfold MC.visits
    simp only [sdp_visitsN_eq]
    exact sdp_fatou_tsum _ _ (fun t => sdp_avN_tendsto AS _ t i k)
  · intro i
    have := sdp_double_liminf AS (↑G : Set S) i (fun _ => 1) (fun _ => ENNReal.one_ne_top)
    simp only [mul_one] at this
    unfold MC.meanPassage
    simp only [sdp_meanPassageN_eq, mul_one]
    exact this

theorem as_passage_cost_liminf_core {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (AS : ApproxSeq Γ) (G : Finset S) (hG : G.Nonempty) (i : S)
    (hm : Γ.meanPassage (↑G : Set S) i < ⊤)
    (hmN : ∀ᶠ N in atTop, AS.meanPassageN (↑G : Set S) N i < ⊤) :
    Γ.passageCost (↑G : Set S) i ≤
      liminf (fun N => AS.passageCostN (↑G : Set S) N i) atTop := by
  unfold MC.passageCost
  simp only [sdp_passageCostN_eq]
  exact sdp_double_liminf AS _ i _ (fun _ => ENNReal.coe_ne_top)

section gen
variable {T : Type*} (Γ : MC T)

lemma sdq_avoid_succ (G : Set T) (t : ℕ) (i k : T) :
    Γ.avoidProb G (t + 1) i k = ∑' j, if j ∈ G then 0 else Γ.P i j * Γ.avoidProb G t j k := by
  rcases t with _ | s
  · simp only [MC.avoidProb, Nat.add_one_ne_zero, if_false, if_true, MC.tabooProb]
    by_cases hk : k ∈ G
    · simp only [hk, if_true]
      symm; refine ENNReal.tsum_eq_zero.2 fun j => ?_
      split_ifs with h1 h2 <;> simp_all
    · simp only [hk, if_false]
      rw [tsum_eq_single k]
      · simp [hk]
      · intro j hj; split_ifs <;> simp_all
  · simp only [MC.avoidProb, Nat.add_one_ne_zero, if_false]
    rw [show s + 1 + 1 = s + 2 from rfl, MC.tabooProb]
    by_cases hk : k ∈ G
    · simp only [hk, if_true]
      symm; exact ENNReal.tsum_eq_zero.2 fun j => by split_ifs <;> simp
    · simp only [hk, if_false]

lemma sdq_first_step (G : Set T) (w : T → ℝ≥0∞) (i : T) :
    ∑' t, ∑' k, Γ.avoidProb G t i k * w k =
      w i + ∑' j, if j ∈ G then 0 else Γ.P i j * ∑' t, ∑' k, Γ.avoidProb G t j k * w k := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  congr 1
  · simp only [MC.avoidProb, if_true]
    rw [tsum_eq_single i]
    · simp
    · intro j hj; simp [Ne.symm hj]
  · simp only [sdq_avoid_succ]
    calc (∑' t, ∑' k, (∑' j, if j ∈ G then 0 else Γ.P i j * Γ.avoidProb G t j k) * w k)
        = ∑' t, ∑' k, ∑' j, (if j ∈ G then 0 else Γ.P i j * (Γ.avoidProb G t j k * w k)) := by
          refine tsum_congr fun t => tsum_congr fun k => ?_
          rw [← ENNReal.tsum_mul_right]
          refine tsum_congr fun j => ?_
          split_ifs <;> simp [mul_assoc]
      _ = ∑' t, ∑' j, ∑' k, (if j ∈ G then 0 else Γ.P i j * (Γ.avoidProb G t j k * w k)) :=
          tsum_congr fun t => ENNReal.tsum_comm
      _ = ∑' j, ∑' t, ∑' k, (if j ∈ G then 0 else Γ.P i j * (Γ.avoidProb G t j k * w k)) :=
          ENNReal.tsum_comm
      _ = _ := by
          refine tsum_congr fun j => ?_
          split_ifs
          · simp
          · rw [← ENNReal.tsum_mul_left]
            exact tsum_congr fun t => by rw [← ENNReal.tsum_mul_left]

lemma sdq_step_t (G : Set T) (w : T → ℝ≥0∞) (t : ℕ) (i : T) :
    ∑' k, Γ.avoidProb G (t + 1) i k * w k =
      ∑' j, if j ∈ G then 0 else Γ.P i j * ∑' k, Γ.avoidProb G t j k * w k := by
  simp only [sdq_avoid_succ]
  calc (∑' k, (∑' j, if j ∈ G then 0 else Γ.P i j * Γ.avoidProb G t j k) * w k)
      = ∑' k, ∑' j, (if j ∈ G then 0 else Γ.P i j * (Γ.avoidProb G t j k * w k)) := by
        refine tsum_congr fun k => ?_
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun j => ?_
        split_ifs <;> simp [mul_assoc]
    _ = ∑' j, ∑' k, (if j ∈ G then 0 else Γ.P i j * (Γ.avoidProb G t j k * w k)) :=
        ENNReal.tsum_comm
    _ = _ := by
        refine tsum_congr fun j => ?_
        split_ifs
        · simp
        · rw [← ENNReal.tsum_mul_left]

lemma sdq_compare (G : Set T) (w y : T → ℝ≥0∞)
    (hy : ∀ i, w i + ∑' j, (if j ∈ G then 0 else Γ.P i j * y j) ≤ y i) (i : T) :
    ∑' t, ∑' k, Γ.avoidProb G t i k * w k ≤ y i := by
  have h0 : ∀ i, ∑' k, Γ.avoidProb G 0 i k * w k = w i := by
    intro i
    simp only [MC.avoidProb, if_true]
    rw [tsum_eq_single i]
    · simp
    · intro j hj; simp [Ne.symm hj]
  have key : ∀ n i, ∑ t ∈ Finset.range n, ∑' k, Γ.avoidProb G t i k * w k ≤ y i := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
      intro i
      rw [Finset.sum_range_succ', h0]
      simp only [sdq_step_t]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine le_trans ?_ (hy i)
      rw [add_comm]
      refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun j => ?_)
      split_ifs
      · simp
      · rw [← Finset.mul_sum]
        exact mul_le_mul_right (ih j) _
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun n => key n i

lemma sdq_nStep_one (i k : T) : Γ.nStep 1 i k = Γ.P i k := by
  simp only [MC.nStep]
  rw [tsum_eq_single i]
  · simp
  · intro j hj; simp [Ne.symm hj]

lemma sdq_nStep_add (s t : ℕ) (i k : T) :
    Γ.nStep (s + t) i k = ∑' j, Γ.nStep s i j * Γ.nStep t j k := by
  induction t generalizing k with
  | zero =>
    simp only [add_zero, MC.nStep]
    rw [tsum_eq_single k]
    · simp
    · intro j hj; simp [hj]
  | succ t ih =>
    rw [← add_assoc]
    simp only [MC.nStep, ih]
    calc (∑' l, (∑' j, Γ.nStep s i j * Γ.nStep t j l) * Γ.P l k)
        = ∑' l, ∑' j, Γ.nStep s i j * (Γ.nStep t j l * Γ.P l k) := by
          refine tsum_congr fun l => ?_
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr fun j => by rw [mul_assoc]
      _ = ∑' j, ∑' l, Γ.nStep s i j * (Γ.nStep t j l * Γ.P l k) := ENNReal.tsum_comm
      _ = _ := tsum_congr fun j => by rw [ENNReal.tsum_mul_left]

lemma sdq_nStep_front (t : ℕ) (i k : T) :
    Γ.nStep (1 + t) i k = ∑' j, Γ.P i j * Γ.nStep t j k := by
  rw [sdq_nStep_add]
  simp only [sdq_nStep_one]

lemma sdq_nStep_sum (t : ℕ) (i : T) : ∑' k, Γ.nStep t i k = 1 := by
  induction t with
  | zero =>
    simp only [MC.nStep]
    rw [tsum_eq_single i]
    · simp
    · intro j hj; simp [Ne.symm hj]
  | succ t ih =>
    simp only [MC.nStep]
    rw [ENNReal.tsum_comm]
    simp only [ENNReal.tsum_mul_left, Γ.P_sum, mul_one, ih]

lemma sdq_closed_avoid (G U : Set T) (hU : ∀ j ∈ U, ∀ l, Γ.P j l ≠ 0 → l ∈ U)
    (hUG : ∀ j ∈ U, j ∉ G) : ∀ t, ∀ j ∈ U, ∀ k, Γ.avoidProb G t j k = Γ.nStep t j k := by
  intro t
  induction t with
  | zero => intro j _ k; simp [MC.avoidProb, MC.nStep]
  | succ t ih =>
    intro j hj k
    rw [sdq_avoid_succ, add_comm, sdq_nStep_front]
    refine tsum_congr fun l => ?_
    by_cases hP : Γ.P j l = 0
    · simp [hP]
    · have hl := hU j hj l hP
      rw [if_neg (hUG l hl), ih l hl k]

lemma sdq_closed_top (G U : Set T) (hU : ∀ j ∈ U, ∀ l, Γ.P j l ≠ 0 → l ∈ U)
    (hUG : ∀ j ∈ U, j ∉ G) (j : T) (hj : j ∈ U) : Γ.meanPassage G j = ⊤ := by
  unfold MC.meanPassage
  simp only [sdq_closed_avoid Γ G U hU hUG _ j hj, sdq_nStep_sum]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

lemma sdq_leads_step (j l z : T) (hP : Γ.P j l ≠ 0) (h : Γ.LeadsTo l z) : Γ.LeadsTo j z := by
  obtain ⟨t, ht⟩ := h
  refine ⟨1 + t, ?_⟩
  rw [sdq_nStep_front]
  exact lt_of_lt_of_le (ENNReal.mul_pos hP ht.ne') (ENNReal.le_tsum l)

lemma sdq_leads_trans (i j k : T) (h1 : Γ.LeadsTo i j) (h2 : Γ.LeadsTo j k) :
    Γ.LeadsTo i k := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  refine ⟨s + t, ?_⟩
  rw [sdq_nStep_add]
  exact lt_of_lt_of_le (ENNReal.mul_pos hs.ne' ht.ne') (ENNReal.le_tsum j)

lemma sdq_leads_refl (i : T) : Γ.LeadsTo i i := ⟨0, by simp [MC.nStep]⟩

lemma sdq_A (z j : T) (h : Γ.meanPassage {z} j < ⊤) : Γ.LeadsTo j z := by
  by_contra hc
  have := sdq_closed_top Γ {z} {j | ¬ Γ.LeadsTo j z}
    (fun a ha l hP hl => ha (sdq_leads_step Γ a l z hP hl))
    (fun a ha hz => ha (by rw [Set.mem_singleton_iff.1 hz]; exact sdq_leads_refl Γ z)) j hc
  rw [this] at h; exact lt_irrefl _ h

lemma sdq_mp_first (G : Set T) (i : T) :
    Γ.meanPassage G i = 1 + ∑' j, if j ∈ G then 0 else Γ.P i j * Γ.meanPassage G j := by
  have := sdq_first_step Γ G (fun _ => 1) i
  simp only [mul_one] at this
  exact this

lemma sdq_B (i z : T) (hi : Γ.PosRecurrent i) (h : Γ.LeadsTo i z) : Γ.LeadsTo z i := by
  by_contra hc
  have hz : Γ.meanPassage {i} z = ⊤ := sdq_closed_top Γ {i} {j | ¬ Γ.LeadsTo j i}
    (fun a ha l hP hl => ha (sdq_leads_step Γ a l i hP hl))
    (fun a ha hz => ha (by rw [Set.mem_singleton_iff.1 hz]; exact sdq_leads_refl Γ i)) z hc
  have hzi : z ≠ i := fun e => hc (e ▸ sdq_leads_refl Γ z)
  have key : ∀ s j, 0 < Γ.nStep s j z → Γ.meanPassage {i} j = ⊤ ∨ Γ.meanPassage {i} i = ⊤ := by
    intro s
    induction s with
    | zero =>
      intro j hj
      simp only [MC.nStep] at hj
      split_ifs at hj with e
      · left; rw [e]; exact hz
      · exact absurd hj (lt_irrefl _)
    | succ s ih =>
      intro j hj
      rw [add_comm, sdq_nStep_front] at hj
      obtain ⟨l, hl⟩ : ∃ l, Γ.P j l * Γ.nStep s l z ≠ 0 := by
        by_contra hne
        push Not at hne
        rw [ENNReal.tsum_eq_zero.2 hne] at hj
        exact lt_irrefl _ hj
      have hP : Γ.P j l ≠ 0 := left_ne_zero_of_mul hl
      have hn : 0 < Γ.nStep s l z := pos_iff_ne_zero.2 (right_ne_zero_of_mul hl)
      rcases ih l hn with h1 | h1
      · by_cases hli : l = i
        · right; rw [hli] at h1; exact h1
        · left
          rw [sdq_mp_first]
          refine top_le_iff.1 (le_trans ?_ le_add_self)
          refine le_trans ?_ (ENNReal.le_tsum l)
          rw [if_neg (by simpa using hli), h1, ENNReal.mul_top hP]
      · right; exact h1
  obtain ⟨s, hs⟩ := h
  rcases key s i hs with h1 | h1 <;> exact absurd h1 (ne_of_lt hi)

lemma sdq_unichain (z : T) (h : ∀ i, Γ.meanPassage {z} i < ⊤) : Γ.IsUnichainWith z := by
  refine ⟨Γ.commClass z, ⟨z, h z, rfl⟩, ⟨sdq_leads_refl Γ z, sdq_leads_refl Γ z⟩, ?_⟩
  rintro R' ⟨i, hi, rfl⟩
  have h1 : Γ.LeadsTo i z := sdq_A Γ z i (h i)
  have h2 : Γ.LeadsTo z i := sdq_B Γ i z hi h1
  ext j
  simp only [MC.commClass, MC.Communicate, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨sdq_leads_trans Γ _ _ _ h2 a, sdq_leads_trans Γ _ _ _ b h1⟩
  · rintro ⟨a, b⟩
    exact ⟨sdq_leads_trans Γ _ _ _ h1 a, sdq_leads_trans Γ _ _ _ b h2⟩

lemma sdp_squeeze (u : ℕ → ℝ≥0∞) (x : ℝ≥0∞) (h1 : x ≤ liminf u atTop)
    (h2 : ∀ᶠ N in atTop, u N ≤ x) : Tendsto u atTop (𝓝 x) := by
  refine tendsto_order.2 ⟨fun b hb => eventually_lt_of_lt_liminf (lt_of_lt_of_le hb h1), ?_⟩
  intro b hb
  filter_upwards [h2] with N hN
  exact lt_of_le_of_lt hN hb

lemma sdp_drift {S : Type*} {Γ : MC S} (AS : ApproxSeq Γ) (q : ℕ → S → S → S → ℝ≥0∞)
    (hq : AS.IsATASWith q) (z : S) (m w : S → ℝ≥0∞) (N : ℕ) (hN : AS.N₀ ≤ N)
    (hzN : z ∈ AS.SN N) (i : S) (hi : i ∈ AS.SN N)
    (hfs : m i = w i + ∑' j, if j ∈ ({z} : Set S) then 0 else Γ.P i j * m j)
    (h37 : ∀ r, r ∉ AS.SN N → ∑ j ∈ (AS.SN N).filter (· ≠ z), q N i r j * m j ≤ m r) :
    w i + ∑' j : AS.SN N, (if j ∈ (Subtype.val ⁻¹' ({z} : Set S) : Set (AS.SN N)) then 0 else
      (AS.chain N hN).P ⟨i, hi⟩ j * m j.1) ≤ m i := by
  rw [hfs]
  refine add_le_add le_rfl ?_
  set F := (AS.SN N).filter (· ≠ z) with hF
  have e1 : ∑' j : AS.SN N, (if j ∈ (Subtype.val ⁻¹' ({z} : Set S) : Set (AS.SN N)) then 0 else
      (AS.chain N hN).P ⟨i, hi⟩ j * m j.1) = ∑ j ∈ F, AS.PN N i j * m j := by
    rw [hF, Finset.sum_filter]
    rw [← Finset.tsum_subtype (AS.SN N) (fun j => if j ≠ z then AS.PN N i j * m j else 0)]
    refine tsum_congr fun j => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ne_eq]
    split_ifs <;> simp [ApproxSeq.chain]
  rw [e1]
  have e2 : ∑ j ∈ F, AS.PN N i j * m j = ∑ j ∈ F, Γ.P i j * m j +
      ∑' r : {r : S // r ∉ AS.SN N}, Γ.P i r.1 * ∑ j ∈ F, q N i r.1 j * m j := by
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [hq.2 N hN i hi j (Finset.mem_filter.1 hj).1])]
    simp only [add_mul, Finset.sum_add_distrib]
    congr 1
    simp only [← ENNReal.tsum_mul_right]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine tsum_congr fun r => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc]
  rw [e2]
  have e3 : ∑ j ∈ F, Γ.P i j * m j = ∑' j, if j ∈ F then Γ.P i j * m j else 0 := by
    rw [tsum_eq_sum (s := F) (fun b hb => by simp [hb])]
    exact Finset.sum_congr rfl fun j hj => by simp [hj]
  have e4 : ∑' r : {r : S // r ∉ AS.SN N}, Γ.P i r.1 * m r.1 =
      ∑' j, if j ∉ AS.SN N then Γ.P i j * m j else 0 := by
    rw [← tsum_subtype_eq_of_support_subset (s := {r : S | r ∉ AS.SN N})]
    · exact tsum_congr fun r => by rw [if_pos r.2]
    · intro j hj
      by_contra hc
      exact hj (by simp only [Set.mem_setOf_eq, not_not] at hc; simp [hc])
  calc ∑ j ∈ F, Γ.P i j * m j + ∑' r : {r : S // r ∉ AS.SN N}, Γ.P i r.1 * ∑ j ∈ F, q N i r.1 j * m j
      ≤ ∑ j ∈ F, Γ.P i j * m j + ∑' r : {r : S // r ∉ AS.SN N}, Γ.P i r.1 * m r.1 :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum fun r => mul_le_mul_right (h37 r.1 r.2) _)
    _ = ∑' j, ((if j ∈ F then Γ.P i j * m j else 0) +
          (if j ∉ AS.SN N then Γ.P i j * m j else 0)) := by
        rw [e3, e4, ENNReal.tsum_add]
    _ ≤ _ := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        by_cases hjz : j = z
        · subst hjz; simp [hF, hzN]
        · by_cases hjS : j ∈ AS.SN N
          · simp [hF, hjS, hjz]
          · simp [hF, hjS, hjz]

end gen

lemma sdp_mp_liminf {S : Type*} {Γ : MC S} (AS : ApproxSeq Γ) (G : Set S) (i : S) :
    Γ.meanPassage G i ≤ liminf (fun N => AS.meanPassageN G N i) atTop := by
  have := sdp_double_liminf AS G i (fun _ => 1) (fun _ => ENNReal.one_ne_top)
  simp only [mul_one] at this
  unfold MC.meanPassage
  simp only [sdp_meanPassageN_eq, mul_one]
  exact this

lemma sdp_pc_liminf {S : Type*} {Γ : MC S} (AS : ApproxSeq Γ) (G : Set S) (i : S) :
    Γ.passageCost G i ≤ liminf (fun N => AS.passageCostN G N i) atTop := by
  unfold MC.passageCost
  simp only [sdp_passageCostN_eq]
  exact sdp_double_liminf AS _ i _ (fun _ => ENNReal.coe_ne_top)

theorem atas_structural_conforming_core {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (z : S) (hz : Γ.IsZStandard z)
    (AS : ApproxSeq Γ) (q : ℕ → S → S → S → ℝ≥0∞) (hq : AS.IsATASWith q) (Nstar : ℕ)
    (h37 : ∀ N, Nstar ≤ N → AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ r, r ∉ AS.SN N →
      ∑ j ∈ (AS.SN N).filter (· ≠ z), q N i r j * Γ.meanPassage {z} j ≤ Γ.meanPassage {z} r)
    (h38 : ∀ N, Nstar ≤ N → AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ r, r ∉ AS.SN N →
      ∑ j ∈ (AS.SN N).filter (· ≠ z), q N i r j * Γ.passageCost {z} j ≤ Γ.passageCost {z} r) :
    AS.IsConforming z := by
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (sdp_ev_mem AS z)
  have hbound : ∀ N, max Nstar N1 ≤ N → ∀ (h : AS.N₀ ≤ N ∧ z ∈ AS.SN N) (i' : AS.SN N),
      (AS.chain N h.1).meanPassage (Subtype.val ⁻¹' {z}) i' ≤ Γ.meanPassage {z} i'.1 ∧
      (AS.chain N h.1).passageCost (Subtype.val ⁻¹' {z}) i' ≤ Γ.passageCost {z} i'.1 := by
    intro N hN h i'
    have hNs : Nstar ≤ N := le_trans (le_max_left _ _) hN
    constructor
    · have := sdq_compare (AS.chain N h.1) (Subtype.val ⁻¹' {z}) (fun _ => 1)
        (fun j => Γ.meanPassage {z} j.1)
        (fun i'' => sdp_drift AS q hq z (fun j => Γ.meanPassage {z} j) (fun _ => 1) N h.1 h.2
          i''.1 i''.2 (sdq_mp_first Γ {z} i''.1) (h37 N hNs h.1 i''.1 i''.2)) i'
      simpa [MC.meanPassage] using this
    · have := sdq_compare (AS.chain N h.1) (Subtype.val ⁻¹' {z}) (fun j => (Γ.C j.1 : ℝ≥0∞))
        (fun j => Γ.passageCost {z} j.1)
        (fun i'' => sdp_drift AS q hq z (fun j => Γ.passageCost {z} j)
          (fun j => (Γ.C j : ℝ≥0∞)) N h.1 h.2
          i''.1 i''.2 (sdq_first_step Γ {z} _ i''.1) (h38 N hNs h.1 i''.1 i''.2)) i'
      exact this
  refine ⟨hz, ⟨max Nstar N1, fun N hN => ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · have h := hN1 N (le_trans (le_max_right _ _) hN)
    refine ⟨h, sdq_unichain _ _ (fun i' => ?_)⟩
    have hs : ({⟨z, h.2⟩} : Set (AS.SN N)) = Subtype.val ⁻¹' {z} := by
      ext x; simp [Subtype.ext_iff]
    rw [hs]
    exact lt_of_le_of_lt (hbound N hN h i').1 (hz i'.1).1
  · apply sdp_squeeze _ _ (sdp_mp_liminf AS _ i)
    filter_upwards [eventually_ge_atTop (max Nstar N1), sdp_ev_mem AS i] with N hN hi
    have h := hN1 N (le_trans (le_max_right _ _) hN)
    unfold ApproxSeq.meanPassageN; rw [dif_pos hi]; exact (hbound N hN h ⟨i, hi.2⟩).1
  · apply sdp_squeeze _ _ (sdp_pc_liminf AS _ i)
    filter_upwards [eventually_ge_atTop (max Nstar N1), sdp_ev_mem AS i] with N hN hi
    have h := hN1 N (le_trans (le_max_right _ _) hN)
    unfold ApproxSeq.passageCostN; rw [dif_pos hi]; exact (hbound N hN h ⟨i, hi.2⟩).2

namespace MKX


/-- Sennott (1999), App. C.1, p. 292: a Markov chain `Γ` on a countable state space `S`, given by
its matrix of transition probabilities `P i j` (the probability that `Γ` moves to `j` during the
next slot when it is in `i`), with `∑_j P_{ij} = 1` for every `i`. -/
structure MC (S : Type*) where
  /-- the transition probability `P_{ij}` -/
  P : S → S → ℝ≥0∞
  /-- every row sums to one -/
  P_sum : ∀ i, ∑' j, P i j = 1

variable {S : Type*} [Countable S]

open Classical in
/-- Sennott (1999), p. 292: the `t`-step transition probability `P^{(t)}_{ij}`, the `ij`th entry of
the product matrix `P^t`, with `P^{(0)}_{ij} = δ_{ij}`. -/
noncomputable def nStep (M : MC S) : ℕ → S → S → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | t + 1, i, j => ∑' k, nStep M t i k * M.P k j

/-- The probability `∏_{s<t} P_{x_s x_{s+1}}` that the chain, started at `x_0`, follows the path
`x_0, x_1, …, x_t` during its first `t` transitions. -/
noncomputable def pathProb (M : MC S) {t : ℕ} (x : Fin (t + 1) → S) : ℝ≥0∞ :=
  ∏ s : Fin t, M.P (x s.castSucc) (x s.succ)

open Classical in
/-- Sennott (1999), p. 295: the taboo probability `_G P^{(t)}_{ik}` of going from `i` to `k` in `t`
slots while avoiding the taboo set `G` at the intermediate times `1, …, t − 1` (the initial state
`i` and the terminal state `k` may lie in `G`). It is the total probability of the paths
`x_0 = i, x_1, …, x_t = k` with `x_s ∉ G` for `0 < s < t`; hence `_G P^{(0)}_{ik} = δ_{ik}` and
`_G P^{(1)}_{ik} = P_{ik}`. -/
noncomputable def taboo (M : MC S) (G : Set S) (t : ℕ) (i k : S) : ℝ≥0∞ :=
  ∑' x : Fin (t + 1) → S,
    if x 0 = i ∧ x (Fin.last t) = k ∧ (∀ s : Fin (t + 1), 0 < s.val → s.val < t → x s ∉ G)
    then pathProb M x else 0

open Classical in
/-- `P(X_t = k, T_{iG} > t | X_0 = i)`: the chain started at `i` is in `k` at time `t` and has not
entered `G` at any of the times `1, …, t` (so the first passage time `T_{iG}` to `G` exceeds `t`).
For `t = 0` it is `δ_{ik}`. -/
noncomputable def avoidProb (M : MC S) (G : Set S) (t : ℕ) (i k : S) : ℝ≥0∞ :=
  ∑' x : Fin (t + 1) → S,
    if x 0 = i ∧ x (Fin.last t) = k ∧ (∀ s : Fin (t + 1), 0 < s.val → x s ∉ G)
    then pathProb M x else 0

/-- Sennott (1999), p. 295: `_G u_{ik}`, the expected number of visits to `k` in a first passage
from `i` to `G`, i.e. `E[#{t : 0 ≤ t < T_{iG}, X_t = k} | X_0 = i]`, where `T_{iG} ≥ 1` is the first
passage time from `i` to `G`. Visits at time `0` are counted and the visit at time `T_{iG}` is not,
which gives the book's conventions `_G u_{ik} = 0` for `k ∈ G`, `i ∉ G` and `_G u_{ik} = δ_{ik}`
for `k ∈ G`, `i ∈ G`. The value is in `[0, ∞]`. -/
noncomputable def visits (M : MC S) (G : Set S) (i k : S) : ℝ≥0∞ :=
  ∑' t : ℕ, avoidProb M G t i k

open Classical in
/-- `P(T_{iG} = t | X_0 = i)`: the law of the first passage time
`T_{iG} = min {t ≥ 1 : X_t ∈ G}` (p. 295). It is `0` for `t = 0` (since `T_{iG} ≥ 1`), and for
`t ≥ 1` it is `∑_{k ∈ G} _G P^{(t)}_{ik}`. -/
noncomputable def firstPassProb (M : MC S) (G : Set S) (i : S) (t : ℕ) : ℝ≥0∞ :=
  if t = 0 then 0 else ∑' k, if k ∈ G then taboo M G t i k else 0

/-- `P(T_{iG} < ∞ | X_0 = i)`, the probability that the chain started at `i` enters `G` at some
time `t ≥ 1`. -/
noncomputable def hitProb (M : MC S) (G : Set S) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, firstPassProb M G i t

open Classical in
/-- Sennott (1999), p. 295: the expected first passage time `m_{iG} = E[T_{iG}]`, computed from the
law of `T_{iG}` as a `[0, ∞]`-valued expectation: `∑_t t · P(T_{iG} = t)` when
`P(T_{iG} < ∞) = 1`, and `∞` when `P(T_{iG} < ∞) < 1` (then `T_{iG} = ∞` with positive
probability). For `G = {j}` this is `m_{ij}`; `m_{ii}` is the expected return time to `i`. -/
noncomputable def meanPassage (M : MC S) (G : Set S) (i : S) : ℝ≥0∞ :=
  if hitProb M G i = 1 then ∑' t : ℕ, (t : ℝ≥0∞) * firstPassProb M G i t else ⊤

/-- Sennott (1999), p. 293: `i` leads to `j` if `P^{(t)}_{ij} > 0` for some `t ≥ 0`. -/
def LeadsTo (M : MC S) (i j : S) : Prop :=
  ∃ t : ℕ, 0 < nStep M t i j

/-- Sennott (1999), p. 293: `i` and `j` communicate if each leads to the other. -/
def Communicate (M : MC S) (i j : S) : Prop :=
  LeadsTo M i j ∧ LeadsTo M j i

/-- The communicating class of `i`: the states that communicate with `i` (p. 293). -/
def commClass (M : MC S) (i : S) : Set S :=
  {j | Communicate M i j}

/-- Sennott (1999), p. 293: `Γ` is irreducible if `S` is a single communicating class. -/
def Irreducible (M : MC S) : Prop :=
  ∀ i j, Communicate M i j

/-- Sennott (1999), p. 293: `i` is transient if the return time `T` to `i` satisfies
`P(T < ∞) < 1`. -/
def Transient (M : MC S) (i : S) : Prop :=
  hitProb M {i} i < 1

/-- Sennott (1999), p. 293: `i` is positive recurrent if `P(T < ∞) = 1` for the return time `T`
to `i` and `m_{ii} = E[T] < ∞`. -/
def PositiveRecurrent (M : MC S) (i : S) : Prop :=
  hitProb M {i} i = 1 ∧ meanPassage M {i} i < ⊤

/-- Sennott (1999), p. 293: `R` is a positive recurrent class: `R` is a communicating class (the
class of one of its states) and every state of `R` is positive recurrent. -/
def IsPosRecClass (M : MC S) (R : Set S) : Prop :=
  (∃ i, R = commClass M i) ∧ ∀ j ∈ R, PositiveRecurrent M j

/-- Sennott (1999), p. 294: the steady state probability `π_j = (m_{jj})^{-1}`, interpreted as `0`
when `m_{jj} = ∞` (the book introduces `π_j` as `lim_n Q^{(n)}_{jj}` and states that it equals
`(m_{jj})^{-1}`). -/
noncomputable def steadyState (M : MC S) (j : S) : ℝ≥0∞ :=
  (meanPassage M {j} j)⁻¹




variable {S : Type*} [Countable S]

open Classical in
/-- Sennott (1999), p. 298: `c_{iG}`, the expected cost of a first passage from `i` to `G`,
`E[∑_{t=0}^{T_{iG}-1} C(X_t) | X_0 = i]`, where each state `k` carries a finite nonnegative cost
`C(k)`. It is computed over the first passage paths `x_0 = i, x_1, …, x_t` (`t ≥ 1`,
`x_1, …, x_{t-1} ∉ G`, `x_t ∈ G`), each weighted by its probability and charged
`C(x_0) + ⋯ + C(x_{t-1})`. The book defines `c_{iG}` only when `m_{iG} < ∞` (then
`T_{iG} < ∞` with probability one and this is the expectation); every result of this development
uses `passageCost` only under that proviso. -/
noncomputable def passageCost (M : MC S) (C : S → ℝ≥0) (G : Set S) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' x : Fin (t + 1) → S,
    if t ≠ 0 ∧ x 0 = i ∧ (∀ s : Fin (t + 1), 0 < s.val → s.val < t → x s ∉ G) ∧
        x (Fin.last t) ∈ G
    then pathProb M x * ∑ s : Fin t, (C (x s.castSucc) : ℝ≥0∞) else 0

/-- Sennott (1999), (C.11), p. 298: `J^{(n)}_i = (1/n) E[∑_{t=0}^{n-1} C(X_t) | X_0 = i]
= ∑_j C(j) Q^{(n)}_{ij}`, the expected cost per unit time in `[0, n − 1]` from `i`, in `[0, ∞]`
(meaningful for `n ≥ 1`). -/
noncomputable def avgCostN (M : MC S) (C : S → ℝ≥0) (n : ℕ) (i : S) : ℝ≥0∞ :=
  (∑ t ∈ Finset.range n, ∑' j, nStep M t i j * (C j : ℝ≥0∞)) / (n : ℝ≥0∞)

/-- Sennott (1999), Proposition C.2.1(i), p. 298: the average cost on a positive recurrent class
`R`, `J_R = ∑_{j ∈ R} π_j C(j)`, a finite or infinite constant. -/
noncomputable def classAvgCost (M : MC S) (C : S → ℝ≥0) (R : Set S) : ℝ≥0∞ :=
  ∑' j : R, steadyState M j * (C j : ℝ≥0∞)

/-- Sennott (1999), Definition C.2.5, p. 301: the Markov chain with costs is `z` standard if
`m_{iz} < ∞` and `c_{iz} < ∞` for all `i ∈ S` (including `i = z`: the expected return time to `z`
and the expected cost of a return to `z` are finite). -/
def IsZStandard (M : MC S) (C : S → ℝ≥0) (z : S) : Prop :=
  ∀ i, meanPassage M {z} i < ⊤ ∧ passageCost M C {z} i < ⊤




set_option linter.unusedSectionVars false
variable {S : Type*} [Countable S]

lemma tsum_snoc {t : ℕ} (f : (Fin (t+2) → S) → ℝ≥0∞) :
    ∑' y, f y = ∑' x : Fin (t+1) → S, ∑' k : S, f (Fin.snoc x k) := by
  calc ∑' y, f y = ∑' c : S × (Fin (t+1) → S), f (Fin.snoc c.2 c.1) :=
        ((Fin.snocEquiv (fun _ => S)).tsum_eq f).symm
    _ = ∑' k : S, ∑' x : Fin (t+1) → S, f (Fin.snoc x k) :=
        ENNReal.tsum_prod (f := fun a b => f (Fin.snoc b a))
    _ = _ := ENNReal.tsum_comm

lemma tsum_cons {t : ℕ} (f : (Fin (t+2) → S) → ℝ≥0∞) :
    ∑' y, f y = ∑' j : S, ∑' x : Fin (t+1) → S, f (Fin.cons j x) := by
  calc ∑' y, f y = ∑' c : S × (Fin (t+1) → S), f (Fin.cons c.1 c.2) :=
        ((Fin.consEquiv (fun _ => S)).tsum_eq f).symm
    _ = _ := ENNReal.tsum_prod (f := fun a b => f (Fin.cons a b))

lemma pathProb_snoc (M : MC S) {t : ℕ} (x : Fin (t+1) → S) (k : S) :
    pathProb M (Fin.snoc x k : Fin (t+2) → S) = pathProb M x * M.P (x (Fin.last t)) k := by
  unfold pathProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl; intro s _
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]

lemma pathProb_cons (M : MC S) {t : ℕ} (x : Fin (t+1) → S) (i : S) :
    pathProb M (Fin.cons i x : Fin (t+2) → S) = M.P i (x 0) * pathProb M x := by
  unfold pathProb
  rw [Fin.prod_univ_succ]
  simp


lemma snoc_zero' {t : ℕ} (x : Fin (t+1) → S) (k : S) :
    (Fin.snoc x k : Fin (t+2) → S) 0 = x 0 := by
  have : (0 : Fin (t+2)) = Fin.castSucc 0 := rfl
  rw [this, Fin.snoc_castSucc]

lemma forall_snoc_iff {t : ℕ} (x : Fin (t+1) → S) (k : S) (Q : S → Prop) (lo : ℕ) :
    (∀ s : Fin (t+2), lo < s.val → s.val < t + 1 → Q ((Fin.snoc x k : Fin (t+2) → S) s)) ↔
    (∀ s : Fin (t+1), lo < s.val → Q (x s)) := by
  rw [Fin.forall_fin_succ']
  simp only [Fin.val_castSucc, Fin.snoc_castSucc, Fin.val_last, lt_irrefl]
  constructor
  · intro h s h1; exact h.1 s h1 s.isLt
  · intro h; exact ⟨fun s h1 _ => h s h1, fun _ h => h.elim⟩

lemma forall_snoc_iff' {t : ℕ} (x : Fin (t+1) → S) (k : S) (Q : S → Prop) (lo : ℕ) (hlo : lo < t + 1) :
    (∀ s : Fin (t+2), lo < s.val → Q ((Fin.snoc x k : Fin (t+2) → S) s)) ↔
    (∀ s : Fin (t+1), lo < s.val → Q (x s)) ∧ Q k := by
  rw [Fin.forall_fin_succ']
  simp only [Fin.val_castSucc, Fin.snoc_castSucc, Fin.val_last, Fin.snoc_last]
  constructor
  · intro h; exact ⟨h.1, h.2 hlo⟩
  · intro h; exact ⟨h.1, fun _ => h.2⟩

open Classical in
lemma avoid_succ_last (M : MC S) (G : Set S) (t : ℕ) (i k : S) :
    avoidProb M G (t+1) i k = if k ∈ G then 0 else ∑' l, avoidProb M G t i l * M.P l k := by
  unfold avoidProb
  rw [tsum_snoc]
  have hL : ∀ x : Fin (t+1) → S, (∑' k' : S,
      (if (Fin.snoc x k' : Fin (t+2) → S) 0 = i ∧ (Fin.snoc x k' : Fin (t+2) → S) (Fin.last (t+1)) = k ∧
        ∀ s : Fin (t + 1 + 1), 0 < s.val → (Fin.snoc x k' : Fin (t+2) → S) s ∉ G
      then pathProb M (Fin.snoc x k' : Fin (t+2) → S) else 0)) =
      if k ∈ G then 0 else (if x 0 = i ∧ ∀ s : Fin (t + 1), 0 < s.val → x s ∉ G then
        pathProb M x * M.P (x (Fin.last t)) k else 0) := by
    intro x
    rw [tsum_eq_single k]
    · simp only [snoc_zero', Fin.snoc_last, forall_snoc_iff' x k (· ∉ G) 0 (by omega), pathProb_snoc]
      by_cases hk : k ∈ G <;> simp [hk]
    · intro k' hk'
      rw [Fin.snoc_last]; simp [hk']
  simp_rw [hL]
  by_cases hk : k ∈ G
  · simp [hk]
  simp only [hk, if_false]
  simp_rw [← ENNReal.tsum_mul_right, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  congr 1; ext x
  rw [tsum_eq_single (x (Fin.last t))]
  · by_cases h : x 0 = i ∧ ∀ s : Fin (t + 1), 0 < s.val → x s ∉ G
    · simp [h]
    · simp only [h, if_false]; rw [if_neg]; tauto
  · intro l hl; rw [if_neg]; intro h; exact hl h.2.1.symm

open Classical in
lemma avoid_zero (M : MC S) (G : Set S) (i k : S) :
    avoidProb M G 0 i k = if i = k then 1 else 0 := by
  unfold avoidProb
  rw [tsum_eq_single (fun _ => i)]
  · by_cases h : i = k
    · subst h; simp [pathProb]
    · simp [h]
  · intro x hx
    rw [if_neg]
    rintro ⟨h0, -, -⟩
    apply hx; funext s; rw [show s = 0 from Fin.ext (by have := s.isLt; omega), h0]

open Classical in
lemma taboo_succ_last (M : MC S) (G : Set S) (t : ℕ) (i k : S) :
    taboo M G (t+1) i k = ∑' l, avoidProb M G t i l * M.P l k := by
  unfold taboo avoidProb
  rw [tsum_snoc]
  have hL : ∀ x : Fin (t+1) → S, (∑' k' : S,
      (if (Fin.snoc x k' : Fin (t+2) → S) 0 = i ∧ (Fin.snoc x k' : Fin (t+2) → S) (Fin.last (t+1)) = k ∧
        ∀ s : Fin (t + 1 + 1), 0 < s.val → s.val < t + 1 → (Fin.snoc x k' : Fin (t+2) → S) s ∉ G
      then pathProb M (Fin.snoc x k' : Fin (t+2) → S) else 0)) =
      (if x 0 = i ∧ ∀ s : Fin (t + 1), 0 < s.val → x s ∉ G then
        pathProb M x * M.P (x (Fin.last t)) k else 0) := by
    intro x
    rw [tsum_eq_single k]
    · simp only [snoc_zero', Fin.snoc_last, forall_snoc_iff x k (· ∉ G) 0, pathProb_snoc]
      simp
    · intro k' hk'
      rw [Fin.snoc_last]; simp [hk']
  simp_rw [hL]
  simp_rw [← ENNReal.tsum_mul_right, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  congr 1; ext x
  rw [tsum_eq_single (x (Fin.last t))]
  · by_cases h : x 0 = i ∧ ∀ s : Fin (t + 1), 0 < s.val → x s ∉ G
    · simp [h]
    · simp only [h, if_false]; rw [if_neg]; tauto
  · intro l hl; rw [if_neg]; intro h; exact hl h.2.1.symm

lemma cons_last' {t : ℕ} (x : Fin (t+1) → S) (j : S) :
    (Fin.cons j x : Fin (t+2) → S) (Fin.last (t+1)) = x (Fin.last t) := by
  rw [← Fin.succ_last, Fin.cons_succ]

lemma forall_cons_iff {t : ℕ} (x : Fin (t+1) → S) (j : S) (Q : S → Prop) :
    (∀ s : Fin (t+2), 0 < s.val → Q ((Fin.cons j x : Fin (t+2) → S) s)) ↔
    Q (x 0) ∧ (∀ s : Fin (t+1), 0 < s.val → Q (x s)) := by
  rw [Fin.forall_fin_succ]
  simp only [Fin.val_zero, lt_irrefl, Fin.val_succ, Fin.cons_succ, IsEmpty.forall_iff, true_and,
    Nat.succ_pos, forall_const]
  constructor
  · intro h; exact ⟨h 0, fun s _ => h s⟩
  · intro h s
    rcases Nat.eq_zero_or_pos s.val with hs | hs
    · have : s = 0 := Fin.ext hs
      subst this; exact h.1
    · exact h.2 s hs

open Classical in
lemma avoid_succ_first (M : MC S) (G : Set S) (t : ℕ) (i k : S) :
    avoidProb M G (t+1) i k = ∑' j, if j ∈ G then 0 else M.P i j * avoidProb M G t j k := by
  unfold avoidProb
  rw [tsum_cons]
  rw [tsum_eq_single i]
  · have hL : ∀ x : Fin (t+1) → S,
        (if (Fin.cons i x : Fin (t+2) → S) 0 = i ∧ (Fin.cons i x : Fin (t+2) → S) (Fin.last (t+1)) = k ∧
          ∀ s : Fin (t + 1 + 1), 0 < s.val → (Fin.cons i x : Fin (t+2) → S) s ∉ G
        then pathProb M (Fin.cons i x : Fin (t+2) → S) else 0) =
        ∑' j, (if j ∈ G then 0 else (if x 0 = j ∧ x (Fin.last t) = k ∧
          ∀ s : Fin (t + 1), 0 < s.val → x s ∉ G then M.P i j * pathProb M x else 0)) := by
      intro x
      rw [tsum_eq_single (x 0)]
      · simp only [Fin.cons_zero, cons_last', forall_cons_iff x i (· ∉ G), pathProb_cons, true_and]
        by_cases h0 : x 0 ∈ G
        · simp [h0]
        · simp [h0]
      · intro j hj; simp [Ne.symm hj]
    simp_rw [hL]
    rw [ENNReal.tsum_comm]
    congr 1; ext j
    by_cases hj : j ∈ G
    · simp [hj]
    · simp only [hj, if_false]
      rw [← ENNReal.tsum_mul_left]
      congr 1; ext x
      split_ifs <;> simp
  · intro j hj
    apply ENNReal.tsum_eq_zero.2
    intro x; rw [Fin.cons_zero, if_neg]; tauto

open Classical in
lemma taboo_zero (M : MC S) (G : Set S) (i k : S) :
    taboo M G 0 i k = if i = k then 1 else 0 := by
  unfold taboo
  rw [tsum_eq_single (fun _ => i)]
  · by_cases h : i = k
    · subst h; simp [pathProb]
    · simp [h]
  · intro x hx
    rw [if_neg]
    rintro ⟨h0, -, -⟩
    apply hx; funext s; rw [show s = 0 from Fin.ext (by have := s.isLt; omega), h0]

lemma avoid_le_nStep (M : MC S) (G : Set S) (t : ℕ) (i k : S) :
    avoidProb M G t i k ≤ nStep M t i k := by
  induction t generalizing k with
  | zero => rw [avoid_zero]; simp [nStep]
  | succ t ih =>
    rw [avoid_succ_last]
    split_ifs
    · simp
    · simp only [nStep]
      exact ENNReal.tsum_le_tsum fun l => by gcongr; exact ih l

lemma taboo_le_nStep (M : MC S) (G : Set S) (t : ℕ) (i k : S) :
    taboo M G t i k ≤ nStep M t i k := by
  cases t with
  | zero => rw [taboo_zero]; simp [nStep]
  | succ t =>
    rw [taboo_succ_last]; simp only [nStep]
    exact ENNReal.tsum_le_tsum fun l => by gcongr; exact avoid_le_nStep M G t i l

open Classical in
/-- probability of jumping into `G` in one step -/
noncomputable def toG (M : MC S) (G : Set S) (l : S) : ℝ≥0∞ :=
  ∑' k, if k ∈ G then M.P l k else 0

open Classical in
lemma fp_succ (M : MC S) (G : Set S) (i : S) (t : ℕ) :
    firstPassProb M G i (t+1) = ∑' l, avoidProb M G t i l * toG M G l := by
  unfold firstPassProb toG
  simp only [Nat.add_one_ne_zero, if_false, taboo_succ_last]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  congr 1; ext k
  split_ifs <;> simp

lemma fp_zero (M : MC S) (G : Set S) (i : S) : firstPassProb M G i 0 = 0 := by
  simp [firstPassProb]

/-- `P(T > t)` -/
noncomputable def survive (M : MC S) (G : Set S) (t : ℕ) (i : S) : ℝ≥0∞ :=
  ∑' k, avoidProb M G t i k

lemma survive_zero (M : MC S) (G : Set S) (i : S) : survive M G 0 i = 1 := by
  unfold survive
  simp_rw [avoid_zero]
  rw [tsum_eq_single i (by intro b hb; simp [Ne.symm hb])]; simp

open Classical in
lemma survive_succ (M : MC S) (G : Set S) (t : ℕ) (i : S) :
    survive M G (t+1) i + firstPassProb M G i (t+1) = survive M G t i := by
  unfold survive
  rw [fp_succ]
  unfold toG
  simp_rw [avoid_succ_last]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm (f := fun l k => avoidProb M G t i l * if k ∈ G then M.P l k else 0),
    ← ENNReal.tsum_add]
  have : ∀ k, ((if k ∈ G then 0 else ∑' l, avoidProb M G t i l * M.P l k) +
      ∑' l, avoidProb M G t i l * if k ∈ G then M.P l k else 0) =
      ∑' l, avoidProb M G t i l * M.P l k := by
    intro k; split_ifs <;> simp
  simp_rw [this]
  rw [ENNReal.tsum_comm]
  congr 1; ext l
  rw [ENNReal.tsum_mul_left, M.P_sum, mul_one]

lemma survive_add_sum (M : MC S) (G : Set S) (i : S) (n : ℕ) :
    survive M G n i + ∑ t ∈ Finset.range (n+1), firstPassProb M G i t = 1 := by
  induction n with
  | zero => simp [survive_zero, fp_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, add_comm _ (firstPassProb M G i (n+1)), ← add_assoc,
      add_comm (firstPassProb M G i (n+1)), survive_succ, ih]

lemma hitProb_le_one (M : MC S) (G : Set S) (i : S) : hitProb M G i ≤ 1 := by
  unfold hitProb
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  calc ∑ t ∈ Finset.range n, firstPassProb M G i t
      ≤ ∑ t ∈ Finset.range (n+1), firstPassProb M G i t :=
        Finset.sum_le_sum_of_subset (by simp)
    _ ≤ survive M G n i + ∑ t ∈ Finset.range (n+1), firstPassProb M G i t := le_add_self
    _ = 1 := survive_add_sum M G i n

lemma hit_eq_one_of_summable (M : MC S) (G : Set S) (i : S)
    (h : ∑' t, survive M G t i ≠ ⊤) : hitProb M G i = 1 := by
  apply le_antisymm (hitProb_le_one M G i)
  have ht := ENNReal.tendsto_atTop_zero_of_tsum_ne_top h
  have key : ∀ n, 1 ≤ survive M G n i + hitProb M G i := by
    intro n
    rw [← survive_add_sum M G i n]
    gcongr
    exact ENNReal.sum_le_tsum _
  have hlim : Tendsto (fun n => survive M G n i + hitProb M G i) atTop (𝓝 (0 + hitProb M G i)) :=
    ht.add tendsto_const_nhds
  rw [zero_add] at hlim
  exact ge_of_tendsto' hlim key

lemma survive_eq_tail (M : MC S) (G : Set S) (i : S) (h : hitProb M G i = 1) (s : ℕ) :
    survive M G s i = ∑' t, firstPassProb M G i (t + (s+1)) := by
  have h1 := survive_add_sum M G i s
  have h2 : ∑ t ∈ Finset.range (s+1), firstPassProb M G i t +
      ∑' t, firstPassProb M G i (t + (s+1)) = 1 := by
    rw [ENNReal.summable.sum_add_tsum_nat_add']
    exact h
  have hfin : ∑ t ∈ Finset.range (s+1), firstPassProb M G i t ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    rw [← h1]; exact le_add_self
  rw [add_comm] at h1
  rw [← h2] at h1
  exact (ENNReal.add_right_inj hfin).1 h1

lemma meanPassage_eq_survive (M : MC S) (G : Set S) (i : S) :
    meanPassage M G i = ∑' t, survive M G t i := by
  unfold meanPassage
  split_ifs with h
  · have e1 : ∀ t : ℕ, (t : ℝ≥0∞) * firstPassProb M G i t =
        ∑' s : ℕ, if s < t then firstPassProb M G i t else 0 := by
      intro t
      rw [tsum_eq_sum (s := Finset.range t)]
      · rw [Finset.sum_ite_of_true (fun s hs => Finset.mem_range.1 hs)]
        simp
      · intro s hs; rw [if_neg]; simpa using hs
    simp_rw [e1]
    rw [ENNReal.tsum_comm]
    congr 1; ext s
    rw [survive_eq_tail M G i h s]
    rw [← ENNReal.summable.sum_add_tsum_nat_add' (k := s+1)]
    · rw [Finset.sum_eq_zero]
      · simp only [zero_add]
        congr 1; ext t; rw [if_pos (by omega)]
      · intro x hx; rw [if_neg]; simp at hx; omega
  · by_contra hne
    exact h (hit_eq_one_of_summable M G i (Ne.symm hne))

lemma visits_sum (M : MC S) (G : Set S) (i : S) :
    ∑' k, visits M G i k = meanPassage M G i := by
  rw [meanPassage_eq_survive]
  unfold visits survive
  exact ENNReal.tsum_comm

lemma hitProb_succ (M : MC S) (G : Set S) (i : S) :
    hitProb M G i = ∑' t, firstPassProb M G i (t+1) := by
  unfold hitProb
  rw [tsum_eq_zero_add' ENNReal.summable, fp_zero, zero_add]

open Classical in
lemma hit_first_step (M : MC S) (G : Set S) (i : S) :
    hitProb M G i = ∑' j, M.P i j * (if j ∈ G then 1 else hitProb M G j) := by
  rw [hitProb_succ, tsum_eq_zero_add' ENNReal.summable]
  have h0 : firstPassProb M G i (0+1) = ∑' j, if j ∈ G then M.P i j else 0 := by
    rw [fp_succ]; simp_rw [avoid_zero]
    rw [tsum_eq_single i (by intro b hb; simp [Ne.symm hb])]; simp [toG]
  have h1 : ∀ t, firstPassProb M G i (t+1+1) =
      ∑' j, if j ∈ G then 0 else M.P i j * firstPassProb M G j (t+1) := by
    intro t
    rw [fp_succ]; simp_rw [avoid_succ_first, fp_succ]
    simp_rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    congr 1; ext j
    split_ifs
    · simp
    · simp_rw [← ENNReal.tsum_mul_left, mul_assoc]
  rw [h0]
  simp_rw [h1]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_add]
  congr 1; ext j
  split_ifs
  · simp
  · simp only [zero_add]
    rw [ENNReal.tsum_mul_left, hitProb_succ]

open Classical in
lemma hit_zero_of_not_leads (M : MC S) (G : Set S) (k : S)
    (h : ∀ g ∈ G, ¬ LeadsTo M k g) : hitProb M G k = 0 := by
  unfold hitProb
  apply ENNReal.tsum_eq_zero.2
  intro t
  unfold firstPassProb
  split_ifs
  · rfl
  apply ENNReal.tsum_eq_zero.2
  intro g
  split_ifs with hg
  · apply le_antisymm _ (zero_le)
    have := taboo_le_nStep M G t k g
    have h2 : nStep M t k g = 0 := by
      by_contra hne; exact h g hg ⟨t, pos_iff_ne_zero.2 hne⟩
    rw [h2] at this; exact this
  · rfl

lemma leadsTo_refl (M : MC S) (i : S) : LeadsTo M i i := ⟨0, by simp [nStep]⟩

lemma exists_pos_of_tsum_pos {α : Type*} {f : α → ℝ≥0∞} (h : 0 < ∑' l, f l) : ∃ l, 0 < f l := by
  by_contra hn
  push_neg at hn
  have : ∑' l, f l = 0 := ENNReal.tsum_eq_zero.2 fun l => le_antisymm (hn l) (zero_le)
  rw [this] at h; exact lt_irrefl _ h

lemma nStep_succ_pos (M : MC S) {t : ℕ} {a b c : S} (h1 : 0 < nStep M t a b) (h2 : 0 < M.P b c) :
    0 < nStep M (t+1) a c := by
  simp only [nStep]
  exact lt_of_lt_of_le (ENNReal.mul_pos h1.ne' h2.ne') (ENNReal.le_tsum b)

lemma leadsTo_trans (M : MC S) {a b c : S} (h1 : LeadsTo M a b) (h2 : LeadsTo M b c) :
    LeadsTo M a c := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  induction t generalizing c with
  | zero =>
    simp only [nStep] at ht
    split_ifs at ht with h
    · subst h; exact ⟨s, hs⟩
    · exact absurd ht (lt_irrefl _)
  | succ t ih =>
    simp only [nStep] at ht
    obtain ⟨m, hm⟩ := exists_pos_of_tsum_pos ht
    have hm1 : 0 < nStep M t b m := pos_iff_ne_zero.2 (left_ne_zero_of_mul hm.ne')
    have hm2 : 0 < M.P m c := pos_iff_ne_zero.2 (right_ne_zero_of_mul hm.ne')
    obtain ⟨u, hu⟩ := ih hm1
    exact ⟨u+1, nStep_succ_pos M hu hm2⟩

lemma leadsTo_of_P (M : MC S) {a b : S} (h : 0 < M.P a b) : LeadsTo M a b :=
  ⟨1, nStep_succ_pos (t := 0) M (by simp [nStep]) h⟩

open Classical in
lemma close_step (M : MC S) (i k : S) (hi : hitProb M {i} i = 1) (hk : 0 < M.P i k) :
    LeadsTo M k i := by
  by_contra hn
  have hki : k ≠ i := by rintro rfl; exact hn (leadsTo_refl M k)
  have h0 : hitProb M {i} k = 0 :=
    hit_zero_of_not_leads M {i} k (by intro g hg; rw [Set.mem_singleton_iff] at hg; subst hg; exact hn)
  have hfs := hit_first_step M {i} i
  rw [hi] at hfs
  have key : (1 : ℝ≥0∞) + M.P i k ≤ 1 + 0 := by
    rw [add_zero]
    nth_rewrite 2 [← M.P_sum i]
    nth_rewrite 1 [hfs]
    have : M.P i k = ∑' j, M.P i j * (if j = k then 1 else 0) := by
      rw [tsum_eq_single k (by intro b hb; simp [hb])]; simp
    rw [this, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro j
    rw [← mul_add]
    apply mul_le_of_le_one_right (zero_le)
    by_cases hj : j = k
    · subst hj; simp [hki, h0]
    · simp only [hj, if_false, add_zero]
      split_ifs
      · exact le_rfl
      · exact hitProb_le_one M {i} j
  have := (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 key
  exact absurd (le_antisymm this (zero_le)) hk.ne'

lemma avoid_succ_self (M : MC S) (i : S) (t : ℕ) : avoidProb M {i} (t+1) i i = 0 := by
  rw [avoid_succ_last]; simp

lemma visits_eq_succ (M : MC S) (G : Set S) (i k : S) :
    visits M G i k = avoidProb M G 0 i k + ∑' t, avoidProb M G (t+1) i k := by
  unfold visits; rw [tsum_eq_zero_add' ENNReal.summable]

lemma visits_self (M : MC S) (i : S) : visits M {i} i i = 1 := by
  rw [visits_eq_succ]; simp [avoid_succ_self, avoid_zero]

lemma visits_ne (M : MC S) (G : Set S) {i k : S} (h : i ≠ k) :
    visits M G i k = ∑' t, avoidProb M G (t+1) i k := by
  rw [visits_eq_succ, avoid_zero]; simp [h]

lemma u_invariant (M : MC S) (i : S) (hi : hitProb M {i} i = 1) (k : S) :
    visits M {i} i k = ∑' l, visits M {i} i l * M.P l k := by
  unfold visits
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [← taboo_succ_last]
  by_cases hk : k = i
  · subst hk
    rw [← visits.eq_def, visits_self, ← hi, hitProb_succ]
    congr 1; ext t
    unfold firstPassProb
    simp only [Nat.add_one_ne_zero, if_false, Set.mem_singleton_iff]
    rw [tsum_eq_single k (by intro b hb; simp [hb])]; simp
  · rw [← visits.eq_def, visits_ne M _ (Ne.symm hk)]
    congr 1; ext t
    rw [taboo_succ_last, avoid_succ_last]; simp [hk]

lemma iterate_inv (M : MC S) (x : S → ℝ≥0∞) (hx : ∀ k, x k = ∑' l, x l * M.P l k) (t : ℕ) (k : S) :
    ∑' l, x l * nStep M t l k = x k := by
  induction t generalizing k with
  | zero =>
    simp only [nStep]
    rw [tsum_eq_single k (by intro b hb; simp [hb])]; simp
  | succ t ih =>
    simp only [nStep]
    simp_rw [← ENNReal.tsum_mul_left, ← mul_assoc]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_right, ih]
    exact (hx k).symm

lemma inv_le_of_lead (M : MC S) (x : S → ℝ≥0∞) (hx : ∀ k, x k = ∑' l, x l * M.P l k) {j i : S}
    (h : LeadsTo M j i) (hz : x i = 0) : x j = 0 := by
  obtain ⟨t, ht⟩ := h
  have := iterate_inv M x hx t i
  rw [hz] at this
  have h2 : x j * nStep M t j i = 0 := le_antisymm (this ▸ ENNReal.le_tsum j) zero_le
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd h3 ht.ne'

lemma U_ge (M : MC S) (i : S) (x : S → ℝ≥0∞) (hx : ∀ k, x k = ∑' l, x l * M.P l k)
    (hxi : x i = 1) (k : S) : visits M {i} i k ≤ x k := by
  by_cases hk : k = i
  · subst hk; rw [visits_self, hxi]
  rw [visits_ne M _ (Ne.symm hk)]
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    by_cases hk' : k = i
    · subst hk'; simp [avoid_succ_self]
    have e : ∀ t, avoidProb M {i} (t+1) i k = ∑' l, avoidProb M {i} t i l * M.P l k := by
      intro t; rw [avoid_succ_last]; simp [hk']
    simp_rw [e]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    rw [hx k]
    apply ENNReal.tsum_le_tsum
    intro l
    rw [← Finset.sum_mul]
    gcongr
    rw [Finset.sum_range_succ']
    by_cases hl : l = i
    · subst hl; simp [avoid_succ_self, avoid_zero, hxi]
    · rw [avoid_zero, if_neg (Ne.symm hl), add_zero]
      exact ih l hl

lemma U_eq (M : MC S) (i : S) (hi : hitProb M {i} i = 1) (hm : meanPassage M {i} i < ⊤)
    (x : S → ℝ≥0∞) (hx : ∀ k, x k = ∑' l, x l * M.P l k)
    (hxi : x i = 1) (hfin : ∀ k, x k ≠ ⊤) (j : S) (hj : LeadsTo M j i) :
    x j = visits M {i} i j := by
  set u := visits M {i} i with hu
  have hle := U_ge M i x hx hxi
  have ufin : ∀ k, u k ≠ ⊤ := fun k =>
    ne_top_of_le_ne_top hm.ne (by rw [← visits_sum]; exact ENNReal.le_tsum k)
  set μ := fun k => x k - u k with hμ
  have hxμ : ∀ k, x k = μ k + u k := fun k => (tsub_add_cancel_of_le (hle k)).symm
  have hinv : ∀ k, μ k = ∑' l, μ l * M.P l k := by
    intro k
    have h1 := hx k
    rw [hxμ k] at h1
    simp_rw [hxμ, add_mul] at h1
    rw [ENNReal.tsum_add, ← u_invariant M i hi k] at h1
    exact (ENNReal.add_left_inj (ufin k)).1 h1
  have hμi : μ i = 0 := by simp [hμ, hxi, hu, visits_self]
  have := inv_le_of_lead M μ hinv hj hμi
  rw [hxμ j, this, zero_add]

lemma pr_mem_lead (M : MC S) {R : Set S} (hR : IsPosRecClass M R) {i j : S} (hi : i ∈ R)
    (hj : j ∈ R) : LeadsTo M j i := by
  obtain ⟨x0, rfl⟩ := hR.1
  exact leadsTo_trans M hj.2 hi.1

lemma pr_nonempty (M : MC S) {R : Set S} (hR : IsPosRecClass M R) : ∃ i, i ∈ R := by
  obtain ⟨x0, rfl⟩ := hR.1
  exact ⟨x0, leadsTo_refl M x0, leadsTo_refl M x0⟩

lemma pr_closed (M : MC S) {R : Set S} (hR : IsPosRecClass M R) {i : S} (hi : i ∈ R)
    {t : ℕ} {l : S} (h : 0 < nStep M t i l) : l ∈ R := by
  have hR2 := hR.2
  obtain ⟨x0, rfl⟩ := hR.1
  have key : ∀ t l, 0 < nStep M t i l → LeadsTo M l i := by
    intro t
    induction t with
    | zero =>
      intro l hl
      simp only [nStep] at hl
      split_ifs at hl with h
      · subst h; exact leadsTo_refl M i
      · exact absurd hl (lt_irrefl _)
    | succ t ih =>
      intro l hl
      simp only [nStep] at hl
      obtain ⟨m, hm⟩ := exists_pos_of_tsum_pos hl
      have hm1 : 0 < nStep M t i m := pos_iff_ne_zero.2 (left_ne_zero_of_mul hm.ne')
      have hm2 : 0 < M.P m l := pos_iff_ne_zero.2 (right_ne_zero_of_mul hm.ne')
      have hmi := ih m hm1
      have hmR : m ∈ commClass M x0 :=
        ⟨leadsTo_trans M hi.1 ⟨t, hm1⟩, leadsTo_trans M hmi hi.2⟩
      exact leadsTo_trans M (close_step M m l (hR2 m hmR).1 hm2) hmi
  have hl := key t l h
  exact ⟨leadsTo_trans M hi.1 ⟨t, h⟩, leadsTo_trans M hl hi.2⟩

lemma pr_visits_out (M : MC S) {R : Set S} (hR : IsPosRecClass M R) (G : Set S) {i l : S}
    (hi : i ∈ R) (hl : l ∉ R) : visits M G i l = 0 := by
  unfold visits
  apply ENNReal.tsum_eq_zero.2
  intro t
  have h1 := avoid_le_nStep M G t i l
  have h2 : nStep M t i l = 0 := by
    by_contra hne; exact hl (pr_closed M hR hi (pos_iff_ne_zero.2 hne))
  rw [h2] at h1; exact le_antisymm h1 zero_le

lemma pr_P_out (M : MC S) {R : Set S} (hR : IsPosRecClass M R) {l k : S}
    (hl : l ∈ R) (hk : k ∉ R) : M.P l k = 0 := by
  by_contra hne
  exact hk (pr_closed M hR hl (nStep_succ_pos (t := 0) M (by simp [nStep]) (pos_iff_ne_zero.2 hne)))

lemma u_le_m (M : MC S) (i k : S) : visits M {i} i k ≤ meanPassage M {i} i := by
  rw [← visits_sum]; exact ENNReal.le_tsum k

lemma m_ne_zero (M : MC S) (i : S) : meanPassage M {i} i ≠ 0 := by
  intro h
  have := u_le_m M i i
  rw [visits_self, h] at this
  exact absurd this (by simp)

lemma pr_key (M : MC S) {R : Set S} (hR : IsPosRecClass M R) {i j : S} (hi : i ∈ R) (hj : j ∈ R) :
    meanPassage M {i} i = meanPassage M {j} j * visits M {i} i j := by
  obtain ⟨hjh, hjm⟩ := hR.2 j hj
  obtain ⟨hih, him⟩ := hR.2 i hi
  set c := visits M {j} j i with hc
  have cfin : c ≠ ⊤ := ne_top_of_le_ne_top hjm.ne (u_le_m M j i)
  have c0 : c ≠ 0 := by
    intro h0
    have := inv_le_of_lead M (visits M {j} j) (u_invariant M j hjh) (pr_mem_lead M hR hi hj) h0
    rw [visits_self] at this; exact one_ne_zero this
  set x := fun k => visits M {j} j k / c with hxdef
  have hx : ∀ k, x k = ∑' l, x l * M.P l k := by
    intro k
    simp only [hxdef, div_eq_mul_inv]
    rw [u_invariant M j hjh k, ← ENNReal.tsum_mul_right]
    congr 1; ext l; ring
  have hxi : x i = 1 := ENNReal.div_self c0 cfin
  have hfin : ∀ k, x k ≠ ⊤ := fun k =>
    ENNReal.div_ne_top (ne_top_of_le_ne_top hjm.ne (u_le_m M j k)) c0
  have hxe : ∀ k, x k = visits M {i} i k := by
    intro k
    by_cases hk : k ∈ R
    · exact U_eq M i hih him x hx hxi hfin k (pr_mem_lead M hR hi hk)
    · simp only [hxdef]
      rw [pr_visits_out M hR {j} hj hk, pr_visits_out M hR {i} hi hk, ENNReal.zero_div]
  have hsum : ∑' k, x k = meanPassage M {j} j / c := by
    simp only [hxdef, div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right, visits_sum]
  simp_rw [hxe] at hsum
  rw [visits_sum] at hsum
  rw [hsum, ← hxe j]
  simp only [hxdef, visits_self, div_eq_mul_inv, one_mul]

lemma pr_formula (M : MC S) {R : Set S} (hR : IsPosRecClass M R) {i j : S} (hi : i ∈ R) (hj : j ∈ R) :
    steadyState M j = (meanPassage M {i} i)⁻¹ * visits M {i} i j := by
  have hk := pr_key M hR hi hj
  have him := (hR.2 i hi).2
  set v := visits M {i} i j
  have vfin : v ≠ ⊤ := ne_top_of_le_ne_top him.ne (u_le_m M i j)
  have v0 : v ≠ 0 := by
    intro h; apply m_ne_zero M i; rw [hk, h, mul_zero]
  unfold steadyState
  rw [hk, ENNReal.mul_inv (Or.inr vfin) (Or.inr v0), mul_assoc, ENNReal.inv_mul_cancel v0 vfin,
    mul_one]

theorem steady_state_core (M : MC S) (R : Set S)
    (hR : IsPosRecClass M R) :
    ((∀ j ∈ R, steadyState M j = ∑' i : R, M.P i j * steadyState M i) ∧
      ∑' j : R, steadyState M j = 1 ∧
      ∀ x : S → ℝ≥0∞, (∀ j ∈ R, x j = ∑' i : R, M.P i j * x i) → ∑' j : R, x j = 1 →
        ∀ j ∈ R, x j = steadyState M j) ∧
    (∀ i ∈ R, ∀ j ∈ R,
      steadyState M j = visits M {i} i j / meanPassage M {i} i ∧
      steadyState M j = steadyState M i * visits M {i} i j) := by
  obtain ⟨i0, hi0⟩ := pr_nonempty M hR
  have hm0 := (hR.2 i0 hi0).2
  have hsupp : ∀ (i : S), i ∈ R → ∀ f : S → ℝ≥0∞,
      ∑' l : R, visits M {i} i l * f l = ∑' l, visits M {i} i l * f l := by
    intro i hi f
    refine tsum_subtype_eq_of_support_subset (f := fun l => visits M {i} i l * f l) (s := R) ?_
    intro l hl
    by_contra hlR
    apply hl
    simp [pr_visits_out M hR {i} hi hlR]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    have e : ∀ l : R, M.P l j * steadyState M l =
        (meanPassage M {j} j)⁻¹ * (visits M {j} j l * M.P l j) := by
      intro l; rw [pr_formula M hR hj l.2]; ring
    rw [tsum_congr e, ENNReal.tsum_mul_left, hsupp j hj (fun l => M.P l j),
      ← u_invariant M j (hR.2 j hj).1 j, visits_self, mul_one]
    rfl
  · have e : ∀ l : R, steadyState M l = (meanPassage M {i0} i0)⁻¹ * (visits M {i0} i0 l * 1) := by
      intro l; rw [pr_formula M hR hi0 l.2, mul_one]
    rw [tsum_congr e, ENNReal.tsum_mul_left, hsupp i0 hi0 (fun _ => 1)]
    simp only [mul_one]
    rw [visits_sum, ENNReal.inv_mul_cancel (m_ne_zero M i0) hm0.ne]
  · intro x hxinv hxs
    classical
    set xt : S → ℝ≥0∞ := fun k => if k ∈ R then x k else 0 with hxt
    have hsub : ∀ k, ∑' l, xt l * M.P l k = ∑' l : R, M.P l k * x l := by
      intro k
      rw [← tsum_subtype_eq_of_support_subset (f := fun l => xt l * M.P l k) (s := R)]
      · apply tsum_congr; intro l; simp [hxt, l.2, mul_comm]
      · intro l hl; by_contra hlR; apply hl; simp [hxt, hlR]
    have hinv : ∀ k, xt k = ∑' l, xt l * M.P l k := by
      intro k
      rw [hsub k]
      by_cases hk : k ∈ R
      · simp only [hxt, hk, if_true]; exact hxinv k hk
      · simp only [hxt, hk, if_false]
        symm; apply ENNReal.tsum_eq_zero.2; intro l
        rw [pr_P_out M hR l.2 hk, zero_mul]
    have hxle : ∀ k ∈ R, x k ≤ 1 := by
      intro k hk; rw [← hxs]; exact ENNReal.le_tsum (⟨k, hk⟩ : R)
    have xtfin : ∀ k, xt k ≠ ⊤ := by
      intro k; simp only [hxt]; split_ifs with hk
      · exact ne_top_of_le_ne_top ENNReal.one_ne_top (hxle k hk)
      · exact ENNReal.zero_ne_top
    have hsumxt : ∑' k, xt k = 1 := by
      rw [← hxs, ← tsum_subtype_eq_of_support_subset (f := xt) (s := R)]
      · apply tsum_congr; intro l; simp [hxt, l.2]
      · intro l hl; by_contra hlR; apply hl; simp [hxt, hlR]
    set c := xt i0 with hc
    have c0 : c ≠ 0 := by
      intro h0
      have : ∀ k, xt k = 0 := by
        intro k
        by_cases hk : k ∈ R
        · exact inv_le_of_lead M xt hinv (pr_mem_lead M hR hi0 hk) h0
        · simp [hxt, hk]
      rw [ENNReal.tsum_eq_zero.2 this] at hsumxt
      exact zero_ne_one hsumxt
    have cfin : c ≠ ⊤ := xtfin i0
    set y := fun k => xt k / c with hy
    have hyinv : ∀ k, y k = ∑' l, y l * M.P l k := by
      intro k
      simp only [hy, div_eq_mul_inv]
      rw [hinv k, ← ENNReal.tsum_mul_right]
      congr 1; ext l; ring
    have hye : ∀ k, y k = visits M {i0} i0 k := by
      intro k
      by_cases hk : k ∈ R
      · exact U_eq M i0 (hR.2 i0 hi0).1 hm0 y hyinv (ENNReal.div_self c0 cfin)
          (fun k => ENNReal.div_ne_top (xtfin k) c0) k (pr_mem_lead M hR hi0 hk)
      · simp only [hy, hxt, hk, if_false, ENNReal.zero_div]
        rw [pr_visits_out M hR {i0} hi0 hk]
    have hxty : ∀ k, xt k = c * y k := fun k => (ENNReal.mul_div_cancel c0 cfin).symm
    have hcm : c * meanPassage M {i0} i0 = 1 := by
      rw [← hsumxt, ← visits_sum, ← ENNReal.tsum_mul_left]
      apply tsum_congr; intro k; rw [hxty k, hye k]
    have hc' := ENNReal.eq_inv_of_mul_eq_one_left hcm
    intro j hj
    have : x j = xt j := by simp [hxt, hj]
    rw [this, hxty j, hye j, hc', pr_formula M hR hi0 hj]
  · intro i hi j hj
    rw [pr_formula M hR hi hj]
    refine ⟨by rw [div_eq_mul_inv, mul_comm], rfl⟩

open Classical in
lemma survive_succ_first (M : MC S) (G : Set S) (t : ℕ) (i : S) :
    survive M G (t+1) i = ∑' j, if j ∈ G then 0 else M.P i j * survive M G t j := by
  unfold survive
  simp_rw [avoid_succ_first]
  rw [ENNReal.tsum_comm]
  congr 1; ext j
  split_ifs
  · simp
  · rw [ENNReal.tsum_mul_left]

open Classical in
lemma mean_bound (M : MC S) (G : Set S) (V : S → ℝ≥0∞)
    (hV : ∀ i, 1 + ∑' j, (if j ∈ G then 0 else M.P i j * V j) ≤ V i) (i : S) :
    meanPassage M G i ≤ V i := by
  rw [meanPassage_eq_survive]
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ', survive_zero]
    simp_rw [survive_succ_first]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), add_comm]
    refine le_trans ?_ (hV i)
    gcongr with j
    split_ifs
    · simp
    · rw [← Finset.mul_sum]; gcongr; exact ih j

open Classical in
lemma visits_first (M : MC S) (G : Set S) (i k : S) :
    visits M G i k = (if i = k then 1 else 0) +
      ∑' j, if j ∈ G then 0 else M.P i j * visits M G j k := by
  rw [visits_eq_succ, avoid_zero]
  congr 1
  simp_rw [avoid_succ_first]
  rw [ENNReal.tsum_comm]
  congr 1; ext j
  split_ifs
  · simp
  · rw [ENNReal.tsum_mul_left]; rfl

open Classical in
lemma wvisits_first (M : MC S) (G : Set S) (w : S → ℝ≥0∞) (i : S) :
    ∑' k, w k * visits M G i k = w i +
      ∑' j, if j ∈ G then 0 else M.P i j * ∑' k, w k * visits M G j k := by
  simp_rw [visits_first M G i, mul_add]
  rw [ENNReal.tsum_add]
  congr 1
  · rw [tsum_eq_single i (by intro b hb; simp [Ne.symm hb])]; simp
  · simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    congr 1; ext j
    split_ifs
    · simp
    · congr 1; ext k; ring

open Classical in
lemma propagate (M : MC S) (z : S) (f : S → ℝ≥0∞)
    (hf : ∀ i, ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * f j) ≤ f i)
    (hz : f z < ⊤) : ∀ t l, 0 < nStep M t z l → f l < ⊤ := by
  intro t
  induction t with
  | zero =>
    intro l hl; simp only [nStep] at hl
    split_ifs at hl with h
    · subst h; exact hz
    · exact absurd hl (lt_irrefl _)
  | succ t ih =>
    intro l hl
    simp only [nStep] at hl
    obtain ⟨m, hm⟩ := exists_pos_of_tsum_pos hl
    have hm1 : 0 < nStep M t z m := pos_iff_ne_zero.2 (left_ne_zero_of_mul hm.ne')
    have hm2 : 0 < M.P m l := pos_iff_ne_zero.2 (right_ne_zero_of_mul hm.ne')
    have hmf := ih m hm1
    by_cases hlz : l = z
    · subst hlz; exact hz
    have : M.P m l * f l ≤ f m := by
      refine le_trans ?_ (hf m)
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum l)
      simp [hlz]
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.mul_top hm2.ne'] at this
    exact absurd (lt_of_lt_of_le hmf this) (lt_irrefl _)

open Classical in
noncomputable def pcT (M : MC S) (C : S → ℝ≥0) (G : Set S) (t : ℕ) (i : S) : ℝ≥0∞ :=
  ∑' x : Fin (t + 1) → S,
    if t ≠ 0 ∧ x 0 = i ∧ (∀ s : Fin (t + 1), 0 < s.val → s.val < t → x s ∉ G) ∧
        x (Fin.last t) ∈ G
    then pathProb M x * ∑ s : Fin t, (C (x s.castSucc) : ℝ≥0∞) else 0

lemma passageCost_eq (M : MC S) (C : S → ℝ≥0) (G : Set S) (i : S) :
    passageCost M C G i = ∑' t, pcT M C G t i := rfl

lemma pcT_zero (M : MC S) (C : S → ℝ≥0) (G : Set S) (i : S) : pcT M C G 0 i = 0 := by
  simp [pcT]

open Classical in
lemma fp_path (M : MC S) (G : Set S) (j : S) (t : ℕ) :
    firstPassProb M G j (t+1) = ∑' x : Fin (t+2) → S,
      if x 0 = j ∧ (∀ s : Fin (t+2), 0 < s.val → s.val < t+1 → x s ∉ G) ∧ x (Fin.last (t+1)) ∈ G
      then pathProb M x else 0 := by
  unfold firstPassProb taboo
  simp only [Nat.add_one_ne_zero, if_false]
  have : ∀ k, (if k ∈ G then ∑' x : Fin (t+1+1) → S, (if x 0 = j ∧ x (Fin.last (t+1)) = k ∧
      (∀ s : Fin (t+1+1), 0 < s.val → s.val < t+1 → x s ∉ G) then pathProb M x else 0) else 0) =
      ∑' x : Fin (t+1+1) → S, (if k ∈ G ∧ x 0 = j ∧ x (Fin.last (t+1)) = k ∧
      (∀ s : Fin (t+1+1), 0 < s.val → s.val < t+1 → x s ∉ G) then pathProb M x else 0) := by
    intro k; split_ifs with hk
    · congr 1; ext x; simp [hk]
    · symm; apply ENNReal.tsum_eq_zero.2; intro x; simp [hk]
  simp_rw [this]
  rw [ENNReal.tsum_comm]
  congr 1; ext x
  rw [tsum_eq_single (x (Fin.last (t+1)))]
  · apply if_congr _ rfl rfl; tauto
  · intro k hk; rw [if_neg]; intro h; exact hk h.2.2.1.symm

lemma forall_cons_iff2 {t : ℕ} (x : Fin (t+2) → S) (j : S) (Q : S → Prop) :
    (∀ s : Fin (t+3), 0 < s.val → s.val < t + 2 → Q ((Fin.cons j x : Fin (t+3) → S) s)) ↔
    Q (x 0) ∧ (∀ s : Fin (t+2), 0 < s.val → s.val < t + 1 → Q (x s)) := by
  rw [Fin.forall_fin_succ]
  simp only [Fin.val_zero, lt_irrefl, Fin.val_succ, Fin.cons_succ, IsEmpty.forall_iff, true_and,
    Nat.succ_pos, forall_const, add_lt_add_iff_right]
  constructor
  · intro h; exact ⟨h 0 (by simp), fun s _ hs => h s hs⟩
  · intro h s hs
    rcases Nat.eq_zero_or_pos s.val with h0 | h0
    · have : s = 0 := Fin.ext h0
      subst this; exact h.1
    · exact h.2 s h0 hs

open Classical in
lemma pcT_succ (M : MC S) (C : S → ℝ≥0) (G : Set S) (t : ℕ) (i : S) :
    pcT M C G (t+1) i = (C i : ℝ≥0∞) * firstPassProb M G i (t+1) +
      ∑' j, if j ∈ G then 0 else M.P i j * pcT M C G t j := by
  have e1 : pcT M C G (t+1) i = ∑' x : Fin (t+2) → S,
      ((if x 0 = i ∧ (∀ s : Fin (t+2), 0 < s.val → s.val < t+1 → x s ∉ G) ∧
        x (Fin.last (t+1)) ∈ G then (C i : ℝ≥0∞) * pathProb M x else 0) +
      (if x 0 = i ∧ (∀ s : Fin (t+2), 0 < s.val → s.val < t+1 → x s ∉ G) ∧
        x (Fin.last (t+1)) ∈ G then pathProb M x * ∑ s : Fin t, (C (x s.succ.castSucc) : ℝ≥0∞)
        else 0)) := by
    unfold pcT
    congr 1; ext x
    have hiff : ∀ P : Prop, (t + 1 ≠ 0 ∧ P) ↔ P := fun P => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    simp only [hiff]
    split_ifs with h
    · rw [Fin.sum_univ_succ]
      simp only [Fin.castSucc_zero, h.1]
      ring
    · simp
  rw [e1, ENNReal.tsum_add, fp_path]
  congr 1
  · rw [← ENNReal.tsum_mul_left]; congr 1; ext x; split_ifs <;> simp
  · cases t with
    | zero =>
      simp [pcT_zero]
    | succ t =>
      rw [tsum_cons, tsum_eq_single i]
      · have hL : ∀ x : Fin (t+2) → S,
            (if (Fin.cons i x : Fin (t+3) → S) 0 = i ∧
              (∀ s : Fin (t+1+2), 0 < s.val → s.val < t+1+1 → (Fin.cons i x : Fin (t+3) → S) s ∉ G) ∧
              (Fin.cons i x : Fin (t+3) → S) (Fin.last (t+1+1)) ∈ G
            then pathProb M (Fin.cons i x : Fin (t+3) → S) *
              ∑ s : Fin (t+1), (C ((Fin.cons i x : Fin (t+3) → S) s.succ.castSucc) : ℝ≥0∞) else 0) =
            ∑' j, if j ∈ G then 0 else
              (if x 0 = j ∧ (∀ s : Fin (t+2), 0 < s.val → s.val < t+1 → x s ∉ G) ∧
                x (Fin.last (t+1)) ∈ G then
                M.P i j * (pathProb M x * ∑ s : Fin (t+1), (C (x s.castSucc) : ℝ≥0∞)) else 0) := by
          intro x
          rw [tsum_eq_single (x 0)]
          · have hc : ∀ s : Fin (t+1), (Fin.cons i x : Fin (t+3) → S) s.succ.castSucc = x s.castSucc := by
              intro s; rw [← Fin.succ_castSucc, Fin.cons_succ]
            simp only [Fin.cons_zero, cons_last', forall_cons_iff2 x i (· ∉ G), pathProb_cons,
              true_and, hc]
            by_cases h0 : x 0 ∈ G
            · simp [h0]
            · simp only [h0, if_false, not_false_eq_true, true_and]
              split_ifs <;> ring
          · intro j hj; simp [Ne.symm hj]
        simp_rw [hL]
        rw [ENNReal.tsum_comm]
        congr 1; ext j
        by_cases hj : j ∈ G
        · simp [hj]
        · simp only [hj, if_false]
          unfold pcT
          rw [← ENNReal.tsum_mul_left]
          congr 1; ext x
          have hiff : ∀ P : Prop, (t + 1 ≠ 0 ∧ P) ↔ P := fun P => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
          simp only [hiff]
          split_ifs <;> simp
      · intro j hj
        apply ENNReal.tsum_eq_zero.2
        intro x; rw [Fin.cons_zero, if_neg]; tauto

open Classical in
lemma pc_bound (M : MC S) (C : S → ℝ≥0) (G : Set S) (V : S → ℝ≥0∞)
    (hV : ∀ i, (C i : ℝ≥0∞) + ∑' j, (if j ∈ G then 0 else M.P i j * V j) ≤ V i) (i : S) :
    passageCost M C G i ≤ V i := by
  rw [passageCost_eq]
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ', pcT_zero, add_zero]
    simp_rw [pcT_succ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine le_trans (add_le_add ?_ ?_) (hV i)
    · apply mul_le_of_le_one_right zero_le
      refine le_trans ?_ (hitProb_le_one M G i)
      unfold hitProb
      rw [tsum_eq_zero_add' ENNReal.summable, fp_zero, zero_add]
      exact ENNReal.sum_le_tsum _
    · apply ENNReal.tsum_le_tsum; intro j
      split_ifs
      · simp
      · rw [← Finset.mul_sum]; gcongr; exact ih j

lemma univ_posrec (M : MC S) (hirr : Irreducible M) (hpr : ∀ i, PositiveRecurrent M i) (z : S) :
    IsPosRecClass M Set.univ :=
  ⟨⟨z, by ext j; simp only [Set.mem_univ, true_iff]; exact hirr z j⟩, fun j _ => hpr j⟩

open Classical in
theorem lyap_part2 (M : MC S) (C : S → ℝ≥0) (hirr : Irreducible M)
    (hpr : ∀ i, PositiveRecurrent M i) (hJ : classAvgCost M C Set.univ < ⊤) (z : S) :
    IsZStandard M C z := by
  have hR := univ_posrec M hirr hpr z
  have hmz := (hpr z).2
  intro i
  obtain ⟨t, ht⟩ := (hirr z i).1
  constructor
  · have e : ∀ i, meanPassage M {z} i = ∑' k, (1 : ℝ≥0∞) * visits M {z} i k := by
      intro i; simp [visits_sum]
    have hf : ∀ i, ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * meanPassage M {z} j) ≤
        meanPassage M {z} i := by
      intro i
      rw [e i, wvisits_first]
      simp_rw [← e]
      exact le_add_self
    exact propagate M z _ hf hmz t i ht
  · set g := fun i => ∑' k, (C k : ℝ≥0∞) * visits M {z} i k with hg
    have hgi : ∀ i, g i = (C i : ℝ≥0∞) + ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * g j) := by
      intro i; exact wvisits_first M {z} (fun k => (C k : ℝ≥0∞)) i
    have hgz : g z < ⊤ := by
      have hu : ∀ k, visits M {z} z k = meanPassage M {z} z * steadyState M k := by
        intro k
        rw [pr_formula M hR (Set.mem_univ z) (Set.mem_univ k), ← mul_assoc,
          ENNReal.mul_inv_cancel (m_ne_zero M z) hmz.ne, one_mul]
      have : g z = meanPassage M {z} z * classAvgCost M C Set.univ := by
        simp only [hg, classAvgCost, hu]
        rw [tsum_univ (f := fun j => steadyState M j * (C j : ℝ≥0∞)), ← ENNReal.tsum_mul_left]
        congr 1; ext k; ring
      rw [this]; exact ENNReal.mul_lt_top hmz hJ
    have hf : ∀ i, ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * g j) ≤ g i := by
      intro i; rw [hgi i]; exact le_add_self
    have hgfin := propagate M z g hf hgz t i ht
    exact lt_of_le_of_lt (pc_bound M C {z} g (fun i => (hgi i).symm.le) i) hgfin

open Classical in
lemma tsum_ite_drop (M : MC S) (z i : S) (f : S → ℝ≥0∞) :
    ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * f j) ≤ ∑' j, M.P i j * f j :=
  ENNReal.tsum_le_tsum fun j => by split_ifs <;> simp

open Classical in
lemma tsum_ite_congr_z (M : MC S) (z i : S) (f g : S → ℝ≥0∞) (h : ∀ j, j ≠ z → f j = g j) :
    ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * f j) =
    ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * g j) := by
  apply tsum_congr; intro j
  by_cases hj : j = z
  · simp [hj]
  · simp [hj, h j hj]

open Classical in
theorem lyap_part1 (M : MC S) (C : S → ℝ≥0) (z : S) (y : S → ℝ≥0) (ε : ℝ≥0) (hε : 0 < ε)
    (hzy : ∑' j, M.P z j * (y j : ℝ≥0∞) < ⊤)
    (hdrift : ∀ i, i ≠ z → ∑' j, M.P i j * (y j : ℝ≥0∞) + ε ≤ y i)
    (r : S → ℝ≥0) (Hs : Finset S) (hzH : z ∈ Hs)
    (hHr : ∀ i ∈ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) < ⊤)
    (hrd : ∀ i ∉ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) + C i ≤ r i) :
    IsZStandard M C z := by
  set e : ℝ≥0∞ := (ε : ℝ≥0∞) with he
  have e0 : e ≠ 0 := by simp [he, hε.ne']
  have et : e ≠ ⊤ := ENNReal.coe_ne_top
  set Py : S → ℝ≥0∞ := fun i => ∑' j, M.P i j * (y j : ℝ≥0∞) with hPy
  set Pr : S → ℝ≥0∞ := fun i => ∑' j, M.P i j * (r j : ℝ≥0∞) with hPr
  intro i
  constructor
  · set Q : S → ℝ≥0∞ := fun i =>
      ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * ((y j : ℝ≥0∞) * e⁻¹)) with hQ
    set V : S → ℝ≥0∞ := fun i => if i = z then 1 + Q z else (y i : ℝ≥0∞) * e⁻¹ with hV
    have hQle : ∀ i, Q i ≤ Py i * e⁻¹ := by
      intro i
      refine le_trans (tsum_ite_drop M z i _) (le_of_eq ?_)
      simp only [hPy]; rw [← ENNReal.tsum_mul_right]; congr 1; ext j; ring
    have hVQ : ∀ i, ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * V j) = Q i := by
      intro i
      apply tsum_ite_congr_z; intro j hj; simp [hV, hj]
    have hVb : ∀ i, 1 + ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * V j) ≤ V i := by
      intro i
      rw [hVQ]
      by_cases hi : i = z
      · subst hi; simp [hV]
      · simp only [hV, hi, if_false]
        calc 1 + Q i ≤ 1 + Py i * e⁻¹ := by gcongr; exact hQle i
          _ = (Py i + e) * e⁻¹ := by rw [add_mul, ENNReal.mul_inv_cancel e0 et, add_comm]
          _ ≤ (y i : ℝ≥0∞) * e⁻¹ := by gcongr; exact hdrift i hi
    refine lt_of_le_of_lt (mean_bound M {z} V hVb i) ?_
    by_cases hi : i = z
    · simp only [hV, hi, if_true]
      refine lt_of_le_of_lt (add_le_add le_rfl (hQle z)) ?_
      exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top,
        ENNReal.mul_lt_top hzy (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 e0))⟩
    · simp only [hV, hi, if_false]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 e0))
  · set b : ℝ≥0∞ := ∑ h ∈ Hs, ((C h : ℝ≥0∞) + Pr h) with hb
    have bfin : b < ⊤ := by
      rw [hb, ENNReal.sum_lt_top]
      intro h hh
      exact ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, hHr h hh⟩
    set K : ℝ≥0∞ := b / e with hK
    have Kfin : K < ⊤ := ENNReal.div_lt_top bfin.ne e0
    have hKe : K * e = b := ENNReal.div_mul_cancel e0 et
    set W : S → ℝ≥0∞ := fun i => (r i : ℝ≥0∞) + K * (y i : ℝ≥0∞) with hW
    have hPW : ∀ i, ∑' j, M.P i j * W j = Pr i + K * Py i := by
      intro i
      simp only [hW, hPr, hPy, mul_add]
      rw [ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
      congr 1; congr 1; ext j; ring
    have hWd : ∀ i, i ≠ z → (C i : ℝ≥0∞) + ∑' j, M.P i j * W j ≤ W i := by
      intro i hi
      rw [hPW]
      by_cases hiH : i ∈ Hs
      · have h1 : (C i : ℝ≥0∞) + Pr i ≤ b :=
          Finset.single_le_sum (f := fun h => (C h : ℝ≥0∞) + Pr h) (fun _ _ => zero_le) hiH
        have h2 : b + K * Py i ≤ K * (y i : ℝ≥0∞) := by
          rw [← hKe, ← mul_add, add_comm]; gcongr; exact hdrift i hi
        calc (C i : ℝ≥0∞) + (Pr i + K * Py i) = ((C i : ℝ≥0∞) + Pr i) + K * Py i := by ring
          _ ≤ b + K * Py i := by gcongr
          _ ≤ K * (y i : ℝ≥0∞) := h2
          _ ≤ W i := le_add_self
      · have h1 := hrd i hiH
        have h2 : K * Py i ≤ K * (y i : ℝ≥0∞) := by
          gcongr; exact le_trans le_self_add (hdrift i hi)
        calc (C i : ℝ≥0∞) + (Pr i + K * Py i) = (Pr i + (C i : ℝ≥0∞)) + K * Py i := by ring
          _ ≤ (r i : ℝ≥0∞) + K * (y i : ℝ≥0∞) := add_le_add h1 h2
    set QW : S → ℝ≥0∞ := fun i =>
      ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * W j) with hQW
    set V : S → ℝ≥0∞ := fun i => if i = z then (C z : ℝ≥0∞) + QW z else W i with hV
    have hVQ : ∀ i, ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * V j) = QW i := by
      intro i
      apply tsum_ite_congr_z; intro j hj; simp [hV, hj]
    have hVb : ∀ i, (C i : ℝ≥0∞) + ∑' j, (if j ∈ ({z} : Set S) then 0 else M.P i j * V j) ≤ V i := by
      intro i
      rw [hVQ]
      by_cases hi : i = z
      · subst hi; simp [hV]
      · simp only [hV, hi, if_false]
        exact le_trans (add_le_add le_rfl (tsum_ite_drop M z i W)) (hWd i hi)
    refine lt_of_le_of_lt (pc_bound M C {z} V hVb i) ?_
    by_cases hi : i = z
    · simp only [hV, hi, if_true]
      refine lt_of_le_of_lt (add_le_add le_rfl (tsum_ite_drop M z z W)) ?_
      rw [hPW]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, ENNReal.add_lt_top.2 ⟨hHr z hzH,
        ENNReal.mul_lt_top Kfin hzy⟩⟩
    · simp only [hV, hi, if_false, hW]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, ENNReal.mul_lt_top Kfin ENNReal.coe_lt_top⟩

theorem lyap_core (M : MC S) (C : S → ℝ≥0) :
    (∀ (z : S) (y : S → ℝ≥0) (ε : ℝ≥0), 0 < ε → ∑' j, M.P z j * (y j : ℝ≥0∞) < ⊤ →
      (∀ i, i ≠ z → ∑' j, M.P i j * (y j : ℝ≥0∞) + ε ≤ y i) →
      ∀ (r : S → ℝ≥0) (Hs : Finset S), z ∈ Hs →
      (∀ i ∈ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) < ⊤) →
      (∀ i ∉ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) + C i ≤ r i) →
      IsZStandard M C z) ∧
    (Irreducible M → (∀ i, PositiveRecurrent M i) → classAvgCost M C Set.univ < ⊤ →
      ∀ z, IsZStandard M C z) :=
  ⟨fun z y ε hε hzy hd r Hs hzH hHr hrd => lyap_part1 M C z y ε hε hzy hd r Hs hzH hHr hrd,
   fun hirr hpr hJ z => lyap_part2 M C hirr hpr hJ z⟩

open Classical in
lemma tsum_compl_eq (G : Set S) (f : S → ℝ≥0∞) :
    ∑' j : ↥Gᶜ, f j = ∑' j, if j ∈ G then 0 else f j := by
  rw [tsum_subtype]; congr 1; ext j; simp [Set.indicator_apply]

lemma ennreal_dct {α : Type*} (F : ℕ → α → ℝ≥0∞) (bound : α → ℝ≥0∞) (hb : ∀ n a, F n a ≤ bound a)
    (hfin : ∑' a, bound a ≠ ⊤) (hlim : ∀ a, Tendsto (fun n => F n a) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' a, F n a) atTop (𝓝 0) := by
  letI : MeasurableSpace α := ⊤
  have := MeasureTheory.tendsto_lintegral_of_dominated_convergence (μ := MeasureTheory.Measure.count)
    (f := fun _ => 0) bound (fun n => measurable_from_top)
    (fun n => Filter.Eventually.of_forall (hb n)) (by rwa [MeasureTheory.lintegral_count])
    (Filter.Eventually.of_forall hlim)
  simpa [MeasureTheory.lintegral_count] using this

lemma avoid_mono (M : MC S) {G : Set S} {g : S} (hg : g ∈ G) (t : ℕ) (i l : S) :
    avoidProb M G t i l ≤ avoidProb M {g} t i l := by
  induction t generalizing l with
  | zero => rw [avoid_zero, avoid_zero]
  | succ t ih =>
    rw [avoid_succ_last, avoid_succ_last]
    by_cases hl : l ∈ G
    · simp [hl]
    · have : l ∉ ({g} : Set S) := by
        rintro rfl; exact hl hg
      simp only [hl, this, if_false]
      exact ENNReal.tsum_le_tsum fun k => by gcongr; exact ih k

lemma mean_mono (M : MC S) {G : Set S} {g : S} (hg : g ∈ G) (i : S) :
    meanPassage M G i ≤ meanPassage M {g} i := by
  rw [meanPassage_eq_survive, meanPassage_eq_survive]
  exact ENNReal.tsum_le_tsum fun t => ENNReal.tsum_le_tsum fun l => avoid_mono M hg t i l

lemma survive_le_one (M : MC S) (G : Set S) (t : ℕ) (i : S) : survive M G t i ≤ 1 := by
  rw [← survive_add_sum M G i t]; exact le_self_add

open Classical in
lemma mean_eq_first (M : MC S) (G : Set S) (i : S) :
    meanPassage M G i = 1 + ∑' j, if j ∈ G then 0 else M.P i j * meanPassage M G j := by
  have e : ∀ i, meanPassage M G i = ∑' k, (1 : ℝ≥0∞) * visits M G i k := by
    intro i; simp [visits_sum]
  rw [e i, wvisits_first]
  simp_rw [← e]

open Classical in
lemma pr_mean_fin (M : MC S) {R : Set S} (hR : IsPosRecClass M R) {i j : S} (hi : i ∈ R)
    (hj : j ∈ R) : meanPassage M {j} i < ⊤ := by
  obtain ⟨t, ht⟩ := pr_mem_lead M hR hi hj
  have hf : ∀ i, ∑' l, (if l ∈ ({j} : Set S) then 0 else M.P i l * meanPassage M {j} l) ≤
      meanPassage M {j} i := by
    intro i; rw [mean_eq_first M {j} i]; exact le_add_self
  exact propagate M j _ hf (hR.2 j hj).2 t i ht

open Classical in
lemma piR_inv (M : MC S) {R : Set S} (hR : IsPosRecClass M R) (l : S) :
    ∑' k, (if k ∈ R then steadyState M k else 0) * M.P k l =
      if l ∈ R then steadyState M l else 0 := by
  have hss := (steady_state_core M R hR).1.1
  by_cases hl : l ∈ R
  · rw [if_pos hl, hss l hl, tsum_subtype (s := R) (f := fun k => M.P k l * steadyState M k)]
    congr 1; ext k; by_cases hk : k ∈ R <;> simp [hk, Set.indicator_apply, mul_comm]
  · rw [if_neg hl]
    apply ENNReal.tsum_eq_zero.2; intro k
    by_cases hk : k ∈ R
    · simp [hk, pr_P_out M hR hk hl]
    · simp [hk]

open Classical in
lemma visits_GG (M : MC S) (G : Set S) {i j : S} (hj : j ∈ G) :
    visits M G i j = if i = j then 1 else 0 := by
  rw [visits_eq_succ, avoid_zero]
  have : ∀ t, avoidProb M G (t+1) i j = 0 := fun t => by rw [avoid_succ_last]; simp [hj]
  simp [this]

open Classical in
theorem first_passage_core (M : MC S) (G : Set S)
    (hG : G.Nonempty) :
    (∀ i, ∀ k ∉ G,
      visits M G i k = (if i = k then 1 else 0) + ∑' t : ℕ, taboo M G (t + 1) i k) ∧
    (∀ i, meanPassage M G i = ∑' k, visits M G i k) ∧
    ((∀ i k, ∀ t : ℕ, 1 ≤ t →
        taboo M G (t + 1) i k = ∑' j : ↥Gᶜ, M.P i j * taboo M G t j k) ∧
      (∀ i k, visits M G i k = (if i = k then 1 else 0) + ∑' j : ↥Gᶜ, M.P i j * visits M G j k) ∧
      (∀ i, meanPassage M G i = 1 + ∑' j : ↥Gᶜ, M.P i j * meanPassage M G j)) ∧
    (∀ R : Set S, IsPosRecClass M R → G ⊆ R →
      (∀ j ∈ R, steadyState M j = ∑' i : G, steadyState M i * visits M G i j) ∧
      ∑' i : G, steadyState M i * meanPassage M G i = 1) ∧
    (∀ R : Set S, IsPosRecClass M R → ∀ i ∈ R, ∀ j ∈ R, meanPassage M {j} i < ⊤) := by
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i k hk
    rw [visits_eq_succ, avoid_zero]
    congr 1; congr 1; ext t
    rw [taboo_succ_last, avoid_succ_last, if_neg hk]
  · intro i; exact (visits_sum M G i).symm
  · intro i k t ht
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [tsum_compl_eq G (fun j => M.P i j * taboo M G (t+1) j k), taboo_succ_last]
    simp_rw [avoid_succ_first]
    simp_rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    congr 1; ext j
    split_ifs
    · simp
    · rw [taboo_succ_last, ← ENNReal.tsum_mul_left]; congr 1; ext l; ring
  · intro i k
    rw [tsum_compl_eq G (fun j => M.P i j * visits M G j k)]; exact visits_first M G i k
  · intro i
    rw [tsum_compl_eq G (fun j => M.P i j * meanPassage M G j)]; exact mean_eq_first M G i
  · intro R hR hGR
    set πR : S → ℝ≥0∞ := fun k => if k ∈ R then steadyState M k else 0 with hπR
    have hinv : ∀ l, ∑' k, πR k * M.P k l = πR l := piR_inv M hR
    have hπsum : ∑' k, πR k = 1 := by
      rw [← (steady_state_core M R hR).1.2.1, tsum_subtype (s := R) (f := steadyState M)]
      congr 1
    have hfix : ∀ j ∈ R, steadyState M j = ∑' i : G, steadyState M i * visits M G i j := by
      intro j hj
      by_cases hjG : j ∈ G
      · rw [tsum_eq_single (⟨j, hjG⟩ : G)]
        · rw [visits_GG M G hjG]; simp
        · intro b hb
          rw [visits_GG M G hjG, if_neg, mul_zero]
          intro h; apply hb; exact Subtype.ext h
      -- j ∉ G
      set Rem : ℕ → ℝ≥0∞ := fun n =>
        ∑' k, πR k * (if k ∈ G then 0 else avoidProb M G n k j) with hRem
      set a : ℕ → ℝ≥0∞ := fun s =>
        ∑' k, πR k * (if k ∈ G then avoidProb M G (s+1) k j else 0) with ha
      have hstep : ∀ n, Rem (n+1) + a n = Rem n := by
        intro n
        simp only [hRem, ha]
        rw [← ENNReal.tsum_add]
        have : ∀ k, πR k * (if k ∈ G then 0 else avoidProb M G (n+1) k j) +
            πR k * (if k ∈ G then avoidProb M G (n+1) k j else 0) =
            πR k * avoidProb M G (n+1) k j := by
          intro k; split_ifs <;> simp
        simp_rw [this, avoid_succ_first]
        simp_rw [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        congr 1; ext l
        split_ifs with hl
        · simp
        · rw [← hinv l, ← ENNReal.tsum_mul_right]
          congr 1; ext k; ring
      have hRem0 : Rem 0 = steadyState M j := by
        simp only [hRem]
        simp_rw [avoid_zero]
        rw [tsum_eq_single j]
        · simp [hjG, hπR, hj]
        · intro b hb; simp [Ne.symm hb, hb]
      have hsum : ∀ n, ∑ s ∈ Finset.range n, a s + Rem n = steadyState M j := by
        intro n
        induction n with
        | zero => simp [hRem0]
        | succ n ih => rw [Finset.sum_range_succ, ← ih, ← hstep n]; ring
      have hRemlim : Tendsto Rem atTop (𝓝 0) := by
        have hle : ∀ n, Rem n ≤ ∑' k, πR k * survive M G n k := by
          intro n
          apply ENNReal.tsum_le_tsum; intro k
          gcongr
          split_ifs
          · exact zero_le
          · exact ENNReal.le_tsum j
        have hd : Tendsto (fun n => ∑' k, πR k * survive M G n k) atTop (𝓝 0) := by
          apply ennreal_dct _ πR
          · intro n k; exact mul_le_of_le_one_right zero_le (survive_le_one M G n k)
          · rw [hπsum]; exact ENNReal.one_ne_top
          · intro k
            by_cases hk : k ∈ R
            · obtain ⟨g, hg⟩ := hG
              have hm : ∑' t, survive M G t k ≠ ⊤ := by
                rw [← meanPassage_eq_survive]
                exact (lt_of_le_of_lt (mean_mono M hg k) (pr_mean_fin M hR hk (hGR hg))).ne
              have := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hm
              simpa using ENNReal.Tendsto.const_mul this (Or.inr
                (ne_top_of_le_ne_top ENNReal.one_ne_top (hπsum ▸ ENNReal.le_tsum k)))
            · simp [hπR, hk]
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hd (fun n => zero_le) hle
      have hlim1 : Tendsto (fun n => ∑ s ∈ Finset.range n, a s) atTop (𝓝 (∑' s, a s)) :=
        ENNReal.tendsto_nat_tsum a
      have hlim2 : Tendsto (fun n => ∑ s ∈ Finset.range n, a s + Rem n) atTop
          (𝓝 (∑' s, a s + 0)) := hlim1.add hRemlim
      simp_rw [hsum, add_zero] at hlim2
      have heq := tendsto_nhds_unique tendsto_const_nhds hlim2
      rw [heq]
      simp only [ha]
      rw [ENNReal.tsum_comm, tsum_subtype (s := G) (f := fun i => steadyState M i * visits M G i j)]
      congr 1; ext k
      by_cases hkG : k ∈ G
      · have hkR := hGR hkG
        have hkj : k ≠ j := fun h => hjG (h ▸ hkG)
        simp only [hπR, hkR, hkG, if_true, Set.indicator_apply]
        rw [ENNReal.tsum_mul_left, visits_ne M G hkj]
      · simp [hkG, Set.indicator_apply]
    refine ⟨hfix, ?_⟩
    simp_rw [← visits_sum]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    rw [← (steady_state_core M R hR).1.2.1]
    rw [← tsum_subtype_eq_of_support_subset (f := fun j => ∑' i : G, steadyState M i * visits M G i j)
      (s := R)]
    · exact tsum_congr fun j => (hfix j j.2).symm
    · intro j hj
      by_contra hjR
      apply hj
      apply ENNReal.tsum_eq_zero.2
      intro i
      simp [pr_visits_out M hR G (hGR i.2) hjR]
  · intro R hR i hi j hj
    exact pr_mean_fin M hR hi hj

open Classical in
lemma hit_split (M : MC S) (G : Set S) (i : S) :
    hitProb M G i = toG M G i + ∑' j, (if j ∈ G then 0 else M.P i j * hitProb M G j) := by
  rw [hit_first_step, toG, ← ENNReal.tsum_add]
  congr 1; ext j; split_ifs <;> simp

open Classical in
lemma pc_split (M : MC S) (C : S → ℝ≥0) (G : Set S) (i : S) :
    passageCost M C G i = (C i : ℝ≥0∞) * hitProb M G i +
      ∑' j, (if j ∈ G then 0 else M.P i j * passageCost M C G j) := by
  rw [passageCost_eq, tsum_eq_zero_add' ENNReal.summable, pcT_zero, zero_add]
  simp_rw [pcT_succ]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ← hitProb_succ, ENNReal.tsum_comm]
  congr 1
  congr 1; ext j
  split_ifs
  · simp
  · rw [ENNReal.tsum_mul_left, passageCost_eq]

open Classical in
lemma iter_eq (M : MC S) (G : Set S) (f g : S → ℝ≥0∞)
    (hf : ∀ i, f i = g i + ∑' j, (if j ∈ G then 0 else M.P i j * f j)) (N : ℕ) (i : S) :
    f i = ∑ s ∈ Finset.range N, ∑' k, avoidProb M G s i k * g k +
      ∑' k, avoidProb M G N i k * f k := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    simp_rw [avoid_zero]
    rw [tsum_eq_single i (by intro b hb; simp [Ne.symm hb])]; simp
  | succ N ih =>
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    simp_rw [avoid_succ_last]
    conv_lhs => arg 1; ext k; rw [hf k]
    simp_rw [mul_add]
    rw [ENNReal.tsum_add]
    congr 1
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    congr 1; ext j
    split_ifs
    · simp
    · rw [← ENNReal.tsum_mul_right]; congr 1; ext k; ring

lemma pointwise_of_tsum_eq {α : Type*} (a b : α → ℝ≥0∞) (hle : ∀ k, b k ≤ a k)
    (heq : ∑' k, b k = ∑' k, a k) (hfin : ∑' k, a k ≠ ⊤) (k : α) : b k = a k := by
  classical
  by_contra hne
  have hlt : b k < a k := lt_of_le_of_ne (hle k) hne
  have h1 := ENNReal.tsum_eq_add_tsum_ite (f := b) k
  have h2 := ENNReal.tsum_eq_add_tsum_ite (f := a) k
  have hle2 : ∑' x, (if x = k then 0 else b x) ≤ ∑' x, (if x = k then 0 else a x) :=
    ENNReal.tsum_le_tsum fun x => by split_ifs <;> simp [hle x]
  have hfin2 : ∑' x, (if x = k then 0 else b x) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (le_trans hle2 (h2 ▸ le_add_self))
  have : ∑' x, b x < ∑' x, a x := by
    rw [h1, h2, add_comm (b k), add_comm (a k)]
    exact ENNReal.add_lt_add_of_le_of_lt hfin2 hle2 hlt
  rw [heq] at this; exact lt_irrefl _ this

lemma hit_support (M : MC S) (G : Set S) (i : S) (hi : hitProb M G i = 1) (N : ℕ) (k : S) :
    avoidProb M G N i k * hitProb M G k = avoidProb M G N i k := by
  have hit := iter_eq M G (hitProb M G) (toG M G) (hit_split M G) N i
  rw [hi] at hit
  have hs := survive_add_sum M G i N
  rw [Finset.sum_range_succ', fp_zero, add_zero] at hs
  simp_rw [fp_succ] at hs
  unfold survive at hs
  have hX : ∑ s ∈ Finset.range N, ∑' k, avoidProb M G s i k * toG M G k ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hs ▸ le_add_self)
  rw [← hs, add_comm] at hit
  have heq := (ENNReal.add_right_inj hX).1 hit
  refine pointwise_of_tsum_eq (fun k => avoidProb M G N i k)
    (fun k => avoidProb M G N i k * hitProb M G k) ?_ heq.symm ?_ k
  · intro k; exact mul_le_of_le_one_right zero_le (hitProb_le_one M G k)
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans le_self_add hs.le)

lemma hit_one_of_mean (M : MC S) (G : Set S) (i : S) (h : meanPassage M G i < ⊤) :
    hitProb M G i = 1 := by
  by_contra hne
  unfold meanPassage at h
  rw [if_neg hne] at h
  exact lt_irrefl _ h

lemma pc_eq_W (M : MC S) (C : S → ℝ≥0) (G : Set S) (i : S) (hm : meanPassage M G i < ⊤) :
    passageCost M C G i = ∑' k, (C k : ℝ≥0∞) * visits M G i k := by
  have hi := hit_one_of_mean M G i hm
  apply le_antisymm
  · exact pc_bound M C G _ (fun i => (wvisits_first M G (fun k => (C k : ℝ≥0∞)) i).symm.le) i
  · have hit := iter_eq M G (passageCost M C G) (fun k => (C k : ℝ≥0∞) * hitProb M G k)
      (pc_split M C G) 
    unfold visits
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    apply ENNReal.tsum_le_of_sum_range_le
    intro N
    rw [hit N i]
    refine le_trans ?_ le_self_add
    apply Finset.sum_le_sum
    intro s _
    apply le_of_eq
    congr 1; ext k
    rw [mul_comm (C k : ℝ≥0∞) (hitProb M G k), ← mul_assoc, hit_support M G i hi s k, mul_comm]

open Classical in
theorem passage_core (M : MC S) (C : S → ℝ≥0) (G : Set S)
    (hG : G.Nonempty) :
    (∀ i, meanPassage M G i < ⊤ →
      passageCost M C G i = ∑' k, (C k : ℝ≥0∞) * visits M G i k) ∧
    (∀ i, meanPassage M G i < ⊤ →
      passageCost M C G i = (C i : ℝ≥0∞) + ∑' j : ↥Gᶜ, M.P i j * passageCost M C G j) ∧
    (∀ R : Set S, IsPosRecClass M R → G ⊆ R →
      classAvgCost M C R = ∑' i : G, steadyState M i * passageCost M C G i) ∧
    (∀ R : Set S, IsPosRecClass M R → classAvgCost M C R < ⊤ →
      ∀ i ∈ R, ∀ j ∈ R, passageCost M C {j} i < ⊤) := by
  refine ⟨fun i hm => pc_eq_W M C G i hm, ?_, ?_, ?_⟩
  · intro i hm
    rw [tsum_compl_eq G (fun j => M.P i j * passageCost M C G j), pc_split,
      hit_one_of_mean M G i hm, mul_one]
  · intro R hR hGR
    have hfp := (first_passage_core M G hG).2.2.2.1 R hR hGR
    have e : ∀ i : G, steadyState M i * passageCost M C G i =
        ∑' k, steadyState M i * ((C k : ℝ≥0∞) * visits M G i k) := by
      intro i
      rw [pc_eq_W M C G i, ENNReal.tsum_mul_left]
      obtain ⟨i, hiG⟩ := i
      exact lt_of_le_of_lt (mean_mono M hiG i) (hR.2 i (hGR hiG)).2
    rw [tsum_congr e, ENNReal.tsum_comm, classAvgCost]
    rw [← tsum_subtype_eq_of_support_subset
      (f := fun k => ∑' i : G, steadyState M i * ((C k : ℝ≥0∞) * visits M G i k)) (s := R)]
    · apply tsum_congr; intro k
      rw [hfp.1 k k.2, ← ENNReal.tsum_mul_right]
      congr 1; ext i; ring
    · intro k hk
      by_contra hkR
      apply hk
      apply ENNReal.tsum_eq_zero.2
      intro i
      simp [pr_visits_out M hR G (hGR i.2) hkR]
  · intro R hR hJ i hi j hj
    obtain ⟨t, ht⟩ := pr_mem_lead M hR hi hj
    have hmj := (hR.2 j hj).2
    set g := fun i => ∑' k, (C k : ℝ≥0∞) * visits M {j} i k with hg
    have hgi : ∀ i, g i = (C i : ℝ≥0∞) + ∑' l, (if l ∈ ({j} : Set S) then 0 else M.P i l * g l) := by
      intro i; exact wvisits_first M {j} (fun k => (C k : ℝ≥0∞)) i
    have hgz : g j < ⊤ := by
      have : g j = meanPassage M {j} j * classAvgCost M C R := by
        simp only [hg, classAvgCost]
        rw [← ENNReal.tsum_mul_left]
        rw [← tsum_subtype_eq_of_support_subset
          (f := fun k => (C k : ℝ≥0∞) * visits M {j} j k) (s := R)]
        · apply tsum_congr; intro k
          rw [pr_formula M hR hj k.2, ← mul_assoc, ← mul_assoc,
            ENNReal.mul_inv_cancel (m_ne_zero M j) hmj.ne, one_mul, mul_comm]
        · intro k hk; by_contra hkR; apply hk
          simp [pr_visits_out M hR {j} hj hkR]
      rw [this]; exact ENNReal.mul_lt_top hmj hJ
    have hf : ∀ i, ∑' l, (if l ∈ ({j} : Set S) then 0 else M.P i l * g l) ≤ g i := by
      intro i; rw [hgi i]; exact le_add_self
    have hgfin := propagate M j g hf hgz t i ht
    exact lt_of_le_of_lt (pc_bound M C {j} g (fun i => (hgi i).symm.le) i) hgfin

lemma renewal_cesaro (p S A : ℕ → ℝ≥0∞) (hp : ∀ s, p s ≤ 1)
    (hm0 : ∑' r, S r ≠ 0) (hmt : ∑' r, S r ≠ ⊤)
    (hid : ∀ n : ℕ, ∑ s ∈ Finset.range n, p s * ∑ r ∈ Finset.range (n - s), S r = n) :
    Tendsto (fun n : ℕ => (∑ s ∈ Finset.range n, p s * ∑ r ∈ Finset.range (n - s), A r) / n)
      atTop (𝓝 ((∑' r, A r) / ∑' r, S r)) := by
  set m := ∑' r, S r with hm
  set q : ℕ → ℝ≥0∞ := fun n => ∑ s ∈ Finset.range n, p s with hq
  have up : ∀ (W : ℕ → ℝ≥0∞) (n : ℕ),
      ∑ s ∈ Finset.range n, p s * ∑ r ∈ Finset.range (n - s), W r ≤ (∑' r, W r) * q n := by
    intro W n; rw [hq, Finset.mul_sum]; apply Finset.sum_le_sum; intro s _
    rw [mul_comm]; gcongr; exact ENNReal.sum_le_tsum _
  have low : ∀ (W : ℕ → ℝ≥0∞) (n L : ℕ), L ≤ n →
      (∑ r ∈ Finset.range L, W r) * q (n - L) ≤
        ∑ s ∈ Finset.range n, p s * ∑ r ∈ Finset.range (n - s), W r := by
    intro W n L hL
    rw [hq, Finset.mul_sum]
    calc _ ≤ ∑ s ∈ Finset.range (n - L), p s * ∑ r ∈ Finset.range (n - s), W r := by
          apply Finset.sum_le_sum; intro s hs; rw [mul_comm]; gcongr
          simp only [Finset.mem_range] at hs; omega
      _ ≤ _ := Finset.sum_le_sum_of_subset (by intro x; simp only [Finset.mem_range]; omega)
  have qsplit : ∀ n L : ℕ, L ≤ n → q n ≤ q (n - L) + L := by
    intro n L hL
    simp only [hq]
    calc ∑ s ∈ Finset.range n, p s = ∑ s ∈ Finset.range ((n - L) + L), p s := by
          rw [Nat.sub_add_cancel hL]
      _ = ∑ s ∈ Finset.range (n - L), p s + ∑ x ∈ Finset.range L, p (n - L + x) :=
          Finset.sum_range_add _ _ _
      _ ≤ ∑ s ∈ Finset.range (n - L), p s + ∑ x ∈ Finset.range L, (1 : ℝ≥0∞) := by
          gcongr with x; exact hp _
      _ = _ := by simp
  have mpos : 0 < m := pos_iff_ne_zero.2 hm0
  -- q n / n → m⁻¹
  have qlim : Tendsto (fun n : ℕ => q n / n) atTop (𝓝 m⁻¹) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [eventually_ge_atTop 1] with n hn
      refine lt_of_lt_of_le ha ?_
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      rw [ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n))]
      have h1 : (n : ℝ≥0∞) ≤ m * q n := by rw [← hid n]; exact up S n
      calc m⁻¹ * n ≤ m⁻¹ * (m * q n) := by gcongr
        _ = q n := by rw [← mul_assoc, ENNReal.inv_mul_cancel hm0 hmt, one_mul]
    · intro b hb
      have hM : Tendsto (fun L => ∑ r ∈ Finset.range L, S r) atTop (𝓝 m) := ENNReal.tendsto_nat_tsum S
      have hMi : Tendsto (fun L => (∑ r ∈ Finset.range L, S r)⁻¹) atTop (𝓝 m⁻¹) :=
        ENNReal.tendsto_inv_iff.2 hM
      obtain ⟨L, hL1, hL2⟩ := (((tendsto_order.1 hMi).2 b hb).and ((tendsto_order.1 hM).1 0 mpos)).exists
      set ML := ∑ r ∈ Finset.range L, S r with hML
      have hMLt : ML ≠ ⊤ := ne_top_of_le_ne_top hmt (ENNReal.sum_le_tsum _)
      have hlim : Tendsto (fun n : ℕ => ML⁻¹ + (L : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) atTop (𝓝 (ML⁻¹ + L * 0)) :=
        tendsto_const_nhds.add (ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
          (Or.inr (ENNReal.natCast_ne_top L)))
      rw [mul_zero, add_zero] at hlim
      filter_upwards [(tendsto_order.1 hlim).2 b hL1, eventually_ge_atTop (max L 1)] with n h1 hn
      refine lt_of_le_of_lt ?_ h1
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hnt : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
      have hLn : L ≤ n := le_trans (le_max_left _ _) hn
      have h2 : ML * q (n - L) ≤ n := by rw [← hid n]; exact low S n L hLn
      have h3 : q (n - L) ≤ n * ML⁻¹ := by
        rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hL2.ne') (Or.inl hMLt), mul_comm]
        exact h2
      rw [div_eq_mul_inv]
      calc q n * (n : ℝ≥0∞)⁻¹ ≤ (n * ML⁻¹ + L) * (n : ℝ≥0∞)⁻¹ := by
            gcongr; exact le_trans (qsplit n L hLn) (by gcongr)
        _ = ML⁻¹ + L * (n : ℝ≥0∞)⁻¹ := by
            rw [add_mul, mul_comm (n : ℝ≥0∞), mul_assoc, ENNReal.mul_inv_cancel hn0 hnt, mul_one]
  rw [div_eq_mul_inv]
  rw [tendsto_order]
  constructor
  · intro a ha
    have hB : Tendsto (fun L => (∑ r ∈ Finset.range L, A r) * m⁻¹) atTop (𝓝 ((∑' r, A r) * m⁻¹)) :=
      ENNReal.Tendsto.mul_const (ENNReal.tendsto_nat_tsum A) (Or.inr (ENNReal.inv_ne_top.2 hm0))
    obtain ⟨L, hL⟩ := ((tendsto_order.1 hB).1 a ha).exists
    set BL := ∑ r ∈ Finset.range L, A r with hBL
    have hlim : Tendsto (fun n : ℕ => BL * (q n / n - (L : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹)) atTop
        (𝓝 (BL * (m⁻¹ - L * 0))) := by
      apply ENNReal.Tendsto.const_mul
      · exact ENNReal.Tendsto.sub qlim (ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
          (Or.inr (ENNReal.natCast_ne_top L))) (Or.inr (by simp))
      · left; simp [hmt]
    rw [mul_zero, tsub_zero] at hlim
    filter_upwards [(tendsto_order.1 hlim).1 a hL, eventually_ge_atTop (max L 1)] with n h1 hn
    refine lt_of_lt_of_le h1 ?_
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hLn : L ≤ n := le_trans (le_max_left _ _) hn
    have e : q n / n - (L : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ = (q n - L) / n := by
      rw [ENNReal.sub_div (fun _ _ => hn0), div_eq_mul_inv (L : ℝ≥0∞)]
    rw [e]
    have h2 : q n - L ≤ q (n - L) := tsub_le_iff_right.2 (qsplit n L hLn)
    calc BL * ((q n - L) / n) ≤ BL * (q (n - L) / n) :=
          mul_le_mul_of_nonneg_left (ENNReal.div_le_div_right h2 _) zero_le
      _ = (BL * q (n - L)) * (n : ℝ≥0∞)⁻¹ := by rw [div_eq_mul_inv, mul_assoc]
      _ ≤ _ := by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right (low A n L hLn) zero_le
  · intro b hb
    have hc : ∑' r, A r ≠ ⊤ := by
      intro h; rw [h, ENNReal.top_mul (ENNReal.inv_ne_zero.2 hmt)] at hb
      exact not_top_lt hb
    have hlim : Tendsto (fun n : ℕ => (∑' r, A r) * (q n / n)) atTop (𝓝 ((∑' r, A r) * m⁻¹)) :=
      ENNReal.Tendsto.const_mul qlim (Or.inr hc)
    filter_upwards [(tendsto_order.1 hlim).2 b hb] with n h1
    refine lt_of_le_of_lt ?_ h1
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
    gcongr
    exact up A n

lemma nStep_sum (M : MC S) (t : ℕ) (i : S) : ∑' k, nStep M t i k = 1 := by
  induction t with
  | zero => simp only [nStep]; rw [tsum_eq_single i (by intro b hb; simp [Ne.symm hb])]; simp
  | succ t ih =>
    simp only [nStep]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, M.P_sum, mul_one]
    exact ih

lemma nStep_le_one (M : MC S) (t : ℕ) (i k : S) : nStep M t i k ≤ 1 := by
  rw [← nStep_sum M t i]; exact ENNReal.le_tsum k

lemma last_exit (M : MC S) (i : S) (t : ℕ) (k : S) :
    nStep M t i k = ∑ s ∈ Finset.range (t+1), nStep M s i i * avoidProb M {i} (t - s) i k := by
  induction t generalizing k with
  | zero => simp [avoid_zero, nStep]
  | succ t ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, avoid_zero]
    by_cases hk : k = i
    · subst hk
      rw [Finset.sum_eq_zero]
      · simp
      · intro s hs
        simp only [Finset.mem_range] at hs
        obtain ⟨r, hr⟩ : ∃ r, t + 1 - s = r + 1 := ⟨t - s, by omega⟩
        rw [hr, avoid_succ_self, mul_zero]
    · rw [if_neg (Ne.symm hk), mul_zero, add_zero]
      simp only [nStep]
      simp_rw [ih]
      simp_rw [Finset.sum_mul]
      rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      apply Finset.sum_congr rfl
      intro s hs
      simp only [Finset.mem_range] at hs
      rw [show t + 1 - s = (t - s) + 1 by omega, avoid_succ_last, if_neg (by simpa using hk),
        ← ENNReal.tsum_mul_left]
      congr 1; ext l; ring

lemma conv_sum (p A : ℕ → ℝ≥0∞) (n : ℕ) :
    ∑ t ∈ Finset.range n, ∑ s ∈ Finset.range (t+1), p s * A (t - s) =
      ∑ s ∈ Finset.range n, p s * ∑ r ∈ Finset.range (n - s), A r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rw [Finset.sum_range_succ (fun s => p s * ∑ r ∈ Finset.range (n + 1 - s), A r) n]
    rw [Finset.sum_range_succ (fun s => p s * A (n - s)) n]
    rw [show n + 1 - n = 1 by omega, Nat.sub_self, Finset.sum_range_one]
    have : ∀ s ∈ Finset.range n, p s * ∑ r ∈ Finset.range (n + 1 - s), A r =
        p s * ∑ r ∈ Finset.range (n - s), A r + p s * A (n - s) := by
      intro s hs
      simp only [Finset.mem_range] at hs
      rw [show n + 1 - s = (n - s) + 1 by omega, Finset.sum_range_succ, mul_add]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    ring

lemma cost_conv (M : MC S) (i : S) (w : S → ℝ≥0∞) (n : ℕ) :
    ∑ t ∈ Finset.range n, ∑' k, nStep M t i k * w k =
      ∑ s ∈ Finset.range n, nStep M s i i *
        ∑ r ∈ Finset.range (n - s), ∑' k, avoidProb M {i} r i k * w k := by
  rw [← conv_sum]
  apply Finset.sum_congr rfl; intro t _
  simp_rw [last_exit M i t, Finset.sum_mul]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl; intro s _
  rw [← ENNReal.tsum_mul_left]; congr 1; ext k; ring

theorem class_avg_core (M : MC S) (C : S → ℝ≥0) (R : Set S)
    (hR : IsPosRecClass M R) :
    (∀ i ∈ R, Tendsto (fun n : ℕ => avgCostN M C n i) atTop (𝓝 (classAvgCost M C R))) ∧
    (∀ i ∈ R, classAvgCost M C R = passageCost M C {i} i / meanPassage M {i} i) ∧
    (∀ n : ℕ, classAvgCost M C R =
      ∑' j : R, steadyState M j * ∑' k, nStep M n j k * (C k : ℝ≥0∞)) := by
  have hii : ∀ i ∈ R, classAvgCost M C R = passageCost M C {i} i / meanPassage M {i} i := by
    intro i hi
    have := (passage_core M C {i} ⟨i, rfl⟩).2.2.1 R hR (by simpa using hi)
    rw [this, tsum_singleton (f := fun x => steadyState M x * passageCost M C {i} x)]
    rw [steadyState, div_eq_mul_inv, mul_comm]
  refine ⟨?_, hii, ?_⟩
  · intro i hi
    rw [hii i hi]
    have hm := (hR.2 i hi).2
    have key := renewal_cesaro (fun s => nStep M s i i)
      (fun r => ∑' k, avoidProb M {i} r i k * 1)
      (fun r => ∑' k, avoidProb M {i} r i k * (C k : ℝ≥0∞))
      (fun s => nStep_le_one M s i i)
    have hS : ∑' r, ∑' k, avoidProb M {i} r i k * 1 = meanPassage M {i} i := by
      rw [meanPassage_eq_survive]; simp [survive]
    have hA : ∑' r, ∑' k, avoidProb M {i} r i k * (C k : ℝ≥0∞) = passageCost M C {i} i := by
      rw [pc_eq_W M C {i} i hm, ENNReal.tsum_comm]
      congr 1; ext k; unfold visits; rw [← ENNReal.tsum_mul_left]; congr 1; ext r; ring
    rw [hS, hA] at key
    have hid : ∀ n : ℕ, ∑ s ∈ Finset.range n, nStep M s i i *
        ∑ r ∈ Finset.range (n - s), ∑' k, avoidProb M {i} r i k * 1 = n := by
      intro n
      rw [← cost_conv]
      simp [nStep_sum]
    have key2 := key (m_ne_zero M i) hm.ne hid
    refine key2.congr ?_
    intro n
    unfold avgCostN
    rw [cost_conv]
  · intro n
    classical
    set πR : S → ℝ≥0∞ := fun k => if k ∈ R then steadyState M k else 0 with hπR
    have hinv : ∀ l, πR l = ∑' k, πR k * M.P k l := fun l => (piR_inv M hR l).symm
    have hit := iterate_inv M πR hinv n
    unfold classAvgCost
    have e1 : ∑' j : R, steadyState M j * ∑' k, nStep M n j k * (C k : ℝ≥0∞) =
        ∑' j, πR j * ∑' k, nStep M n j k * (C k : ℝ≥0∞) := by
      rw [tsum_subtype (s := R) (f := fun j => steadyState M j * ∑' k, nStep M n j k * (C k : ℝ≥0∞))]
      congr 1; ext j; by_cases hj : j ∈ R <;> simp [hπR, hj, Set.indicator_apply]
    have e2 : ∑' j : R, steadyState M j * (C j : ℝ≥0∞) = ∑' j, πR j * (C j : ℝ≥0∞) := by
      rw [tsum_subtype (s := R) (f := fun j => steadyState M j * (C j : ℝ≥0∞))]
      congr 1; ext j; by_cases hj : j ∈ R <;> simp [hπR, hj, Set.indicator_apply]
    rw [e1, e2]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    congr 1; ext k
    rw [← hit k, ← ENNReal.tsum_mul_right]
    congr 1; ext j; ring

lemma shift_div_lim (E : ℕ → ℝ≥0∞) (J : ℝ≥0∞) (hJ : J ≠ ⊤)
    (hE : Tendsto (fun n : ℕ => E n / n) atTop (𝓝 J)) (L : ℕ) :
    Tendsto (fun n : ℕ => E (n - L) / n) atTop (𝓝 J) := by
  have h1 : Tendsto (fun n : ℕ => E (n - L) / ((n - L : ℕ) : ℝ≥0∞)) atTop (𝓝 J) :=
    hE.comp (tendsto_sub_atTop_nat L)
  have h2 : Tendsto (fun n : ℕ => ((n - L : ℕ) : ℝ≥0∞) / n) atTop (𝓝 1) := by
    have hlow : Tendsto (fun n : ℕ => 1 - (L : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) atTop (𝓝 (1 - L * 0)) :=
      ENNReal.Tendsto.sub tendsto_const_nhds (ENNReal.Tendsto.const_mul
        ENNReal.tendsto_inv_nat_nhds_zero (Or.inr (ENNReal.natCast_ne_top L))) (Or.inl ENNReal.one_ne_top)
    rw [mul_zero, tsub_zero] at hlow
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    · filter_upwards [eventually_ge_atTop (max L 1)] with n hn
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hnt : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
      rw [ENNReal.natCast_sub, ENNReal.sub_div (fun _ _ => hn0),
        ENNReal.div_self hn0 hnt, div_eq_mul_inv]
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      rw [ENNReal.div_le_iff hn0 (ENNReal.natCast_ne_top n), one_mul]
      exact_mod_cast Nat.sub_le n L
  have h3 := ENNReal.Tendsto.mul h1 (Or.inr ENNReal.one_ne_top) h2 (Or.inr hJ)
  rw [mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop L] with n hn
  have hb0 : ((n - L : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n - L ≠ 0 by omega)
  have hbt : ((n - L : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  simp only [Pi.mul_apply, div_eq_mul_inv]
  calc E (n - L) * ((n - L : ℕ) : ℝ≥0∞)⁻¹ * (((n - L : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹)
      = E (n - L) * (((n - L : ℕ) : ℝ≥0∞)⁻¹ * ((n - L : ℕ) : ℝ≥0∞)) * (n : ℝ≥0∞)⁻¹ := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hb0 hbt, mul_one]

lemma delay_lim (f E D : ℕ → ℝ≥0∞) (Dmax J : ℝ≥0∞) (hD : ∀ n, D n ≤ Dmax) (hDt : Dmax ≠ ⊤)
    (hf : ∑' s, f s = 1) (hJ : J ≠ ⊤) (hmono : Monotone E)
    (hE : Tendsto (fun n : ℕ => E n / n) atTop (𝓝 J)) :
    Tendsto (fun n : ℕ => (D n + ∑ s ∈ Finset.range n, f s * E (n - s)) / n) atTop (𝓝 J) := by
  have hDlim : Tendsto (fun n : ℕ => D n / n) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => Dmax * (n : ℝ≥0∞)⁻¹) atTop (𝓝 (Dmax * 0)) :=
      ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hDt)
    rw [mul_zero] at this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun n => zero_le)
    intro n; simp only [div_eq_mul_inv]; gcongr; exact hD n
  have hG : Tendsto (fun n : ℕ => (∑ s ∈ Finset.range n, f s * E (n - s)) / n) atTop (𝓝 J) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      have hF : Tendsto (fun L => (∑ s ∈ Finset.range L, f s) * J) atTop (𝓝 (1 * J)) := by
        apply ENNReal.Tendsto.mul_const _ (Or.inr hJ)
        rw [← hf]; exact ENNReal.tendsto_nat_tsum f
      rw [one_mul] at hF
      obtain ⟨L, hL⟩ := ((tendsto_order.1 hF).1 a ha).exists
      set FL := ∑ s ∈ Finset.range L, f s
      have hFL : FL ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hf ▸ ENNReal.sum_le_tsum _)
      have h2 : Tendsto (fun n : ℕ => FL * (E (n - L) / n)) atTop (𝓝 (FL * J)) :=
        ENNReal.Tendsto.const_mul (shift_div_lim E J hJ hE L) (Or.inr hFL)
      filter_upwards [(tendsto_order.1 h2).1 a hL, eventually_ge_atTop L] with n h1 hn
      refine lt_of_lt_of_le h1 ?_
      rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
      gcongr
      rw [Finset.sum_mul]
      calc ∑ s ∈ Finset.range L, f s * E (n - L) ≤ ∑ s ∈ Finset.range L, f s * E (n - s) := by
            apply Finset.sum_le_sum; intro s hs; gcongr; apply hmono
            simp only [Finset.mem_range] at hs; omega
        _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hn)
    · intro b hb
      filter_upwards [(tendsto_order.1 hE).2 b hb] with n h1
      refine lt_of_le_of_lt ?_ h1
      simp only [div_eq_mul_inv]
      gcongr
      calc ∑ s ∈ Finset.range n, f s * E (n - s) ≤ ∑ s ∈ Finset.range n, f s * E n := by
            apply Finset.sum_le_sum; intro s _; gcongr; exact hmono (Nat.sub_le n s)
        _ = (∑ s ∈ Finset.range n, f s) * E n := by rw [Finset.sum_mul]
        _ ≤ 1 * E n := by gcongr; rw [← hf]; exact ENNReal.sum_le_tsum _
        _ = E n := one_mul _
  have := hDlim.add hG
  rw [zero_add] at this
  refine this.congr ?_
  intro n; rw [ENNReal.add_div]

open Classical in
lemma first_entrance (M : MC S) (z i : S) (t : ℕ) (k : S) :
    nStep M t i k = avoidProb M {z} t i k +
      ∑ s ∈ Finset.range (t+1), firstPassProb M {z} i s * nStep M (t - s) z k := by
  induction t generalizing k with
  | zero => simp [avoid_zero, nStep, fp_zero]
  | succ t ih =>
    have e1 : nStep M (t+1) i k = ∑' l, avoidProb M {z} t i l * M.P l k +
        ∑ s ∈ Finset.range (t+1), firstPassProb M {z} i s * nStep M (t + 1 - s) z k := by
      simp only [nStep]
      simp_rw [ih, add_mul, Finset.sum_mul]
      rw [ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      congr 1
      apply Finset.sum_congr rfl; intro s hs
      simp only [Finset.mem_range] at hs
      rw [show t + 1 - s = (t - s) + 1 by omega]
      simp only [nStep]
      rw [← ENNReal.tsum_mul_left]; congr 1; ext l; ring
    rw [e1, ← taboo_succ_last]
    rw [Finset.sum_range_succ (fun s => firstPassProb M {z} i s * nStep M (t + 1 - s) z k) (t+1)]
    rw [Nat.sub_self, add_left_comm, add_comm (taboo M {z} (t+1) i k)]
    congr 1
    by_cases hk : k = z
    · rw [hk, avoid_succ_last, if_pos (Set.mem_singleton z), zero_add]
      simp only [nStep, if_true, mul_one]
      unfold firstPassProb
      rw [if_neg (Nat.add_one_ne_zero t)]
      rw [tsum_eq_single z (by intro b hb; simp [hb])]; simp
    · rw [taboo_succ_last, avoid_succ_last]
      simp [hk, nStep, Ne.symm hk]

lemma recurrent_closed (M : MC S) (i l : S) (hi : hitProb M {i} i = 1) (h : LeadsTo M i l) :
    LeadsTo M l i := by
  obtain ⟨t, ht⟩ := h
  rw [last_exit M i t l] at ht
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht.ne'
  have ha : avoidProb M {i} (t - s) i l ≠ 0 := right_ne_zero_of_mul hs
  have hsup := hit_support M {i} i hi (t - s) l
  by_contra hn
  have h0 : hitProb M {i} l = 0 :=
    hit_zero_of_not_leads M {i} l (by intro g hg; rw [Set.mem_singleton_iff] at hg; subst hg; exact hn)
  rw [h0, mul_zero] at hsup
  exact ha hsup.symm

theorem zstd_core (M : MC S) (C : S → ℝ≥0) (z : S)
    (hz : IsZStandard M C z) :
    ∃ R : Set S, IsPosRecClass M R ∧ z ∈ R ∧ (∀ i ∉ R, Transient M i) ∧
      classAvgCost M C R < ⊤ ∧
      ∀ i, Tendsto (fun n : ℕ => avgCostN M C n i) atTop (𝓝 (classAvgCost M C R)) := by
  have hzz := (hz z).1
  have hzh := hit_one_of_mean M {z} z hzz
  have posrec : ∀ j ∈ commClass M z, PositiveRecurrent M j := by
    intro j hj
    set u := visits M {z} z with hu
    have c0 : u j ≠ 0 := by
      intro h0
      have := inv_le_of_lead M u (u_invariant M z hzh) hj.1 h0
      rw [hu, visits_self] at this; exact one_ne_zero this
    have ct : u j ≠ ⊤ := ne_top_of_le_ne_top hzz.ne (u_le_m M z j)
    set x := fun k => u k / u j with hxdef
    have huinv : ∀ k, u k = ∑' l, u l * M.P l k := u_invariant M z hzh
    have hx : ∀ k, x k = ∑' l, x l * M.P l k := by
      intro k
      simp only [hxdef, div_eq_mul_inv]
      rw [huinv k, ← ENNReal.tsum_mul_right]
      congr 1; ext l; ring
    have hxj : x j = 1 := ENNReal.div_self c0 ct
    have hle := U_ge M j x hx hxj
    have hm : meanPassage M {j} j < ⊤ := by
      rw [← visits_sum]
      refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) ?_
      simp only [hxdef, div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right, hu, visits_sum]
      exact ENNReal.mul_lt_top hzz (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 c0))
    exact ⟨hit_one_of_mean M {j} j hm, hm⟩
  have hR : IsPosRecClass M (commClass M z) := ⟨⟨z, rfl⟩, posrec⟩
  have hzR : z ∈ commClass M z := ⟨leadsTo_refl M z, leadsTo_refl M z⟩
  have hcore := class_avg_core M C (commClass M z) hR
  have hJ : classAvgCost M C (commClass M z) < ⊤ := by
    rw [hcore.2.1 z hzR]
    exact ENNReal.div_lt_top (hz z).2.ne (m_ne_zero M z)
  refine ⟨commClass M z, hR, hzR, ?_, hJ, ?_⟩
  · intro i hi
    have hiz : LeadsTo M i z := by
      by_contra hn
      have h0 : hitProb M {z} i = 0 :=
        hit_zero_of_not_leads M {z} i (by intro g hg; rw [Set.mem_singleton_iff] at hg; subst hg; exact hn)
      rw [hit_one_of_mean M {z} i (hz i).1] at h0
      exact one_ne_zero h0
    refine lt_of_le_of_ne (hitProb_le_one M {i} i) ?_
    intro h1
    exact hi ⟨recurrent_closed M i z h1 hiz, hiz⟩
  · intro i
    set J := classAvgCost M C (commClass M z)
    set Ez : ℕ → ℝ≥0∞ := fun n => ∑ t ∈ Finset.range n, ∑' k, nStep M t z k * (C k : ℝ≥0∞) with hEz
    have hEzl : Tendsto (fun n : ℕ => Ez n / n) atTop (𝓝 J) := hcore.1 z hzR
    set D : ℕ → ℝ≥0∞ := fun n =>
      ∑ t ∈ Finset.range n, ∑' k, avoidProb M {z} t i k * (C k : ℝ≥0∞) with hD
    have hDle : ∀ n, D n ≤ passageCost M C {z} i := by
      intro n
      have : ∑' k, (C k : ℝ≥0∞) * visits M {z} i k =
          ∑' t, ∑' k, avoidProb M {z} t i k * (C k : ℝ≥0∞) := by
        rw [ENNReal.tsum_comm]; congr 1; ext k; unfold visits
        rw [← ENNReal.tsum_mul_left]; congr 1; ext t; ring
      rw [pc_eq_W M C {z} i (hz i).1, this]; exact ENNReal.sum_le_tsum _
    have hf : ∑' s, firstPassProb M {z} i s = 1 := hit_one_of_mean M {z} i (hz i).1
    have hmono : Monotone Ez := by
      intro a b hab
      exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hab)
    have key := delay_lim (fun s => firstPassProb M {z} i s) Ez D (passageCost M C {z} i) J hDle
      (hz i).2.ne hf hJ.ne hmono hEzl
    refine key.congr ?_
    intro n
    unfold avgCostN
    congr 1
    simp only [hD, hEz]
    simp_rw [first_entrance M z i _ _, add_mul, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun t _ => ENNReal.tsum_add), Finset.sum_add_distrib]
    congr 1
    rw [← conv_sum]
    apply Finset.sum_congr rfl; intro t _
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    apply Finset.sum_congr rfl; intro s _
    rw [← ENNReal.tsum_mul_left]; congr 1; ext k; ring


end MKX


/-! ## New material -/

noncomputable def sdxK {T : Type*} (Γ : MC T) : MKX.MC T := ⟨Γ.P, Γ.P_sum⟩

section bridge
variable {T : Type*} [Countable T] (Γ : MC T)

lemma br_nStep (t : ℕ) (i j : T) : MKX.nStep (sdxK Γ) t i j = Γ.nStep t i j := by
  induction t generalizing j with
  | zero => simp [MKX.nStep, MC.nStep]
  | succ t ih => rw [MKX.nStep, MC.nStep]; simp only [ih]; rfl

lemma br_avoid (G : Set T) (t : ℕ) (i k : T) :
    MKX.avoidProb (sdxK Γ) G t i k = Γ.avoidProb G t i k := by
  induction t generalizing i with
  | zero => rw [MKX.avoid_zero]; simp [MC.avoidProb]
  | succ t ih => rw [MKX.avoid_succ_first, sdq_avoid_succ]; simp only [ih]; rfl

lemma br_mean (G : Set T) (hG : G.Nonempty) (i : T) :
    MKX.meanPassage (sdxK Γ) G i = Γ.meanPassage G i := by
  rw [(MKX.first_passage_core (sdxK Γ) G hG).2.1 i, MC.meanPassage]
  simp only [MKX.visits, br_avoid]
  exact ENNReal.tsum_comm

lemma br_pc (G : Set T) (hG : G.Nonempty) (i : T) (hm : Γ.meanPassage G i < ⊤) :
    MKX.passageCost (sdxK Γ) Γ.C G i = Γ.passageCost G i := by
  rw [MKX.pc_eq_W _ _ _ _ (by rwa [br_mean _ _ hG])]
  simp only [MKX.visits, br_avoid, MC.passageCost, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun t => tsum_congr fun k => mul_comm _ _

lemma br_ss (j : T) : MKX.steadyState (sdxK Γ) j = Γ.steadyState j := by
  rw [MKX.steadyState, MC.steadyState, br_mean _ _ (Set.singleton_nonempty j)]

lemma br_cac (R : Set T) : MKX.classAvgCost (sdxK Γ) Γ.C R = Γ.classAvgCost R := by
  unfold MKX.classAvgCost MC.classAvgCost
  exact tsum_congr fun j => by rw [br_ss]

lemma br_leads (i j : T) : MKX.LeadsTo (sdxK Γ) i j ↔ Γ.LeadsTo i j := by
  simp only [MKX.LeadsTo, MC.LeadsTo, br_nStep]

lemma br_comm (z : T) : MKX.commClass (sdxK Γ) z = Γ.commClass z := by
  ext j
  simp only [MKX.commClass, MC.commClass, MKX.Communicate, MC.Communicate, Set.mem_setOf_eq,
    br_leads]

lemma br_zstd (z : T) (hz : Γ.IsZStandard z) : MKX.IsZStandard (sdxK Γ) Γ.C z := fun i =>
  ⟨by rw [br_mean _ _ (Set.singleton_nonempty z)]; exact (hz i).1,
   by rw [br_pc _ _ (Set.singleton_nonempty z) _ (hz i).1]; exact (hz i).2⟩

lemma br_avg (i : T) (L : ℝ≥0∞)
    (h : Tendsto (fun n : ℕ => MKX.avgCostN (sdxK Γ) Γ.C n i) atTop (𝓝 L)) :
    Γ.avgCost i = L := by
  unfold MC.avgCost
  have e : (fun n : ℕ => MKX.avgCostN (sdxK Γ) Γ.C n i) = fun n : ℕ =>
      (∑ t ∈ Finset.range n, ∑' j, Γ.nStep t i j * (Γ.C j : ℝ≥0∞)) / (n : ℝ≥0∞) := by
    funext n; simp only [MKX.avgCostN, br_nStep]
  rw [e] at h
  exact h.limsup_eq

lemma mkx_comm (M : MKX.MC T) (i0 z : T) (h : z ∈ MKX.commClass M i0) :
    MKX.commClass M i0 = MKX.commClass M z := by
  simp only [MKX.commClass, MKX.Communicate, Set.mem_setOf_eq] at h
  ext j
  simp only [MKX.commClass, MKX.Communicate, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, b⟩; exact ⟨MKX.leadsTo_trans M h.2 a, MKX.leadsTo_trans M b h.1⟩
  · rintro ⟨a, b⟩; exact ⟨MKX.leadsTo_trans M h.1 a, MKX.leadsTo_trans M b h.2⟩

end bridge

section mine
variable {S : Type*}

noncomputable def sdxPw (Γ : MC S) (x : S) (w : S → ℝ≥0∞) (i : S) : ℝ≥0∞ :=
  ∑' t, ∑' k, Γ.avoidProb {x} t i k * w k

lemma sdx_pw_first (Γ : MC S) (x : S) (w : S → ℝ≥0∞) (i : S) :
    sdxPw Γ x w i = w i + ∑' j, if j ∈ ({x} : Set S) then 0 else Γ.P i j * sdxPw Γ x w j :=
  sdq_first_step Γ {x} w i

lemma sdx_pw_one (Γ : MC S) (x i : S) : sdxPw Γ x (fun _ => 1) i = Γ.meanPassage {x} i := by
  simp [sdxPw, MC.meanPassage]

lemma sdx_pw_le_mean (Γ : MC S) (x : S) (w : S → ℝ≥0∞) (hw : ∀ k, w k ≤ 1) (i : S) :
    sdxPw Γ x w i ≤ Γ.meanPassage {x} i := by
  rw [← sdx_pw_one]
  exact ENNReal.tsum_le_tsum fun t => ENNReal.tsum_le_tsum fun k => by gcongr; exact hw k

lemma sdx_pw_tendsto_zero (Γ : MC S) (x : S) (W : ℕ → S → ℝ≥0∞) (hW : ∀ N k, W N k ≤ 1)
    (hWl : ∀ k, ∀ᶠ N in atTop, W N k = 0) (i : S) (hi : Γ.meanPassage {x} i < ⊤) :
    Tendsto (fun N => sdxPw Γ x (W N) i) atTop (𝓝 0) := by
  have e : ∀ N, sdxPw Γ x (W N) i = ∑' p : ℕ × S, Γ.avoidProb {x} p.1 i p.2 * W N p.2 := by
    intro N; unfold sdxPw
    exact (ENNReal.tsum_prod (f := fun t k => Γ.avoidProb {x} t i k * W N k)).symm
  simp only [e]
  refine MKX.ennreal_dct (fun N (p : ℕ × S) => Γ.avoidProb {x} p.1 i p.2 * W N p.2)
    (fun (p : ℕ × S) => Γ.avoidProb {x} p.1 i p.2) (fun N p => ?_) ?_ (fun p => ?_)
  · calc _ ≤ Γ.avoidProb {x} p.1 i p.2 * 1 := by gcongr; exact hW N p.2
      _ = _ := mul_one _
  · rw [ENNReal.tsum_prod (f := fun t k => Γ.avoidProb {x} t i k)]; exact ne_of_lt hi
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hWl p.2] with N hN
    simp [hN]

lemma sdx_y_first (Γ : MC S) (x : S) (w W : S → ℝ≥0∞) (K : ℝ≥0∞) (i : S) :
    w i + ∑' j, (if j ∈ ({x} : Set S) then 0 else
      Γ.P i j * (sdxPw Γ x w j + K * sdxPw Γ x W j)) ≤ sdxPw Γ x w i + K * sdxPw Γ x W i := by
  have e : ∑' j, (if j ∈ ({x} : Set S) then 0 else
      Γ.P i j * (sdxPw Γ x w j + K * sdxPw Γ x W j)) =
      ∑' j, (if j ∈ ({x} : Set S) then 0 else Γ.P i j * sdxPw Γ x w j) +
      K * ∑' j, (if j ∈ ({x} : Set S) then 0 else Γ.P i j * sdxPw Γ x W j) := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun j => ?_
    split_ifs
    · simp
    · ring
  rw [e, ← add_assoc, ← sdx_pw_first]
  refine add_le_add le_rfl ?_
  gcongr
  rw [sdx_pw_first Γ x W i]
  exact le_add_self

lemma sdx_drift {Γ : MC S} (AS : ApproxSeq Γ) (z : S) (m w : S → ℝ≥0∞) (q : ℕ → S → S → S → ℝ≥0∞)
    (hq : AS.IsATASWith q) (N : ℕ) (hN : AS.N₀ ≤ N)
    (hzN : z ∈ AS.SN N) (i : S) (hi : i ∈ AS.SN N)
    (hfs : w i + ∑' j, (if j ∈ ({z} : Set S) then 0 else Γ.P i j * m j) ≤ m i)
    (h37 : ∀ r, r ∉ AS.SN N → ∑ j ∈ (AS.SN N).filter (· ≠ z), q N i r j * m j ≤ m r) :
    w i + ∑' j : AS.SN N, (if j ∈ (Subtype.val ⁻¹' ({z} : Set S) : Set (AS.SN N)) then 0 else
      (AS.chain N hN).P ⟨i, hi⟩ j * m j.1) ≤ m i := by
  refine le_trans (add_le_add le_rfl ?_) hfs
  set F := (AS.SN N).filter (· ≠ z) with hF
  have e1 : ∑' j : AS.SN N, (if j ∈ (Subtype.val ⁻¹' ({z} : Set S) : Set (AS.SN N)) then 0 else
      (AS.chain N hN).P ⟨i, hi⟩ j * m j.1) = ∑ j ∈ F, AS.PN N i j * m j := by
    rw [hF, Finset.sum_filter]
    rw [← Finset.tsum_subtype (AS.SN N) (fun j => if j ≠ z then AS.PN N i j * m j else 0)]
    refine tsum_congr fun j => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ne_eq]
    split_ifs <;> simp [ApproxSeq.chain]
  rw [e1]
  have e2 : ∑ j ∈ F, AS.PN N i j * m j = ∑ j ∈ F, Γ.P i j * m j +
      ∑' r : {r : S // r ∉ AS.SN N}, Γ.P i r.1 * ∑ j ∈ F, q N i r.1 j * m j := by
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [hq.2 N hN i hi j (Finset.mem_filter.1 hj).1])]
    simp only [add_mul, Finset.sum_add_distrib]
    congr 1
    simp only [← ENNReal.tsum_mul_right]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine tsum_congr fun r => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc]
  rw [e2]
  have e3 : ∑ j ∈ F, Γ.P i j * m j = ∑' j, if j ∈ F then Γ.P i j * m j else 0 := by
    rw [tsum_eq_sum (s := F) (fun b hb => by simp [hb])]
    exact Finset.sum_congr rfl fun j hj => by simp [hj]
  have e4 : ∑' r : {r : S // r ∉ AS.SN N}, Γ.P i r.1 * m r.1 =
      ∑' j, if j ∉ AS.SN N then Γ.P i j * m j else 0 := by
    rw [← tsum_subtype_eq_of_support_subset (s := {r : S | r ∉ AS.SN N})]
    · exact tsum_congr fun r => by rw [if_pos r.2]
    · intro j hj
      by_contra hc
      exact hj (by simp only [Set.mem_setOf_eq, not_not] at hc; simp [hc])
  calc ∑ j ∈ F, Γ.P i j * m j + ∑' r : {r : S // r ∉ AS.SN N}, Γ.P i r.1 * ∑ j ∈ F, q N i r.1 j * m j
      ≤ ∑ j ∈ F, Γ.P i j * m j + ∑' r : {r : S // r ∉ AS.SN N}, Γ.P i r.1 * m r.1 :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum fun r => mul_le_mul_right (h37 r.1 r.2) _)
    _ = ∑' j, ((if j ∈ F then Γ.P i j * m j else 0) +
          (if j ∉ AS.SN N then Γ.P i j * m j else 0)) := by
        rw [e3, e4, ENNReal.tsum_add]
    _ ≤ _ := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        by_cases hjz : j = z
        · subst hjz; simp [hF, hzN]
        · by_cases hjS : j ∈ AS.SN N
          · simp [hF, hjS, hjz]
          · simp [hF, hjS, hjz]

noncomputable def sdxInd {Γ : MC S} (AS : ApproxSeq Γ) (N : ℕ) (k : S) : ℝ≥0∞ :=
  if k ∈ AS.SN N then 0 else 1

lemma sdxInd_le {Γ : MC S} (AS : ApproxSeq Γ) (N : ℕ) (k : S) : sdxInd AS N k ≤ 1 := by
  unfold sdxInd; split_ifs <;> simp

lemma sdxInd_ev {Γ : MC S} (AS : ApproxSeq Γ) (k : S) : ∀ᶠ N in atTop, sdxInd AS N k = 0 := by
  filter_upwards [sdp_ev_mem AS k] with N hN
  simp [sdxInd, hN.2]

lemma sdx_bound {Γ : MC S} (AS : ApproxSeq Γ) (q : ℕ → S → S → S → ℝ≥0∞)
    (hq : AS.IsATASWith q) (G : Finset S) (hexcess : AS.SendsExcessTo q (↑G : Set S))
    (x : S) (w : S → ℝ≥0∞) (hmG : ∀ g ∈ G, Γ.meanPassage {x} g < ⊤) :
    ∀ᶠ N in atTop, ∀ (h : AS.N₀ ≤ N ∧ x ∈ AS.SN N) (i' : AS.SN N),
      ∑' t, ∑' k : AS.SN N, (AS.chain N h.1).avoidProb (Subtype.val ⁻¹' {x}) t i' k * w k.1 ≤
        sdxPw Γ x w i'.1 + (2 * ∑ g ∈ G, sdxPw Γ x w g) * sdxPw Γ x (sdxInd AS N) i'.1 := by
  have hB : Tendsto (fun N => ∑ g ∈ G, sdxPw Γ x (sdxInd AS N) g) atTop (𝓝 0) := by
    have := tendsto_finset_sum G (fun g hg => sdx_pw_tendsto_zero Γ x (fun N => sdxInd AS N)
      (sdxInd_le AS) (sdxInd_ev AS) g (hmG g hg))
    simpa using this
  have hB2 : ∀ᶠ N in atTop, ∑ g ∈ G, sdxPw Γ x (sdxInd AS N) g ≤ 2⁻¹ :=
    ((tendsto_order.1 hB).2 _ (by simp)).mono fun N h => le_of_lt h
  filter_upwards [hB2] with N hBN
  intro h i'
  refine sdq_compare (AS.chain N h.1) (Subtype.val ⁻¹' {x}) (fun j => w j.1)
    (fun j => sdxPw Γ x w j.1 + (2 * ∑ g ∈ G, sdxPw Γ x w g) * sdxPw Γ x (sdxInd AS N) j.1)
    (fun i'' => sdx_drift AS x
      (fun j => sdxPw Γ x w j + (2 * ∑ g ∈ G, sdxPw Γ x w g) * sdxPw Γ x (sdxInd AS N) j) w
      q hq N h.1 h.2 i''.1 i''.2 (sdx_y_first Γ x w _ _ i''.1) ?_) i'
  intro r hr
  have hi := i''.2
  have h1 := hq.1 N h.1 i''.1 i''.2 r hr
  have h2 := hexcess N h.1 i''.1 i''.2 r hr
  have h2' : ∑ j ∈ (AS.SN N).filter (fun j => j ∈ (↑G : Set S)), q N i''.1 r j = 1 := by
    convert h2
  rw [← Finset.sum_filter_add_sum_filter_not (AS.SN N) (fun j => j ∈ (↑G : Set S)), h2'] at h1
  have h3 : ∑ j ∈ (AS.SN N).filter (fun j => ¬ j ∈ (↑G : Set S)), q N i''.1 r j = 0 := by
    have : (1 : ℝ≥0∞) + ∑ j ∈ (AS.SN N).filter (fun j => ¬ j ∈ (↑G : Set S)), q N i''.1 r j
        = 1 + 0 := by rw [add_zero]; exact h1
    exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 this
  have hq0 : ∀ j ∈ AS.SN N, j ∉ G → q N i''.1 r j = 0 := fun j hj hjG =>
    (Finset.sum_eq_zero_iff.1 h3) j (Finset.mem_filter.2 ⟨hj, by simpa using hjG⟩)
  set A := ∑ g ∈ G, sdxPw Γ x w g with hA
  set y : S → ℝ≥0∞ := fun j => sdxPw Γ x w j + (2 * A) * sdxPw Γ x (sdxInd AS N) j with hy
  set Y := ∑ g ∈ G, y g with hY
  have s1 : ∑ j ∈ (AS.SN N).filter (· ≠ x), q N i''.1 r j * y j ≤
      ∑ j ∈ AS.SN N, (if j ∈ (↑G : Set S) then q N i''.1 r j * Y else 0) := by
    refine le_trans (Finset.sum_le_sum fun j hj => ?_)
      (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
    have hjS := (Finset.mem_filter.1 hj).1
    split_ifs with hjG
    · gcongr
      exact Finset.single_le_sum (f := y) (fun _ _ => zero_le) (by simpa using hjG)
    · rw [hq0 j hjS (by simpa using hjG), zero_mul]
  have s2 : ∑ j ∈ AS.SN N, (if j ∈ (↑G : Set S) then q N i''.1 r j * Y else 0) = Y := by
    rw [← Finset.sum_filter, ← Finset.sum_mul, h2', one_mul]
  have s3 : Y ≤ 2 * A := by
    rw [hY, hy]
    simp only
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hA]
    have : 2 * A * ∑ g ∈ G, sdxPw Γ x (sdxInd AS N) g ≤ A := by
      calc 2 * A * ∑ g ∈ G, sdxPw Γ x (sdxInd AS N) g ≤ 2 * A * 2⁻¹ := by gcongr
        _ = A := by
          rw [mul_comm 2 A, mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
            mul_one]
    calc A + 2 * A * ∑ g ∈ G, sdxPw Γ x (sdxInd AS N) g ≤ A + A := add_le_add le_rfl this
      _ = 2 * A := (two_mul A).symm
  have s4 : 2 * A ≤ y r := by
    have ha : 1 ≤ sdxPw Γ x (sdxInd AS N) r := by
      rw [sdx_pw_first]
      refine le_trans ?_ le_self_add
      simp [sdxInd, hr]
    calc 2 * A = 2 * A * 1 := (mul_one _).symm
      _ ≤ 2 * A * sdxPw Γ x (sdxInd AS N) r := by gcongr
      _ ≤ y r := le_add_self
  calc _ ≤ _ := s1
    _ = Y := s2
    _ ≤ 2 * A := s3
    _ ≤ y r := s4

lemma sdx_squeeze (u v : ℕ → ℝ≥0∞) (x : ℝ≥0∞) (h1 : x ≤ liminf u atTop)
    (h2 : ∀ᶠ N in atTop, u N ≤ v N) (hv : Tendsto v atTop (𝓝 x)) : Tendsto u atTop (𝓝 x) := by
  refine tendsto_order.2 ⟨fun b hb => eventually_lt_of_lt_liminf (lt_of_lt_of_le hb h1), ?_⟩
  intro b hb
  filter_upwards [h2, (tendsto_order.1 hv).2 b hb] with N hN hN'
  exact lt_of_le_of_lt hN hN'

lemma sdx_tendsto {Γ : MC S} (AS : ApproxSeq Γ) (q : ℕ → S → S → S → ℝ≥0∞)
    (hq : AS.IsATASWith q) (G : Finset S) (hexcess : AS.SendsExcessTo q (↑G : Set S))
    (x : S) (w : S → ℝ≥0∞) (hw : ∀ k, w k ≠ ⊤) (hmG : ∀ g ∈ G, Γ.meanPassage {x} g < ⊤)
    (hpG : ∀ g ∈ G, sdxPw Γ x w g < ⊤) (i : S) (hmi : Γ.meanPassage {x} i < ⊤) :
    Tendsto (fun N => ∑' t, ∑' k, sdpAvN AS {x} t N i k * w k) atTop (𝓝 (sdxPw Γ x w i)) := by
  have hK : (2 * ∑ g ∈ G, sdxPw Γ x w g) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.2 fun g hg => ne_of_lt (hpG g hg))
  refine sdx_squeeze _ (fun N => sdxPw Γ x w i +
    (2 * ∑ g ∈ G, sdxPw Γ x w g) * sdxPw Γ x (sdxInd AS N) i) _
    (sdp_double_liminf AS {x} i w hw) ?_ ?_
  · filter_upwards [sdx_bound AS q hq G hexcess x w hmG, sdp_ev_mem AS i, sdp_ev_mem AS x]
      with N hN hi hx
    have := hN ⟨hi.1, hx.2⟩ ⟨i, hi.2⟩
    calc ∑' t, ∑' k, sdpAvN AS {x} t N i k * w k
        = ∑' t, ∑' k : AS.SN N, (AS.chain N hi.1).avoidProb (Subtype.val ⁻¹' {x}) t ⟨i, hi.2⟩ k
            * w k.1 := tsum_congr fun t => (sdp_inner_eq AS {x} t N i hi w).symm
      _ ≤ _ := this
  · have := (sdx_pw_tendsto_zero Γ x (fun N => sdxInd AS N) (sdxInd_le AS) (sdxInd_ev AS) i
      hmi)
    have := ENNReal.Tendsto.const_mul this (Or.inr hK)
    simpa using tendsto_const_nhds.add this

lemma sdx_chain_std {Γ : MC S} (AS : ApproxSeq Γ) (q : ℕ → S → S → S → ℝ≥0∞)
    (hq : AS.IsATASWith q) (G : Finset S) (hexcess : AS.SendsExcessTo q (↑G : Set S))
    (z : S) (hz : Γ.IsZStandard z) :
    ∀ᶠ N in atTop, ∃ h : AS.N₀ ≤ N ∧ z ∈ AS.SN N, ∀ i' : AS.SN N,
      (AS.chain N h.1).meanPassage (Subtype.val ⁻¹' {z}) i' < ⊤ ∧
      (AS.chain N h.1).passageCost (Subtype.val ⁻¹' {z}) i' < ⊤ := by
  have hmG : ∀ g ∈ G, Γ.meanPassage {z} g < ⊤ := fun g _ => (hz g).1
  have hK1 : (2 * ∑ g ∈ G, sdxPw Γ z (fun _ => 1) g) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.2 fun g hg => by
      rw [sdx_pw_one]; exact ne_of_lt (hz g).1)
  have hK2 : (2 * ∑ g ∈ G, sdxPw Γ z (fun k => (Γ.C k : ℝ≥0∞)) g) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.2 fun g hg => ne_of_lt (hz g).2)
  have ha : ∀ N j, sdxPw Γ z (sdxInd AS N) j < ⊤ := fun N j =>
    lt_of_le_of_lt (sdx_pw_le_mean Γ z _ (sdxInd_le AS N) j) (hz j).1
  filter_upwards [sdx_bound AS q hq G hexcess z (fun _ => 1) hmG,
    sdx_bound AS q hq G hexcess z (fun k => (Γ.C k : ℝ≥0∞)) hmG, sdp_ev_mem AS z]
    with N hb1 hb2 h
  refine ⟨h, fun i' => ⟨?_, ?_⟩⟩
  · have := hb1 h i'
    simp only [mul_one] at this
    refine lt_of_le_of_lt this (ENNReal.add_lt_top.2 ⟨?_, ENNReal.mul_lt_top hK1.lt_top (ha N _)⟩)
    rw [sdx_pw_one]; exact (hz _).1
  · have := hb2 h i'
    exact lt_of_le_of_lt this (ENNReal.add_lt_top.2 ⟨(hz _).2,
      ENNReal.mul_lt_top hK2.lt_top (ha N _)⟩)

theorem sdx_part1 [Countable S] (Γ : MC S) (z : S) (hz : Γ.IsZStandard z) (G : Finset S)
    (AS : ApproxSeq Γ) (q : ℕ → S → S → S → ℝ≥0∞) (hq : AS.IsATASWith q)
    (hexcess : AS.SendsExcessTo q (↑G : Set S)) : AS.IsConforming z := by
  have hmG : ∀ g ∈ G, Γ.meanPassage {z} g < ⊤ := fun g _ => (hz g).1
  refine ⟨hz, ?_, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨N1, hN1⟩ := eventually_atTop.1 (sdx_chain_std AS q hq G hexcess z hz)
    refine ⟨N1, fun N hN => ?_⟩
    obtain ⟨h, hb⟩ := hN1 N hN
    refine ⟨h, sdq_unichain _ _ (fun i' => ?_)⟩
    have hs : ({⟨z, h.2⟩} : Set (AS.SN N)) = Subtype.val ⁻¹' {z} := by
      ext x; simp [Subtype.ext_iff]
    rw [hs]
    exact (hb i').1
  · have := sdx_tendsto AS q hq G hexcess z (fun _ => 1) (fun _ => ENNReal.one_ne_top) hmG
      (fun g hg => by rw [sdx_pw_one]; exact hmG g hg) i (hz i).1
    rw [sdx_pw_one] at this
    exact this.congr' (Eventually.of_forall fun N => (sdp_meanPassageN_eq AS {z} N i).symm)
  · have := sdx_tendsto AS q hq G hexcess z (fun k => (Γ.C k : ℝ≥0∞))
      (fun _ => ENNReal.coe_ne_top) hmG (fun g hg => (hz g).2) i (hz i).1
    exact this.congr' (Eventually.of_forall fun N => (sdp_passageCostN_eq AS {z} N i).symm)


theorem sdx_part2 [Countable S] (Γ : MC S) (z : S) (hz : Γ.IsZStandard z) (G : Finset S)
    (AS : ApproxSeq Γ) (q : ℕ → S → S → S → ℝ≥0∞) (hq : AS.IsATASWith q)
    (hexcess : AS.SendsExcessTo q (↑G : Set S)) (hGR : (↑G : Set S) ⊆ Γ.commClass z) :
    AS.IsConformingOn (Γ.commClass z) := by
  obtain ⟨R', hR', hzR', -, hcac, -⟩ := MKX.zstd_core (sdxK Γ) Γ.C z (br_zstd Γ z hz)
  have hRR : R' = Γ.commClass z := by
    obtain ⟨⟨i0, hi0⟩, -⟩ := hR'
    rw [hi0] at hzR' ⊢
    rw [mkx_comm _ i0 z hzR', br_comm]
  subst hRR
  have hfin : ∀ i ∈ Γ.commClass z, ∀ j ∈ Γ.commClass z, Γ.meanPassage {j} i < ⊤ := by
    intro i hi j hj
    have := (MKX.first_passage_core (sdxK Γ) {z} (Set.singleton_nonempty z)).2.2.2.2 _ hR' i hi
      j hj
    rwa [br_mean _ _ (Set.singleton_nonempty j)] at this
  have conf := sdx_part1 Γ z hz G AS q hq hexcess
  refine ⟨⟨z, (hz z).1, rfl⟩, ?_, fun i hi => ⟨?_, ?_⟩⟩
  · rw [← br_cac]; exact hcac
  · have hmG : ∀ g ∈ G, Γ.meanPassage {i} g < ⊤ := fun g hg => hfin g (hGR hg) i hi
    have := sdx_tendsto AS q hq G hexcess i (fun _ => 1) (fun _ => ENNReal.one_ne_top) hmG
      (fun g hg => by rw [sdx_pw_one]; exact hmG g hg) i (hfin i hi i hi)
    rw [sdx_pw_one] at this
    have h2 : Tendsto (fun N => AS.meanPassageN {i} N i) atTop (𝓝 (Γ.meanPassage {i} i)) :=
      this.congr' (Eventually.of_forall fun N => (sdp_meanPassageN_eq AS {i} N i).symm)
    have h3 := tendsto_inv_iff.2 h2
    refine h3.congr' ?_
    filter_upwards [sdp_ev_mem AS i] with N hN
    unfold ApproxSeq.steadyStateN ApproxSeq.meanPassageN MC.steadyState
    rw [dif_pos hN, dif_pos hN]
    have hs : ({⟨i, hN.2⟩} : Set (AS.SN N)) = Subtype.val ⁻¹' {i} := by
      ext x; simp [Subtype.ext_iff]
    rw [hs]
  · have hJ : Γ.classAvgCost (Γ.commClass z) = Γ.passageCost {z} z / Γ.meanPassage {z} z := by
      have := (MKX.class_avg_core (sdxK Γ) Γ.C _ hR').2.1 z hzR'
      rwa [br_cac, br_pc _ _ (Set.singleton_nonempty z) _ (hz z).1,
        br_mean _ _ (Set.singleton_nonempty z)] at this
    rw [hJ]
    have hm0 : Γ.meanPassage {z} z ≠ 0 := by
      intro h0
      have := sdq_mp_first Γ {z} z
      rw [h0] at this
      exact absurd this.symm (ne_of_gt (lt_of_lt_of_le one_pos le_self_add))
    have hlim := ENNReal.Tendsto.div (conf.2.2 z).2 (Or.inr hm0) (conf.2.2 z).1
      (Or.inl (ne_of_lt (hz z).1))
    refine hlim.congr' ?_
    filter_upwards [sdx_chain_std AS q hq G hexcess z hz, sdp_ev_mem AS i] with N hstd hiN
    obtain ⟨h, hb⟩ := hstd
    have hs : ({⟨z, h.2⟩} : Set (AS.SN N)) = Subtype.val ⁻¹' {z} := by
      ext x; simp [Subtype.ext_iff]
    have hstdN : (AS.chain N h.1).IsZStandard ⟨z, h.2⟩ := by
      intro i'; rw [hs]; exact hb i'
    obtain ⟨RN, hRN, hzRN, -, -, hlimN⟩ :=
      MKX.zstd_core (sdxK (AS.chain N h.1)) (AS.chain N h.1).C ⟨z, h.2⟩ (br_zstd _ _ hstdN)
    have e1 := (MKX.class_avg_core (sdxK (AS.chain N h.1)) (AS.chain N h.1).C RN hRN).2.1 _ hzRN
    rw [br_pc _ _ (Set.singleton_nonempty _) _ (hstdN _).1,
      br_mean _ _ (Set.singleton_nonempty _)] at e1
    have e2 := br_avg (AS.chain N h.1) ⟨i, hiN.2⟩ _ (hlimN ⟨i, hiN.2⟩)
    have : AS.avgCostN N i = AS.passageCostN {z} N z / AS.meanPassageN {z} N z := by
      unfold ApproxSeq.avgCostN ApproxSeq.passageCostN ApproxSeq.meanPassageN
      rw [dif_pos hiN, dif_pos h, dif_pos h, ← hs]
      exact e2.trans e1
    exact this.symm

theorem atas_excess_core {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (z : S) (hz : Γ.IsZStandard z) (G : Finset S) (hG : G.Nonempty)
    (AS : ApproxSeq Γ) (q : ℕ → S → S → S → ℝ≥0∞) (hq : AS.IsATASWith q)
    (hexcess : AS.SendsExcessTo q (↑G : Set S)) :
    AS.IsConforming z ∧
      ((↑G : Set S) ⊆ Γ.commClass z → AS.IsConformingOn (Γ.commClass z)) :=
  ⟨sdx_part1 Γ z hz G AS q hq hexcess, fun h => sdx_part2 Γ z hz G AS q hq hexcess h⟩

end mine

end SennottDP.ChainASM

open SennottDP.ChainASM


theorem solution {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (z : S) (hz : Γ.IsZStandard z) (G : Finset S) (hG : G.Nonempty)
    (AS : ApproxSeq Γ) (q : ℕ → S → S → S → ℝ≥0∞) (hq : AS.IsATASWith q)
    (hexcess : AS.SendsExcessTo q (↑G : Set S)) :
    AS.IsConforming z ∧
      ((↑G : Set S) ⊆ Γ.commClass z → AS.IsConformingOn (Γ.commClass z)) := by
  exact atas_excess_core Γ z hz G hG AS q hq hexcess
