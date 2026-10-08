-- Prove2me | solution 1 for SennottDP.ChainASM.as_taboo_visits_passage_limits
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T19:45:59.438319+00:00
-- url     : https://prove2.me/submissions/8a64938f-aa10-462c-9ad2-1bb68b715c35

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

end SennottDP.ChainASM

open SennottDP.ChainASM


theorem solution {S : Type*} [Countable S] [Infinite S]
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
  exact as_taboo_visits_passage_limits_core Γ AS G hG
