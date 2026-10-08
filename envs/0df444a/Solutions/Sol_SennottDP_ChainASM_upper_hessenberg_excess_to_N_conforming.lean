-- Prove2me | solution 1 for SennottDP.ChainASM.upper_hessenberg_excess_to_N_conforming
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T19:57:06.028171+00:00
-- url     : https://prove2.me/submissions/83b058f2-3c7b-4d13-a332-aca5ed60b867

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


lemma sdh_mono (Γ : MC ℕ) (hHess : ∀ i j : ℕ, 2 ≤ i → j + 1 < i → Γ.P i j = 0)
    (N : ℕ) (hN : 1 ≤ N) (w : ℕ → ℝ≥0∞)
    (hfin : ∑' t, ∑' k, Γ.avoidProb {0} t N k * w k ≠ ⊤)
    (hm : ∀ r, Γ.meanPassage {0} r < ⊤) (r : ℕ) (hr : N < r) :
    ∑' t, ∑' k, Γ.avoidProb {0} t N k * w k ≤ ∑' t, ∑' k, Γ.avoidProb {0} t r k * w k := by
  set V : ℕ → ℝ≥0∞ := fun i => ∑' t, ∑' k, Γ.avoidProb {0} t i k * w k with hV
  set a : ℕ → ℕ → ℝ≥0∞ := fun n j => ∑' k, Γ.avoidProb {N} n j k with ha
  set b : ℕ → ℕ → ℝ≥0∞ := fun n j => ∑' k, Γ.avoidProb {0} n j k with hb
  have hP0 : ∀ j, N < j → ∀ l, l < N → Γ.P j l = 0 := fun j hj l hl => hHess j l (by omega) (by omega)
  have h0sum : ∀ (G : Set ℕ) j, ∑' k, Γ.avoidProb G 0 j k = 1 := by
    intro G j
    simp only [MC.avoidProb, if_true]
    rw [tsum_eq_single j]
    · simp
    · intro k hk; simp [Ne.symm hk]
  have hsucc : ∀ (G : Set ℕ) n j, ∑' k, Γ.avoidProb G (n + 1) j k =
      ∑' l, if l ∈ G then 0 else Γ.P j l * ∑' k, Γ.avoidProb G n l k := by
    intro G n j
    have := sdq_step_t Γ G (fun _ => 1) n j
    simpa using this
  have hab : ∀ n j, N < j → a n j ≤ b n j := by
    intro n
    induction n with
    | zero => intro j _; simp only [ha, hb, h0sum]; exact le_rfl
    | succ n ih =>
      intro j hj
      simp only [ha, hb] at ih ⊢
      rw [hsucc, hsucc]
      refine ENNReal.tsum_le_tsum fun l => ?_
      rcases lt_trichotomy l N with hl | hl | hl
      · simp [hP0 j hj l hl]
      · simp [hl]
      · have hl0 : l ≠ 0 := by omega
        have hlN : l ≠ N := by omega
        simp only [Set.mem_singleton_iff, hl0, hlN, if_false]
        exact mul_le_mul_right (ih l hl) _
  have hkey : ∀ n r, N < r → V N ≤ V r + V N * a n r := by
    intro n
    induction n with
    | zero =>
      intro r _
      simp only [ha, h0sum, mul_one]
      exact le_add_self
    | succ n ih =>
      intro r hr
      have e1 : V r = w r + ∑' l, if l ∈ ({0} : Set ℕ) then 0 else Γ.P r l * V l :=
        by convert sdq_first_step Γ {0} w r
      have e2 : a (n + 1) r = ∑' l, if l ∈ ({N} : Set ℕ) then 0 else Γ.P r l * a n l :=
        by convert hsucc {N} n r
      rw [e1, e2, ← ENNReal.tsum_mul_left]
      calc V N = ∑' l, Γ.P r l * V N := by rw [ENNReal.tsum_mul_right, Γ.P_sum, one_mul]
        _ ≤ ∑' l, ((if l ∈ ({0} : Set ℕ) then 0 else Γ.P r l * V l) +
              V N * (if l ∈ ({N} : Set ℕ) then 0 else Γ.P r l * a n l)) := by
          refine ENNReal.tsum_le_tsum fun l => ?_
          rcases lt_trichotomy l N with hl | hl | hl
          · simp [hP0 r hr l hl]
          · have : N ≠ 0 := by omega
            subst hl; simp [this]
          · have hl0 : l ≠ 0 := by omega
            have hlN : l ≠ N := by omega
            simp only [Set.mem_singleton_iff, hl0, hlN, if_false]
            calc Γ.P r l * V N ≤ Γ.P r l * (V l + V N * a n l) := mul_le_mul_right (ih l hl) _
              _ = _ := by ring
        _ ≤ _ := by rw [ENNReal.tsum_add, add_assoc]; exact le_add_self
  have hbt : Tendsto (fun n => b n r) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top (by
      have := (hm r).ne
      simpa [MC.meanPassage] using this)
  have hat : Tendsto (fun n => a n r) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbt (fun n => bot_le)
      (fun n => hab n r hr)
  have hlim : Tendsto (fun n => V r + V N * a n r) atTop (𝓝 (V r + V N * 0)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.const_mul hat (Or.inr hfin))
  rw [mul_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim (fun n => hkey n r hr)


theorem upper_hessenberg_core
    (Γ : MC ℕ) (hz : Γ.IsZStandard 0)
    (hHess : ∀ i j : ℕ, 2 ≤ i → j + 1 < i → Γ.P i j = 0)
    (AS : ApproxSeq Γ) (hN₀ : 1 ≤ AS.N₀)
    (hSN : ∀ N, AS.N₀ ≤ N → AS.SN N = Finset.range (N + 1))
    (q : ℕ → ℕ → ℕ → ℕ → ℝ≥0∞) (hq : AS.IsATASWith q)
    (hexcess : ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ r, r ∉ AS.SN N → q N i r N = 1) :
    AS.IsConforming 0 := by
  have hsum : ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ r, r ∉ AS.SN N → ∀ V : ℕ → ℝ≥0∞,
      ∑ j ∈ (AS.SN N).filter (· ≠ 0), q N i r j * V j = V N := by
    intro N hN i hi r hr V
    have hNS : N ∈ AS.SN N := by rw [hSN N hN]; simp
    have hN0 : N ≠ 0 := by omega
    have hq1 := hq.1 N hN i hi r hr
    rw [← Finset.add_sum_erase _ _ hNS, hexcess N hN i hi r hr] at hq1
    have hrest : ∀ j ∈ (AS.SN N).erase N, q N i r j = 0 := by
      have : ∑ x ∈ (AS.SN N).erase N, q N i r x = 0 := by
        have h2 : (1 : ℝ≥0∞) + ∑ x ∈ (AS.SN N).erase N, q N i r x = 1 + 0 := by
          rw [add_zero]; exact hq1
        exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 h2
      exact Finset.sum_eq_zero_iff.1 this
    rw [Finset.sum_eq_single N]
    · rw [hexcess N hN i hi r hr, one_mul]
    · intro j hj hjN
      rw [hrest j (Finset.mem_erase.2 ⟨hjN, (Finset.mem_filter.1 hj).1⟩), zero_mul]
    · intro h; exact absurd (Finset.mem_filter.2 ⟨hNS, hN0⟩) h
  have hrN : ∀ N, AS.N₀ ≤ N → ∀ r, r ∉ AS.SN N → N < r := by
    intro N hN r hr
    rw [hSN N hN, Finset.mem_range] at hr; omega
  have hmp : ∀ r, Γ.meanPassage {0} r < ⊤ := fun r => (hz r).1
  refine atas_structural_conforming_core Γ 0 hz AS q hq AS.N₀ ?_ ?_
  · intro N _ hN i hi r hr
    refine (show _ = Γ.meanPassage {0} N by
      convert hsum N hN i hi r hr (fun j => Γ.meanPassage {0} j)).trans_le ?_
    have e : ∀ j, Γ.meanPassage {0} j = ∑' t, ∑' k, Γ.avoidProb {0} t j k * (fun _ => (1 : ℝ≥0∞)) k := by
      intro j; simp [MC.meanPassage]
    rw [e, e]
    exact sdh_mono Γ hHess N (by omega) _ (by rw [← e]; exact (hmp N).ne) hmp r (hrN N hN r hr)
  · intro N _ hN i hi r hr
    refine (show _ = Γ.passageCost {0} N by
      convert hsum N hN i hi r hr (fun j => Γ.passageCost {0} j)).trans_le ?_
    exact sdh_mono Γ hHess N (by omega) _ (hz N).2.ne hmp r (hrN N hN r hr)

end SennottDP.ChainASM

open SennottDP.ChainASM


theorem solution
    (Γ : MC ℕ) (hz : Γ.IsZStandard 0)
    (hHess : ∀ i j : ℕ, 2 ≤ i → j + 1 < i → Γ.P i j = 0)
    (AS : ApproxSeq Γ) (hN₀ : 1 ≤ AS.N₀)
    (hSN : ∀ N, AS.N₀ ≤ N → AS.SN N = Finset.range (N + 1))
    (q : ℕ → ℕ → ℕ → ℕ → ℝ≥0∞) (hq : AS.IsATASWith q)
    (hexcess : ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ r, r ∉ AS.SN N → q N i r N = 1) :
    AS.IsConforming 0 := by
  exact upper_hessenberg_core Γ hz hHess AS hN₀ hSN q hq hexcess
