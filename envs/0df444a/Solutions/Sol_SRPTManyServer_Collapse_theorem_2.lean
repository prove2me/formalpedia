-- Prove2me | solution 1 for SRPTManyServer.Collapse.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:20:17.093874+00:00
-- url     : https://prove2.me/submissions/4a601f5e-04b9-4d52-ad15-7a9b69f358dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SRPTManyServer_Collapse_Model
import Theorems.Thm_SRPTManyServer_Collapse_theorem_2_a
import Theorems.Thm_SRPTManyServer_Collapse_theorem_2_b_short


open MeasureTheory ProbabilityTheory Filter Topology Finset SRPTManyServer.Collapse

/-- running average -/
lemma srptC_classAvg_avg (c : ℕ → Prop) (f g I : ℕ → ℝ) (v ν : ℝ)
    (hI : ∀ n, (c n → I n = 1) ∧ (¬ c n → I n = 0))
    (hg : ∀ n, (c n → g n = f n) ∧ (¬ c n → g n = 0))
    (h1 : Tendsto (fun N => classAvg N c f) atTop (𝓝 v))
    (h2 : Tendsto (fun N : ℕ => (∑ n ∈ range N, I n) / N) atTop (𝓝 ν)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, g n) / N) atTop (𝓝 (v * ν)) := by
  classical
  refine (h1.mul h2).congr (fun N => ?_)
  unfold classAvg
  have hsg : ∑ n ∈ range N, g n = ∑ n ∈ (range N).filter c, f n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : c n
    · rw [if_pos h, (hg n).1 h]
    · rw [if_neg h, (hg n).2 h]
  have hsI : ∑ n ∈ range N, I n = (((range N).filter c).card : ℝ) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : c n
    · rw [if_pos h, (hI n).1 h]; norm_num
    · rw [if_neg h, (hI n).2 h]; norm_num
  rw [hsg, hsI]
  have hfilt : ∀ inst : DecidablePred c,
      ((@Finset.filter ℕ c inst (range N)).card : ℝ) = (((range N).filter c).card : ℝ) := by
    intro inst; congr 2
  have hfilt2 : ∀ inst : DecidablePred c,
      ∑ n ∈ @Finset.filter ℕ c inst (range N), f n = ∑ n ∈ (range N).filter c, f n := by
    intro inst; congr 1
  rw [hfilt, hfilt2]
  set k : ℝ := (((range N).filter c).card : ℝ)
  set a : ℝ := ∑ n ∈ (range N).filter c, f n
  by_cases hk : k = 0
  · have hempty : (range N).filter c = ∅ := by
      have : ((range N).filter c).card = 0 := by simpa [k] using hk
      exact Finset.card_eq_zero.mp this
    have : a = 0 := by simp only [a, hempty, Finset.sum_empty]
    rw [this, hk]; simp
  · by_cases hN : (N : ℝ) = 0
    · have : N = 0 := by exact_mod_cast hN
      subst this
      simp [k] at hk
    · field_simp

/-- squeeze with a free truncation level -/
lemma srptC_squeeze (u : ℕ → ℝ) (L : ℝ) (α β : ℕ → ℕ → ℝ) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (hα : ∀ K, Tendsto (α K) atTop (𝓝 0)) (hβ : ∀ K, Tendsto (β K) atTop (𝓝 0))
    (hb : ∀ K s, 1 ≤ s → L - α K s - e K ≤ u s ∧ u s ≤ L + β K s + e K) :
    Tendsto u atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h3 : 0 < ε / 3 := by positivity
  obtain ⟨K, hK0⟩ := Metric.tendsto_atTop.mp he (ε / 3) h3
  have hK := hK0 K le_rfl
  obtain ⟨Na, hNa⟩ := Metric.tendsto_atTop.mp (hα K) (ε / 3) h3
  obtain ⟨Nb, hNb⟩ := Metric.tendsto_atTop.mp (hβ K) (ε / 3) h3
  refine ⟨max 1 (max Na Nb), fun s hs => ?_⟩
  have hs1 : 1 ≤ s := le_trans (le_max_left _ _) hs
  have hsa : Na ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hsb : Nb ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  have ha := hNa s hsa
  have hb' := hNb s hsb
  rw [Real.dist_eq, sub_zero] at ha hb' hK
  obtain ⟨hl, hu⟩ := hb K s hs1
  rw [Real.dist_eq, abs_lt]
  constructor
  · have := (abs_lt.mp ha).2; have := (abs_lt.mp hK).2; linarith
  · have := (abs_lt.mp hb').2; have := (abs_lt.mp hK).2; linarith

noncomputable def srptAvg (f : ℕ → ℝ) (N : ℕ) : ℝ := (∑ n ∈ range N, f n) / N

lemma srptAvg_add (f g : ℕ → ℝ) (N : ℕ) :
    srptAvg (fun n => f n + g n) N = srptAvg f N + srptAvg g N := by
  unfold srptAvg; rw [Finset.sum_add_distrib, add_div]

lemma srptAvg_sub (f g : ℕ → ℝ) (N : ℕ) :
    srptAvg (fun n => f n - g n) N = srptAvg f N - srptAvg g N := by
  unfold srptAvg; rw [Finset.sum_sub_distrib, sub_div]

lemma srptAvg_mul (c : ℝ) (f : ℕ → ℝ) (N : ℕ) :
    srptAvg (fun n => c * f n) N = c * srptAvg f N := by
  unfold srptAvg; rw [← Finset.mul_sum, mul_div_assoc]

lemma srptAvg_one : Tendsto (srptAvg (fun _ => (1:ℝ))) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  unfold srptAvg
  have : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp [this]

lemma srptAvg_le {f g : ℕ → ℝ} (hle : ∀ n, f n ≤ g n) {a b : ℝ}
    (hf : Tendsto (srptAvg f) atTop (𝓝 a)) (hg : Tendsto (srptAvg g) atTop (𝓝 b)) : a ≤ b := by
  refine le_of_tendsto_of_tendsto' hf hg (fun N => ?_)
  unfold srptAvg
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun n _ => hle n)) (Nat.cast_nonneg N)

lemma srptAvg_tendsto_eq {f g : ℕ → ℝ} (h : ∀ n, f n = g n) {a : ℝ}
    (hf : Tendsto (srptAvg f) atTop (𝓝 a)) : Tendsto (srptAvg g) atTop (𝓝 a) := by
  have : f = g := funext h
  rwa [← this]

lemma srptC_core (Sx Tx : ℕ → ℝ) (tau θ G : ℝ) (e : ℕ → ℝ)
    (C : ℕ → ℕ → Prop) (I W : ℕ → ℕ → ℝ)
    (pServ1 pServ2 wServ w1 wAb w2 wAll : ℕ → ℝ)
    (hG0 : 0 < G) (hG1 : G < 1)
    (hT : ∀ n, 0 ≤ Tx n)
    (hI : ∀ s n, (C s n → I s n = 1) ∧ (¬ C s n → I s n = 0))
    (hW : ∀ s, 1 ≤ s → ∀ n, 0 ≤ W s n ∧ W s n ≤ Tx n ∧ (¬ C s n → W s n = Tx n))
    (hB1 : Tendsto (srptAvg (fun n => if Sx n ≤ tau then (1:ℝ) else 0)) atTop (𝓝 G))
    (hB2 : Tendsto (srptAvg (fun n => if tau < Sx n then Tx n else 0)) atTop (𝓝 ((1 - G) / θ)))
    (hB3 : ∀ K : ℕ, Tendsto (srptAvg (fun n => if (K:ℝ) < Tx n then Tx n else 0)) atTop
      (𝓝 (e K)))
    (he : Tendsto e atTop (𝓝 0))
    (h_pServ1 : ∀ s, 1 ≤ s → Tendsto (fun N => classAvg N (fun n => Sx n ≤ tau) (I s)) atTop
      (𝓝 (pServ1 s)))
    (h_pServ2 : ∀ s, 1 ≤ s → Tendsto (fun N => classAvg N (fun n => tau < Sx n) (I s)) atTop
      (𝓝 (pServ2 s)))
    (h_wServ : ∀ s, 1 ≤ s → Tendsto (fun N => classAvg N (C s) (W s)) atTop (𝓝 (wServ s)))
    (h_w1 : ∀ s, 1 ≤ s → Tendsto (fun N => classAvg N (fun n => Sx n ≤ tau) (W s)) atTop
      (𝓝 (w1 s)))
    (h_wAb : ∀ s, 1 ≤ s → Tendsto (fun N => classAvg N (fun n => ¬ C s n) (W s)) atTop
      (𝓝 (wAb s)))
    (h_w2 : ∀ s, 1 ≤ s → Tendsto (fun N => classAvg N (fun n => tau < Sx n) (W s)) atTop
      (𝓝 (w2 s)))
    (h_wAll : ∀ s, 1 ≤ s → Tendsto (fun N => classAvg N (fun _ => True) (W s)) atTop
      (𝓝 (wAll s)))
    (hp1 : Tendsto pServ1 atTop (𝓝 1)) (hp2 : Tendsto pServ2 atTop (𝓝 0))
    (hw1 : Tendsto w1 atTop (𝓝 0)) :
    Tendsto wServ atTop (𝓝 0) ∧ Tendsto wAb atTop (𝓝 (1 / θ)) ∧
      Tendsto w2 atTop (𝓝 (1 / θ)) ∧ Tendsto wAll atTop (𝓝 ((1 - G) / θ)) := by
  classical
  have hcase : ∀ n, (Sx n ≤ tau ∧ ¬ tau < Sx n) ∨ (¬ Sx n ≤ tau ∧ tau < Sx n) := by
    intro n
    by_cases h' : Sx n ≤ tau
    · exact Or.inl ⟨h', not_lt.mpr h'⟩
    · exact Or.inr ⟨h', lt_of_not_ge h'⟩
  -- the long-job indicator
  have hL : Tendsto (srptAvg (fun n => if tau < Sx n then (1:ℝ) else 0)) atTop (𝓝 (1 - G)) := by
    have h := srptAvg_one.sub hB1
    refine h.congr (fun N => ?_)
    rw [← srptAvg_sub]
    congr 1; funext n
    rcases hcase n with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have hTe : ∀ K : ℕ, ∀ n, 0 ≤ (if (K:ℝ) < Tx n then Tx n else 0) := by
    intro K n; split_ifs <;> simp [hT n]
  have he0 : ∀ K : ℕ, 0 ≤ e K := by
    intro K
    refine ge_of_tendsto' (hB3 K) (fun N => ?_)
    unfold srptAvg
    exact div_nonneg (Finset.sum_nonneg (fun n _ => hTe K n)) (Nat.cast_nonneg N)
  have hI01 : ∀ s n, (I s n = 1 ∧ C s n) ∨ (I s n = 0 ∧ ¬ C s n) := by
    intro s n
    by_cases hc : C s n
    · exact Or.inl ⟨(hI s n).1 hc, hc⟩
    · exact Or.inr ⟨(hI s n).2 hc, hc⟩
  -- per-system relations
  have key : ∀ s, 1 ≤ s →
      wAll s = w1 s * G + w2 s * (1 - G) ∧
      (∀ K : ℕ, (1 - G) / θ - K * (pServ2 s * (1 - G)) - e K ≤ w2 s * (1 - G) ∧
        w2 s * (1 - G) ≤ (1 - G) / θ + 0 + e K) ∧
      (∀ K : ℕ, (1 - G) / θ - K * (pServ2 s * (1 - G)) - e K ≤
          wAb s * (1 - (pServ1 s * G + pServ2 s * (1 - G))) ∧
        wAb s * (1 - (pServ1 s * G + pServ2 s * (1 - G))) ≤
          (1 - G) / θ + K * (G - pServ1 s * G) + e K) ∧
      (∀ K : ℕ, 0 - 0 - e K ≤ wServ s * (pServ1 s * G + pServ2 s * (1 - G)) ∧
        wServ s * (pServ1 s * G + pServ2 s * (1 - G)) ≤
          0 + (w1 s * G + K * (pServ2 s * (1 - G))) + e K) := by
    intro s hs
    have hWs := hW s hs
    have P1 : Tendsto (srptAvg (fun n => if Sx n ≤ tau then I s n else 0)) atTop
        (𝓝 (pServ1 s * G)) :=
      srptC_classAvg_avg _ (I s) _ _ _ _ (fun n => by split_ifs <;> simp_all)
        (fun n => by split_ifs <;> simp_all) (h_pServ1 s hs) hB1
    have P2 : Tendsto (srptAvg (fun n => if tau < Sx n then I s n else 0)) atTop
        (𝓝 (pServ2 s * (1 - G))) :=
      srptC_classAvg_avg _ (I s) _ _ _ _ (fun n => by split_ifs <;> simp_all)
        (fun n => by split_ifs <;> simp_all) (h_pServ2 s hs) hL
    have Q1 : Tendsto (srptAvg (fun n => if Sx n ≤ tau then W s n else 0)) atTop
        (𝓝 (w1 s * G)) :=
      srptC_classAvg_avg _ (W s) _ _ _ _ (fun n => by split_ifs <;> simp_all)
        (fun n => by split_ifs <;> simp_all) (h_w1 s hs) hB1
    have Q2 : Tendsto (srptAvg (fun n => if tau < Sx n then W s n else 0)) atTop
        (𝓝 (w2 s * (1 - G))) :=
      srptC_classAvg_avg _ (W s) _ _ _ _ (fun n => by split_ifs <;> simp_all)
        (fun n => by split_ifs <;> simp_all) (h_w2 s hs) hL
    have Qall : Tendsto (srptAvg (W s)) atTop (𝓝 (wAll s * 1)) :=
      srptC_classAvg_avg (fun _ => True) (W s) (W s) (fun _ => 1) _ _ (fun n => by simp)
        (fun n => by simp) (h_wAll s hs) srptAvg_one
    have Cnt : Tendsto (srptAvg (I s)) atTop
        (𝓝 (pServ1 s * G + pServ2 s * (1 - G))) := by
      refine (P1.add P2).congr (fun N => ?_)
      rw [← srptAvg_add]; congr 1; funext n
      rcases hcase n with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
    have QS : Tendsto (srptAvg (fun n => I s n * W s n)) atTop
        (𝓝 (wServ s * (pServ1 s * G + pServ2 s * (1 - G)))) :=
      srptC_classAvg_avg (C s) (W s) _ (I s) _ _ (hI s)
        (fun n => by rcases hI01 s n with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all)
        (h_wServ s hs) Cnt
    have Dcnt : Tendsto (srptAvg (fun n => 1 - I s n)) atTop
        (𝓝 (1 - (pServ1 s * G + pServ2 s * (1 - G)))) := by
      refine (srptAvg_one.sub Cnt).congr (fun N => ?_)
      rw [← srptAvg_sub]
    have QA : Tendsto (srptAvg (fun n => (1 - I s n) * W s n)) atTop
        (𝓝 (wAb s * (1 - (pServ1 s * G + pServ2 s * (1 - G))))) :=
      srptC_classAvg_avg (fun n => ¬ C s n) (W s) _ (fun n => 1 - I s n) _ _
        (fun n => by rcases hI01 s n with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all)
        (fun n => by rcases hI01 s n with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all) (h_wAb s hs) Dcnt
    have hlow : ∀ K : ℕ, Tendsto (srptAvg (fun n => (if tau < Sx n then Tx n else 0)
        - (K:ℝ) * (if tau < Sx n then I s n else 0)
        - (if (K:ℝ) < Tx n then Tx n else 0))) atTop
        (𝓝 ((1 - G) / θ - K * (pServ2 s * (1 - G)) - e K)) := by
      intro K
      refine ((hB2.sub (P2.const_mul (K:ℝ))).sub (hB3 K)).congr (fun N => ?_)
      rw [srptAvg_sub, srptAvg_sub, srptAvg_mul]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h := Q1.add Q2
      have h' : Tendsto (srptAvg (W s)) atTop (𝓝 (w1 s * G + w2 s * (1 - G))) := by
        refine h.congr (fun N => ?_)
        rw [← srptAvg_add]; congr 1; funext n
        rcases hcase n with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
      have := tendsto_nhds_unique Qall h'
      linarith
    · intro K
      have hK0 : (0:ℝ) ≤ K := Nat.cast_nonneg K
      constructor
      · refine srptAvg_le (fun n => ?_) (hlow K) Q2
        obtain ⟨hW0, hWT, hWab⟩ := hWs n
        have hTK := hTe K n
        rcases hcase n with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp only [if_neg h2]; linarith
        · simp only [if_pos h2]
          rcases hI01 s n with ⟨hi, hc⟩ | ⟨hi, hc⟩
          · rw [hi]
            split_ifs with h3
            · linarith
            · push_neg at h3; linarith
          · rw [hi, hWab hc]; linarith
      · have hup : w2 s * (1 - G) ≤ (1 - G) / θ :=
          srptAvg_le (fun n => by
            obtain ⟨hW0, hWT, hWab⟩ := hWs n
            split_ifs <;> linarith) Q2 hB2
        linarith [he0 K]
    · intro K
      have hK0 : (0:ℝ) ≤ K := Nat.cast_nonneg K
      constructor
      · refine srptAvg_le (fun n => ?_) (hlow K) QA
        obtain ⟨hW0, hWT, hWab⟩ := hWs n
        have hTK := hTe K n
        have hTn := hT n
        rcases hI01 s n with ⟨hi, hc⟩ | ⟨hi, hc⟩
        · rw [hi]
          rcases hcase n with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [if_neg h2]; linarith
          · simp only [if_pos h2]
            split_ifs with h3
            · linarith
            · push_neg at h3; linarith
        · rw [hi, hWab hc]
          rcases hcase n with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [if_neg h2]; linarith
          · simp only [if_pos h2]; linarith
      · have hupper : Tendsto (srptAvg (fun n => (if tau < Sx n then Tx n else 0)
            + (K:ℝ) * ((if Sx n ≤ tau then (1:ℝ) else 0) - (if Sx n ≤ tau then I s n else 0))
            + (if (K:ℝ) < Tx n then Tx n else 0))) atTop
            (𝓝 ((1 - G) / θ + K * (G - pServ1 s * G) + e K)) := by
          refine ((hB2.add ((hB1.sub P1).const_mul (K:ℝ))).add (hB3 K)).congr (fun N => ?_)
          rw [srptAvg_add, srptAvg_add, srptAvg_mul, srptAvg_sub]
        refine srptAvg_le (fun n => ?_) QA hupper
        obtain ⟨hW0, hWT, hWab⟩ := hWs n
        have hTK := hTe K n
        have hTn := hT n
        rcases hI01 s n with ⟨hi, hc⟩ | ⟨hi, hc⟩
        · rw [hi]
          rcases hcase n with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [if_neg h2, if_pos h1]; linarith
          · simp only [if_pos h2, if_neg h1]; linarith
        · rw [hi, hWab hc]
          rcases hcase n with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [if_neg h2, if_pos h1]
            split_ifs with h3
            · linarith
            · push_neg at h3; linarith
          · simp only [if_pos h2, if_neg h1]; linarith
    · intro K
      have hK0 : (0:ℝ) ≤ K := Nat.cast_nonneg K
      constructor
      · have : 0 ≤ wServ s * (pServ1 s * G + pServ2 s * (1 - G)) :=
          ge_of_tendsto' QS (fun N => by
            unfold srptAvg
            refine div_nonneg (Finset.sum_nonneg (fun n _ => ?_)) (Nat.cast_nonneg N)
            obtain ⟨hW0, hWT, hWab⟩ := hWs n
            rcases hI01 s n with ⟨hi, hc⟩ | ⟨hi, hc⟩ <;> rw [hi] <;> linarith)
        linarith [he0 K]
      · have hupper : Tendsto (srptAvg (fun n => (if Sx n ≤ tau then W s n else 0)
            + (K:ℝ) * (if tau < Sx n then I s n else 0)
            + (if (K:ℝ) < Tx n then Tx n else 0))) atTop
            (𝓝 (0 + (w1 s * G + K * (pServ2 s * (1 - G))) + e K)) := by
          rw [zero_add]
          refine ((Q1.add (P2.const_mul (K:ℝ))).add (hB3 K)).congr (fun N => ?_)
          rw [srptAvg_add, srptAvg_add, srptAvg_mul]
        refine srptAvg_le (fun n => ?_) QS hupper
        obtain ⟨hW0, hWT, hWab⟩ := hWs n
        have hTK := hTe K n
        rcases hI01 s n with ⟨hi, hc⟩ | ⟨hi, hc⟩
        · rw [hi]
          rcases hcase n with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [if_neg h2, if_pos h1]; linarith
          · simp only [if_pos h2, if_neg h1]
            split_ifs with h3
            · linarith
            · push_neg at h3; linarith
        · rw [hi]
          rcases hcase n with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [if_neg h2, if_pos h1]; linarith
          · simp only [if_pos h2, if_neg h1]; linarith
  -- limits as s → ∞
  have hG1' : (0:ℝ) < 1 - G := by linarith
  have hq : Tendsto (fun s => pServ1 s * G + pServ2 s * (1 - G)) atTop (𝓝 G) := by
    have := (hp1.mul_const G).add (hp2.mul_const (1 - G))
    simpa using this
  have hd : Tendsto (fun s => 1 - (pServ1 s * G + pServ2 s * (1 - G))) atTop (𝓝 (1 - G)) :=
    tendsto_const_nhds.sub hq
  have hα : ∀ K : ℕ, Tendsto (fun s => (K:ℝ) * (pServ2 s * (1 - G))) atTop (𝓝 0) := by
    intro K
    have := (hp2.mul_const (1 - G)).const_mul (K:ℝ)
    simpa using this
  -- w2
  have hu2 : Tendsto (fun s => w2 s * (1 - G)) atTop (𝓝 ((1 - G) / θ)) :=
    srptC_squeeze _ _ (fun K s => (K:ℝ) * (pServ2 s * (1 - G))) (fun _ _ => 0) e he hα
      (fun _ => tendsto_const_nhds) (fun K s hs => (key s hs).2.1 K)
  have hw2 : Tendsto w2 atTop (𝓝 (1 / θ)) := by
    have := hu2.div_const (1 - G)
    have e1 : (1 - G) / θ / (1 - G) = 1 / θ := by field_simp
    rw [e1] at this
    refine this.congr (fun s => ?_)
    field_simp
  -- wAll
  have hwAll : Tendsto wAll atTop (𝓝 ((1 - G) / θ)) := by
    have := (hw1.mul_const G).add (hw2.mul_const (1 - G))
    have e1 : 0 * G + 1 / θ * (1 - G) = (1 - G) / θ := by ring
    rw [e1] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with s hs
    exact ((key s hs).1).symm
  -- wAb
  have huA : Tendsto (fun s => wAb s * (1 - (pServ1 s * G + pServ2 s * (1 - G)))) atTop
      (𝓝 ((1 - G) / θ)) := by
    refine srptC_squeeze _ _ (fun K s => (K:ℝ) * (pServ2 s * (1 - G)))
      (fun K s => (K:ℝ) * (G - pServ1 s * G)) e he hα (fun K => ?_)
      (fun K s hs => (key s hs).2.2.1 K)
    have := ((tendsto_const_nhds (x := G)).sub (hp1.mul_const G)).const_mul (K:ℝ)
    simpa using this
  have hwAb : Tendsto wAb atTop (𝓝 (1 / θ)) := by
    have := huA.div hd hG1'.ne'
    have e1 : (1 - G) / θ / (1 - G) = 1 / θ := by field_simp
    rw [e1] at this
    refine this.congr' ?_
    filter_upwards [hd.eventually (lt_mem_nhds hG1')] with s hs
    rw [Pi.div_apply]; exact mul_div_cancel_right₀ _ hs.ne'
  -- wServ
  have huS : Tendsto (fun s => wServ s * (pServ1 s * G + pServ2 s * (1 - G))) atTop (𝓝 0) := by
    refine srptC_squeeze _ _ (fun _ _ => 0)
      (fun K s => w1 s * G + (K:ℝ) * (pServ2 s * (1 - G))) e he
      (fun _ => tendsto_const_nhds) (fun K => ?_) (fun K s hs => (key s hs).2.2.2 K)
    have := (hw1.mul_const G).add (hα K)
    simpa using this
  have hwS : Tendsto wServ atTop (𝓝 0) := by
    have := huS.div hq hG0.ne'
    rw [zero_div] at this
    refine this.congr' ?_
    filter_upwards [hq.eventually (lt_mem_nhds hG0)] with s hs
    rw [Pi.div_apply]; exact mul_div_cancel_right₀ _ hs.ne'
  exact ⟨hwS, hwAb, hw2, hwAll⟩


open MeasureTheory ProbabilityTheory Filter Topology Set SRPTManyServer.Collapse

section PartA

variable (s : ℕ) (x : SRPTManyServer.Collapse.Stream) (δ : ℕ → ℝ → ℝ)

lemma srptA_ii (hδ : IsSRPTSchedule s x δ) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (δ n) volume a b := by
  refine intervalIntegrable_const (c := (1:ℝ)) |>.mono_fun (hδ.2.1 n).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun u => ?_)
  rcases hδ.1 n u with h | h <;> simp [h]

lemma srptA_ii' (hδ : IsSRPTSchedule s x δ) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun u => 1 - δ n u) volume a b :=
  intervalIntegrable_const.sub (srptA_ii s x δ hδ n a b)

lemma srptA_served_cont (hδ : IsSRPTSchedule s x δ) (n : ℕ) :
    Continuous (fun t => served x δ n t) :=
  intervalIntegral.continuous_primitive (fun a b => srptA_ii s x δ hδ n a b) _

lemma srptA_queued_cont (hδ : IsSRPTSchedule s x δ) (n : ℕ) :
    Continuous (fun t => queued x δ n t) := by
  unfold queued
  exact (continuous_id.sub continuous_const).sub (srptA_served_cont s x δ hδ n)

lemma srptA_queued_diff (hδ : IsSRPTSchedule s x δ) (n : ℕ) (a b : ℝ) :
    queued x δ n b - queued x δ n a = ∫ u in a..b, (1 - δ n u) := by
  unfold queued served
  rw [intervalIntegral.integral_sub intervalIntegrable_const (srptA_ii s x δ hδ n a b)]
  have := intervalIntegral.integral_interval_sub_left (srptA_ii s x δ hδ n (x.A n) b)
    (srptA_ii s x δ hδ n (x.A n) a)
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  linarith

lemma srptA_queued_A (n : ℕ) : queued x δ n (x.A n) = 0 := by
  unfold queued served; simp

lemma srptA_queued_mono (hδ : IsSRPTSchedule s x δ) (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    queued x δ n a ≤ queued x δ n b := by
  have h := srptA_queued_diff s x δ hδ n a b
  have : 0 ≤ ∫ u in a..b, (1 - δ n u) := by
    refine intervalIntegral.integral_nonneg hab (fun u _ => ?_)
    rcases hδ.1 n u with h | h <;> simp [h]
  linarith

lemma srptA_measure (hδ : IsSRPTSchedule s x δ) (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    volume ({u | δ n u = 0} ∩ Ioc a b) = ENNReal.ofReal (∫ u in a..b, (1 - δ n u)) := by
  have hV : MeasurableSet {u | δ n u = 0} := (hδ.2.1 n) (measurableSet_singleton 0)
  have hind : ∀ u, 1 - δ n u = ({u | δ n u = 0} : Set ℝ).indicator (1 : ℝ → ℝ) u := by
    intro u
    rcases hδ.1 n u with h | h
    · simp [h]
    · simp [h]
  rw [intervalIntegral.integral_of_le hab]
  simp_rw [hind]
  rw [integral_indicator_one hV, Measure.real, Measure.restrict_apply hV]
  rw [ENNReal.ofReal_toReal]
  refine ne_top_of_le_ne_top (measure_Ioc_lt_top (μ := (volume : Measure ℝ)) (a := a) (b := b)).ne ?_
  exact measure_mono inter_subset_right

lemma srptA_measure_Icc (hδ : IsSRPTSchedule s x δ) (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    volume ({u | δ n u = 0} ∩ Icc a b) ≤ ENNReal.ofReal (∫ u in a..b, (1 - δ n u)) := by
  rw [← srptA_measure s x δ hδ n hab]
  calc volume ({u | δ n u = 0} ∩ Icc a b)
      ≤ volume (({u | δ n u = 0} ∩ Ioc a b) ∪ {a}) := by
        refine measure_mono (fun u hu => ?_)
        rcases eq_or_lt_of_le hu.2.1 with h | h
        · right; exact h.symm
        · left; exact ⟨hu.1, h, hu.2.2⟩
    _ ≤ volume ({u | δ n u = 0} ∩ Ioc a b) + volume ({a} : Set ℝ) := measure_union_le _ _
    _ = volume ({u | δ n u = 0} ∩ Ioc a b) := by simp

/-- The waiting time is at most the patience. -/
lemma srptA_wait_le (hδ : IsSRPTSchedule s x δ) (n : ℕ) (hT : 0 < x.T n) :
    volume {t | Present x δ n t ∧ δ n t = 0} ≤ ENNReal.ofReal (x.T n) := by
  set U := {t | Present x δ n t ∧ δ n t = 0} with hU
  have hq := srptA_queued_cont s x δ hδ n
  have hbound : ∀ b : ℝ, volume (U ∩ Iic b) ≤ ENNReal.ofReal (x.T n) := by
    intro b
    by_cases hb : b < x.A n
    · have : U ∩ Iic b = ∅ := by
        ext t
        simp only [mem_inter_iff, Set.mem_Iic, mem_empty_iff_false, iff_false, not_and]
        intro ht htb
        exact absurd (ht.1.1.trans htb) (not_le.mpr hb)
      rw [this, measure_empty]; exact bot_le
    push_neg at hb
    -- find b' with A ≤ b', q b' ≤ T and U ∩ Iic b ⊆ V ∩ Icc A b'
    have hex : ∃ b', x.A n ≤ b' ∧ queued x δ n b' ≤ x.T n ∧
        U ∩ Iic b ⊆ {u | δ n u = 0} ∩ Icc (x.A n) b' := by
      by_cases hqb : queued x δ n b < x.T n
      · refine ⟨b, hb, hqb.le, fun t ht => ⟨ht.1.2, ht.1.1.1, ht.2⟩⟩
      · push_neg at hqb
        have hivt := intermediate_value_Icc hb hq.continuousOn
        have hmem : x.T n ∈ Icc (queued x δ n (x.A n)) (queued x δ n b) := by
          rw [srptA_queued_A]; exact ⟨hT.le, hqb⟩
        obtain ⟨c, hc, hqc⟩ := hivt hmem
        refine ⟨c, hc.1, hqc.le, fun t ht => ⟨ht.1.2, ht.1.1.1, ?_⟩⟩
        by_contra hct
        push_neg at hct
        have := srptA_queued_mono s x δ hδ n hct.le
        have h3 := ht.1.1.2.2
        linarith
    obtain ⟨b', hAb', hqb', hsub⟩ := hex
    calc volume (U ∩ Iic b) ≤ volume ({u | δ n u = 0} ∩ Icc (x.A n) b') := measure_mono hsub
      _ ≤ ENNReal.ofReal (∫ u in (x.A n)..b', (1 - δ n u)) :=
          srptA_measure_Icc s x δ hδ n hAb'
      _ ≤ ENNReal.ofReal (x.T n) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := srptA_queued_diff s x δ hδ n (x.A n) b'
          rw [srptA_queued_A] at this
          linarith
  have hU_eq : U = ⋃ k : ℕ, U ∩ Iic (k : ℝ) := by
    ext t
    simp only [mem_iUnion, mem_inter_iff, Set.mem_Iic]
    constructor
    · intro ht
      obtain ⟨k, hk⟩ := exists_nat_ge t
      exact ⟨k, ht, hk⟩
    · rintro ⟨k, ht, _⟩; exact ht
  have hmono : Monotone (fun k : ℕ => U ∩ Iic (k : ℝ)) := by
    intro i j hij t ht
    exact ⟨ht.1, le_trans (show t ≤ (i:ℝ) from ht.2) (by exact_mod_cast hij)⟩
  have ht := tendsto_measure_iUnion_atTop (μ := volume) hmono
  rw [← hU_eq] at ht
  exact le_of_tendsto' ht (fun k => hbound k)

/-- An abandoning customer waits exactly her patience. -/
lemma srptA_wait_ge (hδ : IsSRPTSchedule s x δ) (n : ℕ) (hT : 0 < x.T n)
    (hnc : ¬ Completes x δ n) :
    ENNReal.ofReal (x.T n) ≤ volume {t | Present x δ n t ∧ δ n t = 0} := by
  have hlt : ∀ t, x.A n ≤ t → served x δ n t < x.S n := by
    intro t ht
    by_contra h
    push_neg at h
    exact hnc ⟨t, ht, h⟩
  have hq := srptA_queued_cont s x δ hδ n
  set K := {t | x.A n ≤ t ∧ x.T n ≤ queued x δ n t} with hK
  have hKc : IsClosed K :=
    (isClosed_le continuous_const continuous_id).inter (isClosed_le continuous_const hq)
  have hb0 : x.A n + x.S n + x.T n ∈ K := by
    have hS : 0 < x.S n := by
      have := hlt (x.A n) le_rfl
      unfold served at this; simpa using this
    refine ⟨by linarith, ?_⟩
    have := hlt (x.A n + x.S n + x.T n) (by linarith)
    unfold queued; linarith
  have hKne : K.Nonempty := ⟨_, hb0⟩
  have hKbdd : BddBelow K := ⟨x.A n, fun t ht => ht.1⟩
  set c := sInf K with hc
  have hcK : c ∈ K := hKc.csInf_mem hKne hKbdd
  have hsub : {u | δ n u = 0} ∩ Ioo (x.A n) c ⊆ {t | Present x δ n t ∧ δ n t = 0} := by
    intro t ht
    obtain ⟨hδt, hAt, htc⟩ := ht
    refine ⟨⟨hAt.le, ?_, ?_⟩, hδt⟩
    · unfold remaining; have := hlt t hAt.le; linarith
    · by_contra hcon
      push_neg at hcon
      have : c ≤ t := csInf_le hKbdd ⟨hAt.le, hcon⟩
      linarith
  have hmeas := srptA_measure s x δ hδ n hcK.1
  have hqd := srptA_queued_diff s x δ hδ n (x.A n) c
  rw [srptA_queued_A] at hqd
  calc ENNReal.ofReal (x.T n) ≤ ENNReal.ofReal (∫ u in (x.A n)..c, (1 - δ n u)) :=
        ENNReal.ofReal_le_ofReal (by linarith [hcK.2])
    _ = volume ({u | δ n u = 0} ∩ Ioc (x.A n) c) := hmeas.symm
    _ ≤ volume (({u | δ n u = 0} ∩ Ioo (x.A n) c) ∪ {c}) := by
        refine measure_mono (fun u hu => ?_)
        rcases eq_or_lt_of_le hu.2.2 with h | h
        · right; exact h
        · left; exact ⟨hu.1, hu.2.1, h⟩
    _ ≤ volume ({u | δ n u = 0} ∩ Ioo (x.A n) c) + volume ({c} : Set ℝ) := measure_union_le _ _
    _ = volume ({u | δ n u = 0} ∩ Ioo (x.A n) c) := by simp
    _ ≤ volume {t | Present x δ n t ∧ δ n t = 0} := measure_mono hsub

lemma srptA_waiting (hδ : IsSRPTSchedule s x δ) (n : ℕ) (hT : 0 < x.T n) :
    0 ≤ waitingTime x δ n ∧ waitingTime x δ n ≤ x.T n ∧
      (¬ Completes x δ n → waitingTime x δ n = x.T n) := by
  have hle := srptA_wait_le s x δ hδ n hT
  refine ⟨ENNReal.toReal_nonneg, ?_, fun hnc => ?_⟩
  · unfold waitingTime
    exact ENNReal.toReal_le_of_le_ofReal hT.le hle
  · unfold waitingTime
    have hge := srptA_wait_ge s x δ hδ n hT hnc
    rw [le_antisymm hle hge, ENNReal.toReal_ofReal hT.le]

end PartA


open MeasureTheory ProbabilityTheory Filter Topology Set SRPTManyServer.Collapse

lemma srptB_slln {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → β) (hX : ∀ n, Measurable (X n))
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) P))
    (hid : ∀ n, P.map (X n) = P.map (X 0)) (φ : β → ℝ) (hφ : Measurable φ)
    (hint : Integrable φ (P.map (X 0))) :
    ∀ᵐ ω ∂P, Tendsto (srptAvg (fun n => φ (X n ω))) atTop
      (𝓝 (∫ y, φ y ∂(P.map (X 0)))) := by
  have hint' : Integrable (φ ∘ X 0) P :=
    (integrable_map_measure hφ.aestronglyMeasurable (hX 0).aemeasurable).mp hint
  have hsl := strong_law_ae (μ := P) (fun n => φ ∘ X n) hint'
    (fun i j hij => (hind hij).comp hφ hφ)
    (fun i => (IdentDistrib.mk (hX i).aemeasurable (hX 0).aemeasurable (hid i)).comp hφ)
  have hE : P[φ ∘ X 0] = ∫ y, φ y ∂(P.map (X 0)) :=
    (integral_map (hX 0).aemeasurable hφ.aestronglyMeasurable).symm
  rw [hE] at hsl
  filter_upwards [hsl] with ω hω
  refine hω.congr (fun N => ?_)
  unfold srptAvg
  simp only [Function.comp, smul_eq_mul]
  rw [div_eq_inv_mul]

section Model

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (νS νT : Measure ℝ)
  (E S T : ℕ → Ω → ℝ)

lemma srptB_meas (hmodel : IsArrivalModel P νS νT E S T) :
    ∀ i : Fin 3 × ℕ, Measurable ((![E, S, T] i.1) i.2) := by
  rintro ⟨k, n⟩
  fin_cases k
  · exact hmodel.measE n
  · exact hmodel.measS n
  · exact hmodel.measT n

lemma srptB_pair_indep (hmodel : IsArrivalModel P νS νT E S T) {i j : ℕ} (hij : i ≠ j) :
    IndepFun (fun ω => (S i ω, T i ω)) (fun ω => (S j ω, T j ω)) P := by
  classical
  have h := hmodel.indep.indepFun_finset {((1 : Fin 3), i), ((2 : Fin 3), i)}
    {((1 : Fin 3), j), ((2 : Fin 3), j)} (by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with h | h <;> simp_all [Prod.ext_iff])
    (srptB_meas P νS νT E S T hmodel)
  let a1 : ↥({((1 : Fin 3), i), ((2 : Fin 3), i)} : Finset (Fin 3 × ℕ)) := ⟨((1 : Fin 3), i), by simp⟩
  let a2 : ↥({((1 : Fin 3), i), ((2 : Fin 3), i)} : Finset (Fin 3 × ℕ)) := ⟨((2 : Fin 3), i), by simp⟩
  let b1 : ↥({((1 : Fin 3), j), ((2 : Fin 3), j)} : Finset (Fin 3 × ℕ)) := ⟨((1 : Fin 3), j), by simp⟩
  let b2 : ↥({((1 : Fin 3), j), ((2 : Fin 3), j)} : Finset (Fin 3 × ℕ)) := ⟨((2 : Fin 3), j), by simp⟩
  have hc := h.comp ((measurable_pi_apply a1).prodMk (measurable_pi_apply a2))
    ((measurable_pi_apply b1).prodMk (measurable_pi_apply b2))
  exact hc

lemma srptB_E_indep (hmodel : IsArrivalModel P νS νT E S T) {i j : ℕ} (hij : i ≠ j) :
    IndepFun (E i) (E j) P := by
  have h := hmodel.indep.indepFun
    (i := ((0 : Fin 3), i)) (j := ((0 : Fin 3), j)) (by simp [hij])
  exact h

lemma srptB_pair_law (hmodel : IsArrivalModel P νS νT E S T) (n : ℕ) :
    P.map (fun ω => (S n ω, T n ω)) = νS.prod νT := by
  haveI := hmodel.isProb
  have hST : IndepFun (S n) (T n) P := by
    have h := hmodel.indep.indepFun
      (i := ((1 : Fin 3), n)) (j := ((2 : Fin 3), n)) (by simp)
    exact h
  rw [(indepFun_iff_map_prod_eq_prod_map_map (hmodel.measS n).aemeasurable
    (hmodel.measT n).aemeasurable).mp hST, hmodel.lawS n, hmodel.lawT n]

/-- SLLN for products `f(S_n) g(T_n)`. -/
lemma srptB_slln_prod (hmodel : IsArrivalModel P νS νT E S T)
    [IsProbabilityMeasure νS] [IsProbabilityMeasure νT]
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f νS) (hgi : Integrable g νT) :
    ∀ᵐ ω ∂P, Tendsto (srptAvg (fun n => f (S n ω) * g (T n ω))) atTop
      (𝓝 ((∫ a, f a ∂νS) * (∫ b, g b ∂νT))) := by
  haveI := hmodel.isProb
  have hlaw := srptB_pair_law P νS νT E S T hmodel
  have h := srptB_slln P (fun n ω => (S n ω, T n ω))
    (fun n => (hmodel.measS n).prodMk (hmodel.measT n))
    (fun i j hij => srptB_pair_indep P νS νT E S T hmodel hij)
    (fun n => by rw [hlaw n, hlaw 0])
    (fun z : ℝ × ℝ => f z.1 * g z.2) ((hf.comp measurable_fst).mul (hg.comp measurable_snd))
    (by rw [hlaw 0]; exact hfi.mul_prod hgi)
  rw [hlaw 0, integral_prod_mul] at h
  exact h

end Model

section Facts

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (νS νT : Measure ℝ)
  (E S T : ℕ → Ω → ℝ)

lemma srptB_Iic_zero (ν : Measure ℝ) (hac : ν ≪ volume) (h : ν (Iio 0) = 0) :
    ν (Iic 0) = 0 := by
  have h0 : ν {0} = 0 := hac (Real.volume_singleton)
  refine le_antisymm ?_ bot_le
  calc ν (Iic 0) ≤ ν (Iio 0 ∪ {0}) := measure_mono (fun x hx => by
        rcases eq_or_lt_of_le (show x ≤ 0 from hx) with h' | h'
        · right; exact h'
        · left; exact h')
    _ ≤ ν (Iio 0) + ν {0} := measure_union_le _ _
    _ = 0 := by rw [h, h0, add_zero]

lemma srptB_exp_Iic : expMeasure 1 (Iic 0) = 0 := by
  refine srptB_Iic_zero _ (withDensity_absolutelyContinuous _ _) ?_
  unfold expMeasure gammaMeasure
  rw [withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

lemma srptB_pos_ae (X : Ω → ℝ) (hX : Measurable X) (ν : Measure ℝ) (hlaw : P.map X = ν)
    (h : ν (Iic 0) = 0) : ∀ᵐ ω ∂P, 0 < X ω := by
  rw [ae_iff]
  have : {ω | ¬ 0 < X ω} = X ⁻¹' Iic 0 := by ext ω; simp
  rw [this, ← Measure.map_apply hX measurableSet_Iic, hlaw, h]

lemma srptB_G (νS νT : Measure ℝ) (g : ℝ → ℝ) (rho mu theta tau : ℝ)
    (hstd : Standing νS νT g rho mu theta tau) :
    0 < (νS (Iic tau)).toReal ∧ (νS (Iic tau)).toReal < 1 := by
  haveI := hstd.probS
  have hρμ : 0 < rho * mu := mul_pos (by linarith [hstd.rho_gt]) hstd.mu_pos
  have hthr := hstd.threshold
  constructor
  · rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := νS (Iic tau))) with h | h
    · exfalso
      have h0 : νS (Iic tau) = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).mp h.symm with h' | h'
        · exact h'
        · exact absurd h' (measure_ne_top _ _)
      rw [setIntegral_measure_zero _ h0] at hthr
      have : 0 < 1 / (rho * mu) := by positivity
      linarith
    · exact h
  · by_contra hcon
    push_neg at hcon
    have h1 : (νS (Iic tau)).toReal = 1 := le_antisymm (by
      have := prob_le_one (μ := νS) (s := Iic tau)
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)) hcon
    have hc : νS (Iic tau)ᶜ = 0 := by
      rw [prob_compl_eq_zero_iff measurableSet_Iic]
      have : νS (Iic tau) ≠ ⊤ := measure_ne_top _ _
      rw [← ENNReal.ofReal_toReal this, h1, ENNReal.ofReal_one]
    have hsplit := integral_add_compl (μ := νS) (f := fun x => x) (measurableSet_Iic (a := tau)) hstd.intS
    rw [setIntegral_measure_zero _ hc, add_zero, hthr, hstd.meanS] at hsplit
    have hmu := hstd.mu_pos
    have hρ := hstd.rho_gt
    field_simp at hsplit
    nlinarith

end Facts

noncomputable def srptE (νT : Measure ℝ) (K : ℕ) : ℝ :=
  ∫ b, (Ioi (K:ℝ)).indicator (fun b => b) b ∂νT

section Facts2

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (νS νT : Measure ℝ)
  (E S T : ℕ → Ω → ℝ)

lemma srptB_E_tendsto (νT : Measure ℝ) [IsProbabilityMeasure νT] (hint : Integrable id νT) :
    Tendsto (srptE νT) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := νT)
    (F := fun K : ℕ => fun b : ℝ => (Ioi (K:ℝ)).indicator (fun b => b) b) (f := fun _ => (0:ℝ))
    (fun b => ‖b‖)
    (fun K => (measurable_id.indicator measurableSet_Ioi).aestronglyMeasurable)
    hint.norm
    (fun K => Filter.Eventually.of_forall (fun b => by
      rw [Set.indicator_apply]; split_ifs <;> simp))
    (Filter.Eventually.of_forall (fun b => by
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨K0, hK0⟩ := exists_nat_ge b
      filter_upwards [eventually_ge_atTop K0] with K hK
      have : ¬ b ∈ Ioi (K:ℝ) := by
        simp only [Set.mem_Ioi, not_lt]
        exact hK0.trans (by exact_mod_cast hK)
      rw [Set.indicator_of_notMem this]))
  show Tendsto (fun K : ℕ => ∫ b, (Ioi (K:ℝ)).indicator (fun b => b) b ∂νT) atTop (𝓝 0)
  simpa using h

lemma srptB_facts (g : ℝ → ℝ) (rho mu theta tau : ℝ)
    (hstd : Standing νS νT g rho mu theta tau) (hmodel : IsArrivalModel P νS νT E S T) :
    ∀ᵐ ω ∂P,
      Tendsto (srptAvg (fun n => if S n ω ≤ tau then (1:ℝ) else 0)) atTop
        (𝓝 (νS (Iic tau)).toReal) ∧
      Tendsto (srptAvg (fun n => if tau < S n ω then T n ω else 0)) atTop
        (𝓝 ((1 - (νS (Iic tau)).toReal) / theta)) ∧
      ∀ K : ℕ, Tendsto (srptAvg (fun n => if (K:ℝ) < T n ω then T n ω else 0)) atTop
        (𝓝 (srptE νT K)) := by
  haveI := hstd.probS
  haveI := hstd.probT
  have h1 := srptB_slln_prod P νS νT E S T hmodel ((Iic tau).indicator (fun _ => (1:ℝ)))
    (fun _ => 1) (measurable_const.indicator measurableSet_Iic) measurable_const
    ((integrable_const 1).indicator measurableSet_Iic) (integrable_const 1)
  have h2 := srptB_slln_prod P νS νT E S T hmodel ((Ioi tau).indicator (fun _ => (1:ℝ)))
    (fun b => b) (measurable_const.indicator measurableSet_Ioi) measurable_id
    ((integrable_const 1).indicator measurableSet_Ioi) hstd.intT
  have h3 : ∀ᵐ ω ∂P, ∀ K : ℕ, Tendsto
      (srptAvg (fun n => (fun _ => (1:ℝ)) (S n ω) * (Ioi (K:ℝ)).indicator (fun b => b) (T n ω)))
      atTop (𝓝 ((∫ a, (fun _ => (1:ℝ)) a ∂νS) *
        (∫ b, (Ioi (K:ℝ)).indicator (fun b => b) b ∂νT))) := by
    rw [ae_all_iff]
    intro K
    exact srptB_slln_prod P νS νT E S T hmodel (fun _ => 1)
      ((Ioi (K:ℝ)).indicator (fun b => b)) measurable_const
      (measurable_id.indicator measurableSet_Ioi) (integrable_const 1)
      (hstd.intT.indicator measurableSet_Ioi)
  filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
  refine ⟨?_, ?_, fun K => ?_⟩
  · have e1 : (∫ a, (Iic tau).indicator (fun _ => (1:ℝ)) a ∂νS) * (∫ b, (fun _ => (1:ℝ)) b ∂νT)
        = (νS (Iic tau)).toReal := by
      rw [integral_indicator_const _ measurableSet_Iic]; simp [Measure.real]
    rw [e1] at hω1
    refine hω1.congr (fun N => ?_)
    congr 1; funext n
    by_cases h : S n ω ≤ tau <;> simp [Set.indicator_apply, h]
  · have e1 : (∫ a, (Ioi tau).indicator (fun _ => (1:ℝ)) a ∂νS) * (∫ b, b ∂νT)
        = (1 - (νS (Iic tau)).toReal) / theta := by
      rw [integral_indicator_const _ measurableSet_Ioi, ← compl_Iic, measureReal_compl measurableSet_Iic]
      have := hstd.meanT
      rw [this]; simp [Measure.real]; ring
    rw [e1] at hω2
    refine hω2.congr (fun N => ?_)
    congr 1; funext n
    by_cases h : tau < S n ω <;> simp [Set.indicator_apply, h]
  · have h := hω3 K
    simp only [integral_const, smul_eq_mul, mul_one, one_mul, probReal_univ] at h
    refine h.congr (fun N => ?_)
    congr 1

end Facts2

section Adm

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (νS νT : Measure ℝ)
  (E S T : ℕ → Ω → ℝ)

lemma srptB_div (hmodel : IsArrivalModel P νS νT E S T) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), E k ω) atTop atTop := by
  haveI := hmodel.isProb
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  set φ : ℝ → ℝ := fun x => max 0 (min x 1) with hφ
  have hφm : Measurable φ := measurable_const.max (measurable_id.min measurable_const)
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => le_max_left _ _
  have hφ1 : ∀ x, φ x ≤ 1 := fun x => max_le zero_le_one (min_le_right _ _)
  have hlaw0 : P.map (E 0) = expMeasure 1 := hmodel.lawE 0
  have hint : Integrable φ (P.map (E 0)) := by
    rw [hlaw0]
    refine Integrable.of_bound hφm.aestronglyMeasurable 1 (Filter.Eventually.of_forall
      (fun x => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 x)]; exact hφ1 x
  have hsl := srptB_slln P E hmodel.measE (fun i j hij => srptB_E_indep P νS νT E S T hmodel hij)
    (fun n => by rw [hmodel.lawE n, hlaw0]) φ hφm hint
  set m := ∫ y, φ y ∂(P.map (E 0)) with hm
  have hmpos : 0 < m := by
    rw [hm, hlaw0, integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hφ0)
      (by rw [← hlaw0]; exact hint)]
    have hsub : Ioi (0:ℝ) ⊆ Function.support φ := by
      intro x hx
      simp only [Function.mem_support, hφ]
      have : 0 < min x 1 := lt_min hx one_pos
      exact (lt_max_of_lt_right this).ne'
    have h1 : expMeasure 1 (Ioi 0) = 1 := by
      rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, srptB_exp_Iic, tsub_zero]
    calc (0 : ENNReal) < 1 := one_pos
      _ = expMeasure 1 (Ioi 0) := h1.symm
      _ ≤ expMeasure 1 (Function.support φ) := measure_mono hsub
  have hEpos : ∀ᵐ ω ∂P, ∀ k, 0 < E k ω :=
    ae_all_iff.mpr (fun k => srptB_pos_ae P (E k) (hmodel.measE k) _ (hmodel.lawE k)
      srptB_exp_Iic)
  filter_upwards [hsl, hEpos] with ω hω hpos
  have hsum : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, φ (E k ω)) atTop atTop := by
    have := tendsto_natCast_atTop_atTop.atTop_mul_pos hmpos hω
    refine this.congr (fun N => ?_)
    unfold srptAvg
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · have : (N:ℝ) ≠ 0 := by exact_mod_cast h.ne'
      field_simp
  have hsum' := hsum.comp (tendsto_add_atTop_nat 1)
  refine tendsto_atTop_mono (fun n => ?_) hsum'
  simp only [Function.comp]
  refine Finset.sum_le_sum (fun k _ => ?_)
  have := hpos k
  simp only [hφ]
  exact max_le this.le (min_le_left _ _)

lemma srptB_adm (g : ℝ → ℝ) (rho mu theta tau : ℝ)
    (hstd : Standing νS νT g rho mu theta tau) (hmodel : IsArrivalModel P νS νT E S T) :
    ∀ᵐ ω ∂P, ∀ s : ℕ, 1 ≤ s → (arrivalStream rho mu s E S T ω).Admissible := by
  have hEpos : ∀ᵐ ω ∂P, ∀ k, 0 < E k ω :=
    ae_all_iff.mpr (fun k => srptB_pos_ae P (E k) (hmodel.measE k) _ (hmodel.lawE k)
      srptB_exp_Iic)
  have hSI : νS (Iic 0) = 0 :=
    srptB_Iic_zero νS (by rw [hstd.density]; exact withDensity_absolutelyContinuous _ _)
      hstd.nonnegS
  have hTI : νT (Iic 0) = 0 := srptB_Iic_zero νT hstd.contT hstd.nonnegT
  have hSpos : ∀ᵐ ω ∂P, ∀ n, 0 < S n ω :=
    ae_all_iff.mpr (fun n => srptB_pos_ae P (S n) (hmodel.measS n) _ (hmodel.lawS n) hSI)
  have hTpos : ∀ᵐ ω ∂P, ∀ n, 0 < T n ω :=
    ae_all_iff.mpr (fun n => srptB_pos_ae P (T n) (hmodel.measT n) _ (hmodel.lawT n) hTI)
  filter_upwards [hEpos, hSpos, hTpos, srptB_div P νS νT E S T hmodel] with ω hE hS hT hdiv
  intro s hs
  have hc : 0 < rho * mu * s := by
    have := hstd.rho_gt; have := hstd.mu_pos
    have : (1:ℝ) ≤ s := by exact_mod_cast hs
    positivity
  refine ⟨?_, ?_, ?_, hS, hT⟩
  · refine strictMono_nat_of_lt_succ (fun n => ?_)
    simp only [arrivalStream]
    refine div_lt_div_of_pos_right ?_ hc
    rw [Finset.sum_range_succ _ (n + 1)]
    linarith [hE (n + 1)]
  · simp only [arrivalStream]
    exact div_nonneg (Finset.sum_nonneg (fun k _ => (hE k).le)) hc.le
  · simp only [arrivalStream]
    exact hdiv.atTop_div_const hc

end Adm


open MeasureTheory ProbabilityTheory Filter Topology Set SRPTManyServer.Collapse

lemma srptM_ae_forall {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ℕ → Ω → Prop}
    (h : ∀ s : ℕ, 1 ≤ s → ∀ᵐ ω ∂P, p s ω) : ∀ᵐ ω ∂P, ∀ s : ℕ, 1 ≤ s → p s ω := by
  rw [ae_all_iff]
  intro s
  by_cases hs : 1 ≤ s
  · exact (h s hs).mono (fun ω hω _ => hω)
  · exact Filter.Eventually.of_forall (fun ω h' => absurd h' hs)

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (νS νT : Measure ℝ) (g : ℝ → ℝ) (rho mu theta tau : ℝ)
    (hstd : Standing νS νT g rho mu theta tau)
    (E S T : ℕ → Ω → ℝ) (hmodel : IsArrivalModel P νS νT E S T)
    (δ : ℕ → Ω → ℕ → ℝ → ℝ)
    (hδ : ∀ s : ℕ, 1 ≤ s → ∀ ω, (arrivalStream rho mu s E S T ω).Admissible →
      IsSRPTSchedule s (arrivalStream rho mu s E S T ω) (δ s ω))
    (pServ1 pServ2 wServ w1 wAb w2 wAll : ℕ → ℝ)
    (h_pServ1 : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P (fun n ω => S n ω ≤ tau)
      (fun n ω => servedInd (arrivalStream rho mu s E S T ω) (δ s ω) n) (pServ1 s))
    (h_pServ2 : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P (fun n ω => tau < S n ω)
      (fun n ω => servedInd (arrivalStream rho mu s E S T ω) (δ s ω) n) (pServ2 s))
    (h_wServ : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P
      (fun n ω => Completes (arrivalStream rho mu s E S T ω) (δ s ω) n)
      (fun n ω => waitingTime (arrivalStream rho mu s E S T ω) (δ s ω) n) (wServ s))
    (h_w1 : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P (fun n ω => S n ω ≤ tau)
      (fun n ω => waitingTime (arrivalStream rho mu s E S T ω) (δ s ω) n) (w1 s))
    (h_wAb : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P
      (fun n ω => ¬ Completes (arrivalStream rho mu s E S T ω) (δ s ω) n)
      (fun n ω => waitingTime (arrivalStream rho mu s E S T ω) (δ s ω) n) (wAb s))
    (h_w2 : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P (fun n ω => tau < S n ω)
      (fun n ω => waitingTime (arrivalStream rho mu s E S T ω) (δ s ω) n) (w2 s))
    (h_wAll : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P (fun _ _ => True)
      (fun n ω => waitingTime (arrivalStream rho mu s E S T ω) (δ s ω) n) (wAll s)) :
    Tendsto pServ1 atTop (𝓝 1) ∧ Tendsto pServ2 atTop (𝓝 0) ∧
    Tendsto wServ atTop (𝓝 0) ∧ Tendsto w1 atTop (𝓝 0) ∧
    Tendsto wAb atTop (𝓝 (1 / theta)) ∧ Tendsto w2 atTop (𝓝 (1 / theta)) ∧
    Tendsto wAll atTop (𝓝 ((1 - (νS (Set.Iic tau)).toReal) / theta)) := by
  haveI := hmodel.isProb
  haveI := hstd.probT
  obtain ⟨hG0, hG1⟩ := srptB_G νS νT g rho mu theta tau hstd
  obtain ⟨hp1, hp2⟩ := SRPTManyServer.Collapse.theorem_2_a P νS νT g rho mu theta tau hstd
    E S T hmodel δ hδ pServ1 pServ2 h_pServ1 h_pServ2
  have hw1 := SRPTManyServer.Collapse.theorem_2_b_short P νS νT g rho mu theta tau hstd
    E S T hmodel δ hδ pServ1 pServ2 w1 h_pServ1 h_pServ2 h_w1
  have hall := (srptB_facts P νS νT E S T g rho mu theta tau hstd hmodel).and
    ((srptB_adm P νS νT E S T g rho mu theta tau hstd hmodel).and
    ((srptM_ae_forall P h_pServ1).and ((srptM_ae_forall P h_pServ2).and
    ((srptM_ae_forall P h_wServ).and ((srptM_ae_forall P h_w1).and
    ((srptM_ae_forall P h_wAb).and ((srptM_ae_forall P h_w2).and
    (srptM_ae_forall P h_wAll))))))))
  haveI : (ae P).NeBot := ae_neBot.mpr (IsProbabilityMeasure.ne_zero P)
  obtain ⟨ω, ⟨hB1, hB2, hB3⟩, hadm, c1, c2, c3, c4, c5, c6, c7⟩ := hall.exists
  have hTpos : ∀ n, 0 < T n ω := (hadm 1 le_rfl).2.2.2.2
  have core := srptC_core (fun n => S n ω) (fun n => T n ω) tau theta
    (νS (Set.Iic tau)).toReal (srptE νT)
    (fun s n => Completes (arrivalStream rho mu s E S T ω) (δ s ω) n)
    (fun s n => servedInd (arrivalStream rho mu s E S T ω) (δ s ω) n)
    (fun s n => waitingTime (arrivalStream rho mu s E S T ω) (δ s ω) n)
    pServ1 pServ2 wServ w1 wAb w2 wAll hG0 hG1 (fun n => (hTpos n).le)
    (fun s n => by
      unfold servedInd
      constructor
      · intro h; simp [h]
      · intro h; simp [h])
    (fun s hs n => srptA_waiting s _ _ (hδ s hs ω (hadm s hs)) n (hTpos n))
    hB1 hB2 hB3 (srptB_E_tendsto νT hstd.intT)
    c1 c2 c3 c4 c5 c6 c7 hp1 hp2 hw1
  obtain ⟨hS, hA, h2, hAll⟩ := core
  exact ⟨hp1, hp2, hS, hw1, hA, h2, hAll⟩
