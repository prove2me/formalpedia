-- Prove2me | solution 1 for TailRiskSharing.VaRTail.exists_quantile_uniform
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-11-04T13:46:43.363559+00:00
-- url     : https://prove2.me/submissions/467d79f8-8b0e-45e3-8960-d20c74e66249

import Definitions.Def_TailRiskSharing_VaRTail_Setting
import Mathlib.Probability.CDF

open MeasureTheory Set Filter Topology

namespace FreshQUniform

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Small positive subsets exist in an atomless space. -/
lemma exists_small (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (s : Set Ω) (hs : MeasurableSet s)
    (hpos : 0 < P.real s) (ε : ℝ) (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < P.real t ∧ P.real t ≤ ε := by
  have claim : ∀ n : ℕ, ∃ t ⊆ s, MeasurableSet t ∧ 0 < P.real t ∧
      P.real t ≤ P.real s / 2 ^ n := by
    intro n
    induction n with
    | zero => exact ⟨s, subset_rfl, hs, hpos, by simp⟩
    | succ n ih =>
      obtain ⟨t, hts, ht, htpos, htle⟩ := ih
      have htpos' : 0 < P t := by
        rw [measureReal_def] at htpos; exact ENNReal.toReal_pos_iff.1 htpos |>.1
      obtain ⟨r, hrt, hr, hrpos, hrlt⟩ := hP t ht htpos'
      have hrpos' : 0 < P.real r := ENNReal.toReal_pos hrpos.ne' (measure_ne_top _ _)
      have hrlt' : P.real r < P.real t :=
        (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 hrlt
      have hdiff : P.real (t \ r) = P.real t - P.real r := measureReal_sdiff hrt hr
      have hpow : P.real s / 2 ^ (n + 1) = (P.real s / 2 ^ n) / 2 := by
        rw [pow_succ]; ring
      by_cases h : P.real r ≤ P.real t / 2
      · exact ⟨r, hrt.trans hts, hr, hrpos', by rw [hpow]; linarith⟩
      · refine ⟨t \ r, sdiff_subset.trans hts, ht.diff hr, by rw [hdiff]; linarith, ?_⟩
        rw [hdiff, hpow]; push Not at h; linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P.real s / 2 ^ n < ε := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (P.real s + 1) by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨n, ?_⟩
    have h1 : P.real s ≤ 1 := measureReal_le_one
    rw [div_lt_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hn
    have : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
    nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) n, measureReal_nonneg (μ := P) (s := s)]
  obtain ⟨t, hts, ht, htpos, htle⟩ := claim n
  exact ⟨t, hts, ht, htpos, htle.trans hn.le⟩

/-- Sierpiński: an atomless probability measure takes every intermediate value on subsets. -/
lemma sierpinski (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (s : Set Ω) (hs : MeasurableSet s)
    (c : ℝ) (hc0 : 0 ≤ c) (hcs : c ≤ P.real s) :
    ∃ t ⊆ s, MeasurableSet t ∧ P.real t = c := by
  classical
  let cand : Set Ω → Set (Set Ω) := fun t =>
    {r | MeasurableSet r ∧ r ⊆ s \ t ∧ P.real t + P.real r ≤ c}
  let β : Set Ω → ℝ := fun t => sSup ((fun r => P.real r) '' cand t)
  have hbdd : ∀ t, BddAbove ((fun r => P.real r) '' cand t) := fun t =>
    ⟨1, by rintro _ ⟨r, -, rfl⟩; exact measureReal_le_one⟩
  have key : ∀ t, P.real t ≤ c → ∃ r, r ∈ cand t ∧ β t / 2 ≤ P.real r := by
    intro t ht
    have hne : ((fun r => P.real r) '' cand t).Nonempty :=
      ⟨_, ∅, ⟨MeasurableSet.empty, empty_subset _, by simpa using ht⟩, rfl⟩
    by_cases hb : β t ≤ 0
    · exact ⟨∅, ⟨MeasurableSet.empty, empty_subset _, by simpa using ht⟩, by simp; linarith⟩
    · push Not at hb
      obtain ⟨_, ⟨r, hr, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne (show β t / 2 < β t by linarith)
      exact ⟨r, hr, hlt.le⟩
  let nxt : Set Ω → Set Ω := fun t =>
    t ∪ (if h : P.real t ≤ c then Classical.choose (key t h) else ∅)
  let I : Set Ω → Prop := fun t => MeasurableSet t ∧ t ⊆ s ∧ P.real t ≤ c
  have hnxt : ∀ t, I t → I (nxt t) ∧ β t / 2 ≤ P.real (nxt t) - P.real t := by
    intro t ⟨ht, hts, htc⟩
    have hspec := Classical.choose_spec (key t htc)
    set r := Classical.choose (key t htc) with hr_def
    obtain ⟨⟨hr, hrs, hrc⟩, hrb⟩ := hspec
    have hnx : nxt t = t ∪ r := by simp only [nxt, dif_pos htc, ← hr_def]
    have hdisj : Disjoint t r := by
      rw [Set.disjoint_left]; intro x hx hxr; exact (hrs hxr).2 hx
    have hm : P.real (t ∪ r) = P.real t + P.real r := measureReal_union hdisj hr
    rw [hnx]
    refine ⟨⟨ht.union hr, union_subset hts (hrs.trans sdiff_subset), by rw [hm]; exact hrc⟩,
      by rw [hm]; linarith⟩
  let sq : ℕ → Set Ω := fun n => nxt^[n] ∅
  have hsqI : ∀ n, I (sq n) := by
    intro n
    induction n with
    | zero => exact ⟨MeasurableSet.empty, empty_subset _, by simp [sq]; exact hc0⟩
    | succ n ih =>
      show I (nxt^[n+1] ∅)
      rw [Function.iterate_succ_apply']
      exact (hnxt _ ih).1
  have hsq_succ : ∀ n, sq (n+1) = nxt (sq n) := fun n => Function.iterate_succ_apply' _ _ _
  have hmono : Monotone sq := by
    apply monotone_nat_of_le_succ
    intro n; rw [hsq_succ]; exact subset_union_left
  set T := ⋃ n, sq n with hT
  have hTs : T ⊆ s := iUnion_subset fun n => (hsqI n).2.1
  have hTm : MeasurableSet T := MeasurableSet.iUnion fun n => (hsqI n).1
  have hlim : Tendsto (fun n => P.real (sq n)) atTop (𝓝 (P.real T)) := by
    have := tendsto_measure_iUnion_atTop (μ := P) hmono
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  have hTc : P.real T ≤ c := le_of_tendsto' hlim fun n => (hsqI n).2.2
  refine ⟨T, hTs, hTm, le_antisymm hTc ?_⟩
  by_contra hlt
  push Not at hlt
  have hdpos : 0 < P.real (s \ T) := by
    rw [measureReal_sdiff hTs hTm]; linarith
  obtain ⟨r, hrs, hr, hrpos, hrle⟩ := exists_small P hP (s \ T) (hs.diff hTm) hdpos
    (c - P.real T) (by linarith)
  have hstep : ∀ n, P.real r / 2 ≤ P.real (sq (n+1)) - P.real (sq n) := by
    intro n
    have hsT : sq n ⊆ T := subset_iUnion sq n
    have hc : r ∈ cand (sq n) := by
      refine ⟨hr, fun x hx => ⟨(hrs hx).1, fun hxn => (hrs hx).2 (hsT hxn)⟩, ?_⟩
      have := measureReal_mono (μ := P) hsT
      linarith
    have hle : P.real r ≤ β (sq n) := le_csSup (hbdd _) ⟨r, hc, rfl⟩
    rw [hsq_succ]
    have := (hnxt _ (hsqI n)).2
    linarith
  have hgrow : ∀ n : ℕ, (n : ℝ) * (P.real r / 2) ≤ P.real (sq n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => have := hstep n; push_cast; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / P.real r)
  have h1 := hgrow n
  have h2 : P.real (sq n) ≤ 1 := measureReal_le_one
  rw [div_lt_iff₀ hrpos] at hn
  nlinarith

/-- Relative Sierpiński: between two nested measurable sets. -/
lemma sierpinski_between (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (lo hi : Set Ω) (hlo : MeasurableSet lo)
    (hhi : MeasurableSet hi) (hsub : lo ⊆ hi) (c : ℝ) (h1 : P.real lo ≤ c) (h2 : c ≤ P.real hi) :
    ∃ m, MeasurableSet m ∧ lo ⊆ m ∧ m ⊆ hi ∧ P.real m = c := by
  obtain ⟨t, hts, ht, htc⟩ := sierpinski P hP (hi \ lo) (hhi.diff hlo) (c - P.real lo)
    (by linarith) (by rw [measureReal_sdiff hsub hlo]; linarith)
  have hdisj : Disjoint lo t := by
    rw [Set.disjoint_left]; intro x hx hxt; exact (hts hxt).2 hx
  refine ⟨lo ∪ t, hlo.union ht, subset_union_left,
    union_subset hsub (hts.trans sdiff_subset), ?_⟩
  rw [measureReal_union hdisj ht, htc]; ring

section CDF

variable (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)

local notation "F" => TailRiskSharing.VaRConv.distFn P X

lemma F_eq_cdf (hX : Measurable X) (x : ℝ) : F x = ProbabilityTheory.cdf (P.map X) x := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  rw [ProbabilityTheory.cdf_eq_real, map_measureReal_apply hX measurableSet_Iic]
  rfl

lemma F_mono (hX : Measurable X) : Monotone F := by
  intro a b hab; rw [F_eq_cdf P X hX, F_eq_cdf P X hX]
  exact ProbabilityTheory.monotone_cdf _ hab

lemma F_le_one (x : ℝ) : F x ≤ 1 := measureReal_le_one

lemma F_nonneg (x : ℝ) : 0 ≤ F x := measureReal_nonneg

/-- The left quantile `F⁻¹(q) = inf {x | q ≤ F x}`. -/
noncomputable def xq (q : ℝ) : ℝ := sInf {x | q ≤ F x}

lemma S_nonempty (hX : Measurable X) {q : ℝ} (hq : q < 1) : {x | q ≤ F x}.Nonempty := by
  have ht : Tendsto F atTop (𝓝 1) := by
    have := ProbabilityTheory.tendsto_cdf_atTop (P.map X)
    exact this.congr fun x => (F_eq_cdf P X hX x).symm
  obtain ⟨x, hx⟩ := (ht.eventually (lt_mem_nhds hq)).exists
  exact ⟨x, hx.le⟩

lemma S_bdd (hX : Measurable X) {q : ℝ} (hq : 0 < q) : BddBelow {x | q ≤ F x} := by
  have ht : Tendsto F atBot (𝓝 0) := by
    have := ProbabilityTheory.tendsto_cdf_atBot (P.map X)
    exact this.congr fun x => (F_eq_cdf P X hX x).symm
  obtain ⟨M, hM⟩ := eventually_atBot.1 (ht.eventually (gt_mem_nhds hq))
  refine ⟨M, fun x hx => ?_⟩
  by_contra h; push Not at h
  have := hM x h.le
  exact absurd hx (not_le.2 this)

lemma lt_of_lt_xq (hX : Measurable X) {q x : ℝ} (hq : 0 < q) (hx : x < xq P X q) : F x < q := by
  by_contra h; push Not at h
  exact absurd (csInf_le (S_bdd P X hX hq) h) (not_le.2 hx)

lemma le_F_xq (hX : Measurable X) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : q ≤ F (xq P X q) := by
  have hrc : ContinuousWithinAt F (Ioi (xq P X q)) (xq P X q) := by
    have := (ProbabilityTheory.cdf (P.map X)).right_continuous (xq P X q)
    have h2 : ContinuousWithinAt F (Ici (xq P X q)) (xq P X q) := by
      have hfun : F = ProbabilityTheory.cdf (P.map X) := funext (F_eq_cdf P X hX)
      rw [hfun]; exact this
    exact h2.mono Ioi_subset_Ici_self
  apply ge_of_tendsto hrc
  filter_upwards [self_mem_nhdsWithin] with y hy
  obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt (S_nonempty P X hX hq1) (show xq P X q < y from hy)
  exact hz.trans (F_mono P X hX hzy.le)

lemma xq_mono (hX : Measurable X) {q q' : ℝ} (hq : 0 < q) (hq' : q' < 1) (h : q ≤ q') :
    xq P X q ≤ xq P X q' :=
  csInf_le_csInf (S_bdd P X hX hq) (S_nonempty P X hX hq')
    (fun x (hx : q' ≤ F x) => show q ≤ F x from h.trans hx)

lemma measure_lt_xq (hX : Measurable X) {q : ℝ} (hq0 : 0 < q) :
    P.real {ω | X ω < xq P X q} ≤ q := by
  set x := xq P X q
  let B : ℕ → Set Ω := fun n => {ω | X ω ≤ x - 1 / ((n:ℝ) + 1)}
  have hB : Monotone B := by
    intro m n hmn ω hω
    simp only [B, mem_setOf_eq] at hω ⊢
    have : 1 / ((n:ℝ) + 1) ≤ 1 / ((m:ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    linarith
  have hU : (⋃ n, B n) = {ω | X ω < x} := by
    ext ω; simp only [mem_iUnion, mem_setOf_eq, B]
    constructor
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n:ℝ) + 1) := by positivity
      linarith
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < x - X ω by linarith)
      exact ⟨n, by linarith⟩
  have hlim : Tendsto (fun n => P.real (B n)) atTop (𝓝 (P.real {ω | X ω < x})) := by
    rw [← hU]
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_measure_iUnion_atTop hB)
  refine le_of_tendsto' hlim fun n => ?_
  have h := lt_of_lt_xq P X hX hq0 (show x - 1 / ((n:ℝ) + 1) < x by
    have : 0 < 1 / ((n:ℝ) + 1) := by positivity
    linarith)
  exact h.le

end CDF

section Dyadic

variable (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)

def Lset (q : ℝ) : Set Ω := {ω | X ω < xq P X q}
def Hset (q : ℝ) : Set Ω := {ω | X ω ≤ xq P X q}

noncomputable def dy (n k : ℕ) : ℝ := (k : ℝ) / 2 ^ n

lemma dy_double (n i : ℕ) : dy (n+1) (2*i) = dy n i := by
  simp only [dy]; push_cast; rw [pow_succ]; field_simp

lemma dy_odd (n j : ℕ) : dy (n+1) (2*j+1) = (dy n j + dy n (j+1)) / 2 := by
  simp only [dy]; push_cast; rw [pow_succ]; field_simp; ring

lemma dy_lt {n k k' : ℕ} (h : k < k') : dy n k < dy n k' := by
  simp only [dy]; apply div_lt_div_of_pos_right _ (by positivity); exact_mod_cast h

lemma dy_le {n k k' : ℕ} (h : k ≤ k') : dy n k ≤ dy n k' := by
  simp only [dy]; apply div_le_div_of_nonneg_right _ (by positivity); exact_mod_cast h

lemma dy_zero (n : ℕ) : dy n 0 = 0 := by simp [dy]
lemma dy_top (n : ℕ) : dy n (2^n) = 1 := by simp [dy]

def Inv (n : ℕ) (f : ℕ → Set Ω) : Prop :=
  (∀ k ≤ 2^n, MeasurableSet (f k) ∧ P.real (f k) = dy n k ∧
    ((0 < k ∧ k < 2^n) → Lset P X (dy n k) ⊆ f k ∧ f k ⊆ Hset P X (dy n k))) ∧
  (∀ k < 2^n, f k ⊆ f (k+1)) ∧ f 0 = ∅ ∧ f (2^n) = univ

def Good (n : ℕ) (f : ℕ → Set Ω) (k : ℕ) (m : Set Ω) : Prop :=
  MeasurableSet m ∧ f (k/2) ∪ Lset P X (dy (n+1) k) ⊆ m ∧
    m ⊆ f (k/2+1) ∩ Hset P X (dy (n+1) k) ∧ P.real m = dy (n+1) k

lemma step (hP : TailRiskSharing.VaRConv.IsAtomless P) (hX : Measurable X) {n : ℕ}
    {f : ℕ → Set Ω} (hI : Inv P X n f) {j : ℕ} (hj : j < 2^n) :
    ∃ m, Good P X n f (2*j+1) m := by
  have hk : (2*j+1)/2 = j := by omega
  unfold Good; rw [hk]
  set q := dy (n+1) (2*j+1) with hq
  have hqa : dy n j < q := by rw [hq, dy_odd]; linarith [dy_lt (n := n) (Nat.lt_succ_self j)]
  have hqb : q < dy n (j+1) := by rw [hq, dy_odd]; linarith [dy_lt (n := n) (Nat.lt_succ_self j)]
  have hq0 : 0 < q := lt_of_le_of_lt (by rw [← dy_zero n]; exact dy_le (Nat.zero_le _)) hqa
  have hq1 : q < 1 := lt_of_lt_of_le hqb (by rw [← dy_top n]; exact dy_le hj)
  obtain ⟨ha_m, ha_P, ha_C⟩ := hI.1 j hj.le
  obtain ⟨hb_m, hb_P, hb_C⟩ := hI.1 (j+1) hj
  have hab : f j ⊆ f (j+1) := hI.2.1 j hj
  have hLm : MeasurableSet (Lset P X q) := measurableSet_lt hX measurable_const
  have hHm : MeasurableSet (Hset P X q) := measurableSet_le hX measurable_const
  have hLH : Lset P X q ⊆ Hset P X q := fun ω (h : X ω < _) => show X ω ≤ _ from h.le
  have hHq : q ≤ P.real (Hset P X q) := le_F_xq P X hX hq0 hq1
  have hLq : P.real (Lset P X q) ≤ q := measure_lt_xq P X hX hq0
  -- lower side
  have hlo : f j ⊆ Hset P X q ∧ P.real (f j ∪ Lset P X q) ≤ q := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; rw [hI.2.2.1]; simp only [empty_union]; exact ⟨empty_subset _, hLq⟩
    · have hC := ha_C ⟨hpos, hj⟩
      have ha0 : 0 < dy n j := by
        rw [← dy_zero n]; exact dy_lt hpos
      have hmono := xq_mono P X hX ha0 hq1 hqa.le
      refine ⟨hC.2.trans fun ω (h : X ω ≤ _) => show X ω ≤ _ from h.trans hmono, ?_⟩
      rcases hmono.lt_or_eq with hlt | heq
      · have : f j ∪ Lset P X q ⊆ Lset P X q :=
          union_subset (hC.2.trans fun ω (h : X ω ≤ _) => show X ω < _ from
            lt_of_le_of_lt h hlt) subset_rfl
        exact (measureReal_mono this).trans hLq
      · have : f j ∪ Lset P X q ⊆ f j := by
          refine union_subset subset_rfl ?_
          have : Lset P X q = Lset P X (dy n j) := by simp only [Lset, heq]
          rw [this]; exact hC.1
        exact (measureReal_mono this).trans (by rw [ha_P]; exact hqa.le)
  have hhi : Lset P X q ⊆ f (j+1) ∧ q ≤ P.real (f (j+1) ∩ Hset P X q) := by
    rcases (Nat.succ_le_of_lt hj).lt_or_eq with hlt | heq
    · have hC := hb_C ⟨Nat.succ_pos _, hlt⟩
      have hb1 : dy n (j+1) < 1 := by rw [← dy_top n]; exact dy_lt hlt
      have hmono := xq_mono P X hX hq0 hb1 hqb.le
      have hLL : Lset P X q ⊆ Lset P X (dy n (j+1)) := fun ω (h : X ω < _) =>
        show X ω < _ from lt_of_lt_of_le h hmono
      refine ⟨hLL.trans hC.1, ?_⟩
      rcases hmono.lt_or_eq with hlt' | heq'
      · have : Hset P X q ⊆ f (j+1) ∩ Hset P X q :=
          subset_inter ((show Hset P X q ⊆ Lset P X (dy n (j+1)) from fun ω (h : X ω ≤ _) =>
            show X ω < _ from lt_of_le_of_lt h hlt').trans hC.1) subset_rfl
        exact hHq.trans (measureReal_mono this)
      · have : f (j+1) ⊆ f (j+1) ∩ Hset P X q := by
          refine subset_inter subset_rfl ?_
          have : Hset P X q = Hset P X (dy n (j+1)) := by simp only [Hset, heq']
          rw [this]; exact hC.2
        exact (by rw [hb_P]; exact hqb.le : q ≤ P.real (f (j+1))).trans (measureReal_mono this)
    · have heq2 : j + 1 = 2^n := heq
      rw [heq2, hI.2.2.2]
      exact ⟨subset_univ _, by simpa using hHq⟩
  obtain ⟨m, hm, h1, h2, h3⟩ := sierpinski_between P hP (f j ∪ Lset P X q)
    (f (j+1) ∩ Hset P X q) (ha_m.union hLm) (hb_m.inter hHm)
    (union_subset (subset_inter hab hlo.1) (subset_inter hhi.1 hLH)) q hlo.2 hhi.2
  exact ⟨m, hm, h1, h2, h3⟩

open Classical in
noncomputable def nextLevel (n : ℕ) (f : ℕ → Set Ω) : ℕ → Set Ω := fun k =>
  if Even k then f (k/2) else
    if h : ∃ m, Good P X n f k m then Classical.choose h else ∅

noncomputable def A : ℕ → ℕ → Set Ω
  | 0 => fun k => if k = 0 then ∅ else univ
  | n+1 => nextLevel P X n (A n)

lemma A_succ_even (n i : ℕ) : A P X (n+1) (2*i) = A P X n i := by
  show nextLevel P X n (A P X n) (2*i) = _
  simp only [nextLevel, even_two_mul, if_true]
  congr 1; omega

lemma A_succ_odd (n j : ℕ) (h : ∃ m, Good P X n (A P X n) (2*j+1) m) :
    Good P X n (A P X n) (2*j+1) (A P X (n+1) (2*j+1)) := by
  show Good P X n (A P X n) (2*j+1) (nextLevel P X n (A P X n) (2*j+1))
  have hne : ¬ Even (2*j+1) := by rintro ⟨r, hr⟩; omega
  simp only [nextLevel, hne, if_false, dif_pos h]
  exact Classical.choose_spec h

lemma inv_A (hP : TailRiskSharing.VaRConv.IsAtomless P) (hX : Measurable X) :
    ∀ n, Inv P X n (A P X n) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun k hk => ?_, fun k hk => ?_, by simp [A], by simp [A]⟩
    · interval_cases k
      · simp [A, dy]
      · simp [A, dy]
    · simp at hk; subst hk; simp [A]
  | succ n ih =>
    have hodd : ∀ j < 2^n, Good P X n (A P X n) (2*j+1) (A P X (n+1) (2*j+1)) :=
      fun j hj => A_succ_odd P X n j (step P X hP hX ih hj)
    have hk1 : ∀ j, (2*j+1)/2 = j := fun j => by omega
    refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
    · obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
      · rw [A_succ_even, dy_double]
        have hi : i ≤ 2^n := by rw [pow_succ] at hk; omega
        obtain ⟨h1, h2, h3⟩ := ih.1 i hi
        refine ⟨h1, h2, fun hc => h3 ⟨by omega, by rw [pow_succ] at hc; omega⟩⟩
      · have hi : i < 2^n := by rw [pow_succ] at hk; omega
        obtain ⟨g1, g2, g3, g4⟩ := hodd i hi
        rw [hk1] at g2 g3
        exact ⟨g1, g4, fun _ => ⟨subset_union_right.trans g2, g3.trans inter_subset_right⟩⟩
    · obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
      · have hi : i < 2^n := by rw [pow_succ] at hk; omega
        obtain ⟨g1, g2, g3, g4⟩ := hodd i hi
        rw [hk1] at g2
        rw [A_succ_even]; exact subset_union_left.trans g2
      · have hi : i < 2^n := by rw [pow_succ] at hk; omega
        obtain ⟨g1, g2, g3, g4⟩ := hodd i hi
        rw [hk1] at g3
        have : 2*i+1+1 = 2*(i+1) := by ring
        rw [this, A_succ_even]; exact g3.trans inter_subset_left
    · rw [show (0:ℕ) = 2*0 from rfl, A_succ_even]; exact ih.2.2.1
    · rw [pow_succ, mul_comm, A_succ_even]; exact ih.2.2.2

lemma A_lift (n d k : ℕ) : A P X (n+d) (k * 2^d) = A P X n k := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, pow_succ, show k * (2^d * 2) = 2 * (k * 2^d) by ring, A_succ_even, ih]

lemma A_mono_level (hP : TailRiskSharing.VaRConv.IsAtomless P) (hX : Measurable X) (n : ℕ)
    {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (h2 : k₂ ≤ 2^n) : A P X n k₁ ⊆ A P X n k₂ := by
  induction k₂, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ k hk ih => exact (ih (by omega)).trans ((inv_A P X hP hX n).2.1 k (by omega))

lemma A_mono (hP : TailRiskSharing.VaRConv.IsAtomless P) (hX : Measurable X) {m n k' k : ℕ}
    (hk : k ≤ 2^n) (hle : dy m k' ≤ dy n k) : A P X m k' ⊆ A P X n k := by
  have e1 := A_lift P X m n k'
  have e2 := A_lift P X n m k
  rw [Nat.add_comm n m] at e2
  rw [← e1, ← e2]
  have hineq : k' * 2^n ≤ k * 2^m := by
    simp only [dy] at hle
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at hle
    exact_mod_cast hle
  apply A_mono_level P X hP hX (m+n) hineq
  rw [pow_add, mul_comm (2^m)]; exact Nat.mul_le_mul_right _ hk

end Dyadic

section Final

variable (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)

lemma le_of_forall_pow {a b : ℝ} (h : ∀ n : ℕ, a ≤ b + 1 / 2^n) : a ≤ b := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (show (1/2 : ℝ) < 1 by norm_num)
  have := h n
  rw [one_div_pow] at hn
  linarith

lemma dy_succ (n k : ℕ) : dy n (k+1) = dy n k + 1 / 2^n := by
  simp only [dy]; push_cast; ring

lemma dy_nonneg (n k : ℕ) : 0 ≤ dy n k := by simp only [dy]; positivity

def Rset (ω : Ω) : Set ℝ := {r | ∃ n k, k ≤ 2^n ∧ ω ∈ A P X n k ∧ r = dy n k}

noncomputable def U (ω : Ω) : ℝ := sInf (Rset P X ω)

lemma R_nonempty (ω : Ω) : (Rset P X ω).Nonempty :=
  ⟨1, 0, 1, by simp, by simp [A], by simp [dy]⟩

lemma R_bdd (ω : Ω) : BddBelow (Rset P X ω) :=
  ⟨0, by rintro _ ⟨n, k, -, -, rfl⟩; exact dy_nonneg n k⟩

lemma U_le_dy {ω : Ω} {n k : ℕ} (hk : k ≤ 2^n) (h : ω ∈ A P X n k) : U P X ω ≤ dy n k :=
  csInf_le (R_bdd P X ω) ⟨n, k, hk, h, rfl⟩

lemma U_nonneg (ω : Ω) : 0 ≤ U P X ω :=
  le_csInf (R_nonempty P X ω) (by rintro _ ⟨n, k, -, -, rfl⟩; exact dy_nonneg n k)

lemma U_le_one (ω : Ω) : U P X ω ≤ 1 := by
  have := U_le_dy P X (n := 0) (k := 1) (ω := ω) (by simp) (by simp [A])
  simpa [dy] using this

lemma mem_of_U_lt (hP : TailRiskSharing.VaRConv.IsAtomless P) (hX : Measurable X) {ω : Ω}
    {n k : ℕ} (hk : k ≤ 2^n) (h : U P X ω < dy n k) : ω ∈ A P X n k := by
  obtain ⟨_, ⟨m, k', hk', hω, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (R_nonempty P X ω) h
  exact A_mono P X hP hX hk hlt.le hω

lemma U_meas (hP : TailRiskSharing.VaRConv.IsAtomless P) (hX : Measurable X) :
    Measurable (U P X) := by
  apply measurable_of_Iio
  intro v
  have : U P X ⁻¹' Iio v = ⋃ n, ⋃ k, ⋃ (_ : k ≤ 2^n ∧ dy n k < v), A P X n k := by
    ext ω
    simp only [mem_preimage, mem_Iio, mem_iUnion]
    constructor
    · intro h
      obtain ⟨_, ⟨m, k', hk', hω, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (R_nonempty P X ω) h
      exact ⟨m, k', ⟨hk', hlt⟩, hω⟩
    · rintro ⟨n, k, ⟨hk, hlt⟩, hω⟩
      exact lt_of_le_of_lt (U_le_dy P X hk hω) hlt
  rw [this]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun k =>
    MeasurableSet.iUnion fun h => ((inv_A P X hP hX n).1 k h.1).1

lemma cdf_U (hP : TailRiskSharing.VaRConv.IsAtomless P) (hX : Measurable X) {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : P.real {ω | U P X ω ≤ v} = v := by
  rcases hv1.lt_or_eq with hv1 | rfl
  · have hbound : ∀ n : ℕ, P.real {ω | U P X ω ≤ v} ≤ v + 1 / 2^n ∧
        v ≤ P.real {ω | U P X ω ≤ v} + 1 / 2^n := by
      intro n
      set k := ⌊v * 2^n⌋₊ with hkdef
      have hpow : (0:ℝ) < 2^n := by positivity
      have hk1 : (k:ℝ) ≤ v * 2^n := Nat.floor_le (by positivity)
      have hk2 : v * 2^n < (k:ℝ) + 1 := Nat.lt_floor_add_one _
      have hkn : k + 1 ≤ 2^n := by
        have : k < 2^n := by
          rw [hkdef, Nat.floor_lt (by positivity)]; push_cast; nlinarith
        omega
      have hdk : dy n k ≤ v := by simp only [dy]; rw [div_le_iff₀ hpow]; exact hk1
      have hdk1 : v < dy n (k+1) := by
        simp only [dy]; rw [lt_div_iff₀ hpow]; push_cast; exact hk2
      have hs := dy_succ n k
      obtain ⟨hm1, hP1, -⟩ := (inv_A P X hP hX n).1 k (by omega)
      obtain ⟨hm2, hP2, -⟩ := (inv_A P X hP hX n).1 (k+1) hkn
      have sub1 : A P X n k ⊆ {ω | U P X ω ≤ v} := fun ω hω =>
        (U_le_dy P X (by omega) hω).trans hdk
      have sub2 : {ω | U P X ω ≤ v} ⊆ A P X n (k+1) := fun ω (hω : U P X ω ≤ v) =>
        mem_of_U_lt P X hP hX hkn (lt_of_le_of_lt hω hdk1)
      have i1 := measureReal_mono (μ := P) sub1
      have i2 := measureReal_mono (μ := P) sub2
      constructor <;> linarith
    exact le_antisymm (le_of_forall_pow fun n => (hbound n).1)
      (le_of_forall_pow fun n => (hbound n).2)
  · have : {ω | U P X ω ≤ 1} = univ := eq_univ_of_forall fun ω => U_le_one P X ω
    rw [this]; simp

lemma map_U (hP : TailRiskSharing.VaRConv.IsAtomless P) (hX : Measurable X) :
    P.map (U P X) = volume.restrict (Icc (0:ℝ) 1) := by
  have hUm := U_meas P X hP hX
  have : IsFiniteMeasure (P.map (U P X)) := inferInstance
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [Measure.map_apply hUm measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge a 0 with ha | ha
  · have h1 : U P X ⁻¹' Iic a = ∅ := eq_empty_of_forall_notMem fun ω (h : U P X ω ≤ a) =>
      absurd (U_nonneg P X ω) (not_le.2 (lt_of_le_of_lt h ha))
    have h2 : Iic a ∩ Icc (0:ℝ) 1 = ∅ := eq_empty_of_forall_notMem fun x hx =>
      absurd (hx.2.1) (not_le.2 (lt_of_le_of_lt hx.1 ha))
    rw [h1, h2]; simp
  rcases lt_or_ge a 1 with ha1 | ha1
  · have h2 : Iic a ∩ Icc (0:ℝ) 1 = Icc 0 a := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    rw [h2, Real.volume_Icc, sub_zero]
    have := cdf_U P X hP hX ha ha1.le
    rw [show ENNReal.ofReal a = ENNReal.ofReal (P.real {ω | U P X ω ≤ a}) by rw [this],
      measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rfl
  · have h1 : U P X ⁻¹' Iic a = univ := eq_univ_of_forall fun ω =>
      show U P X ω ≤ a from (U_le_one P X ω).trans ha1
    have h2 : Iic a ∩ Icc (0:ℝ) 1 = Icc 0 1 := inter_eq_right.2 fun x hx => hx.2.trans ha1
    rw [h1, h2, Real.volume_Icc]; simp

local notation "F" => TailRiskSharing.VaRConv.distFn P X

lemma U_le_F (hP : TailRiskSharing.VaRConv.IsAtomless P) (hX : Measurable X) (ω : Ω) :
    U P X ω ≤ F (X ω) := by
  set p := F (X ω) with hp
  rcases lt_or_ge p 1 with hp1 | hp1
  · apply le_of_forall_pow
    intro n
    set k := ⌊p * 2^n⌋₊ + 1 with hkdef
    have hpow : (0:ℝ) < 2^n := by positivity
    have hp0 : 0 ≤ p := F_nonneg P X _
    have hk1 : ((⌊p * 2^n⌋₊ : ℕ) : ℝ) ≤ p * 2^n := Nat.floor_le (by positivity)
    have hk2 : p * 2^n < ((⌊p * 2^n⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hkn : k ≤ 2^n := by
      have : ⌊p * 2^n⌋₊ < 2^n := by
        rw [Nat.floor_lt (by positivity)]; push_cast; nlinarith
      omega
    have hdk : p < dy n k := by
      simp only [dy, hkdef]; rw [lt_div_iff₀ hpow]; push_cast; exact hk2
    have hdk' : dy n k ≤ p + 1 / 2^n := by
      rw [hkdef, dy_succ]; simp only [dy]
      have : ((⌊p * 2^n⌋₊ : ℕ) : ℝ) / 2^n ≤ p := by rw [div_le_iff₀ hpow]; exact hk1
      linarith
    have hmem : ω ∈ A P X n k := by
      rcases hkn.lt_or_eq with hlt | heq
      · have hk0 : 0 < k := by omega
        have hC := ((inv_A P X hP hX n).1 k hkn).2.2 ⟨hk0, hlt⟩
        apply hC.1
        show X ω < xq P X (dy n k)
        by_contra hc; push Not at hc
        have hq0 : 0 < dy n k := lt_of_le_of_lt hp0 hdk
        have hq1 : dy n k < 1 := by rw [← dy_top n]; exact dy_lt hlt
        have := (le_F_xq P X hX hq0 hq1).trans (F_mono P X hX hc)
        linarith
      · rw [heq, (inv_A P X hP hX n).2.2.2]; trivial
    exact (U_le_dy P X hkn hmem).trans hdk'
  · exact (U_le_one P X ω).trans hp1

theorem main (hP : TailRiskSharing.VaRConv.IsAtomless P) (hX : Measurable X) :
    TailRiskSharing.VaRTail.IsQuantileUniform P X (U P X) := by
  have hUm := U_meas P X hP hX
  refine ⟨hUm, map_U P X hP hX, ?_⟩
  have h0 : ∀ᵐ ω ∂P, 0 < U P X ω := by
    rw [ae_iff]
    have hset : {ω | ¬ 0 < U P X ω} = {ω | U P X ω ≤ 0} := by ext; simp
    rw [hset]
    have := cdf_U P X hP hX le_rfl zero_le_one
    rwa [measureReal_eq_zero_iff] at this
  have hr : ∀ r : ℚ, ∀ᵐ ω ∂P, U P X ω ≤ F r → X ω ≤ r := by
    intro r
    rw [ae_iff]
    have hset : {ω | ¬ (U P X ω ≤ F r → X ω ≤ r)} =
        {ω | U P X ω ≤ F r} \ {ω | X ω ≤ r} := by ext; simp
    rw [hset]
    have hsub : {ω | X ω ≤ (r:ℝ)} ⊆ {ω | U P X ω ≤ F r} := fun ω (h : X ω ≤ r) =>
      show U P X ω ≤ F r from (U_le_F P X hP hX ω).trans (F_mono P X hX h)
    have hm : MeasurableSet {ω | X ω ≤ (r:ℝ)} := measurableSet_le hX measurable_const
    have h1 := cdf_U P X hP hX (F_nonneg P X r) (F_le_one P X r)
    have h2 : P.real ({ω | U P X ω ≤ F r} \ {ω | X ω ≤ r}) = 0 := by
      rw [measureReal_sdiff hsub hm, h1]; simp [TailRiskSharing.VaRConv.distFn]
    rwa [measureReal_eq_zero_iff] at h2
  filter_upwards [h0, ae_all_iff.2 hr] with ω hω0 hωr
  unfold TailRiskSharing.VaRConv.VaRL
  rw [sub_sub_cancel]
  have hmem : X ω ∈ {x | U P X ω ≤ F x} := U_le_F P X hP hX ω
  have hbdd := S_bdd P X hX hω0
  apply le_antisymm (csInf_le hbdd hmem)
  by_contra hlt; push Not at hlt
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
  obtain ⟨x, hx, hxr⟩ := exists_lt_of_csInf_lt ⟨_, hmem⟩ hr1
  have : U P X ω ≤ F r := (show U P X ω ≤ F x from hx).trans (F_mono P X hX hxr.le)
  exact absurd (hωr r this) (not_le.2 hr2)

end Final

end FreshQUniform

open MeasureTheory

namespace TailRiskSharing.VaRTail

theorem exists_quantile_uniform {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (X : Ω → ℝ) (hX : X ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ))) :
    ∃ U : Ω → ℝ, IsQuantileUniform P X U :=
  ⟨FreshQUniform.U P X, FreshQUniform.main P X hP hX⟩

end TailRiskSharing.VaRTail


-- Platform entry point: restates the target verbatim.
namespace TailRiskSharing.VaRTail

theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (X : Ω → ℝ) (hX : X ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ))) :
    ∃ U : Ω → ℝ, IsQuantileUniform P X U := by
  apply @TailRiskSharing.VaRTail.exists_quantile_uniform <;> assumption

end TailRiskSharing.VaRTail
