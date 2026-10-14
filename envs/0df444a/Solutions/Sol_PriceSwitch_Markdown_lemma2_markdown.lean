-- Prove2me | solution 1 for PriceSwitch.Markdown.lemma2_markdown
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:10:37.833723+00:00
-- url     : https://prove2.me/submissions/adae5f74-282f-4914-ac56-7f309895fea0

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model



namespace PriceSwitch.Markdown

open Nat

noncomputable def FF (n : ℕ) (m : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, Real.exp (-m) * m ^ k / (k ! : ℝ)

lemma hasDerivAt_FF (n : ℕ) (m : ℝ) :
    HasDerivAt (FF (n + 1)) (-(Real.exp (-m) * m ^ n / (n ! : ℝ))) m := by
  induction n with
  | zero =>
    have h : FF 1 = fun m => Real.exp (-m) := by funext m; simp [FF]
    rw [h]
    have := (Real.hasDerivAt_exp (-m)).comp m (hasDerivAt_neg m)
    refine this.congr_deriv ?_
    simp
  | succ n ih =>
    have h : FF (n + 1 + 1) = fun m => FF (n + 1) m + Real.exp (-m) * m ^ (n + 1) / ((n + 1) ! : ℝ) := by
      funext m; simp [FF, Finset.sum_range_succ _ (n + 1)]
    rw [h]
    have h1 : HasDerivAt (fun m : ℝ => Real.exp (-m)) (-Real.exp (-m)) m := by
      have := (Real.hasDerivAt_exp (-m)).comp m (hasDerivAt_neg m)
      exact this.congr_deriv (by simp)
    have h2 := ((h1.mul (hasDerivAt_pow (n + 1) m)).div_const ((n + 1) ! : ℝ))
    refine (ih.add h2).congr_deriv ?_
    rw [Nat.factorial_succ]
    push_cast
    have : (n ! : ℝ) ≠ 0 := by positivity
    have h3 : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

lemma FF_zero_succ (n : ℕ) : FF (n + 1) 0 = 1 := by
  simp [FF, Finset.sum_range_succ', zero_pow_eq]

lemma FF_cont (n : ℕ) : Continuous (FF (n + 1)) :=
  continuous_iff_continuousAt.2 fun m => (hasDerivAt_FF n m).continuousAt

lemma FF_anti (n : ℕ) : StrictAntiOn (FF (n + 1)) (Set.Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0) (FF_cont n).continuousOn
  intro x hx
  rw [interior_Ici] at hx
  have hx' : (0:ℝ) < x := hx
  rw [(hasDerivAt_FF n x).deriv]
  have : 0 < Real.exp (-x) * x ^ n / (n ! : ℝ) := by positivity
  linarith

lemma FF_succ_sub (n : ℕ) (m : ℝ) :
    FF (n + 1 + 1) m - FF (n + 1) m = Real.exp (-m) * m ^ (n + 1) / ((n + 1) ! : ℝ) := by
  simp [FF, Finset.sum_range_succ _ (n + 1)]

lemma FF_tendsto (n : ℕ) : Filter.Tendsto (FF (n + 1)) Filter.atTop (nhds 0) := by
  unfold FF
  have : ∀ k ∈ Finset.range (n + 1), Filter.Tendsto (fun m : ℝ => Real.exp (-m) * m ^ k / (k ! : ℝ))
      Filter.atTop (nhds 0) := by
    intro k _
    have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).div_const (k ! : ℝ)
    simp only [zero_div] at this
    refine this.congr fun m => ?_
    ring
  simpa using tendsto_finsetSum _ this

lemma G_eq (a la b lb : ℝ) (n : ℕ) (t : ℝ) (ht : 0 ≤ lb * t) :
    G a la b lb n t = la * (a - b) + b * (la - lb) * FF n (lb * t) := by
  unfold G PriceSwitch.Markdown.poissonTail FF
  have h : ((lb * t).toNNReal : ℝ) = lb * t := Real.coe_toNNReal _ ht
  simp only [ProbabilityTheory.poissonPMFReal, h]
  ring



lemma zero_struct (a la b lb : ℝ) (hp : IsMarkdownPair a la b lb) (k : ℕ) :
    ∃ s : ℝ, 0 < s ∧ G a la b lb (k + 1) s = 0 ∧
      (∀ u, 0 ≤ u → u < s → G a la b lb (k + 1) u < 0) ∧
      (∀ u, s < u → 0 < G a la b lb (k + 1) u) := by
  obtain ⟨hb, hla, hab, hll, hr⟩ := hp
  have hd : 0 < b * (lb - la) := mul_pos hb (by linarith)
  have he : 0 < la * (a - b) := mul_pos hla (by linarith)
  have hlb : 0 < lb := by linarith
  set g := fun t => G a la b lb (k + 1) t with hg
  have hmono : ∀ u v : ℝ, 0 ≤ u → u < v → g u < g v := by
    intro u v hu huv
    simp only [hg]
    have hu' : 0 ≤ lb * u := by positivity
    have hv' : 0 ≤ lb * v := by nlinarith
    rw [G_eq _ _ _ _ _ u hu', G_eq _ _ _ _ _ v hv']
    have := FF_anti k (show lb * u ∈ Set.Ici 0 from hu')
      (show lb * v ∈ Set.Ici 0 from hv') (by nlinarith)
    nlinarith
  have hcont : ContinuousOn g (Set.Ici 0) := by
    have : ContinuousOn (fun t => la * (a - b) + b * (la - lb) * FF (k + 1) (lb * t)) (Set.Ici 0) :=
      (continuous_const.add (continuous_const.mul ((FF_cont k).comp (continuous_const.mul continuous_id)))).continuousOn
    refine this.congr fun t ht => ?_
    simp only [hg]
    exact G_eq _ _ _ _ _ _ (mul_nonneg hlb.le ht)
  have h0 : g 0 < 0 := by
    simp only [hg]
    rw [G_eq _ _ _ _ _ _ (by simp), mul_zero, FF_zero_succ]
    nlinarith
  obtain ⟨T, hT0, hT⟩ : ∃ T : ℝ, 0 ≤ T ∧ 0 < g T := by
    have ht : Filter.Tendsto (fun T : ℝ => FF (k + 1) (lb * T)) Filter.atTop (nhds 0) :=
      (FF_tendsto k).comp (Filter.tendsto_id.const_mul_atTop hlb)
    have hev := (ht.eventually (gt_mem_nhds (show (0:ℝ) < la * (a - b) / (b * (lb - la)) by positivity)))
    obtain ⟨T, hT⟩ := (hev.and (Filter.eventually_ge_atTop 0)).exists
    refine ⟨T, hT.2, ?_⟩
    simp only [hg]
    rw [G_eq _ _ _ _ _ _ (mul_nonneg hlb.le hT.2)]
    have := hT.1
    rw [lt_div_iff₀ hd] at this
    nlinarith
  have hivt := intermediate_value_Icc hT0 (hcont.mono Set.Icc_subset_Ici_self)
  obtain ⟨s, hs, hgs⟩ := hivt (show (0:ℝ) ∈ Set.Icc (g 0) (g T) from ⟨h0.le, hT.le⟩)
  have hs0 : 0 < s := by
    rcases hs.1.eq_or_lt with h | h
    · rw [← h] at hgs; linarith
    · exact h
  refine ⟨s, hs0, hgs, fun u hu hus => ?_, fun u hsu => ?_⟩
  · have := hmono u s hu hus; linarith
  · have := hmono s u hs.1 hsu; linarith

lemma sInf_zero_eq (a la b lb : ℝ) (n : ℕ) (s : ℝ) (hs : 0 < s)
    (h0 : G a la b lb n s = 0)
    (hpos : ∀ u, 0 ≤ u → u < s → G a la b lb n u < 0)
    (hneg : ∀ u, s < u → 0 < G a la b lb n u) :
    sInf {u : ℝ | 0 ≤ u ∧ G a la b lb n u = 0} = s := by
  have : {u : ℝ | 0 ≤ u ∧ G a la b lb n u = 0} = {s} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hu, hu0⟩
      rcases lt_trichotomy u s with h | h | h
      · have := hpos u hu h; linarith
      · exact h
      · have := hneg u h; linarith
    · rintro rfl; exact ⟨hs.le, h0⟩
  rw [this, csInf_singleton]


theorem lemma2_core (a la b lb : ℝ) (hpair : IsMarkdownPair a la b lb) :
    let y : ℕ → ℝ := fun n => sInf {s : ℝ | 0 ≤ s ∧ G a la b lb n s = 0}
    (∀ n, 1 ≤ n → ∃ s, 0 ≤ s ∧ G a la b lb n s = 0) ∧
    0 < y 1 ∧
    StrictMonoOn y (Set.Ici 1) ∧
    (∀ n, 1 ≤ n → ∀ s, 0 ≤ s → s < y n → G a la b lb n s < 0) ∧
    (∀ n, 1 ≤ n → ∀ s, y n < s → 0 < G a la b lb n s) := by
  intro y
  have key : ∀ n : ℕ, 1 ≤ n → ∃ s : ℝ, 0 < s ∧ G a la b lb n s = 0 ∧
      y n = s ∧
      (∀ u, 0 ≤ u → u < s → G a la b lb n u < 0) ∧
      (∀ u, s < u → 0 < G a la b lb n u) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s, hs, h0, hpos, hneg⟩ := zero_struct a la b lb hpair k
    exact ⟨s, hs, h0, sInf_zero_eq _ _ _ _ _ s hs h0 hpos hneg, hpos, hneg⟩
  have hd : 0 < b * (lb - la) := mul_pos hpair.pos_price (by have := hpair.rate_lt; linarith)
  refine ⟨fun n hn => ?_, ?_, ?_, fun n hn s hs hlt => ?_, fun n hn s hlt => ?_⟩
  · obtain ⟨s, hs, h0, -⟩ := key n hn
    exact ⟨s, hs.le, h0⟩
  · obtain ⟨s, hs, h0, he, -⟩ := key 1 le_rfl
    rw [he]; exact hs
  · have step : ∀ n : ℕ, 1 ≤ n → y n < y (n + 1) := by
      intro n hn
      obtain ⟨s, hs, h0, he, hpos, hneg⟩ := key n hn
      obtain ⟨s', hs', h0', he', hpos', hneg'⟩ := key (n + 1) (by omega)
      rw [he, he']
      by_contra hcon
      push_neg at hcon
      have h1 : 0 ≤ G a la b lb (n + 1) s := by
        rcases hcon.eq_or_lt with h | h
        · rw [← h]; exact h0'.ge
        · exact (hneg' s h).le
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hlbs : 0 ≤ lb * s := by
        have := hpair.pos_rate; have := hpair.rate_lt
        have : 0 < lb := by linarith
        positivity
      have h2 := G_eq a la b lb (k + 1 + 1) s hlbs
      have h3 := G_eq a la b lb (k + 1) s hlbs
      have h4 := FF_succ_sub k (lb * s)
      have h5 : 0 < Real.exp (-(lb * s)) * (lb * s) ^ (k + 1) / ((k + 1) ! : ℝ) := by
        have := hpair.pos_rate; have := hpair.rate_lt
        have : 0 < lb := by linarith
        positivity
      rw [h3] at h0
      rw [h2] at h1
      nlinarith
    intro m hm n hn hmn
    simp only [Set.mem_Ici] at hm hn
    induction n, hn using Nat.le_induction with
    | base => omega
    | succ n hn ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hmn with h | h
      · exact (ih h).trans (step n hn)
      · subst h; exact step m hm
  · obtain ⟨s', hs', h0, he, hpos, hneg⟩ := key n hn
    rw [he] at hlt
    exact hpos s hs hlt
  · obtain ⟨s', hs', h0, he, hpos, hneg⟩ := key n hn
    rw [he] at hlt
    exact hneg s hlt

end PriceSwitch.Markdown

open PriceSwitch.Markdown


theorem solution (a la b lb : ℝ) (hpair : IsMarkdownPair a la b lb) :
    let y : ℕ → ℝ := fun n => sInf {s : ℝ | 0 ≤ s ∧ G a la b lb n s = 0}
    (∀ n, 1 ≤ n → ∃ s, 0 ≤ s ∧ G a la b lb n s = 0) ∧
    0 < y 1 ∧
    StrictMonoOn y (Set.Ici 1) ∧
    (∀ n, 1 ≤ n → ∀ s, 0 ≤ s → s < y n → G a la b lb n s < 0) ∧
    (∀ n, 1 ≤ n → ∀ s, y n < s → 0 < G a la b lb n s) := by
  exact lemma2_core a la b lb hpair
