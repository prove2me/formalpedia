-- Prove2me | solution 1 for SendSplit.Existence.six_implies_seven_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:35:21.945333+00:00
-- url     : https://prove2.me/submissions/be2282e6-ae45-4f2f-b12b-2d6226719fca

import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Definitions.Def_SendSplit_Existence_AugmentedGraph



namespace SendSplit.Existence
variable {n : ℕ}

section RealLemmas
variable {f : ℝ → ℝ}

lemma cc_diff (hf : ConcaveOn ℝ (Set.Ici 0) f) {t : ℝ} (ht : 0 < t) :
    DifferentiableWithinAt ℝ f (Set.Ioi t) t := by
  have h := (hf.neg).differentiableWithinAt_Ioi_of_mem_interior (x := t) (by simpa using ht)
  simpa using h.neg

lemma cc_F2 (hf : ConcaveOn ℝ (Set.Ici 0) f) {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    (f s - f t) / (s - t) ≤ derivWithin f (Set.Ioi t) t := by
  have := hf.slope_le_rightDeriv (x := t) (y := s) (Set.mem_Ici.2 ht.le)
    (Set.mem_Ici.2 (ht.le.trans hts.le)) hts (cc_diff hf ht)
  rwa [slope_def_field] at this

lemma cc_F3 (hf : ConcaveOn ℝ (Set.Ici 0) f) {t s : ℝ} (ht : 0 ≤ t) (hts : t < s) :
    derivWithin f (Set.Ioi s) s ≤ (f s - f t) / (s - t) := by
  have hs : 0 < s := ht.trans_lt hts
  have hd := (cc_diff hf hs).hasDerivWithinAt
  apply le_of_tendsto <| (hasDerivWithinAt_iff_tendsto_slope' Set.self_notMem_Ioi).mp hd
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : s < y := hy
  rw [slope_def_field]
  exact hf.slope_anti_adjacent (Set.mem_Ici.2 ht) (Set.mem_Ici.2 (hs.le.trans hy'.le)) hts hy'

lemma cc_F4 (hf : ConcaveOn ℝ (Set.Ici 0) f) {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) :
    derivWithin f (Set.Ioi s) s ≤ derivWithin f (Set.Ioi t) t := by
  rcases eq_or_lt_of_le hts with rfl | h
  · exact le_rfl
  · exact (cc_F3 hf ht.le h).trans (cc_F2 hf ht h)

/-- tangent line bound -/
lemma cc_tangent (hf : ConcaveOn ℝ (Set.Ici 0) f) {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    f s ≤ f t + derivWithin f (Set.Ioi t) t * (s - t) := by
  have := cc_F2 hf ht hts
  rw [div_le_iff₀ (by linarith)] at this
  linarith

/-- chord bound: f(s)/s ≥ f(T)/T ≥ d(T) -/
lemma cc_lower (hf : ConcaveOn ℝ (Set.Ici 0) f) (h0 : f 0 = 0) {s T : ℝ} (hs : 0 < s) (hsT : s < T) :
    derivWithin f (Set.Ioi T) T * s ≤ f s := by
  have h1 := cc_F3 hf (le_refl 0) (hs.trans hsT)
  have h2 := hf.slope_anti_adjacent (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 (hs.trans hsT).le) hs hsT
  simp only [h0, sub_zero] at h1 h2
  have hT : 0 < T := hs.trans hsT
  -- d T ≤ f T / T ≤ f s / s
  have h3 : derivWithin f (Set.Ioi T) T ≤ f s / s := by
    have : f T / T ≤ f s / s := by
      have hh : (f T - f s) / (T - s) ≤ f s / s := h2
      rw [div_le_div_iff₀ (by linarith) hs] at hh
      rw [div_le_div_iff₀ hT hs]
      nlinarith
    exact h1.trans this
  rwa [le_div_iff₀ hs] at h3

end RealLemmas
lemma sum_in_eq (G : ArcGraph n) (g : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => (j, i) ∈ G.A), g j i = ∑ p ∈ G.A, g p.1 p.2 := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  rw [← Finset.sum_product' (f := fun j i => if (j, i) ∈ G.A then g j i else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext p; simp

lemma sum_out_eq (G : ArcGraph n) (g : Fin n → Fin n → ℝ) :
    ∑ i, ∑ k ∈ Finset.univ.filter (fun k => (i, k) ∈ G.A), g i k = ∑ p ∈ G.A, g p.1 p.2 := by
  classical
  simp only [Finset.sum_filter]
  rw [← Finset.sum_product' (f := fun j i => if (j, i) ∈ G.A then g j i else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext p; simp

theorem flow_le_core (G : ArcGraph n) (r : Fin n → ℝ)
    (x : Fin n → Fin n → ℝ) (hx : IsFlow G r x) (p : Fin n × Fin n) (hp : p ∈ G.A)
    (hpC : ¬ SameComponent G p.1 p.2) :
    x p.1 p.2 ≤ ∑ i, max (r i) 0 := by
  classical
  obtain ⟨⟨hnn, hzero⟩, hcons⟩ := hx
  set Q : Finset (Fin n) := Finset.univ.filter (fun i => Reach G p.2 i) with hQ
  have hmem : ∀ i, i ∈ Q ↔ Reach G p.2 i := by intro i; simp [hQ]
  have hclosed : ∀ q ∈ G.A, q.1 ∈ Q → q.2 ∈ Q := by
    intro q hq h1
    rw [hmem] at h1 ⊢
    exact Relation.ReflTransGen.tail h1 hq
  have hpa : p.1 ∉ Q := by
    intro h
    rw [hmem] at h
    exact hpC ⟨Relation.ReflTransGen.single hp, h⟩
  have hb : p.2 ∈ Q := by rw [hmem]; exact Relation.ReflTransGen.refl
  have h1 : ∑ i ∈ Q, r i = ∑ q ∈ G.A, ((if q.2 ∈ Q then x q.1 q.2 else 0) - (if q.1 ∈ Q then x q.1 q.2 else 0)) := by
    have e1 := sum_in_eq G (fun j i => if i ∈ Q then x j i else 0)
    have e2 := sum_out_eq G (fun i k => if i ∈ Q then x i k else 0)
    rw [Finset.sum_sub_distrib, ← e1, ← e2, ← Finset.sum_sub_distrib]
    have : ∑ i ∈ Q, r i = ∑ i, if i ∈ Q then r i else 0 := by
      rw [hQ, Finset.sum_filter]; simp [hQ]
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i ∈ Q
    · simp only [h, if_true, ← hcons i]
    · simp [h]
  have h2 : x p.1 p.2 ≤ ∑ q ∈ G.A, ((if q.2 ∈ Q then x q.1 q.2 else 0) - (if q.1 ∈ Q then x q.1 q.2 else 0)) := by
    rw [← Finset.add_sum_erase _ _ hp]
    have : (if p.2 ∈ Q then x p.1 p.2 else 0) - (if p.1 ∈ Q then x p.1 p.2 else 0) = x p.1 p.2 := by
      simp [hb, hpa]
    rw [this]
    have : 0 ≤ ∑ q ∈ G.A.erase p, ((if q.2 ∈ Q then x q.1 q.2 else 0) - (if q.1 ∈ Q then x q.1 q.2 else 0)) := by
      refine Finset.sum_nonneg fun q hq => ?_
      have hqA := Finset.mem_of_mem_erase hq
      by_cases h : q.1 ∈ Q
      · simp [h, hclosed q hqA h]
      · by_cases h' : q.2 ∈ Q <;> simp [h, h', hnn]
    linarith
  have h3 : ∑ i ∈ Q, r i ≤ ∑ i, max (r i) 0 := by
    calc ∑ i ∈ Q, r i ≤ ∑ i ∈ Q, max (r i) 0 := Finset.sum_le_sum fun i _ => le_max_left _ _
      _ ≤ ∑ i, max (r i) 0 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => le_max_right _ _
  linarith


lemma slope_mul_le {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ici 0) f) (h0 : f 0 = 0) {a : ℝ} (ha : 0 ≤ a) :
    slopeAtInfty f * ((a : ℝ) : EReal) ≤ ((f a : ℝ) : EReal) := by
  rcases eq_or_lt_of_le ha with rfl | hpos
  · simp [h0]
  · have hle : slopeAtInfty f ≤ ((derivWithin f (Set.Ioi (a+1)) (a+1) : ℝ) : EReal) :=
      iInf₂_le (a+1) (by linarith)
    have hlow := cc_lower hf h0 hpos (by linarith : a < a + 1)
    generalize slopeAtInfty f = e at hle ⊢
    induction e using EReal.rec with
    | bot => rw [EReal.bot_mul_coe_of_pos hpos]; exact bot_le
    | coe r =>
      rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
      have := EReal.coe_le_coe_iff.1 hle
      nlinarith
    | top => exact absurd (top_le_iff.1 hle) (EReal.coe_ne_top _)

lemma chain_cons (G : ArcGraph n) (S : Finset (Fin n)) (cost : Option (Fin n) → Option (Fin n) → EReal)
    (i j : Fin n) (tl : List (Option (Fin n))) (hij : (i, j) ∈ G.A)
    (hl : IsAugChain G S (some j) none (some j :: tl)) :
    IsAugChain G S (some i) none (some i :: some j :: tl) ∧
    chainCost cost (some i :: some j :: tl) = cost (some i) (some j) + chainCost cost (some j :: tl) := by
  obtain ⟨h1, h2, h3⟩ := hl
  refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
  · rw [List.isChain_cons_cons]; exact ⟨hij, h1⟩
  · simpa [List.getLast?_cons_cons] using h3
  · simp [chainCost]

theorem six_core {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) (r : Fin n → ℝ) (S : Finset (Fin n))
    (hS : IsSinkSelection G S) (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ)
    (hext : ∀ p ∈ G.A, ¬ SameComponent G p.1 p.2 →
      b p.1 p.2 * (∑ i, max (r i) 0) ≤ c p.1 p.2 (∑ i, max (r i) 0))
    (h6 : ∀ u, HasMinCostChain G S (augCost G c b bν) u) :
    (∀ x, IsFlow G r x → ∀ p ∈ G.A,
        augCost G c b bν (some p.1) (some p.2) * ((x p.1 p.2 : ℝ) : EReal)
          ≤ ((c p.1 p.2 (x p.1 p.2) : ℝ) : EReal)) ∧
      (∀ i, minChainCost G S (augCost G c b bν) i ≠ ⊥ ∧
        minChainCost G S (augCost G c b bν) i ≠ ⊤) ∧
      ∀ p ∈ G.A, minChainCost G S (augCost G c b bν) p.1
        ≤ augCost G c b bν (some p.1) (some p.2) + minChainCost G S (augCost G c b bν) p.2 := by
  classical
  have hmin : ∀ i, ∃ l, IsAugChain G S (some i) none l ∧
      minChainCost G S (augCost G c b bν) i = chainCost (augCost G c b bν) l ∧
      chainCost (augCost G c b bν) l ≠ ⊥ ∧ chainCost (augCost G c b bν) l ≠ ⊤ := by
    intro i
    obtain ⟨l, hl, hb, ht, hle⟩ := h6 (some i)
    refine ⟨l, hl, le_antisymm (iInf₂_le l hl) (le_iInf₂ fun l' hl' => hle l' hl'), hb, ht⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx p hp
    have hxp : 0 ≤ x p.1 p.2 := hx.1.1 _ _
    by_cases hsc : SameComponent G p.1 p.2
    · have : augCost G c b bν (some p.1) (some p.2) = slopeAtInfty (c p.1 p.2) := by
        simp [augCost, hsc]
      rw [this]
      exact slope_mul_le (hc p hp).1 (hc p hp).2 hxp
    · have : augCost G c b bν (some p.1) (some p.2) = ((b p.1 p.2 : ℝ) : EReal) := by
        simp [augCost, hsc]
      rw [this, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      have hxD := flow_le_core G r x hx p hp hsc
      rcases eq_or_lt_of_le hxp with h0 | hpos
      · rw [← h0, mul_zero, (hc p hp).2]
      · set D := ∑ i, max (r i) 0 with hD
        have hDpos : 0 < D := lt_of_lt_of_le hpos hxD
        have hcc := (hc p hp).1
        have hmix := hcc.2 (Set.mem_Ici.2 hDpos.le) (Set.mem_Ici.2 (le_refl (0:ℝ)))
          (div_nonneg hxp hDpos.le) (sub_nonneg.2 ((div_le_one hDpos).2 hxD) : (0:ℝ) ≤ 1 - x p.1 p.2 / D)
          (by ring)
        simp only [smul_eq_mul, (hc p hp).2, mul_zero, add_zero] at hmix
        have e : x p.1 p.2 / D * D = x p.1 p.2 := by field_simp
        rw [e] at hmix
        have h2 := hext p hp hsc
        have h3 : x p.1 p.2 / D * (b p.1 p.2 * D) ≤ x p.1 p.2 / D * c p.1 p.2 D :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg hxp hDpos.le)
        have e2 : x p.1 p.2 / D * (b p.1 p.2 * D) = b p.1 p.2 * x p.1 p.2 := by field_simp
        linarith
  · intro i
    obtain ⟨l, _, hl, hb, ht⟩ := hmin i
    rw [hl]; exact ⟨hb, ht⟩
  · intro p hp
    obtain ⟨l', hl', hl'eq, hb', ht'⟩ := hmin p.2
    obtain ⟨hch, hhead, hlast⟩ := hl'
    cases l' with
    | nil => simp at hhead
    | cons a tl =>
      have ha : a = some p.2 := by simpa using hhead
      subst ha
      obtain ⟨hchain, hcost⟩ := chain_cons G S (augCost G c b bν) p.1 p.2 tl hp ⟨hch, hhead, hlast⟩
      rw [hl'eq, ← hcost]
      exact iInf₂_le _ hchain

end SendSplit.Existence

open SendSplit.Existence


theorem solution {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) (r : Fin n → ℝ) (S : Finset (Fin n))
    (hS : IsSinkSelection G S) (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ)
    (hext : ∀ p ∈ G.A, ¬ SameComponent G p.1 p.2 →
      b p.1 p.2 * (∑ i, max (r i) 0) ≤ c p.1 p.2 (∑ i, max (r i) 0))
    (h6 : ∀ u, HasMinCostChain G S (augCost G c b bν) u) :
    (∀ x, IsFlow G r x → ∀ p ∈ G.A,
        augCost G c b bν (some p.1) (some p.2) * ((x p.1 p.2 : ℝ) : EReal)
          ≤ ((c p.1 p.2 (x p.1 p.2) : ℝ) : EReal)) ∧
      (∀ i, minChainCost G S (augCost G c b bν) i ≠ ⊥ ∧
        minChainCost G S (augCost G c b bν) i ≠ ⊤) ∧
      ∀ p ∈ G.A, minChainCost G S (augCost G c b bν) p.1
        ≤ augCost G c b bν (some p.1) (some p.2) + minChainCost G S (augCost G c b bν) p.2 := by
  exact six_core G c hc r S hS b bν hext h6
