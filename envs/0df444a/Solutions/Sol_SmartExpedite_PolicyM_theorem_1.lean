-- Prove2me | solution 1 for SmartExpedite.PolicyM.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:41:37.021634+00:00
-- url     : https://prove2.me/submissions/f44933e7-5ede-4103-9de8-b34f38caec8b

import Mathlib
import Definitions.Def_SmartExpedite_PolicyM_Model

open SmartExpedite.PolicyM

namespace SEXP

set_option linter.unusedSectionVars false

variable {K : ℕ}

lemma occ_add (a b : Fin K → ℕ) (l : ℕ) : occ (a + b) l = occ a l + occ b l := by
  unfold occ; split_ifs <;> simp

lemma occ_ev (s l : ℕ) : occ (ev K s) l = if l = s ∧ 1 ≤ l ∧ l ≤ K then 1 else 0 := by
  unfold occ ev
  by_cases h : 1 ≤ l ∧ l ≤ K
  · rw [dif_pos h]; simp only
    by_cases h2 : l = s
    · rw [if_pos (by omega), if_pos ⟨h2, h⟩]
    · rw [if_neg (by omega), if_neg (by tauto)]
  · rw [dif_neg h, if_neg (by tauto)]

lemma ev_zero : ev K 0 = 0 := by
  funext j; simp [ev]

lemma sum_mul_occ_ev (f : ℕ → ℕ) (s x y : ℕ) :
    ∑ l ∈ Finset.Icc x y, f l * occ (ev K s) l =
      if x ≤ s ∧ s ≤ y ∧ 1 ≤ s ∧ s ≤ K then f s else 0 := by
  simp_rw [occ_ev, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  by_cases h : x ≤ s ∧ s ≤ y ∧ 1 ≤ s ∧ s ≤ K
  · rw [if_pos h]
    have : (Finset.Icc x y).filter (fun l => l = s ∧ 1 ≤ l ∧ l ≤ K) = {s} := by
      ext l; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]; omega
    rw [this, Finset.sum_singleton]
  · rw [if_neg h]
    have : (Finset.Icc x y).filter (fun l => l = s ∧ 1 ≤ l ∧ l ≤ K) = ∅ := by
      ext l; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
    rw [this, Finset.sum_empty]

lemma seg_add (a b : Fin K → ℕ) (x y : ℕ) : seg (a + b) x y = seg a x y + seg b x y := by
  unfold seg; simp_rw [occ_add]; rw [Finset.sum_add_distrib]

lemma seg_ev (s x y : ℕ) :
    seg (ev K s) x y = if x ≤ s ∧ s ≤ y ∧ 1 ≤ s ∧ s ≤ K then 1 else 0 := by
  have := sum_mul_occ_ev (K := K) (fun _ => 1) s x y
  simpa [seg] using this

lemma seg_split (n : Fin K → ℕ) (x c y : ℕ) (h1 : x ≤ c + 1) (h2 : c ≤ y) :
    seg n x y = seg n x c + seg n (c + 1) y := by
  unfold seg
  have e : ∀ a b : ℕ, Finset.Icc a b = Finset.Ico a (b + 1) := fun a b => rfl
  rw [e, e, e, Finset.sum_Ico_consecutive _ h1 (by omega)]

lemma ev_le (a : Fin K → ℕ) (s : ℕ) (h : s = 0 ∨ 0 < occ a s) : ev K s ≤ a := by
  intro j
  simp only [ev]
  split_ifs with hj
  · rcases h with h | h
    · omega
    · unfold occ at h
      rw [dif_pos (by omega)] at h
      have : (⟨s - 1, by omega⟩ : Fin K) = j := by ext; simp; omega
      rw [this] at h; exact h
  · exact Nat.zero_le _

lemma occ_add_ev_self (q : Fin K → ℕ) (s : ℕ) (h1 : 1 ≤ s) (h2 : s ≤ K) :
    0 < occ (q + ev K s) s := by
  rw [occ_add, occ_ev, if_pos ⟨rfl, h1, h2⟩]; omega


def RouteOK (K : ℕ) (u : ℕ → ℕ → ℕ∞) (m : ℕ) (n : Fin K → ℕ) (j : ℕ) : Prop :=
  m + 1 ≤ j ∧ j ≤ K ∧ (∀ l, j ≤ l → l ≤ K - 1 → (seg n (m + 1) l : ℕ∞) < u m l) ∧
    (m + 2 ≤ j → u m (j - 1) ≤ (seg n (m + 1) (j - 1) : ℕ∞))

lemma expNode_ok (u : ℕ → ℕ → ℕ∞) (m : ℕ) (n : Fin K → ℕ) (hm : m < K) :
    RouteOK K u m n (expNode K u m n) := by
  unfold expNode
  simp only
  set S := (Finset.Icc (m + 1) (K - 1)).filter (fun k => u m k ≤ (seg n (m + 1) k : ℕ∞)) with hS
  by_cases h : S.Nonempty
  · rw [dif_pos h]
    have hmem0 := Finset.max'_mem S h
    have hmem : S.max' h ∈ Finset.Icc (m + 1) (K - 1) ∧ u m (S.max' h) ≤ (seg n (m + 1) (S.max' h) : ℕ∞) :=
      Finset.mem_filter.mp hmem0
    rw [Finset.mem_Icc] at hmem
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro l hl1 hl2
      by_contra hc
      have : l ∈ S := by
        rw [hS, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, hl2⟩, not_lt.mp hc⟩
      have := Finset.le_max' S l this
      omega
    · intro _
      simpa using hmem.2
  · rw [dif_neg h]
    refine ⟨le_rfl, by omega, ?_, fun h' => by omega⟩
    intro l hl1 hl2
    by_contra hc
    apply h
    refine ⟨l, ?_⟩
    rw [hS, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, hl2⟩, not_lt.mp hc⟩

lemma routeOK_unique {u : ℕ → ℕ → ℕ∞} {m : ℕ} {n : Fin K → ℕ} {j j' : ℕ}
    (h : RouteOK K u m n j) (h' : RouteOK K u m n j') : j = j' := by
  rcases h with ⟨a1, a2, a3, a4⟩
  rcases h' with ⟨b1, b2, b3, b4⟩
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := b4 (by omega)
    have := a3 (j' - 1) (by omega) (by omega)
    exact absurd ‹u m (j' - 1) ≤ _› (not_le.mpr this)
  · have := a4 (by omega)
    have := b3 (j - 1) (by omega) (by omega)
    exact absurd ‹u m (j - 1) ≤ _› (not_le.mpr this)

lemma expNode_eq_iff (u : ℕ → ℕ → ℕ∞) (m : ℕ) (n : Fin K → ℕ) (hm : m < K) (j : ℕ) :
    expNode K u m n = j ↔ RouteOK K u m n j :=
  ⟨fun h => h ▸ expNode_ok u m n hm, fun h => routeOK_unique (expNode_ok u m n hm) h⟩

lemma arrNode_eq (u : ℕ → ℕ → ℕ∞) (n : Fin K → ℕ) (hK : 1 ≤ K) (htop : u 0 K = ⊤) :
    arrNode K u n = expNode K u 0 n := by
  unfold arrNode expNode
  simp only [zero_add]
  have : (Finset.Icc 1 K).filter (fun k => u 0 k ≤ (seg n 1 k : ℕ∞)) =
      (Finset.Icc 1 (K - 1)).filter (fun k => u 0 k ≤ (seg n 1 k : ℕ∞)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      by_contra hc
      have : k = K := by omega
      subst this
      rw [htop, top_le_iff] at h3
      exact ENat.natCast_ne_top _ h3
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
  rw [this]

lemma umono {K : ℕ} {u : ℕ → ℕ → ℕ∞} (hu : IsPolicyParam K u) {i j j' : ℕ}
    (hij : i < j) (hjj : j ≤ j') (hj' : j' ≤ K) : u i j ≤ u i j' := by
  induction j', hjj using Nat.le_induction with
  | base => exact le_rfl
  | succ j' hj ih => exact (ih (by omega)).trans (hu.1 i j' (by omega) (by omega))


lemma seg_add_ev_in {q : Fin K → ℕ} {s a b : ℕ} (h : a ≤ s ∧ s ≤ b ∧ 1 ≤ s ∧ s ≤ K) :
    seg (q + ev K s) a b = seg q a b + 1 := by
  rw [seg_add, seg_ev, if_pos h]

lemma seg_add_ev_out {q : Fin K → ℕ} {s a b : ℕ} (h : ¬ (a ≤ s ∧ s ≤ b ∧ 1 ≤ s ∧ s ≤ K)) :
    seg (q + ev K s) a b = seg q a b := by
  rw [seg_add, seg_ev, if_neg h, add_zero]

lemma mem_SM {u : ℕ → ℕ → ℕ∞} {n : Fin K → ℕ} :
    n ∈ SM K u ↔ ∀ k l, k < l → l ≤ K → (seg n (k + 1) l : ℕ∞) ≤ u k l := Iff.rfl

lemma sm_of_add {u : ℕ → ℕ → ℕ∞} {q r : Fin K → ℕ} (h : q + r ∈ SM K u) : q ∈ SM K u := by
  intro k l hkl hl
  have := h k l hkl hl
  rw [seg_add] at this
  exact le_trans (by exact_mod_cast Nat.le_add_right _ _) this

lemma sm_add_evK {u : ℕ → ℕ → ℕ∞} (hu : IsPolicyParam K u) {n : Fin K → ℕ}
    (h : n ∈ SM K u) : n + ev K K ∈ SM K u := by
  intro k l hkl hl
  by_cases hlK : l = K
  · subst hlK; rw [hu.2.2 k hkl]; exact le_top
  · rw [seg_add_ev_out (by omega)]; exact h k l hkl hl

lemma lift_ne_top {x : ℕ∞} (h : x ≠ ⊤) : ∃ a : ℕ, x = a :=
  ⟨x.toNat, (ENat.natCast_toNat h).symm⟩

/-- Closure of `S_M(u)` under the routed move `q + e_s → q + e_j` (s = 0 is an arrival). -/
lemma closure {u : ℕ → ℕ → ℕ∞} (hu : IsPolicyParam K u) (hA : AssumptionA K u)
    (q : Fin K → ℕ) (s : ℕ) (hs : s < K) (hsSM : q + ev K s ∈ SM K u) :
    q + ev K (expNode K u s (q + ev K s)) ∈ SM K u := by
  obtain ⟨r1, r2, r3, r4⟩ := expNode_ok u s (q + ev K s) hs
  set j := expNode K u s (q + ev K s)
  intro k l hkl hlK
  by_cases hc : k + 1 ≤ j ∧ j ≤ l ∧ 1 ≤ j ∧ j ≤ K
  swap
  · rw [seg_add_ev_out hc]; exact sm_of_add hsSM k l hkl hlK
  rw [seg_add_ev_in hc]
  by_cases hlK' : l = K
  · subst hlK'; rw [hu.2.2 k hkl]; exact le_top
  have hb := r3 l (by omega) (by omega)
  rw [seg_add_ev_out (by omega)] at hb
  rcases lt_trichotomy k s with hks | hks | hks
  · have := hsSM k l hkl hlK
    rw [seg_add_ev_in (by omega)] at this
    exact_mod_cast this
  · subst hks
    rw [Nat.cast_add, Nat.cast_one, ENat.add_one_le_iff (ENat.natCast_ne_top _)]; exact hb
  · have h4 := r4 (by omega)
    rw [seg_add_ev_out (by omega)] at h4
    have h5 := hsSM s (j - 1) (by omega) (by omega)
    rw [seg_add_ev_out (by omega)] at h5
    have hsp := seg_split q (s + 1) (j - 1) l (by omega) (by omega)
    have e1 : j - 1 + 1 = j := by omega
    rw [e1] at hsp
    obtain ⟨A, hA'⟩ : ∃ A : ℕ, u s (j - 1) = A := ⟨_, le_antisymm h4 h5⟩
    rw [hA'] at h4 h5
    by_cases hkj : k = j - 1
    · subst hkj
      have tri := hA.1 s (j - 1) l (by omega) (by omega) hlK
      rw [e1]
      by_cases ht : u (j - 1) l = ⊤
      · rw [ht]; exact le_top
      obtain ⟨b, hb'⟩ := lift_ne_top ht
      rw [hb', hA'] at tri
      obtain ⟨c, hc'⟩ := lift_ne_top (ne_top_of_le_ne_top (by simp) tri)
      rw [hc'] at tri hb
      rw [hb']
      norm_cast at tri hb h4 h5 ⊢
      omega
    · have sup := hA.2 s k (j - 1) l hks (by omega) (by omega) hlK
      by_cases ht : u k l = ⊤
      · rw [ht]; exact le_top
      obtain ⟨b, hb'⟩ := lift_ne_top ht
      rw [hb', hA'] at sup
      have hfin : u k (j - 1) + u s l ≠ ⊤ := ne_top_of_le_ne_top (by simp) sup
      obtain ⟨d, hd⟩ := lift_ne_top (WithTop.add_ne_top.mp hfin).1
      obtain ⟨c, hc'⟩ := lift_ne_top (WithTop.add_ne_top.mp hfin).2
      rw [hd, hc'] at sup
      rw [hc'] at hb
      have h6 := hsSM k (j - 1) (by omega) (by omega)
      rw [seg_add_ev_out (by omega), hd] at h6
      have hsp2 := seg_split q (k + 1) (j - 1) l (by omega) (by omega)
      rw [e1] at hsp2
      rw [hb']
      norm_cast at sup hb h6 h4 ⊢
      omega


lemma enat_eq_of_le_not {x : ℕ} {y : ℕ∞} (h1 : (x : ℕ∞) ≤ y) (h2 : ¬ (x : ℕ∞) + 1 ≤ y) :
    y = x := by
  by_cases ht : y = ⊤
  · exact absurd (ht ▸ le_top) h2
  obtain ⟨b, hb⟩ := lift_ne_top ht
  subst hb
  norm_cast at h1 h2 ⊢
  omega

section Core
variable {u : ℕ → ℕ → ℕ∞} (hu : IsPolicyParam K u) (hA : AssumptionA K u)
  (q : Fin K → ℕ) (i : ℕ) (hi1 : 1 ≤ i) (hiK : i ≤ K) (hn : q + ev K i ∈ SM K u)
include hu hA hi1 hiK hn

lemma core_imp (s : ℕ) (hs : s < K) (hP : q + ev K s ∈ SM K u ∧ expNode K u s (q + ev K s) = i) :
    s < i ∧ (s + 2 ≤ i → u s (i - 1) ≤ (seg q (s + 1) (i - 1) : ℕ∞)) ∧
      (∀ k l, k < s → s ≤ l → l ≤ i - 1 → (seg q (k + 1) l : ℕ∞) + 1 ≤ u k l) := by
  obtain ⟨hSM, hE⟩ := hP
  obtain ⟨r1, r2, r3, r4⟩ := expNode_ok u s (q + ev K s) hs
  rw [hE] at r1 r2 r3 r4
  refine ⟨by omega, fun h => ?_, fun k l hk hl hl2 => ?_⟩
  · have := r4 h
    rwa [seg_add_ev_out (by omega)] at this
  · have := hSM k l (by omega) (by omega)
    rw [seg_add_ev_in (by omega)] at this
    exact_mod_cast this

lemma core_of (s : ℕ) (hs : s < i)
    (hT : s + 2 ≤ i → u s (i - 1) ≤ (seg q (s + 1) (i - 1) : ℕ∞))
    (hC : ∀ k l, k < s → s ≤ l → l ≤ i - 1 → (seg q (k + 1) l : ℕ∞) + 1 ≤ u k l) :
    q + ev K s ∈ SM K u ∧ expNode K u s (q + ev K s) = i := by
  constructor
  · intro k l hkl hlK
    by_cases hc : k + 1 ≤ s ∧ s ≤ l ∧ 1 ≤ s ∧ s ≤ K
    · rw [seg_add_ev_in hc]
      by_cases hli : l ≤ i - 1
      · exact_mod_cast hC k l (by omega) (by omega) hli
      · have := hn k l hkl hlK
        rwa [seg_add_ev_in (by omega)] at this
    · rw [seg_add_ev_out hc]; exact sm_of_add hn k l hkl hlK
  · rw [expNode_eq_iff u s _ (by omega)]
    refine ⟨by omega, hiK, fun l hl hl2 => ?_, fun h => ?_⟩
    · rw [seg_add_ev_out (by omega)]
      have := hn s l (by omega) (by omega)
      rw [seg_add_ev_in (by omega)] at this
      rw [← ENat.add_one_le_iff (ENat.natCast_ne_top _)]
      exact_mod_cast this
    · rw [seg_add_ev_out (by omega)]; exact hT h

lemma core_unique (s s' : ℕ) (hs : s < K) (hs' : s' < K)
    (hP : q + ev K s ∈ SM K u ∧ expNode K u s (q + ev K s) = i)
    (hP' : q + ev K s' ∈ SM K u ∧ expNode K u s' (q + ev K s') = i) : s = s' := by
  have key : ∀ a b, a < K → b < K → a < b →
      (q + ev K a ∈ SM K u ∧ expNode K u a (q + ev K a) = i) →
      (q + ev K b ∈ SM K u ∧ expNode K u b (q + ev K b) = i) → False := by
    intro a b ha hb hab Pa Pb
    obtain ⟨a1, a2, _⟩ := core_imp hu hA q i hi1 hiK hn a ha Pa
    obtain ⟨b1, _, b3⟩ := core_imp hu hA q i hi1 hiK hn b hb Pb
    have h1 := a2 (by omega)
    have h2 := b3 a (i - 1) hab (by omega) le_rfl
    have := h2.trans h1
    norm_cast at this
    omega
  rcases lt_trichotomy s s' with h | h | h
  · exact (key s s' hs hs' h hP hP').elim
  · exact h
  · exact (key s' s hs' hs h hP' hP).elim

lemma core_exists : ∃ s, s < i ∧ q + ev K s ∈ SM K u ∧ expNode K u s (q + ev K s) = i := by
  classical
  have hex : ∃ s, s < i ∧ (s + 2 ≤ i → u s (i - 1) ≤ (seg q (s + 1) (i - 1) : ℕ∞)) :=
    ⟨i - 1, by omega, fun h => by omega⟩
  set t := Nat.find hex with ht
  obtain ⟨t1, t2⟩ := Nat.find_spec hex
  rw [← ht] at t1 t2
  refine ⟨t, t1, core_of hu hA q i hi1 hiK hn t t1 t2 ?_⟩
  intro k l hk hl hl2
  have hmin := Nat.find_min hex (show k < Nat.find hex from hk)
  have hk2 : k + 2 ≤ i ∧ (seg q (k + 1) (i - 1) : ℕ∞) < u k (i - 1) := by
    by_contra hc
    apply hmin
    refine ⟨by omega, fun h => ?_⟩
    by_contra hc2
    exact hc ⟨h, not_le.mp hc2⟩
  have hb := hn k l (by omega) (by omega)
  rw [seg_add_ev_out (by omega)] at hb
  by_contra hnot
  have heq := enat_eq_of_le_not hb hnot
  by_cases hli : l = i - 1
  · subst hli; rw [heq] at hk2; exact lt_irrefl _ hk2.2
  have tT := t2 (by omega)
  have tS := hn t (i - 1) (by omega) (by omega)
  rw [seg_add_ev_out (by omega)] at tS
  obtain ⟨A, hA'⟩ : ∃ A : ℕ, u t (i - 1) = A := ⟨_, le_antisymm tT tS⟩
  have hAeq : seg q (t + 1) (i - 1) = A := by
    rw [hA'] at tT tS; norm_cast at tT tS; omega
  have sp1 := seg_split q (k + 1) t (i - 1) (by omega) (by omega)
  by_cases hlt : l = t
  · rw [hlt] at heq
    have tri := hA.1 k t (i - 1) hk (by omega) (by omega)
    rw [heq, hA'] at tri
    have h2 := hk2.2
    have := lt_of_lt_of_le h2 tri
    norm_cast at this
    omega
  · have sup := hA.2 k t l (i - 1) hk (by omega) (by omega) (by omega)
    rw [heq, hA'] at sup
    have hfin : u t l + u k (i - 1) ≠ ⊤ := ne_top_of_le_ne_top (by simp) sup
    obtain ⟨c, hc'⟩ := lift_ne_top (WithTop.add_ne_top.mp hfin).1
    obtain ⟨d, hd⟩ := lift_ne_top (WithTop.add_ne_top.mp hfin).2
    rw [hc', hd] at sup
    have h2 := hk2.2
    rw [hd] at h2
    have sp2 := seg_split q (k + 1) t l (by omega) (by omega)
    have hY := hn t l (by omega) (by omega)
    rw [seg_add_ev_out (by omega), hc'] at hY
    norm_cast at sup h2 hY
    omega

end Core

/-- Unified event rate: source `0` is the arrival stream. -/
def cc (lam : ℝ) (mu : ℕ → ℝ) (s : ℕ) : ℝ := if s = 0 then lam else mu s

lemma rate_eq (u : ℕ → ℕ → ℕ∞) (lam : ℝ) (mu : ℕ → ℝ) (hK : 1 ≤ K) (hu : IsPolicyParam K u)
    (a b : Fin K → ℕ) :
    rate K u lam mu a b =
      (∑ s ∈ Finset.Icc 0 (K - 1),
        if (s = 0 ∨ 0 < occ a s) ∧ b = a - ev K s + ev K (expNode K u s a) then cc lam mu s else 0) +
      (if 0 < occ a K ∧ b = a - ev K K then mu K else 0) := by
  unfold rate
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
  have hI : Finset.Ioc 0 (K - 1) = Finset.Icc 1 (K - 1) := by ext x; simp; omega
  rw [hI]
  rw [arrNode_eq u a hK (hu.2.2 0 (by omega))]
  simp only [ev_zero, tsub_zero, true_or, true_and, cc, if_true]
  congr 2
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mem_Icc] at hx
  have hx0 : x ≠ 0 := by omega
  simp [hx0]

lemma cc_pos {lam : ℝ} {mu : ℕ → ℝ} (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    {s : ℕ} (hs : s ≤ K) : 0 < cc lam mu s := by
  unfold cc; split_ifs with h
  · exact hlam
  · exact hmu s (by omega) hs

/-- Any positive-rate (nonzero) transition is a routed move or a departure. -/
lemma rate_ne_zero_imp (u : ℕ → ℕ → ℕ∞) (lam : ℝ) (mu : ℕ → ℝ) (hK : 1 ≤ K)
    (hu : IsPolicyParam K u) (a b : Fin K → ℕ) (h : rate K u lam mu a b ≠ 0) :
    (∃ s, s ≤ K - 1 ∧ (s = 0 ∨ 0 < occ a s) ∧ b = a - ev K s + ev K (expNode K u s a)) ∨
      (0 < occ a K ∧ b = a - ev K K) := by
  rw [rate_eq u lam mu hK hu] at h
  by_cases h2 : 0 < occ a K ∧ b = a - ev K K
  · exact Or.inr h2
  rw [if_neg h2, add_zero] at h
  obtain ⟨s, hs, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.mem_Icc] at hs
  by_cases h3 : (s = 0 ∨ 0 < occ a s) ∧ b = a - ev K s + ev K (expNode K u s a)
  · exact Or.inl ⟨s, hs.2, h3⟩
  · rw [if_neg h3] at hne; exact absurd rfl hne

lemma seg_zero (x y : ℕ) : seg (0 : Fin K → ℕ) x y = 0 := by
  unfold seg occ; simp

lemma zero_mem_SM (u : ℕ → ℕ → ℕ∞) : (0 : Fin K → ℕ) ∈ SM K u := by
  intro k l _ _; rw [seg_zero]; simp

/-- `S_M(u)` is closed under every positive-rate transition. -/
lemma sm_step {u : ℕ → ℕ → ℕ∞} {lam : ℝ} {mu : ℕ → ℝ} (hK : 1 ≤ K)
    (hu : IsPolicyParam K u) (hA : AssumptionA K u) {a b : Fin K → ℕ} (ha : a ∈ SM K u)
    (h : rate K u lam mu a b ≠ 0) : b ∈ SM K u := by
  rcases rate_ne_zero_imp u lam mu hK hu a b h with ⟨s, hs, hg, hb⟩ | ⟨hg, hb⟩
  · have h0 : a - ev K s + ev K s = a := tsub_add_cancel_of_le (ev_le a s hg)
    have hc := closure hu hA (a - ev K s) s (by omega) (by rw [h0]; exact ha)
    rw [h0] at hc
    rw [hb]; exact hc
  · have h0 : a - ev K K + ev K K = a := tsub_add_cancel_of_le (ev_le a K (Or.inr hg))
    rw [hb]; exact sm_of_add (h0.symm ▸ ha)

def phi (n : Fin K → ℕ) : ℕ := ∑ l ∈ Finset.Icc 1 K, l * occ n l

lemma phi_add_ev (q : Fin K → ℕ) (s : ℕ) (hs : s ≤ K) : phi (q + ev K s) = phi q + s := by
  unfold phi
  simp_rw [occ_add, mul_add]
  rw [Finset.sum_add_distrib, sum_mul_occ_ev (fun l => l)]
  split_ifs with h
  · rfl
  · have : s = 0 := by omega
    subst this; rfl

lemma rate_pos_move {u : ℕ → ℕ → ℕ∞} {lam : ℝ} {mu : ℕ → ℝ} (hK : 1 ≤ K)
    (hu : IsPolicyParam K u) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (q : Fin K → ℕ) (s : ℕ) (hs : s ≤ K - 1) :
    0 < rate K u lam mu (q + ev K s) (q + ev K (expNode K u s (q + ev K s))) := by
  rw [rate_eq u lam mu hK hu]
  have hnonneg : ∀ x ∈ Finset.Icc 0 (K - 1), 0 ≤ (if (x = 0 ∨ 0 < occ (q + ev K s) x) ∧
      q + ev K (expNode K u s (q + ev K s)) = q + ev K s - ev K x + ev K (expNode K u x (q + ev K s))
      then cc lam mu x else 0) := by
    intro x hx; rw [Finset.mem_Icc] at hx
    split_ifs
    · exact (cc_pos hlam hmu (by omega)).le
    · exact le_rfl
  have hterm : (if (s = 0 ∨ 0 < occ (q + ev K s) s) ∧
      q + ev K (expNode K u s (q + ev K s)) = q + ev K s - ev K s + ev K (expNode K u s (q + ev K s))
      then cc lam mu s else 0) = cc lam mu s := by
    rw [if_pos]
    refine ⟨?_, by rw [add_tsub_cancel_right]⟩
    by_cases h0 : s = 0
    · exact Or.inl h0
    · exact Or.inr (occ_add_ev_self q s (by omega) (by omega))
  have h1 := Finset.single_le_sum hnonneg (Finset.mem_Icc.mpr ⟨Nat.zero_le s, hs⟩)
  rw [hterm] at h1
  have h2 : 0 ≤ (if 0 < occ (q + ev K s) K ∧
      q + ev K (expNode K u s (q + ev K s)) = q + ev K s - ev K K then mu K else 0) := by
    split_ifs
    · exact (hmu K hK le_rfl).le
    · exact le_rfl
  have := cc_pos hlam hmu (show s ≤ K by omega)
  linarith

theorem reach_eq {u : ℕ → ℕ → ℕ∞} {lam : ℝ} {mu : ℕ → ℝ} (hK : 1 ≤ K) (hlam : 0 < lam)
    (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (hu : IsPolicyParam K u) (hA : AssumptionA K u) :
    {n : Fin K → ℕ | Relation.ReflTransGen
      (fun a b => 0 < rate K u lam mu a b) 0 n} = SM K u := by
  ext n
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    induction h with
    | refl => exact zero_mem_SM u
    | tail _ hab ih => exact sm_step hK hu hA ih (ne_of_gt hab)
  · intro hn
    suffices H : ∀ N, ∀ n : Fin K → ℕ, phi n = N → n ∈ SM K u →
        Relation.ReflTransGen (fun a b => 0 < rate K u lam mu a b) 0 n from H _ n rfl hn
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro n hN hn
      by_cases hz : n = 0
      · subst hz; exact Relation.ReflTransGen.refl
      obtain ⟨j, hj⟩ : ∃ j : Fin K, n j ≠ 0 := by
        by_contra hc; push Not at hc; exact hz (funext hc)
      set i := j.val + 1 with hi
      have hocc : 0 < occ n i := by
        unfold occ; rw [dif_pos (by omega)]
        have : (⟨i - 1, by omega⟩ : Fin K) = j := by ext; simp [hi]
        rw [this]; omega
      set q := n - ev K i
      have hq : q + ev K i = n := tsub_add_cancel_of_le (ev_le n i (Or.inr hocc))
      obtain ⟨s, hsi, hP1, hP2⟩ := core_exists hu hA q i (by omega) (by omega) (hq ▸ hn)
      have hphi : phi (q + ev K s) < N := by
        rw [← hN, ← hq, phi_add_ev q s (by omega), phi_add_ev q i (by omega)]; omega
      have hreach := ih _ hphi _ rfl hP1
      have hrate := rate_pos_move hK hu hlam hmu (lam := lam) q s (by omega)
      rw [hP2, hq] at hrate
      exact Relation.ReflTransGen.tail hreach hrate

lemma inflow_pointwise (u : ℕ → ℕ → ℕ∞) (lam : ℝ) (mu : ℕ → ℝ) (hK : 1 ≤ K)
    (hu : IsPolicyParam K u) (n p : Fin K → ℕ) (f : (Fin K → ℕ) → ℝ) :
    f p * rate K u lam mu p n =
      (∑ i ∈ Finset.Icc 1 K, ∑ s ∈ Finset.Icc 0 (K - 1),
        (if p = n - ev K i + ev K s then
          (if 0 < occ n i ∧ expNode K u s (n - ev K i + ev K s) = i
            then f (n - ev K i + ev K s) * cc lam mu s else 0) else 0)) +
      (if p = n + ev K K then f (n + ev K K) * mu K else 0) := by
  rw [rate_eq u lam mu hK hu, mul_add, Finset.mul_sum, Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_Icc] at hs
    rw [mul_ite, mul_zero]
    have ok := expNode_ok u s p (by omega)
    obtain ⟨j, hj⟩ : ∃ j, expNode K u s p = j := ⟨_, rfl⟩
    rw [hj] at ok ⊢
    rw [Finset.sum_eq_single j]
    · by_cases hC : (s = 0 ∨ 0 < occ p s) ∧ n = p - ev K s + ev K j
      · obtain ⟨hg, hb⟩ := hC
        have hp : p = n - ev K j + ev K s := by
          rw [hb, add_tsub_cancel_right, tsub_add_cancel_of_le (ev_le p s hg)]
        have hocc : 0 < occ n j := by rw [hb]; exact occ_add_ev_self _ j (by have := ok.1; omega) ok.2.1
        rw [if_pos ⟨hg, hb⟩, if_pos hp, if_pos ⟨hocc, by rw [← hp, hj]⟩, ← hp]
      · rw [if_neg hC]
        split_ifs with h1 h2
        · exfalso; apply hC
          have e1 : p - ev K s = n - ev K j := by rw [h1, add_tsub_cancel_right]
          refine ⟨?_, by rw [e1, tsub_add_cancel_of_le (ev_le n j (Or.inr h2.1))]⟩
          by_cases h0 : s = 0
          · exact Or.inl h0
          · right; rw [h1]; exact occ_add_ev_self _ s (Nat.pos_of_ne_zero h0) (by have := hs.2; omega)
        · rfl
        · rfl
    · intro i hi hij
      split_ifs with h1 h2
      · exfalso; apply hij
        have := h2.2
        rw [← h1, hj] at this
        exact this.symm
      · rfl
      · rfl
    · intro hj'; exfalso; apply hj'; rw [Finset.mem_Icc]; exact ⟨by have := ok.1; omega, ok.2.1⟩
  · rw [mul_ite, mul_zero]
    by_cases hp : p = n + ev K K
    · subst hp
      rw [if_pos ⟨occ_add_ev_self n K hK le_rfl, by rw [add_tsub_cancel_right]⟩, if_pos rfl]
    · rw [if_neg hp, if_neg]
      rintro ⟨h1, h2⟩; apply hp; rw [h2, tsub_add_cancel_of_le (ev_le p K (Or.inr h1))]

lemma inflow_tsum (u : ℕ → ℕ → ℕ∞) (lam : ℝ) (mu : ℕ → ℝ) (hK : 1 ≤ K)
    (hu : IsPolicyParam K u) (n : Fin K → ℕ) (f : (Fin K → ℕ) → ℝ) :
    ∑' p, f p * rate K u lam mu p n =
      (∑ i ∈ Finset.Icc 1 K, ∑ s ∈ Finset.Icc 0 (K - 1),
          (if 0 < occ n i ∧ expNode K u s (n - ev K i + ev K s) = i
            then f (n - ev K i + ev K s) * cc lam mu s else 0)) +
      f (n + ev K K) * mu K := by
  rw [show (fun p => f p * rate K u lam mu p n) = _ from
    funext (fun p => inflow_pointwise u lam mu hK hu n p f)]
  rw [Summable.tsum_add (summable_sum fun i _ => summable_sum fun s _ =>
      (hasSum_ite_eq _ _).summable) (hasSum_ite_eq _ _).summable]
  rw [Summable.tsum_finsetSum (fun i _ => summable_sum fun s _ => (hasSum_ite_eq _ _).summable)]
  congr 1
  · apply Finset.sum_congr rfl; intro i _
    rw [Summable.tsum_finsetSum (fun s _ => (hasSum_ite_eq _ _).summable)]
    apply Finset.sum_congr rfl; intro s _
    exact tsum_ite_eq _ _
  · exact tsum_ite_eq _ _

lemma prod_pow_occ_ev (x : ℕ → ℝ) (s : ℕ) :
    ∏ k ∈ Finset.Icc 1 K, x k ^ occ (ev K s) k = if 1 ≤ s ∧ s ≤ K then x s else 1 := by
  rw [Finset.prod_congr rfl (g := fun k => if k = s then x k else 1)]
  · rw [Finset.prod_ite_eq']; simp only [Finset.mem_Icc]
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [occ_ev]
    by_cases h : k = s
    · rw [if_pos ⟨h, hk⟩, if_pos h, pow_one]
    · rw [if_neg (by tauto), if_neg h, pow_zero]

lemma weight_add (lam : ℝ) (mu : ℕ → ℝ) (a b : Fin K → ℕ) :
    weight K lam mu (a + b) = weight K lam mu a * weight K lam mu b := by
  unfold weight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro k _
  rw [occ_add, pow_add]

lemma weight_ev (lam : ℝ) (mu : ℕ → ℝ) (s : ℕ) :
    weight K lam mu (ev K s) = if 1 ≤ s ∧ s ≤ K then lam / mu s else 1 :=
  prod_pow_occ_ev (fun k => lam / mu k) s

lemma cc_weight {lam : ℝ} {mu : ℕ → ℝ} (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (q : Fin K → ℕ) (s : ℕ) (hs : s ≤ K) :
    cc lam mu s * weight K lam mu (q + ev K s) = lam * weight K lam mu q := by
  rw [weight_add, weight_ev]
  unfold cc
  split_ifs with h1 h2
  · omega
  · ring
  · have := (hmu s (by omega) hs).ne'
    field_simp
  · omega

lemma weight_pos {lam : ℝ} {mu : ℕ → ℝ} (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (n : Fin K → ℕ) : 0 < weight K lam mu n := by
  unfold weight
  apply Finset.prod_pos
  intro k hk; rw [Finset.mem_Icc] at hk
  exact pow_pos (div_pos hlam (hmu k hk.1 hk.2)) _

lemma weight_zero (lam : ℝ) (mu : ℕ → ℝ) : weight K lam mu 0 = 1 := by
  unfold weight occ; simp

lemma prod_Icc_occ (F : ℕ → ℕ → ℝ) (n : Fin K → ℕ) :
    ∏ k ∈ Finset.Icc 1 K, F k (occ n k) = ∏ j : Fin K, F (j.val + 1) (n j) := by
  have h1 : ∀ j : Fin K, F (j.val + 1) (n j) = F (j.val + 1) (occ n (j.val + 1)) := by
    intro j; congr 1; unfold occ; rw [dif_pos (by omega)]; congr 1
  rw [Finset.prod_congr rfl (fun j _ => h1 j),
    Fin.prod_univ_eq_prod_range (fun i => F (i + 1) (occ n (i + 1))) K, Finset.range_eq_Ico,
    Finset.prod_Ico_add' (fun x => F x (occ n x)) 0 K 1]
  rfl

lemma summable_pi_prod (H : Fin K → ℕ → ℝ) (hH : ∀ j x, 0 ≤ H j x) (hs : ∀ j, Summable (H j)) :
    Summable (fun n : Fin K → ℕ => ∏ j, H j (n j)) := by
  classical
  apply summable_of_sum_le (c := ∏ j, ∑' x, H j x)
  · intro n; exact Finset.prod_nonneg (fun j _ => hH j _)
  · intro t
    set N := t.sup (fun x => Finset.univ.sup x) + 1
    have ht : t ⊆ Fintype.piFinset (fun _ : Fin K => Finset.range N) := by
      intro x hx
      rw [Fintype.mem_piFinset]
      intro j
      rw [Finset.mem_range]
      have h1 : x j ≤ Finset.univ.sup x := Finset.le_sup (f := x) (Finset.mem_univ j)
      have h2 : Finset.univ.sup x ≤ t.sup (fun x => Finset.univ.sup x) :=
        Finset.le_sup (f := fun x => Finset.univ.sup x) hx
      omega
    calc ∑ x ∈ t, ∏ j, H j (x j)
        ≤ ∑ x ∈ Fintype.piFinset (fun _ : Fin K => Finset.range N), ∏ j, H j (x j) :=
          Finset.sum_le_sum_of_subset_of_nonneg ht
            (fun x _ _ => Finset.prod_nonneg (fun j _ => hH j _))
      _ = ∏ j, ∑ y ∈ Finset.range N, H j y := (Finset.prod_univ_sum _ _).symm
      _ ≤ ∏ j, ∑' x, H j x := by
          apply Finset.prod_le_prod
          · intro j _; exact Finset.sum_nonneg (fun y _ => hH j y)
          · intro j _; exact (hs j).sum_le_tsum _ (fun y _ => hH j y)

lemma summable_ind {u : ℕ → ℕ → ℕ∞} {lam : ℝ} {mu : ℕ → ℝ} (hK : 1 ≤ K) (hlam : 0 < lam)
    (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k) (hstab : lam < mu K)
    (hfin : ∀ i, 1 ≤ i → i ≤ K - 1 → u 0 i ≠ ⊤) :
    Summable ((SM K u).indicator (weight K lam mu)) := by
  classical
  set B := ∑ l ∈ Finset.Icc 1 (K - 1), (u 0 l).toNat with hB
  have hbound : ∀ n ∈ SM K u, ∀ l, 1 ≤ l → l ≤ K - 1 → occ n l ≤ B := by
    intro n hn l hl1 hl2
    have e1 : occ n l ≤ seg n 1 l := by
      unfold seg
      exact Finset.single_le_sum (f := occ n) (fun _ _ => Nat.zero_le _)
        (Finset.mem_Icc.mpr ⟨hl1, le_rfl⟩)
    have e2 : seg n 1 l ≤ (u 0 l).toNat := by
      have h := hn 0 l (by omega) (by omega)
      obtain ⟨a, ha⟩ := lift_ne_top (hfin l hl1 hl2)
      rw [ha] at h ⊢
      simp only [zero_add] at h
      rw [ENat.toNat_natCast]; exact_mod_cast h
    have e3 : (u 0 l).toNat ≤ B :=
      Finset.single_le_sum (f := fun l => (u 0 l).toNat) (fun _ _ => Nat.zero_le _)
        (Finset.mem_Icc.mpr ⟨hl1, hl2⟩)
    omega
  have hr0 : 0 ≤ lam / mu K := (div_pos hlam (hmu K hK le_rfl)).le
  have hr1 : lam / mu K < 1 := (div_lt_one (hmu K hK le_rfl)).mpr hstab
  set H : Fin K → ℕ → ℝ := fun j x =>
    if j.val + 1 = K then (lam / mu K) ^ x else if x ≤ B then (lam / mu (j.val + 1)) ^ x else 0
    with hHdef
  have hH : ∀ j x, 0 ≤ H j x := by
    intro j x
    simp only [hHdef]
    split_ifs
    · exact pow_nonneg hr0 _
    · exact pow_nonneg (div_pos hlam (hmu _ (by omega) (by omega))).le _
    · exact le_rfl
  have hs : ∀ j, Summable (H j) := by
    intro j
    by_cases hj : j.val + 1 = K
    · have : H j = fun x => (lam / mu K) ^ x := by funext x; simp only [hHdef, if_pos hj]
      rw [this]; exact summable_geometric_of_lt_one hr0 hr1
    · apply summable_of_ne_finset_zero (s := Finset.range (B + 1))
      intro x hx
      rw [Finset.mem_range] at hx
      simp only [hHdef, if_neg hj]
      rw [if_neg (by omega)]
  apply Summable.of_nonneg_of_le _ _ (summable_pi_prod H hH hs)
  · intro n; exact Set.indicator_nonneg (fun n _ => (weight_pos hlam hmu n).le) n
  · intro n
    by_cases hn : n ∈ SM K u
    · rw [Set.indicator_of_mem hn]
      unfold weight
      rw [prod_Icc_occ (fun k x => (lam / mu k) ^ x) n]
      apply le_of_eq
      apply Finset.prod_congr rfl
      intro j _
      simp only [hHdef]
      by_cases hj : j.val + 1 = K
      · rw [if_pos hj, hj]
      · rw [if_neg hj, if_pos]
        have := hbound n hn (j.val + 1) (by omega) (by omega)
        unfold occ at this
        rw [dif_pos (by omega)] at this
        simpa using this
    · rw [Set.indicator_of_notMem hn]
      exact Finset.prod_nonneg (fun j _ => hH j _)

lemma piM_of_mem {u : ℕ → ℕ → ℕ∞} {lam : ℝ} {mu : ℕ → ℝ} {n : Fin K → ℕ} (h : n ∈ SM K u) :
    piM K u lam mu n = weight K lam mu n / normG K u lam mu := by
  unfold piM; rw [Set.indicator_of_mem h]

lemma piM_of_notMem {u : ℕ → ℕ → ℕ∞} {lam : ℝ} {mu : ℕ → ℝ} {n : Fin K → ℕ} (h : n ∉ SM K u) :
    piM K u lam mu n = 0 := by
  unfold piM; rw [Set.indicator_of_notMem h, zero_div]

lemma node_inflow {u : ℕ → ℕ → ℕ∞} {lam : ℝ} {mu : ℕ → ℝ}
    (hu : IsPolicyParam K u) (hA : AssumptionA K u)
    (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (n : Fin K → ℕ) (hn : n ∈ SM K u) (i : ℕ) (hi1 : 1 ≤ i) (hiK : i ≤ K) :
    (∑ s ∈ Finset.Icc 0 (K - 1),
      (if 0 < occ n i ∧ expNode K u s (n - ev K i + ev K s) = i
        then piM K u lam mu (n - ev K i + ev K s) * cc lam mu s else 0)) =
      if 0 < occ n i then mu i * piM K u lam mu n else 0 := by
  by_cases hocc : 0 < occ n i
  swap
  · rw [if_neg hocc]
    apply Finset.sum_eq_zero; intro s _; rw [if_neg (by tauto)]
  rw [if_pos hocc]
  set q := n - ev K i with hqdef
  have hq : q + ev K i = n := tsub_add_cancel_of_le (ev_le n i (Or.inr hocc))
  have hn' : q + ev K i ∈ SM K u := hq ▸ hn
  obtain ⟨t, hti, hP1, hP2⟩ := core_exists hu hA q i hi1 hiK hn'
  rw [Finset.sum_eq_single t]
  · rw [if_pos ⟨hocc, hP2⟩, piM_of_mem hP1, piM_of_mem hn]
    have hw : weight K lam mu n = weight K lam mu q * (lam / mu i) := by
      rw [← hq, weight_add, weight_ev, if_pos ⟨hi1, hiK⟩]
    have h1 : weight K lam mu (q + ev K t) / normG K u lam mu * cc lam mu t =
        (cc lam mu t * weight K lam mu (q + ev K t)) / normG K u lam mu := by ring
    rw [h1, cc_weight hmu q t (by omega), hw]
    have := (hmu i hi1 hiK).ne'
    field_simp
  · intro s hs hst
    rw [Finset.mem_Icc] at hs
    split_ifs with h
    · by_cases hm : q + ev K s ∈ SM K u
      · exact absurd (core_unique hu hA q i hi1 hiK hn' s t (by omega) (by omega) ⟨hm, h.2⟩
          ⟨hP1, hP2⟩) hst
      · rw [piM_of_notMem hm, zero_mul]
    · rfl
  · intro ht; exfalso; apply ht; rw [Finset.mem_Icc]; omega

theorem global_balance {u : ℕ → ℕ → ℕ∞} {lam : ℝ} {mu : ℕ → ℝ} (hK : 1 ≤ K) (hlam : 0 < lam)
    (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (hu : IsPolicyParam K u) (hA : AssumptionA K u) (n : Fin K → ℕ) :
    piM K u lam mu n * outRate K lam mu n =
      ∑' m, piM K u lam mu m * rate K u lam mu m n := by
  by_cases hn : n ∈ SM K u
  · rw [inflow_tsum u lam mu hK hu n (piM K u lam mu)]
    rw [Finset.sum_congr rfl (fun i hi => node_inflow (lam := lam) hu hA hmu n hn i
      (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2)]
    have hdep : piM K u lam mu (n + ev K K) * mu K = lam * piM K u lam mu n := by
      rw [piM_of_mem (sm_add_evK hu hn), piM_of_mem hn, weight_add, weight_ev,
        if_pos ⟨hK, le_rfl⟩]
      have := (hmu K hK le_rfl).ne'
      field_simp
    rw [hdep]
    unfold outRate
    rw [mul_add, Finset.mul_sum, add_comm]
    congr 1
    · apply Finset.sum_congr rfl; intro k _
      split_ifs <;> ring
    · ring
  · rw [piM_of_notMem hn, zero_mul]
    symm
    rw [show (fun m => piM K u lam mu m * rate K u lam mu m n) = fun _ => (0 : ℝ) from ?_]
    · exact tsum_zero
    funext m
    by_cases hm : m ∈ SM K u
    · by_cases hr : rate K u lam mu m n = 0
      · rw [hr, mul_zero]
      · exact absurd (sm_step hK hu hA hm hr) hn
    · rw [piM_of_notMem hm, zero_mul]

end SEXP

open SmartExpedite.PolicyM in
theorem solution (K : ℕ) (u : ℕ → ℕ → ℕ∞) (lam : ℝ) (mu : ℕ → ℝ)
    (hK : 1 ≤ K) (hlam : 0 < lam)
    (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (hu : IsPolicyParam K u) (hA : AssumptionA K u) :
    {n : Fin K → ℕ | Relation.ReflTransGen
      (fun a b => 0 < rate K u lam mu a b) 0 n} = SM K u ∧
    (lam < mu K →
      (∀ i, 1 ≤ i → i ≤ K - 1 → u 0 i ≠ ⊤) →
      Summable ((SM K u).indicator (weight K lam mu)) ∧
      0 < normG K u lam mu ∧
      HasSum (piM K u lam mu) 1 ∧
      ∀ n, piM K u lam mu n * outRate K lam mu n =
        ∑' m, piM K u lam mu m * rate K u lam mu m n) := by
  refine ⟨SEXP.reach_eq hK hlam hmu hu hA, fun hstab hfin => ?_⟩
  have hsum := SEXP.summable_ind (u := u) hK hlam hmu hstab hfin
  have hnn : ∀ j, 0 ≤ (SM K u).indicator (weight K lam mu) j :=
    fun j => Set.indicator_nonneg (fun n _ => (SEXP.weight_pos hlam hmu n).le) j
  have hG : 0 < normG K u lam mu := by
    unfold normG
    have h0 := hsum.le_tsum 0 (fun j _ => hnn j)
    rw [Set.indicator_of_mem (SEXP.zero_mem_SM u), SEXP.weight_zero] at h0
    linarith
  refine ⟨hsum, hG, ?_, fun n => SEXP.global_balance hK hlam hmu hu hA n⟩
  have := hsum.hasSum.div_const (normG K u lam mu)
  have e : (∑' (b : Fin K → ℕ), (SM K u).indicator (weight K lam mu) b) = normG K u lam mu := rfl
  rw [e, div_self hG.ne'] at this
  exact this
