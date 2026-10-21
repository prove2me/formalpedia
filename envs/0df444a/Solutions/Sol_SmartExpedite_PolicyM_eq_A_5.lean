-- Prove2me | solution 1 for SmartExpedite.PolicyM.eq_A_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:31:39.184042+00:00
-- url     : https://prove2.me/submissions/9ec4b2cf-cca5-4fd8-885a-bf9a8be085a5

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

end SEXP

open SmartExpedite.PolicyM in
theorem solution (K : ℕ) (u : ℕ → ℕ → ℕ∞)
    (hK : 1 ≤ K) (hu : IsPolicyParam K u) (hA : AssumptionA K u) :
    ∀ n ∈ SM K u, ∀ m, 1 ≤ m → m ≤ K - 1 → 0 < occ n m →
      n - ev K m + ev K (expNode K u m n) ∈ SM K u := by
  intro n hn m hm1 hm2 hocc
  have hle := SEXP.ev_le n m (Or.inr hocc)
  have h0 : n - ev K m + ev K m = n := tsub_add_cancel_of_le hle
  have := SEXP.closure hu hA (n - ev K m) m (by omega) (by rw [h0]; exact hn)
  rwa [h0] at this
