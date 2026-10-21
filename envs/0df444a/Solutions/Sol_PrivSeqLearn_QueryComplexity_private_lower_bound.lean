-- Prove2me | solution 1 for PrivSeqLearn.QueryComplexity.private_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:00:14.233712+00:00
-- url     : https://prove2.me/submissions/e0d47391-0aa2-48fa-90c9-c69483c2e311

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting
import Definitions.Def_PrivSeqLearn_QueryComplexity_SpecialIntervals

set_option autoImplicit false
open PrivSeqLearn.QueryComplexity

lemma psl_coverable_mono_set {δ : ℝ} {L : ℕ} {U V : Set ℝ} (hUV : U ⊆ V)
    (h : Coverable δ L V) : Coverable δ L U := by
  obtain ⟨a, b, hs, hl⟩ := h
  exact ⟨a, b, hUV.trans hs, hl⟩

lemma psl_bounded_coverable {δ : ℝ} (hδ : 0 < δ) {V : Set ℝ} (hV : Bornology.IsBounded V) :
    ∃ L, Coverable δ L V := by
  obtain ⟨R, hR⟩ := hV.subset_closedBall 0
  refine ⟨⌈2 * R / δ⌉₊ + 1, fun j => -R + (j : ℕ) * δ, fun j => -R + ((j : ℕ) + 1) * δ, ?_, ?_⟩
  · intro x hx
    have hx' := hR hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hx'
    obtain ⟨h1, h2⟩ := hx'
    have hpos : 0 ≤ (x + R) / δ := div_nonneg (by linarith) hδ.le
    set j := ⌊(x + R) / δ⌋₊ with hj
    have hjle : (j : ℝ) ≤ (x + R) / δ := Nat.floor_le hpos
    have hjlt : (x + R) / δ < j + 1 := Nat.lt_floor_add_one _
    have hjn : j < ⌈2 * R / δ⌉₊ + 1 := by
      have h3 : (x + R) / δ ≤ 2 * R / δ := by
        apply div_le_div_of_nonneg_right _ hδ.le; linarith
      have h4 : (j : ℝ) ≤ ⌈2 * R / δ⌉₊ := hjle.trans (h3.trans (Nat.le_ceil _))
      have : j ≤ ⌈2 * R / δ⌉₊ := by exact_mod_cast h4
      omega
    rw [Set.mem_iUnion]
    refine ⟨⟨j, hjn⟩, ?_, ?_⟩
    · have := (le_div_iff₀ hδ).1 hjle
      show -R + (j : ℝ) * δ ≤ x
      linarith
    · have := (div_lt_iff₀ hδ).1 hjlt
      show x ≤ -R + ((j : ℝ) + 1) * δ
      linarith
  · intro j
    show -R + ((j : ℕ) + 1) * δ - (-R + (j : ℕ) * δ) ≤ δ
    linarith

theorem psl_coverNumber_mono (δ : ℝ) (L : ℕ) (U V : Set ℝ) (hδ : 0 < δ) (hUV : U ⊆ V)
    (hV : Bornology.IsBounded V) (hU : L ≤ coverNumber δ U) :
    L ≤ coverNumber δ V := by
  obtain ⟨L0, hL0⟩ := psl_bounded_coverable hδ hV
  have hne : {L | Coverable δ L V}.Nonempty := ⟨L0, hL0⟩
  have hmem : Coverable δ (sInf {L | Coverable δ L V}) V := Nat.sInf_mem hne
  have h2 : coverNumber δ U ≤ coverNumber δ V :=
    Nat.sInf_le (psl_coverable_mono_set hUV hmem)
  exact hU.trans h2

lemma psl_cov_insert {δ : ℝ} {n : ℕ} {E : Set ℝ} (c d : ℝ) (hcd : d - c ≤ δ)
    (h : Coverable δ n E) : Coverable δ (n + 1) (E ∪ Set.Icc c d) := by
  obtain ⟨a, b, hs, hl⟩ := h
  refine ⟨(Fin.cons c a : Fin (n + 1) → ℝ), (Fin.cons d b : Fin (n + 1) → ℝ), ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · have := hs hx
      simp only [Set.mem_iUnion] at this ⊢
      obtain ⟨j, hj⟩ := this
      exact ⟨j.succ, by simpa using hj⟩
    · simp only [Set.mem_iUnion]
      exact ⟨0, by simpa using hx⟩
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hcd
    · simpa using hl j

def pslU (𝒥 : Finset (ℝ × ℝ)) : Set ℝ := ⋃ J ∈ 𝒥, Set.Ico J.1 J.2

def pslF (δ : ℝ) (𝒥 : Finset (ℝ × ℝ)) : Set ℝ := {s | δ ≤ s ∧ ∃ J ∈ 𝒥, s = J.1 ∨ s = J.2}

lemma pslF_finite (δ : ℝ) (𝒥 : Finset (ℝ × ℝ)) : (pslF δ 𝒥).Finite := by
  apply Set.Finite.subset
    ((Finset.finite_toSet (𝒥.image Prod.fst)).union (Finset.finite_toSet (𝒥.image Prod.snd)))
  rintro s ⟨_, J, hJ, hs⟩
  rcases hs with rfl | rfl
  · exact Or.inl (by simp; exact ⟨J.2, hJ⟩)
  · exact Or.inr (by simp; exact ⟨J.1, hJ⟩)

lemma pslF_mono (δ : ℝ) {𝒥 𝒦 : Finset (ℝ × ℝ)} (h : 𝒦 ⊆ 𝒥) : pslF δ 𝒦 ⊆ pslF δ 𝒥 := by
  rintro s ⟨hs, J, hJ, hJs⟩
  exact ⟨hs, J, h hJ, hJs⟩

open Classical in
lemma psl_chain_step (δ : ℝ) (𝒥 R : Finset (ℝ × ℝ)) (J1 : ℝ × ℝ) (c d : ℝ) (m'' : ℕ)
    (hRsub : R ⊆ 𝒥) (hJ1R : J1 ∈ R) (hJ1lt : J1.1 < J1.2) (hJ1δ : δ ≤ J1.2)
    (hmin : ∀ J ∈ 𝒥, J1.1 ≤ J.1)
    (hrest : ∀ J ∈ 𝒥 \ R, J1.2 < J.1) (hlt : ∀ J ∈ 𝒥, J.1 < J.2)
    (hcd : d - c ≤ δ) (hR : ∀ J ∈ R, Set.Ico J.1 J.2 ⊆ Set.Icc c d)
    (hcov : Coverable δ m'' (pslU (𝒥 \ R)))
    (hm : 2 * m'' ≤ (pslF δ (𝒥 \ R)).ncard + (if ∃ J ∈ 𝒥 \ R, J.1 < δ then 1 else 0)) :
    Coverable δ (m'' + 1) (pslU 𝒥) ∧
      2 * (m'' + 1) ≤ (pslF δ 𝒥).ncard + (if ∃ J ∈ 𝒥, J.1 < δ then 1 else 0) := by
  have hFfin := pslF_finite δ 𝒥
  have hsubF : pslF δ (𝒥 \ R) ⊆ pslF δ 𝒥 := pslF_mono δ Finset.sdiff_subset
  have hcount : ∀ N : Set ℝ, N.Finite → N ⊆ pslF δ 𝒥 → Disjoint N (pslF δ (𝒥 \ R)) →
      (pslF δ (𝒥 \ R)).ncard + N.ncard ≤ (pslF δ 𝒥).ncard := by
    intro N hN hNF hdis
    have hF'fin : (pslF δ (𝒥 \ R)).Finite := hFfin.subset hsubF
    rw [← Set.ncard_union_eq hdis.symm hF'fin hN]
    exact Set.ncard_le_ncard (Set.union_subset hsubF hNF) hFfin
  have hdisj : ∀ s : ℝ, s ∈ pslF δ (𝒥 \ R) → J1.2 < s := by
    rintro s ⟨_, J, hJ, hs⟩
    have h1 := hrest J hJ
    have h2 := hlt J (Finset.mem_sdiff.1 hJ).1
    rcases hs with rfl | rfl <;> linarith
  refine ⟨?_, ?_⟩
  · have hsub : pslU 𝒥 ⊆ pslU (𝒥 \ R) ∪ Set.Icc c d := by
      intro x hx
      simp only [pslU, Set.mem_iUnion] at hx
      obtain ⟨J, hJ, hxJ⟩ := hx
      by_cases hJR : J ∈ R
      · exact Or.inr (hR J hJR hxJ)
      · left
        simp only [pslU, Set.mem_iUnion]
        exact ⟨J, Finset.mem_sdiff.2 ⟨hJ, hJR⟩, hxJ⟩
    exact psl_coverable_mono_set hsub (psl_cov_insert c d hcd hcov)
  · by_cases hδa : δ ≤ J1.1
    · have hflag : ¬ ∃ J ∈ 𝒥, J.1 < δ := by
        rintro ⟨J, hJ, hJδ⟩
        have := hmin J hJ
        linarith
      have hflag' : ¬ ∃ J ∈ 𝒥 \ R, J.1 < δ := by
        rintro ⟨J, hJ, hJδ⟩
        exact hflag ⟨J, (Finset.mem_sdiff.1 hJ).1, hJδ⟩
      rw [if_neg hflag] 
      rw [if_neg hflag'] at hm
      have hN : (pslF δ (𝒥 \ R)).ncard + ({J1.1, J1.2} : Set ℝ).ncard ≤ (pslF δ 𝒥).ncard := by
        apply hcount _ (Set.toFinite _)
        · intro s hs
          rcases hs with rfl | rfl
          · exact ⟨hδa, J1, hRsub hJ1R, Or.inl rfl⟩
          · exact ⟨hJ1δ, J1, hRsub hJ1R, Or.inr rfl⟩
        · rw [Set.disjoint_left]
          intro s hs hsF
          have := hdisj s hsF
          rcases hs with rfl | rfl <;> linarith
      rw [Set.ncard_pair (ne_of_lt hJ1lt)] at hN
      omega
    · have hflag : ∃ J ∈ 𝒥, J.1 < δ := ⟨J1, hRsub hJ1R, not_le.1 hδa⟩
      have hflag' : ¬ ∃ J ∈ 𝒥 \ R, J.1 < δ := by
        rintro ⟨J, hJ, hJδ⟩
        have := hrest J hJ
        linarith
      rw [if_pos hflag]
      rw [if_neg hflag'] at hm
      have hN : (pslF δ (𝒥 \ R)).ncard + ({J1.2} : Set ℝ).ncard ≤ (pslF δ 𝒥).ncard := by
        apply hcount _ (Set.toFinite _)
        · intro s hs
          rw [Set.mem_singleton_iff] at hs
          subst hs
          exact ⟨hJ1δ, J1, hRsub hJ1R, Or.inr rfl⟩
        · rw [Set.disjoint_left]
          intro s hs hsF
          have := hdisj s hsF
          rw [Set.mem_singleton_iff] at hs
          linarith
      rw [Set.ncard_singleton] at hN
      omega

open Classical in
lemma psl_chain_cover (ϵ δ : ℝ) (h2 : 2 * ϵ ≤ δ) :
    ∀ (n : ℕ) (𝒥 : Finset (ℝ × ℝ)), 𝒥.card = n →
      (∀ J ∈ 𝒥, J.1 < J.2 ∧ J.2 - J.1 ≤ ϵ) →
      (∀ J ∈ 𝒥, ∀ J' ∈ 𝒥, J ≠ J' → J.2 ≤ J'.1 ∨ J'.2 ≤ J.1) →
      (∀ J ∈ 𝒥, δ ≤ J.2) →
      ∃ m, Coverable δ m (pslU 𝒥) ∧
        2 * m ≤ (pslF δ 𝒥).ncard + (if ∃ J ∈ 𝒥, J.1 < δ then 1 else 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro 𝒥 hcard h1 h2' h3
  rcases 𝒥.eq_empty_or_nonempty with rfl | hne
  · refine ⟨0, ⟨Fin.elim0, Fin.elim0, ?_, fun j => Fin.elim0 j⟩, Nat.zero_le _⟩
    intro x hx
    simp [pslU] at hx
  · obtain ⟨J1, hJ1, hmin⟩ := Finset.exists_min_image 𝒥 Prod.fst hne
    have hJ1' := h1 J1 hJ1
    have hlt : ∀ J ∈ 𝒥, J.1 < J.2 := fun J hJ => (h1 J hJ).1
    have hsep : ∀ J ∈ 𝒥, J ≠ J1 → J1.2 ≤ J.1 := by
      intro J hJ hne'
      rcases h2' J hJ J1 hJ1 hne' with h | h
      · exfalso; have := hmin J hJ; have := (h1 J hJ).1; linarith
      · exact h
    -- the generic recursive call
    have hrec : ∀ R : Finset (ℝ × ℝ), R ⊆ 𝒥 → J1 ∈ R → ∀ c d : ℝ, d - c ≤ δ →
        (∀ J ∈ R, Set.Ico J.1 J.2 ⊆ Set.Icc c d) → (∀ J ∈ 𝒥 \ R, J1.2 < J.1) →
        ∃ m, Coverable δ m (pslU 𝒥) ∧
          2 * m ≤ (pslF δ 𝒥).ncard + (if ∃ J ∈ 𝒥, J.1 < δ then 1 else 0) := by
      intro R hRsub hJ1R c d hcd hR hrest
      have hlt' : (𝒥 \ R).card < n := by
        rw [← hcard]
        exact Finset.card_lt_card (Finset.sdiff_ssubset hRsub ⟨J1, hJ1R⟩)
      obtain ⟨m'', hcov, hm⟩ := ih _ hlt' (𝒥 \ R) rfl
        (fun J hJ => h1 J (Finset.mem_sdiff.1 hJ).1)
        (fun J hJ J' hJ' => h2' J (Finset.mem_sdiff.1 hJ).1 J' (Finset.mem_sdiff.1 hJ').1)
        (fun J hJ => h3 J (Finset.mem_sdiff.1 hJ).1)
      exact ⟨m'' + 1, psl_chain_step δ 𝒥 R J1 c d m'' hRsub hJ1R hJ1'.1 (h3 J1 hJ1) (hmin) hrest
        hlt hcd hR hcov hm⟩
    by_cases hadj : ∃ J2 ∈ 𝒥, J2.1 = J1.2
    · obtain ⟨J2, hJ2, hJ21⟩ := hadj
      have hJ2ne : J2 ≠ J1 := by
        intro e; rw [e] at hJ21; linarith [hJ1'.1]
      have hJ2' := h1 J2 hJ2
      refine hrec {J1, J2} ?_ (by simp) J1.1 J2.2 ?_ ?_ ?_
      · intro J hJ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hJ
        rcases hJ with rfl | rfl <;> assumption
      · linarith [hJ1'.2, hJ2'.2]
      · intro J hJ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hJ
        rcases hJ with rfl | rfl
        · intro x hx
          exact ⟨hx.1, by linarith [hx.2, hJ2'.1]⟩
        · intro x hx
          exact ⟨by linarith [hx.1, hJ1'.1], hx.2.le⟩
      · intro J hJ
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hJ
        obtain ⟨hJ, hn1, hn2⟩ := hJ
        have e1 := hsep J hJ hn1
        rcases h2' J hJ J2 hJ2 hn2 with h | h
        · exfalso; have := (h1 J hJ).1; linarith
        · linarith [hJ2'.1]
    · push_neg at hadj
      refine hrec {J1} ?_ (by simp) J1.1 J1.2 ?_ ?_ ?_
      · intro J hJ
        rw [Finset.mem_singleton] at hJ
        rw [hJ]; exact hJ1
      · linarith [hJ1'.2, hJ1'.1]
      · intro J hJ
        rw [Finset.mem_singleton] at hJ
        rw [hJ]
        intro x hx
        exact ⟨hx.1, hx.2.le⟩
      · intro J hJ
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hJ
        have e1 := hsep J hJ.1 hJ.2
        exact lt_of_le_of_ne e1 (fun e => hadj J hJ.1 e.symm)


lemma psl_hist_congr {N : ℕ} (φ : Strategy N) (x x' : ℝ) (y : Fin φ.Ybar)
    (h : ∀ k : Fin N, decide (queries φ x y k ≤ x') = decide (queries φ x y k ≤ x)) :
    ∀ k, k ≤ N → hist φ x' y k = hist φ x y k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hk' : k < N := hk
    have e := ih hk'.le
    have h2 : decide (φ.query (hist φ x y k) y ≤ x') = decide (φ.query (hist φ x y k) y ≤ x) :=
      h ⟨k, hk'⟩
    show hist φ x' y k ++ [decide (φ.query (hist φ x' y k) y ≤ x')] =
      hist φ x y k ++ [decide (φ.query (hist φ x y k) y ≤ x)]
    rw [e, h2]

lemma psl_final {N : ℕ} (ϵ : ℝ) (φ : Strategy N) (hacc : IsAccurate ϵ φ)
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) (y : Fin φ.Ybar) (a b : ℝ)
    (hax : a ≤ x) (hxb : x < b)
    (hcons : ∀ w ∈ queryPoints (queries φ x y), w ≤ a ∨ b ≤ w) :
    b - a ≤ ϵ := by
  have ha0 : 0 ≤ a := by
    have h0 : (0 : ℝ) ∈ queryPoints (queries φ x y) := by simp [queryPoints]
    rcases hcons 0 h0 with h | h
    · exact h
    · exfalso; linarith [hx.1]
  have hb1 : b ≤ 1 := by
    have h1 : (1 : ℝ) ∈ queryPoints (queries φ x y) := by simp [queryPoints]
    rcases hcons 1 h1 with h | h
    · exfalso; linarith [hx.2]
    · exact h
  have hsame : ∀ x' ∈ Set.Ico a b, ∀ k : Fin N,
      decide (queries φ x y k ≤ x') = decide (queries φ x y k ≤ x) := by
    intro x' hx' k
    have hk : queries φ x y k ∈ queryPoints (queries φ x y) := by simp [queryPoints]
    rcases hcons _ hk with h | h
    · have h1 : queries φ x y k ≤ x' := h.trans hx'.1
      have h2 : queries φ x y k ≤ x := h.trans hax
      simp [h1, h2]
    · have h1 : ¬ queries φ x y k ≤ x' := not_le.2 (lt_of_lt_of_le hx'.2 h)
      have h2 : ¬ queries φ x y k ≤ x := not_le.2 (lt_of_lt_of_le hxb h)
      simp [h1, h2]
  have hest : ∀ x' ∈ Set.Ico a b, estimate φ x' y = estimate φ x y := by
    intro x' hx'
    unfold estimate
    rw [psl_hist_congr φ x x' y (hsame x' hx') N le_rfl]
  have hacc' : ∀ x' ∈ Set.Ico a b, |estimate φ x y - x'| ≤ ϵ / 2 := by
    intro x' hx'
    have := hacc x' ⟨ha0.trans hx'.1, hx'.2.trans_le hb1⟩ y
    rw [hest x' hx'] at this
    exact this
  by_contra hlt
  push_neg at hlt
  have h1 := hacc' a ⟨le_rfl, by linarith [hlt, hax, hxb]⟩
  have hϵ : 0 ≤ ϵ := by linarith [abs_nonneg (estimate φ x y - a)]
  have hx' : (a + ϵ + b) / 2 ∈ Set.Ico a b := ⟨by linarith, by linarith⟩
  have h2 := hacc' _ hx'
  rw [abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]


theorem psl_eq_20 {N : ℕ} (ϵ : ℝ) (φ : Strategy N) (hacc : IsAccurate ϵ φ) (q : Fin N → ℝ) :
    infoSet φ q ⊆ specialUnion ϵ q := by
  rintro x ⟨hx, y, rfl⟩
  have hfin : (queryPoints (queries φ x y)).Finite :=
    ((Set.finite_range _).insert 1).insert 0
  have h0 : (0 : ℝ) ∈ queryPoints (queries φ x y) := by simp [queryPoints]
  have h1 : (1 : ℝ) ∈ queryPoints (queries φ x y) := by simp [queryPoints]
  have hne1 : {w ∈ queryPoints (queries φ x y) | w ≤ x}.Nonempty := ⟨0, h0, hx.1⟩
  have hne2 : {w ∈ queryPoints (queries φ x y) | x < w}.Nonempty := ⟨1, h1, hx.2⟩
  obtain ⟨a, ⟨ha, hax⟩, hamax⟩ := Set.exists_max_image _ id (hfin.subset (fun w hw => hw.1)) hne1
  obtain ⟨b, ⟨hb, hxb⟩, hbmin⟩ := Set.exists_min_image _ id (hfin.subset (fun w hw => hw.1)) hne2
  have hcons : ∀ w ∈ queryPoints (queries φ x y), w ≤ a ∨ b ≤ w := by
    intro w hw
    by_cases hwx : w ≤ x
    · exact Or.inl (hamax w ⟨hw, hwx⟩)
    · exact Or.inr (hbmin w ⟨hw, not_le.1 hwx⟩)
  have hle := psl_final ϵ φ hacc x hx y a b hax hxb hcons
  simp only [specialUnion, Set.mem_iUnion]
  exact ⟨a, b, ⟨ha, hb, lt_of_le_of_lt hax hxb, hle, hcons⟩, hax, hxb⟩

open Classical in
/-- number of queries at positions `≥ j` landing in `(0, δ)` -/
noncomputable def pslCnt {N : ℕ} (φ : Strategy N) (δ x : ℝ) (y : Fin φ.Ybar) (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun k : Fin N => j ≤ k.val ∧ queries φ x y k ∈ Set.Ioo (0 : ℝ) δ)).card

lemma pslCnt_succ_le {N : ℕ} (φ : Strategy N) (δ x : ℝ) (y : Fin φ.Ybar) (j : ℕ) :
    pslCnt φ δ x y (j + 1) ≤ pslCnt φ δ x y j := by
  unfold pslCnt
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact ⟨by omega, hk.2⟩

lemma pslCnt_succ_add {N : ℕ} (φ : Strategy N) (δ x : ℝ) (y : Fin φ.Ybar) (j : ℕ) (hj : j < N)
    (hP : queries φ x y ⟨j, hj⟩ ∈ Set.Ioo (0 : ℝ) δ) :
    pslCnt φ δ x y (j + 1) + 1 ≤ pslCnt φ δ x y j := by
  classical
  unfold pslCnt
  have hnot : (⟨j, hj⟩ : Fin N) ∉ Finset.univ.filter
      (fun k : Fin N => j + 1 ≤ k.val ∧ queries φ x y k ∈ Set.Ioo (0 : ℝ) δ) := by
    simp
  rw [← Finset.card_insert_of_notMem hnot]
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_insert] at hk
  rcases hk with rfl | hk
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_rfl, hP⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact ⟨by omega, hk.2⟩

lemma pslCnt_zero {N : ℕ} (φ : Strategy N) (δ x : ℝ) (y : Fin φ.Ybar) :
    pslCnt φ δ x y 0 = {k : Fin N | queries φ x y k ∈ Set.Ioo (0 : ℝ) δ}.ncard := by
  classical
  unfold pslCnt
  rw [← Set.ncard_coe_finset]
  congr 1
  ext k
  simp

lemma psl_vol_bound {N : ℕ} (ϵ δ : ℝ) (φ : Strategy N) (hacc : IsAccurate ϵ φ)
    (hδ1 : δ ≤ 1) (y : Fin φ.Ybar) :
    ∀ d m j (h : List Bool), j + d = N →
      (∀ x ∈ Set.Ioo (0 : ℝ) δ, hist φ x y j = h → pslCnt φ δ x y j ≤ m) →
      MeasureTheory.volume {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y j = h} ≤
        2 ^ m * ENNReal.ofReal ϵ := by
  intro d
  induction d with
  | zero =>
    intro m j h hjN _
    have hjN' : j = N := by omega
    subst hjN'
    have hsub : {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y j = h} ⊆
        Set.Icc (φ.est h y - ϵ / 2) (φ.est h y + ϵ / 2) := by
      rintro x ⟨hx, hxh⟩
      have := hacc x ⟨hx.1.le, lt_of_lt_of_le hx.2 hδ1⟩ y
      have e : estimate φ x y = φ.est h y := by
        unfold estimate; rw [hxh]
      rw [e, abs_le] at this
      constructor <;> linarith [this.1, this.2]
    calc MeasureTheory.volume {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y j = h}
        ≤ MeasureTheory.volume (Set.Icc (φ.est h y - ϵ / 2) (φ.est h y + ϵ / 2)) :=
          MeasureTheory.measure_mono hsub
      _ = ENNReal.ofReal ϵ := by
          rw [Real.volume_Icc]; congr 1; ring
      _ ≤ 2 ^ m * ENNReal.ofReal ϵ :=
          le_mul_of_one_le_left bot_le (one_le_pow₀ (by norm_num))
  | succ d ih =>
    intro m j h hjN hcnt
    have hj : j < N := by omega
    set c := φ.query h y with hc
    have hstep : ∀ x : ℝ, hist φ x y j = h →
        hist φ x y (j + 1) = h ++ [decide (c ≤ x)] := by
      intro x hx
      show hist φ x y j ++ [decide (φ.query (hist φ x y j) y ≤ x)] = _
      rw [hx]
    have hback : ∀ (x : ℝ) (b : Bool), hist φ x y (j + 1) = h ++ [b] → hist φ x y j = h := by
      intro x b hx
      have : hist φ x y j ++ [decide (φ.query (hist φ x y j) y ≤ x)] = h ++ [b] := hx
      exact (List.append_inj' this rfl).1
    by_cases hcI : c ∈ Set.Ioo (0 : ℝ) δ
    · -- informative query
      have hinfo : ∀ x : ℝ, hist φ x y j = h → queries φ x y ⟨j, hj⟩ ∈ Set.Ioo (0 : ℝ) δ := by
        intro x hx
        show φ.query (hist φ x y j) y ∈ _
        rw [hx]; exact hcI
      cases m with
      | zero =>
        have : {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y j = h} = ∅ := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
          intro hx hxh
          have h1 := hcnt x hx hxh
          have h2 := pslCnt_succ_add φ δ x y j hj (hinfo x hxh)
          omega
        rw [this]; simp
      | succ m' =>
        have hb : ∀ b : Bool, MeasureTheory.volume
            {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y (j + 1) = h ++ [b]} ≤
            2 ^ m' * ENNReal.ofReal ϵ := by
          intro b
          apply ih m' (j + 1) (h ++ [b]) (by omega)
          intro x hx hxh
          have hxj := hback x b hxh
          have h1 := hcnt x hx hxj
          have h2 := pslCnt_succ_add φ δ x y j hj (hinfo x hxj)
          omega
        have hsub : {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y j = h} ⊆
            {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y (j + 1) = h ++ [true]} ∪
            {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y (j + 1) = h ++ [false]} := by
          rintro x ⟨hx, hxh⟩
          simp only [Set.mem_union, Set.mem_setOf_eq]
          rw [hstep x hxh]
          cases hd : decide (c ≤ x)
          · exact Or.inr ⟨hx, rfl⟩
          · exact Or.inl ⟨hx, rfl⟩
        calc MeasureTheory.volume {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y j = h}
            ≤ MeasureTheory.volume ({x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y (j + 1) = h ++ [true]} ∪
              {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y (j + 1) = h ++ [false]}) :=
              MeasureTheory.measure_mono hsub
          _ ≤ _ := MeasureTheory.measure_union_le _ _
          _ ≤ 2 ^ m' * ENNReal.ofReal ϵ + 2 ^ m' * ENNReal.ofReal ϵ := add_le_add (hb true) (hb false)
          _ = 2 ^ (m' + 1) * ENNReal.ofReal ϵ := by rw [pow_succ]; ring
    · -- uninformative query: the response is the same for all x ∈ (0, δ)
      have hconst : ∀ x ∈ Set.Ioo (0 : ℝ) δ, decide (c ≤ x) = decide (c ≤ 0) := by
        intro x hx
        by_cases hc0 : c ≤ 0
        · have : c ≤ x := hc0.trans hx.1.le
          simp [hc0, this]
        · have hδc : δ ≤ c := by
            by_contra hlt
            exact hcI ⟨not_le.1 hc0, not_le.1 hlt⟩
          have : ¬ c ≤ x := not_le.2 (lt_of_lt_of_le hx.2 hδc)
          simp [hc0, this]
      have hsub : {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y j = h} ⊆
          {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y (j + 1) = h ++ [decide (c ≤ 0)]} := by
        rintro x ⟨hx, hxh⟩
        refine ⟨hx, ?_⟩
        rw [hstep x hxh, hconst x hx]
      calc MeasureTheory.volume {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y j = h}
          ≤ MeasureTheory.volume
              {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y (j + 1) = h ++ [decide (c ≤ 0)]} :=
            MeasureTheory.measure_mono hsub
        _ ≤ 2 ^ m * ENNReal.ofReal ϵ := by
          apply ih m (j + 1) (h ++ [decide (c ≤ 0)]) (by omega)
          intro x hx hxh
          have hxj := hback x _ hxh
          exact (pslCnt_succ_le φ δ x y j).trans (hcnt x hx hxj)

lemma psl_lemma_7_1 {N : ℕ} (ϵ δ : ℝ) (φ : Strategy N) (hacc : IsAccurate ϵ φ) (hϵ : 0 < ϵ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (y : Fin φ.Ybar) :
    ∃ x ∈ Set.Ioo (0 : ℝ) δ,
      ⌈Real.logb 2 (δ / ϵ)⌉₊ ≤ {k : Fin N | queries φ x y k ∈ Set.Ioo (0 : ℝ) δ}.ncard := by
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < ⌈Real.logb 2 (δ / ϵ)⌉₊ := by
    have := hcon (δ / 2) ⟨by linarith, by linarith⟩
    omega
  set t := ⌈Real.logb 2 (δ / ϵ)⌉₊ with ht
  have hm : ∀ x ∈ Set.Ioo (0 : ℝ) δ, pslCnt φ δ x y 0 ≤ t - 1 := by
    intro x hx
    rw [pslCnt_zero]
    have := hcon x hx
    omega
  have hvol := psl_vol_bound ϵ δ φ hacc hδ1 y N (t - 1) 0 [] (by omega)
    (fun x hx _ => hm x hx)
  have hset : {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y 0 = []} = Set.Ioo 0 δ := by
    ext x; simp [hist]
  rw [hset, Real.volume_Ioo] at hvol
  have h2 : δ ≤ 2 ^ (t - 1) * ϵ := by
    have : ENNReal.ofReal (δ - 0) ≤ ENNReal.ofReal (2 ^ (t - 1) * ϵ) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      simpa [ENNReal.ofReal_pow] using hvol
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    linarith
  have h3 : δ / ϵ ≤ 2 ^ (t - 1) := by
    rw [div_le_iff₀ hϵ]; exact h2
  have h4 : Real.logb 2 (δ / ϵ) ≤ ((t - 1 : ℕ) : ℝ) := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_natCast]
    exact h3
  have h5 : ((t - 1 : ℕ) : ℝ) < Real.logb 2 (δ / ϵ) := Nat.lt_ceil.1 (by omega)
  linarith

theorem psl_special_cover_bound {N : ℕ} (ϵ δ : ℝ) (hϵ : 0 < ϵ) (h2ϵδ : 2 * ϵ < δ)
    (q : Fin N → ℝ) (hq : ∀ k, q k ∈ Set.Ico (0 : ℝ) 1) :
    2 * coverNumber δ (specialUnion ϵ q) ≤ (specialQueries ϵ δ q).ncard + 3 := by
  classical
  have hP : ∀ w ∈ queryPoints q, 0 ≤ w ∧ w ≤ 1 := by
    intro w hw
    simp only [queryPoints, Set.mem_insert_iff, Set.mem_range] at hw
    rcases hw with rfl | rfl | ⟨k, rfl⟩
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨(hq k).1, (hq k).2.le⟩
  have hPfin : (queryPoints q).Finite := ((Set.finite_range q).insert 1).insert 0
  have hSfin : {J : ℝ × ℝ | IsSpecial ϵ q J.1 J.2}.Finite :=
    (hPfin.prod hPfin).subset (fun J hJ => ⟨hJ.1, hJ.2.1⟩)
  set 𝒥 : Finset (ℝ × ℝ) := hSfin.toFinset.filter (fun J => δ ≤ J.2) with h𝒥
  have hmem : ∀ J, J ∈ 𝒥 ↔ IsSpecial ϵ q J.1 J.2 ∧ δ ≤ J.2 := by
    intro J; simp [h𝒥]
  have hspec : ∀ J ∈ 𝒥, J.1 < J.2 ∧ J.2 - J.1 ≤ ϵ := fun J hJ =>
    ⟨((hmem J).1 hJ).1.2.2.1, ((hmem J).1 hJ).1.2.2.2.1⟩
  have hdis : ∀ J ∈ 𝒥, ∀ J' ∈ 𝒥, J ≠ J' → J.2 ≤ J'.1 ∨ J'.2 ≤ J.1 := by
    intro J hJ J' hJ' hne
    obtain ⟨hs, _⟩ := (hmem J).1 hJ
    obtain ⟨hs', _⟩ := (hmem J').1 hJ'
    obtain ⟨ha, hb, hab, _, hc⟩ := hs
    obtain ⟨ha', hb', hab', _, hc'⟩ := hs'
    rcases hc J'.1 ha' with h1 | h1
    · rcases hc' J.1 ha with h2 | h2
      · exfalso
        have e1 : J.1 = J'.1 := le_antisymm h2 h1
        rcases hc J'.2 hb' with h3 | h3
        · linarith
        · rcases hc' J.2 hb with h4 | h4
          · linarith
          · exact hne (Prod.ext e1 (le_antisymm h3 h4))
      · exact Or.inr h2
    · exact Or.inl h1
  obtain ⟨m, hcov, hm⟩ := psl_chain_cover ϵ δ h2ϵδ.le 𝒥.card 𝒥 rfl hspec hdis
    (fun J hJ => ((hmem J).1 hJ).2)
  have hflag : (if ∃ J ∈ 𝒥, J.1 < δ then 1 else 0) ≤ 1 := by split_ifs <;> simp
  have hFsub : pslF δ 𝒥 ⊆ specialQueries ϵ δ q := by
    rintro s ⟨hs, J, hJ, hJs⟩
    obtain ⟨hsp, _⟩ := (hmem J).1 hJ
    refine ⟨hs, ?_, J.1, J.2, hsp, hJs⟩
    rcases hJs with rfl | rfl
    · exact (hP _ hsp.1).2
    · exact (hP _ hsp.2.1).2
  have hQfin : (specialQueries ϵ δ q).Finite := hPfin.subset (by
    rintro s ⟨_, _, a, b, hsp, hs⟩
    rcases hs with rfl | rfl
    · exact hsp.1
    · exact hsp.2.1)
  have hcard := Set.ncard_le_ncard hFsub hQfin
  have hsubU : specialUnion ϵ q ⊆ pslU 𝒥 ∪ Set.Icc 0 δ := by
    intro x hx
    simp only [specialUnion, Set.mem_iUnion] at hx
    obtain ⟨a, b, hsp, hxab⟩ := hx
    by_cases hb : δ ≤ b
    · left
      simp only [pslU, Set.mem_iUnion]
      exact ⟨(a, b), (hmem (a, b)).2 ⟨hsp, hb⟩, hxab⟩
    · right
      exact ⟨(hP a hsp.1).1.trans hxab.1, by linarith [hxab.2, not_le.1 hb]⟩
  have hcov' : Coverable δ (m + 1) (specialUnion ϵ q) :=
    psl_coverable_mono_set hsubU (psl_cov_insert 0 δ (by linarith) hcov)
  have hle : coverNumber δ (specialUnion ϵ q) ≤ m + 1 := Nat.sInf_le hcov'
  omega


lemma psl_hist_length {N : ℕ} (φ : Strategy N) (x : ℝ) (y : Fin φ.Ybar) :
    ∀ k, (hist φ x y k).length = k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [hist, ih]

theorem solution (ϵ δ : ℝ) (L : ℕ) (hϵ : 0 < ϵ) (hδ : 0 < δ) (hL : 2 ≤ L)
    (h2ϵδ : 2 * ϵ < δ) (hδL : δ ≤ 1 / (L : ℝ))
    (N : ℕ) (φ : Strategy N) (hφ : QueriesInUnit φ) (hpriv : IsPrivate ϵ δ L φ) :
    ⌈Real.logb 2 (δ / ϵ)⌉ + 2 * (L : ℤ) - 4 ≤ (N : ℤ) := by
  classical
  obtain ⟨hacc, hpr⟩ := hpriv
  have hδ1 : δ ≤ 1 := by
    have : (1 : ℝ) / L ≤ 1 := by
      have hL' : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
      rw [div_le_one (by linarith)]; exact hL'
    linarith
  let y : Fin φ.Ybar := ⟨0, φ.Ybar_pos⟩
  obtain ⟨x, hx, hcnt⟩ := psl_lemma_7_1 ϵ δ φ hacc hϵ hδ hδ1 y
  have hx01 : x ∈ Set.Ico (0 : ℝ) 1 := ⟨hx.1.le, lt_of_lt_of_le hx.2 hδ1⟩
  have hq : ∀ k, queries φ x y k ∈ Set.Ico (0 : ℝ) 1 := by
    intro k
    show φ.query (hist φ x y k) y ∈ _
    exact hφ _ (by rw [psl_hist_length]; exact k.2) y
  have hqQ : queries φ x y ∈ Qset φ x := ⟨y, rfl⟩
  have hL1 := hpr x hx01 _ hqQ
  have hsub := psl_eq_20 ϵ φ hacc (queries φ x y)
  generalize queries φ x y = q at hq hqQ hL1 hsub hcnt
  have hPb : ∀ w ∈ queryPoints q, 0 ≤ w ∧ w ≤ 1 := by
    intro w hw
    simp only [queryPoints, Set.mem_insert_iff, Set.mem_range] at hw
    rcases hw with rfl | rfl | ⟨k, rfl⟩
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨(hq k).1, (hq k).2.le⟩
  have hbdd : Bornology.IsBounded (specialUnion ϵ q) := by
    apply (Metric.isBounded_Icc (0 : ℝ) 1).subset
    intro z hz
    simp only [specialUnion, Set.mem_iUnion] at hz
    obtain ⟨a, b, hsp, hz⟩ := hz
    exact ⟨(hPb a hsp.1).1.trans hz.1, hz.2.le.trans (hPb b hsp.2.1).2⟩
  have hL2 : L ≤ coverNumber δ (specialUnion ϵ q) :=
    psl_coverNumber_mono δ L _ _ hδ hsub hbdd hL1
  have hK := psl_special_cover_bound ϵ δ hϵ h2ϵδ q hq
  have hAB : Disjoint {k : Fin N | q k ∈ Set.Ioo (0 : ℝ) δ} {k : Fin N | q k ∈ Set.Ico δ 1} :=
    Set.disjoint_left.2 fun k hA hB => absurd hA.2 (not_lt.2 hB.1)
  have hAB' : {k : Fin N | q k ∈ Set.Ioo (0 : ℝ) δ}.ncard +
      {k : Fin N | q k ∈ Set.Ico δ 1}.ncard ≤ N := by
    rw [← Set.ncard_union_eq hAB (Set.toFinite _) (Set.toFinite _)]
    calc _ ≤ (Set.univ : Set (Fin N)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = N := by simp [Set.ncard_univ]
  have hSQ : specialQueries ϵ δ q ⊆ q '' {k : Fin N | q k ∈ Set.Ico δ 1} ∪ {1} := by
    rintro s ⟨hs1, hs2, a, b, hsp, hs⟩
    have hmem : s ∈ queryPoints q := by
      rcases hs with rfl | rfl
      · exact hsp.1
      · exact hsp.2.1
    simp only [queryPoints, Set.mem_insert_iff, Set.mem_range] at hmem
    rcases hmem with h0 | h1 | ⟨k, hk⟩
    · exfalso; linarith
    · right; exact h1
    · left
      refine ⟨k, ⟨?_, ?_⟩, hk⟩
      · show δ ≤ q k
        rw [hk]; exact hs1
      · exact (hq k).2
  have hKB : (specialQueries ϵ δ q).ncard ≤ {k : Fin N | q k ∈ Set.Ico δ 1}.ncard + 1 := by
    calc _ ≤ (q '' {k : Fin N | q k ∈ Set.Ico δ 1} ∪ {1}).ncard :=
          Set.ncard_le_ncard hSQ ((Set.toFinite _).union (Set.toFinite _))
      _ ≤ (q '' {k : Fin N | q k ∈ Set.Ico δ 1}).ncard + ({1} : Set ℝ).ncard :=
          Set.ncard_union_le _ _
      _ ≤ {k : Fin N | q k ∈ Set.Ico δ 1}.ncard + 1 := by
          rw [Set.ncard_singleton]
          exact Nat.add_le_add_right (Set.ncard_image_le (Set.toFinite _)) 1
  have h3 : ⌈Real.logb 2 (δ / ϵ)⌉ ≤ (⌈Real.logb 2 (δ / ϵ)⌉₊ : ℤ) :=
    Int.ceil_le.2 (by exact_mod_cast Nat.le_ceil _)
  omega
