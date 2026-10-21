-- Prove2me | solution 1 for PrivSeqLearn.QueryComplexity.special_cover_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:58:08.638524+00:00
-- url     : https://prove2.me/submissions/891b1338-ae91-4691-a564-050952951955

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting
import Definitions.Def_PrivSeqLearn_QueryComplexity_SpecialIntervals

set_option autoImplicit false
open PrivSeqLearn.QueryComplexity

lemma psl_coverable_mono_set {δ : ℝ} {L : ℕ} {U V : Set ℝ} (hUV : U ⊆ V)
    (h : Coverable δ L V) : Coverable δ L U := by
  obtain ⟨a, b, hs, hl⟩ := h
  exact ⟨a, b, hUV.trans hs, hl⟩

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

theorem solution {N : ℕ} (ϵ δ : ℝ) (hϵ : 0 < ϵ) (h2ϵδ : 2 * ϵ < δ)
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
