-- Prove2me | solution 1 for StableCount.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:25:47.959021+00:00
-- url     : https://prove2.me/submissions/fdc7620b-a09f-45fa-a6c7-ad831217ca89

import Mathlib
import Definitions.Def_StableCount_Groups

section
namespace StableCount

open StableMatching

namespace Dev.L52

variable {n : ℕ}

/-- the partner of the person `p` of sex `s` in the `m`-th matching of the chain -/
def partner (Q : Member n) : Sex → Fin (Q.R + 1) → Fin n → Fin n
  | .man, m, p => Q.μ m p
  | .woman, m, p => (Q.μ m).symm p

theorem moves_iff (Q : Member n) (s : Sex) (i : Fin Q.R) (p : Fin n) :
    Q.moves s i p ↔ partner Q s i.castSucc p ≠ partner Q s i.succ p := by
  cases s <;> rfl

/-- no move before `m` means the partner is the initial one -/
theorem partner_eq_zero (Q : Member n) (s : Sex) (p : Fin n) (m : Fin (Q.R + 1))
    (h : ∀ k : Fin Q.R, (k : ℕ) < m → ¬ Q.moves s k p) : partner Q s m p = partner Q s 0 p := by
  obtain ⟨m, hm⟩ := m
  induction m with
  | zero => rfl
  | succ m ih =>
    have hmR : m < Q.R := by omega
    have h1 := ih (by omega) (fun k hk => h k (by simp only [Fin.val_mk] at hk ⊢; omega))
    have h2 := h ⟨m, hmR⟩ (by simp)
    rw [moves_iff] at h2
    push_neg at h2
    rw [← h1]
    exact h2.symm

/-- no move between `a` and `b` -/
theorem partner_eq_of_no_move (Q : Member n) (s : Sex) (p : Fin n) (a b : Fin (Q.R + 1))
    (hab : a ≤ b) (h : ∀ k : Fin Q.R, (a : ℕ) ≤ k → (k : ℕ) < b → ¬ Q.moves s k p) :
    partner Q s b p = partner Q s a p := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have hab' : a ≤ b := hab
  induction b, hab' using Nat.le_induction with
  | base => rfl
  | succ b hab' ih =>
    have hbR : b < Q.R := by omega
    have h1 := ih (by omega) (Fin.mk_le_mk.mpr hab')
      (fun k hk1 hk2 => h k hk1 (by simp only [Fin.val_mk] at hk2 ⊢; omega))
    have h2 := h ⟨b, hbR⟩ (by simpa using hab') (by simp)
    rw [moves_iff] at h2
    push_neg at h2
    rw [← h1]
    exact h2.symm

open Classical in
theorem rank_sum {R : ℕ} (g : ℕ → ℝ) (S : Finset (Fin R)) :
    ∑ i ∈ S, g ((S.filter fun j => j ≤ i).card) = ∑ r ∈ Finset.Icc 1 S.card, g r := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S ha ih =>
    have han : a ∉ S := fun h => lt_irrefl _ (ha a h)
    rw [Finset.sum_insert han, Finset.card_insert_of_notMem han]
    have h1 : ((insert a S).filter fun j => j ≤ a).card = S.card + 1 := by
      have : (insert a S).filter (fun j => j ≤ a) = insert a S := by
        apply Finset.filter_true_of_mem
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact le_refl _
        · exact (ha j hj).le
      rw [this, Finset.card_insert_of_notMem han]
    have h2 : ∀ i ∈ S, ((insert a S).filter fun j => j ≤ i).card = (S.filter fun j => j ≤ i).card := by
      intro i hi
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hj | hj, hji⟩
        · exact absurd (hj ▸ hji) (not_le.mpr (ha i hi))
        · exact ⟨hj, hji⟩
      · rintro ⟨hj, hji⟩
        exact ⟨Or.inr hj, hji⟩
    rw [h1, Finset.sum_congr rfl (fun i hi => by rw [h2 i hi]), ih,
      Finset.sum_Icc_succ_top (by omega)]
    ring

theorem shares_of_consecutive (Q : Member n) (w : Fin n) (i j : Fin Q.R) (hij : i < j)
    (hi : Q.moves .woman i w) (hj : Q.moves .woman j w)
    (hno : ∀ k : Fin Q.R, i < k → k < j → ¬ Q.moves .woman k w) : Q.sharesMan i j := by
  have hsame : (Q.μ j.castSucc).symm w = (Q.μ i.succ).symm w := by
    have := partner_eq_of_no_move Q .woman w i.succ j.castSucc
      (by rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hij) (fun k hk1 hk2 => by
        apply hno k
        · simp only [Fin.val_succ] at hk1; exact hk1
        · simpa using hk2)
    simpa [partner] using this
  refine ⟨(Q.μ i.succ).symm w, ?_, ?_⟩
  · show Q.μ i.castSucc _ ≠ Q.μ i.succ _
    intro heq
    apply hi
    have h1 : Q.μ i.succ ((Q.μ i.succ).symm w) = w := Equiv.apply_symm_apply _ _
    have h2 : (Q.μ i.castSucc).symm w = (Q.μ i.succ).symm w := by
      rw [Equiv.symm_apply_eq]; rw [heq, h1]
    exact h2
  · show Q.μ j.castSucc _ ≠ Q.μ j.succ _
    intro heq
    apply hj
    have h1 : Q.μ j.castSucc ((Q.μ i.succ).symm w) = w := by
      rw [← hsame]; exact Equiv.apply_symm_apply _ _
    have h3 : Q.μ j.succ ((Q.μ i.succ).symm w) = w := by rw [← heq]; exact h1
    have h4 : (Q.μ j.succ).symm w = (Q.μ i.succ).symm w := by
      rw [Equiv.symm_apply_eq]; exact h3.symm
    rw [hsame, h4]

open Classical in
theorem le_of_woman (Q : Member n) (w : Fin n) :
    ∀ (d : ℕ) (i j : Fin Q.R), (j : ℕ) - i = d → i < j → Q.moves .woman i w →
      Q.moves .woman j w → Q.le i j := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i j hd hij hi hj
    set T : Finset (Fin Q.R) := Finset.univ.filter fun k => i < k ∧ Q.moves .woman k w with hT
    have hTne : T.Nonempty := ⟨j, by simp [hT, hij, hj]⟩
    set k0 := T.min' hTne with hk0
    have hk0T : k0 ∈ T := Finset.min'_mem _ _
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hk0T
    have hk0le : k0 ≤ j := Finset.min'_le _ _ (by simp [hT, hij, hj])
    have hcons : Q.sharesMan i k0 := by
      apply shares_of_consecutive Q w i k0 hk0T.1 hi hk0T.2
      intro k hk1 hk2 hmv
      have : k ∈ T := by simp [hT, hk1, hmv]
      exact absurd (Finset.min'_le _ _ this) (not_le.mpr hk2)
    have h1 : Q.le i k0 := Relation.ReflTransGen.single ⟨hk0T.1, hcons⟩
    rcases hk0le.lt_or_eq with hlt | heq
    · have h2 : Q.le k0 j := ih ((j : ℕ) - k0) (by have := hk0T.1; rw [Fin.lt_def] at this; omega)
        k0 j rfl hlt hk0T.2 hj
      exact Relation.ReflTransGen.trans h1 h2
    · rw [← heq]; exact h1

theorem le_of_chain (Q : Member n) (s : Sex) (p : Fin n) (i j : Fin Q.R) (hij : i < j)
    (hi : Q.moves s i p) (hj : Q.moves s j p) : Q.le i j := by
  cases s
  · exact Relation.ReflTransGen.single ⟨hij, p, hi, hj⟩
  · exact le_of_woman Q p _ i j rfl hij hi hj

open Classical in
theorem W_sub (h : ℕ → ℝ) {R : ℕ} (C T : Finset (Fin R)) (hT : T ⊆ C)
    (hsuf : ∀ i ∈ T, ∀ j ∈ C, i < j → j ∈ T) :
    W h C.card - W h (C \ T).card = ∑ i ∈ T, h ((C.filter fun j => j ≤ i).card) := by
  have h1 : W h C.card = ∑ i ∈ C, h ((C.filter fun j => j ≤ i).card) := by
    rw [rank_sum]; rfl
  have h2 : W h (C \ T).card = ∑ i ∈ C \ T, h ((C.filter fun j => j ≤ i).card) := by
    unfold W
    rw [← rank_sum h (C \ T)]
    refine Finset.sum_congr rfl fun i hi => ?_
    congr 2
    ext j
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hjC, -⟩, hji⟩
      exact ⟨hjC, hji⟩
    · rintro ⟨hjC, hji⟩
      refine ⟨⟨hjC, fun hjT => ?_⟩, hji⟩
      have hiC := (Finset.mem_sdiff.mp hi)
      rcases hji.lt_or_eq with hlt | heq
      · exact hiC.2 (hsuf j hjT i hiC.1 hlt)
      · exact hiC.2 (heq ▸ hjT)
  rw [h1, h2, ← Finset.sum_sdiff hT]
  ring

open Classical in
theorem qLoss_eq (Q : Member n) (h : ℕ → ℝ) (s : Sex) (b : Fin Q.R) :
    Q.qLoss h s b = ∑ p : Fin n, ∑ i ∈ (Q.chainOf s p).filter (fun i => i ∈ Q.up b),
      h (Q.rank s p i) := by
  have hF : ∀ P : Finset (Fin Q.R), Q.Fon h s P = ∑ p : Fin n, W h (Q.degOn P s p) := by
    intro P
    unfold Member.Fon
    cases s
    · rfl
    · exact Equiv.sum_comp (Q.μ 0) (fun p => W h (Q.degOn P .woman p))
  unfold Member.qLoss
  rw [hF, hF, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e1 : Q.degOn Finset.univ s p = (Q.chainOf s p).card := by
    simp [Member.degOn]
  have e2 : Q.degOn (Finset.univ \ Q.up b) s p =
      ((Q.chainOf s p) \ ((Q.chainOf s p).filter fun i => i ∈ Q.up b)).card := by
    unfold Member.degOn
    congr 1
    ext i
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter]
    tauto
  rw [e1, e2, W_sub h _ _ (Finset.filter_subset _ _)]
  · rfl
  · intro i hi j hj hij
    simp only [Finset.mem_filter, Member.chainOf, Finset.mem_univ, true_and] at hi hj ⊢
    refine ⟨hj, ?_⟩
    have hbi : Q.le b i := by simpa [Member.up] using hi.2
    have := le_of_chain Q s p i j hij hi.1 hj
    simp only [Member.up, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.trans hbi this

theorem mem_chainOf (Q : Member n) (s : Sex) (p : Fin n) (i : Fin Q.R) :
    i ∈ Q.chainOf s p ↔ Q.moves s i p := by
  unfold Member.chainOf
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem first_spec (Q : Member n) (v : Fin n) (hv : v ∈ Q.V) :
    Q.moves .man (Q.first v hv) v ∧ ∀ k : Fin Q.R, k < Q.first v hv → ¬ Q.moves .man k v := by
  have hne : (Q.chainOf .man v).Nonempty := Finset.card_pos.mp (Finset.mem_filter.mp hv).2
  refine ⟨?_, fun k hk hmv => ?_⟩
  · exact (mem_chainOf Q .man v _).mp (Finset.min'_mem (Q.chainOf .man v) hne)
  · have hk' : k ∈ Q.chainOf .man v := (mem_chainOf Q .man v k).mpr hmv
    exact absurd (Finset.min'_le _ k hk') (not_le.mpr hk)

theorem man_eq_first (Q : Member n) (v : Fin n) (hv : v ∈ Q.V) (m : Fin (Q.R + 1))
    (hm : (m : ℕ) ≤ Q.first v hv) : Q.μ m v = Q.μ 0 v := by
  obtain ⟨-, h2⟩ := first_spec Q v hv
  have := partner_eq_zero Q .man v m (fun k hk hmv =>
    h2 k (by rw [Fin.lt_def]; omega) hmv)
  simpa [partner] using this

theorem first_mem_chain (Q : Member n) (s : Sex) (v : Fin n) (hv : v ∈ Q.V) :
    Q.first v hv ∈ Q.chainOf s (Q.person s v) := by
  obtain ⟨h1, h2⟩ := first_spec Q v hv
  rw [mem_chainOf]
  cases s
  · exact h1
  · have e0 := man_eq_first Q v hv
    change (Q.μ (Q.first v hv).castSucc).symm (Q.μ 0 v) ≠ (Q.μ (Q.first v hv).succ).symm (Q.μ 0 v)
    have a1 : (Q.μ (Q.first v hv).castSucc).symm (Q.μ 0 v) = v := by
      rw [Equiv.symm_apply_eq]; exact (e0 _ (by simp)).symm
    intro heq
    have h3 : (Q.μ (Q.first v hv).succ).symm (Q.μ 0 v) = v := by rw [← heq]; exact a1
    rw [Equiv.symm_apply_eq] at h3
    have h4 := e0 (Q.first v hv).castSucc (by simp)
    have h5 : Q.μ (Q.first v hv).castSucc v ≠ Q.μ (Q.first v hv).succ v := h1
    exact h5 (by rw [h4, ← h3])

theorem first_rank (Q : Member n) (s : Sex) (v : Fin n) (hv : v ∈ Q.V) :
    Q.rank s (Q.person s v) (Q.first v hv) = 1 := by
  obtain ⟨h1, h2⟩ := first_spec Q v hv
  unfold Member.rank
  rw [Finset.card_eq_one]
  refine ⟨Q.first v hv, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hj, hji⟩
    rcases hji.lt_or_eq with hlt | heq
    · exfalso
      rw [mem_chainOf] at hj
      cases s
      · exact h2 j hlt hj
      · have e0 := man_eq_first Q v hv
        change (Q.μ j.castSucc).symm (Q.μ 0 v) ≠ (Q.μ j.succ).symm (Q.μ 0 v) at hj
        apply hj
        have hjl : (j : ℕ) < Q.first v hv := hlt
        have a1 : (Q.μ j.castSucc).symm (Q.μ 0 v) = v := by
          rw [Equiv.symm_apply_eq]; exact (e0 _ (by simp; omega)).symm
        have a2 : (Q.μ j.succ).symm (Q.μ 0 v) = v := by
          rw [Equiv.symm_apply_eq]; exact (e0 _ (by simp; omega)).symm
        rw [a1, a2]
    · exact heq
  · intro hj
    exact ⟨hj ▸ first_mem_chain Q s v hv, hj ▸ le_refl _⟩

theorem chain_empty_of_not_V (Q : Member n) (s : Sex) (v : Fin n) (hv : v ∉ Q.V) :
    Q.chainOf s (Q.person s v) = ∅ := by
  have hman : ∀ i : Fin Q.R, ¬ Q.moves .man i v := by
    intro i hi
    apply hv
    unfold Member.V
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold Member.dL Member.deg
    exact Finset.card_pos.mpr ⟨i, (mem_chainOf Q .man v i).mpr hi⟩
  ext i
  rw [mem_chainOf]
  simp only [Finset.notMem_empty, iff_false]
  cases s
  · exact hman i
  · have e0 : ∀ m : Fin (Q.R + 1), Q.μ m v = Q.μ 0 v := by
      intro m
      have := partner_eq_zero Q .man v m (fun k _ => hman k)
      simpa [partner] using this
    change ¬ ((Q.μ i.castSucc).symm (Q.μ 0 v) ≠ (Q.μ i.succ).symm (Q.μ 0 v))
    have a1 : (Q.μ i.castSucc).symm (Q.μ 0 v) = v := by
      rw [Equiv.symm_apply_eq]; exact (e0 _).symm
    have a2 : (Q.μ i.succ).symm (Q.μ 0 v) = v := by
      rw [Equiv.symm_apply_eq]; exact (e0 _).symm
    rw [a1, a2]; exact fun h => h rfl

theorem sum_person (Q : Member n) (s : Sex) (g : Fin n → ℝ)
    (hg : ∀ p, Q.chainOf s p = ∅ → g p = 0) :
    ∑ p : Fin n, g p = ∑ v ∈ Q.V, g (Q.person s v) := by
  have h1 : ∑ p : Fin n, g p = ∑ v : Fin n, g (Q.person s v) := by
    cases s
    · rfl
    · exact (Equiv.sum_comp (Q.μ 0) g).symm
  rw [h1]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun v _ hv => ?_
  exact hg _ (chain_empty_of_not_V Q s v hv)

open Classical in
theorem sum_q (Q : Member n) (h : ℕ → ℝ) (s : Sex) :
    ∑ v ∈ Q.V, Q.atFirst (Q.qLoss h s) v =
      ∑ p : Fin n, ∑ i ∈ Q.chainOf s p, (Q.s i : ℝ) * h (Q.rank s p i) := by
  -- the relation `b_v ⪯ i`
  let LF : Fin n → Fin Q.R → Prop := fun v i => ∃ hv : v ∈ Q.V, Q.le (Q.first v hv) i
  have hat : ∀ v, Q.atFirst (Q.qLoss h s) v =
      ∑ p : Fin n, ∑ i ∈ (Q.chainOf s p).filter (fun i => LF v i), h (Q.rank s p i) := by
    intro v
    by_cases hv : v ∈ Q.V
    · simp only [Member.atFirst, hv, dif_pos]
      rw [qLoss_eq]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr ?_ fun _ _ => rfl
      ext i
      simp only [Finset.mem_filter, LF, Member.up, Finset.mem_univ, true_and]
      exact and_congr_right fun _ => ⟨fun hh => ⟨hv, hh⟩, fun ⟨_, hh⟩ => hh⟩
    · simp only [Member.atFirst, hv, dif_neg, not_false_eq_true]
      symm
      refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun i hi => ?_
      exfalso
      simp only [Finset.mem_filter, LF] at hi
      obtain ⟨-, hv', -⟩ := hi
      exact hv hv'
  have hcount : ∀ i : Fin Q.R, (Q.V.filter fun v => LF v i).card = Q.s i := by
    intro i
    have : Q.V.filter (fun v => LF v i) = Q.support i := by
      ext v
      rw [Finset.mem_filter, Member.support, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, LF, Member.IsFirst]
      constructor
      · rintro ⟨hv, hv', hle⟩
        exact ⟨_, ⟨hv, rfl⟩, hle⟩
      · rintro ⟨j, ⟨hv, hj⟩, hle⟩
        exact ⟨hv, hv, hj ▸ hle⟩
    unfold Member.s
    rw [this]
  simp_rw [hat]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcount i]

end Dev.L52

theorem chk_lemma_5_2 {n : ℕ} (h : ℕ → ℝ) (Q : Member n) (s : Sex) :
    ∑ v ∈ Q.V, Q.atFirst (Q.qLoss h s) v = ∑ v ∈ Q.V, Hsum h (Q.dL s v) + Q.Omega h s ∧
    ∀ (v : Fin n) (hv : v ∈ Q.V),
      Q.first v hv ∈ Q.chainOf s (Q.person s v) ∧
      Q.rank s (Q.person s v) (Q.first v hv) = 1 ∧
      Q.omegaTerm h s v (Q.first v hv) = ((Q.s (Q.first v hv) : ℝ) - 2) * h 1 := by
  refine ⟨?_, fun v hv => ⟨Dev.L52.first_mem_chain Q s v hv, Dev.L52.first_rank Q s v hv, ?_⟩⟩
  · rw [Dev.L52.sum_q]
    rw [Dev.L52.sum_person Q s
      (fun p => ∑ i ∈ Q.chainOf s p, (Q.s i : ℝ) * h (Q.rank s p i)) (fun p hp => by simp [hp])]
    unfold Member.Omega
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hH : Hsum h (Q.dL s v) = ∑ i ∈ Q.chainOf s (Q.person s v),
        ((Q.rank s (Q.person s v) i : ℝ) + 1) * h (Q.rank s (Q.person s v) i) := by
      unfold Hsum Member.dL Member.deg
      rw [← Dev.L52.rank_sum (fun r => ((r : ℝ) + 1) * h r)]
      rfl
    rw [hH, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold Member.omegaTerm
    ring
  · unfold Member.omegaTerm
    rw [Dev.L52.first_rank Q s v hv]
    push_cast
    ring

end StableCount
end

theorem solution : type_of% @StableCount.chk_lemma_5_2 := @StableCount.chk_lemma_5_2
