-- Prove2me | solution 1 for PigeonholeDesign.Upper.component_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:29:14.832983+00:00
-- url     : https://prove2.me/submissions/b2c1a0b5-c16a-4d00-a275-5587d7404e43

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting
import Definitions.Def_PigeonholeDesign_Upper_Stopping
import Theorems.Thm_PigeonholeDesign_Upper_assign_balanced

open PigeonholeDesign.Upper

namespace PHUAux

section Prefix
variable {E ι : Type*} [DecidableEq ι] {T : ℕ} (hole : E → ι) (x : Fin T → E)
  (coin : Fin T → Bool)

lemma pa_length (k : ℕ) : (prefixAssign T (cellOf hole x) (coinOf coin) k).length = k := by
  induction k with
  | zero => simp [prefixAssign]
  | succ k ih => simp [prefixAssign, ih]

lemma pa_succ (k : ℕ) : ∃ v, prefixAssign T (cellOf hole x) (coinOf coin) (k + 1) =
    prefixAssign T (cellOf hole x) (coinOf coin) k ++ [v] := ⟨_, rfl⟩

lemma pa_getD (k i : ℕ) (hi : i < k) :
    (prefixAssign T (cellOf hole x) (coinOf coin) k).getD i false =
    (prefixAssign T (cellOf hole x) (coinOf coin) (i + 1)).getD i false := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · rw [← ih h]
      obtain ⟨v, hv⟩ := pa_succ hole x coin k
      rw [hv, List.getD_append _ _ _ _ (by rw [pa_length]; exact h)]
    · subst h; rfl

lemma pa_last (n : ℕ) (h : n < T) :
    prefixAssign T (cellOf hole x) (coinOf coin) (n + 1) =
    prefixAssign T (cellOf hole x) (coinOf coin) n ++ [assign hole x coin ⟨n, h⟩] := by
  obtain ⟨v, hv⟩ := pa_succ hole x coin n
  rw [hv]
  congr 2
  unfold assign
  simp only
  rw [pa_getD hole x coin T n h, hv, List.getD_append_right _ _ _ _ (by rw [pa_length])]
  simp [pa_length]

lemma assign_eq (n : ℕ) (h : n < T) :
    assign hole x coin ⟨n, h⟩ =
      (let L := prefixAssign T (cellOf hole x) (coinOf coin) n
       let a0 := ((List.range n).zip L).countP
          (fun sb => cellOf hole x sb.1 = cellOf hole x n ∧ sb.2 = false)
       let a1 := ((List.range n).zip L).countP
          (fun sb => cellOf hole x sb.1 = cellOf hole x n ∧ sb.2 = true)
       if L.count false = T / 2 then true
          else if L.count true = T / 2 then false
          else if a0 < a1 then false
          else if a1 < a0 then true
          else coinOf coin n) := by
  have h1 := pa_last hole x coin n h
  have h2 : prefixAssign T (cellOf hole x) (coinOf coin) (n + 1) =
      prefixAssign T (cellOf hole x) (coinOf coin) n ++ [(let L := prefixAssign T (cellOf hole x) (coinOf coin) n
       let a0 := ((List.range n).zip L).countP
          (fun sb => cellOf hole x sb.1 = cellOf hole x n ∧ sb.2 = false)
       let a1 := ((List.range n).zip L).countP
          (fun sb => cellOf hole x sb.1 = cellOf hole x n ∧ sb.2 = true)
       if L.count false = T / 2 then true
          else if L.count true = T / 2 then false
          else if a0 < a1 then false
          else if a1 < a0 then true
          else coinOf coin n)] := rfl
  rw [h1] at h2
  simpa using h2


lemma card_lt_succ {T : ℕ} (P : Fin T → Prop) [DecidablePred P] (n : ℕ) (h : n < T) :
    (Finset.univ.filter (fun t : Fin T => (t : ℕ) < n + 1 ∧ P t)).card =
      (Finset.univ.filter (fun t : Fin T => (t : ℕ) < n ∧ P t)).card +
        if P ⟨n, h⟩ then 1 else 0 := by
  by_cases hP : P ⟨n, h⟩
  · rw [if_pos hP, ← Finset.card_insert_of_notMem (s := Finset.univ.filter
      (fun t : Fin T => (t : ℕ) < n ∧ P t)) (a := ⟨n, h⟩) (by simp)]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h3 | h3
      · exact Or.inr ⟨h3, h2⟩
      · left; exact Fin.ext h3
    · rintro (h1 | ⟨h1, h2⟩)
      · subst h1; exact ⟨by simp, hP⟩
      · exact ⟨by omega, h2⟩
  · rw [if_neg hP, add_zero]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h3 | h3
      · exact ⟨h3, h2⟩
      · have ht : t = ⟨n, h⟩ := Fin.ext h3
        exact absurd (ht ▸ h2) hP
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

lemma pa_count (b : Bool) (n : ℕ) (hn : n ≤ T) :
    (prefixAssign T (cellOf hole x) (coinOf coin) n).count b =
      (Finset.univ.filter (fun t : Fin T => (t : ℕ) < n ∧ assign hole x coin t = b)).card := by
  induction n with
  | zero => simp [prefixAssign]
  | succ n ih =>
    have h : n < T := by omega
    rw [pa_last hole x coin n h, List.count_append, ih (by omega),
      card_lt_succ (fun t => assign hole x coin t = b) n h]
    simp [List.count_singleton, beq_iff_eq]

lemma pa_countP (v : Option ι) (b : Bool) (n : ℕ) (hn : n ≤ T) :
    ((List.range n).zip (prefixAssign T (cellOf hole x) (coinOf coin) n)).countP
        (fun sb => cellOf hole x sb.1 = v ∧ sb.2 = b) =
      (Finset.univ.filter (fun t : Fin T => (t : ℕ) < n ∧
        (some (hole (x t)) = v ∧ assign hole x coin t = b))).card := by
  induction n with
  | zero => simp [prefixAssign]
  | succ n ih =>
    have h : n < T := by omega
    rw [pa_last hole x coin n h, List.range_succ,
      List.zip_append (by rw [List.length_range, pa_length]), List.countP_append, ih (by omega),
      card_lt_succ (fun t => some (hole (x t)) = v ∧ assign hole x coin t = b) n h]
    simp [cellOf, h]

end Prefix

/-- number of control/treated subjects among the first `n` -/
def nCtrl {T : ℕ} (w : Fin T → Bool) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun t : Fin T => (t : ℕ) < n ∧ w t = false)).card

def nTrt {T : ℕ} (w : Fin T → Bool) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun t : Fin T => (t : ℕ) < n ∧ w t = true)).card

section Inv
variable {ι : Type*} [DecidableEq ι] {T : ℕ} (cell : Fin T → ι) (w : Fin T → Bool) (τ : ℕ)

def matchedG : Finset (Fin T) :=
  Finset.univ.filter (fun s => (s : ℕ) < τ ∧
    (Even (Finset.univ.filter (fun s' : Fin T => (s' : ℕ) < τ ∧ cell s' = cell s)).card ∨
      ∃ s' : Fin T, s < s' ∧ (s' : ℕ) < τ ∧ cell s' = cell s))

def cnt (n : ℕ) (k : ι) (b : Bool) : ℕ :=
  (Finset.univ.filter (fun s : Fin T => (s : ℕ) < n ∧ (cell s = k ∧ w s = b))).card

def Step2 : Prop := ∀ t : Fin T, (t : ℕ) < τ →
  (cnt cell w t (cell t) false < cnt cell w t (cell t) true → w t = false) ∧
  (cnt cell w t (cell t) true < cnt cell w t (cell t) false → w t = true)

lemma inv (hτ : τ ≤ T) (hS : Step2 cell w τ) : ∀ n, n ≤ τ → ∀ k,
    cnt cell w n k false ≤ cnt cell w n k true + 1 ∧
      cnt cell w n k true ≤ cnt cell w n k false + 1 := by
  intro n
  induction n with
  | zero => intro _ k; simp [cnt]
  | succ n ih =>
    intro hn k
    have hT : n < T := lt_of_lt_of_le (by omega) hτ
    have h0 := ih (by omega) k
    have hS' := hS ⟨n, hT⟩ (by simp; omega)
    simp only [cnt] at h0 hS' ⊢
    rw [card_lt_succ _ n hT, card_lt_succ _ n hT]
    by_cases hk : cell ⟨n, hT⟩ = k
    · subst hk
      cases hw : w ⟨n, hT⟩ <;> simp [hw] at hS' ⊢ <;> omega
    · simp [hk]; omega

lemma cnt_add (n : ℕ) (k : ι) : cnt cell w n k false + cnt cell w n k true =
    (Finset.univ.filter (fun s : Fin T => (s : ℕ) < n ∧ cell s = k)).card := by
  rw [← Finset.card_filter_add_card_filter_not (fun s => w s = false)]
  simp only [cnt, Finset.filter_filter]
  congr 2 <;> ext s <;> simp [and_assoc]

lemma cell_balanced (hτ : τ ≤ T) (hS : Step2 cell w τ) (k : ι) :
    (Finset.univ.filter (fun t => t ∈ matchedG cell τ ∧ (cell t = k ∧ w t = false))).card =
    (Finset.univ.filter (fun t => t ∈ matchedG cell τ ∧ (cell t = k ∧ w t = true))).card := by
  set P := Finset.univ.filter (fun s : Fin T => (s : ℕ) < τ ∧ cell s = k) with hP
  have key : ∀ n, n ≤ τ →
      Even (Finset.univ.filter (fun s : Fin T => (s : ℕ) < n ∧ cell s = k)).card →
      cnt cell w n k false = cnt cell w n k true := by
    intro n hn he
    have h1 := inv cell w τ hτ hS n hn k
    have h2 := cnt_add cell w n k
    obtain ⟨r, hr⟩ := he
    omega
  rcases Nat.even_or_odd P.card with he | ho
  · have e : ∀ b, (Finset.univ.filter (fun t => t ∈ matchedG cell τ ∧ (cell t = k ∧ w t = b))) =
        Finset.univ.filter (fun s : Fin T => (s : ℕ) < τ ∧ (cell s = k ∧ w s = b)) := by
      intro b; ext t
      simp only [matchedG, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨h1, _⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨⟨h1, Or.inl ?_⟩, h2, h3⟩
        subst h2; exact he
    rw [e, e]; exact key _ le_rfl he
  · have hne : P.Nonempty := by
      rw [← Finset.card_pos]; obtain ⟨r, hr⟩ := ho; omega
    set ℓ := P.max' hne with hℓdef
    have hℓ : ℓ ∈ P := P.max'_mem hne
    have hℓ' : (ℓ : ℕ) < τ ∧ cell ℓ = k := by simpa [hP] using hℓ
    have e : ∀ b, (Finset.univ.filter (fun t => t ∈ matchedG cell τ ∧ (cell t = k ∧ w t = b))) =
        Finset.univ.filter (fun s : Fin T => (s : ℕ) < (ℓ : ℕ) ∧ (cell s = k ∧ w s = b)) := by
      intro b; ext t
      simp only [matchedG, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨h1, h4⟩, h2, h3⟩
        refine ⟨?_, h2, h3⟩
        rcases h4 with h4 | ⟨s', hs1, hs2, hs3⟩
        · exfalso; subst h2; exact (Nat.not_even_iff_odd.2 ho) h4
        · have hs' : s' ∈ P := by simp [hP]; exact ⟨hs2, hs3.trans h2⟩
          have := P.le_max' s' hs'
          exact lt_of_lt_of_le (Fin.lt_def.1 hs1) (Fin.le_def.1 this)
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨by omega, Or.inr ⟨ℓ, Fin.lt_def.2 h1, hℓ'.1, hℓ'.2.trans h2.symm⟩⟩, h2, h3⟩
    rw [e, e]
    apply key _ (le_of_lt hℓ'.1)
    have hPe : P = insert ℓ (Finset.univ.filter (fun s : Fin T => (s : ℕ) < ℓ ∧ cell s = k)) := by
      ext s; simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hs : s = ℓ
        · left; exact hs
        · right; refine ⟨?_, h2⟩
          have := P.le_max' s (by simp [hP]; exact ⟨h1, h2⟩)
          exact Fin.lt_def.1 (lt_of_le_of_ne this hs)
      · rintro (rfl | ⟨h1, h2⟩)
        · exact hℓ'
        · exact ⟨by omega, h2⟩
    rw [hPe, Finset.card_insert_of_notMem (by simp)] at ho
    obtain ⟨r, hr⟩ := ho; exact ⟨r, by omega⟩

lemma unmatched_injG : ∀ s : Fin T, (s : ℕ) < τ → s ∉ matchedG cell τ → ∀ s' : Fin T, (s' : ℕ) < τ →
    s' ∉ matchedG cell τ → cell s = cell s' → s = s' := by
  have key : ∀ s : Fin T, (s : ℕ) < τ → s ∉ matchedG cell τ → ∀ s' : Fin T, (s' : ℕ) < τ →
      cell s = cell s' → ¬ s < s' := by
    intro s hs hs1 s' hs' hc hlt
    apply hs1
    simp only [matchedG, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hs, Or.inr ⟨s', hlt, hs', hc.symm⟩⟩
  intro s hs hs1 s' hs' hs1' hc
  rcases lt_trichotomy s s' with h | h | h
  · exact absurd h (key s hs hs1 s' hs' hc)
  · exact h
  · exact absurd h (key s' hs' hs1' s hs hc.symm)

end Inv

lemma split_count {ι : Type*} [DecidableEq ι] {T : ℕ} (cell : Fin T → ι) (τ : ℕ) (s : Fin T)
    (hs : (s : ℕ) < τ) :
    (Finset.univ.filter (fun s' : Fin T => (s' : ℕ) < τ ∧ cell s' = cell s)).card =
    (Finset.univ.filter (fun s' : Fin T => s' < s ∧ cell s' = cell s)).card + 1 +
    (Finset.univ.filter (fun s' : Fin T => s < s' ∧ (s' : ℕ) < τ ∧ cell s' = cell s)).card := by
  rw [← Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun s' : Fin T => (s' : ℕ) < τ ∧ cell s' = cell s)) (fun s' => s' < s),
    add_assoc]
  congr 1
  · congr 1; ext t; simp only [Finset.filter_filter, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h', h⟩
    · rintro ⟨h', h⟩; exact ⟨⟨lt_trans (Fin.lt_def.1 h') hs, h⟩, h'⟩
  · rw [add_comm, ← Finset.card_insert_of_notMem (a := s)
      (s := Finset.univ.filter (fun s' : Fin T => s < s' ∧ (s' : ℕ) < τ ∧ cell s' = cell s))
      (by simp)]
    congr 1; ext t
    simp only [Finset.filter_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases eq_or_lt_of_le (not_lt.1 h3) with h | h
      · left; exact h.symm
      · right; exact ⟨h, h1, h2⟩
    · rintro (rfl | ⟨h1, h2, h3⟩)
      · exact ⟨⟨hs, rfl⟩, lt_irrefl _⟩
      · exact ⟨⟨h2, h3⟩, not_lt.2 h1.le⟩

section Upper
variable {E ι : Type*} [DecidableEq ι] {T : ℕ} (hole : E → ι) (x : Fin T → E)
  (coin : Fin T → Bool)

lemma matched_eq : matched hole x coin = matchedG (fun t => hole (x t)) (tau hole x coin) := by
  apply Finset.ext; intro s
  unfold matched matchedG
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, cellRank, cellCount]
  constructor
  · rintro ⟨hs, h⟩
    refine ⟨hs, ?_⟩
    have hc := split_count (fun t => hole (x t)) (tau hole x coin) s hs
    rw [hc] at h
    by_cases hm : 0 < (Finset.univ.filter (fun s' : Fin T => s < s' ∧
        (s' : ℕ) < tau hole x coin ∧ hole (x s') = hole (x s))).card
    · right
      obtain ⟨t, ht⟩ := Finset.card_pos.1 hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      exact ⟨t, ht⟩
    · left
      rw [hc, Nat.even_iff]
      omega
  · rintro ⟨hs, h⟩
    refine ⟨hs, ?_⟩
    have hc := split_count (fun t => hole (x t)) (tau hole x coin) s hs
    rw [hc]
    rw [hc, Nat.even_iff] at h
    rcases h with h | ⟨t, ht⟩
    · omega
    · have : 0 < (Finset.univ.filter (fun s' : Fin T => s < s' ∧
          (s' : ℕ) < tau hole x coin ∧ hole (x s') = hole (x s))).card :=
        Finset.card_pos.2 ⟨t, by simpa using ht⟩
      omega

lemma tauU_le : tau hole x coin ≤ T := by
  unfold tau
  rcases Set.eq_empty_or_nonempty {n : ℕ | 1 ≤ n ∧ n ≤ T ∧
    ((prefixAssign T (cellOf hole x) (coinOf coin) n).count false = T / 2 ∨
     (prefixAssign T (cellOf hole x) (coinOf coin) n).count true = T / 2)} with h | h
  · rw [h, Nat.sInf_empty]; omega
  · exact (Nat.sInf_mem h).2.1

lemma tauU_spec (n : ℕ) (h1 : 1 ≤ n) (h2 : n < tau hole x coin) :
    ¬ (nCtrl (assign hole x coin) n = T / 2 ∨ nTrt (assign hole x coin) n = T / 2) := by
  intro hP
  have hle := tauU_le hole x coin
  have hn : n ≤ T := by omega
  have hmem : n ∈ {n : ℕ | 1 ≤ n ∧ n ≤ T ∧
      ((prefixAssign T (cellOf hole x) (coinOf coin) n).count false = T / 2 ∨
       (prefixAssign T (cellOf hole x) (coinOf coin) n).count true = T / 2)} := by
    refine ⟨h1, hn, ?_⟩
    rw [pa_count hole x coin false n hn, pa_count hole x coin true n hn]; exact hP
  exact Nat.notMem_of_lt_sInf h2 hmem

lemma tauU_mem (hT2 : 2 ≤ T) (hTe : Even T) :
    1 ≤ tau hole x coin ∧ (nCtrl (assign hole x coin) (tau hole x coin) = T / 2 ∨
      nTrt (assign hole x coin) (tau hole x coin) = T / 2) := by
  have hbal := PigeonholeDesign.Upper.assign_balanced hTe hole x coin
  have hmem : T ∈ {n : ℕ | 1 ≤ n ∧ n ≤ T ∧
      ((prefixAssign T (cellOf hole x) (coinOf coin) n).count false = T / 2 ∨
       (prefixAssign T (cellOf hole x) (coinOf coin) n).count true = T / 2)} := by
    refine ⟨by omega, le_rfl, Or.inl ?_⟩
    rw [pa_count hole x coin false T le_rfl, ← hbal.1]
    congr 1; ext t; simp
  have h := Nat.sInf_mem ⟨T, hmem⟩
  have hle := tauU_le hole x coin
  unfold tau at hle ⊢
  refine ⟨h.1, ?_⟩
  have h3 := h.2.2
  rw [pa_count hole x coin false _ hle, pa_count hole x coin true _ hle] at h3
  exact h3

lemma step2U (hT : 2 ≤ T) :
    Step2 (fun t => hole (x t)) (assign hole x coin) (tau hole x coin) := by
  intro t ht
  have hspec : ¬ (nCtrl (assign hole x coin) t = T / 2 ∨ nTrt (assign hole x coin) t = T / 2) := by
    rcases Nat.eq_zero_or_pos (t : ℕ) with h0 | h0
    · rw [h0]; simp [nCtrl, nTrt]; omega
    · exact tauU_spec hole x coin t h0 ht
  have heq := assign_eq hole x coin t t.2
  simp only [Fin.eta] at heq
  rw [pa_count hole x coin false t (le_of_lt t.2), pa_count hole x coin true t (le_of_lt t.2),
    pa_countP hole x coin _ false t (le_of_lt t.2),
    pa_countP hole x coin _ true t (le_of_lt t.2)] at heq
  simp only [nCtrl, nTrt] at hspec
  push Not at hspec
  rw [if_neg hspec.1, if_neg hspec.2] at heq
  have hc : cellOf hole x t = some (hole (x t)) := by simp [cellOf, t.2]
  simp only [hc, Option.some.injEq] at heq
  unfold cnt
  constructor
  · intro h; rw [heq, if_pos h]
  · intro h; rw [heq, if_neg (not_lt.2 h.le), if_pos h]

end Upper

section PartA
open MeasureTheory

/-- step function `u ↦ 1[a < u]` -/
noncomputable def st (a u : ℝ) : ℝ := if a < u then 1 else 0

lemma st_nonneg (a u : ℝ) : 0 ≤ st a u := by unfold st; split_ifs <;> norm_num

lemma st_le_one (a u : ℝ) : st a u ≤ 1 := by unfold st; split_ifs <;> norm_num

lemma st_meas (a : ℝ) : Measurable (st a) := by
  unfold st
  exact Measurable.ite measurableSet_Ioi measurable_const measurable_const

lemma ii_gen (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (h : ∀ u, |f u| ≤ M) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded ?_ hf.aestronglyMeasurable (M := M)
    (Filter.Eventually.of_forall (fun u => by rw [Real.norm_eq_abs]; exact h u))
  rw [Set.uIoc]; exact measure_Ioc_lt_top.ne

lemma st_ii (c : ℝ) (a b : ℝ) : IntervalIntegrable (st c) volume a b :=
  ii_gen _ (st_meas c) 1 (fun u => by
    rw [abs_le]; exact ⟨by linarith [st_nonneg c u], st_le_one c u⟩) a b

lemma st_int (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) : ∫ u in (0 : ℝ)..1, st a u = 1 - a := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a) (st_ii a 0 a) (st_ii a a 1)]
  have h1 : ∫ u in (0 : ℝ)..a, st a u = ∫ u in (0 : ℝ)..a, (0 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    rw [Set.uIoc_of_le ha.1] at hu
    simp [st, not_lt.2 hu.2]
  have h2 : ∫ u in a..(1 : ℝ), st a u = ∫ u in a..(1 : ℝ), (1 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    rw [Set.uIoc_of_le ha.2] at hu
    simp [st, hu.1]
  rw [h1, h2]; simp

variable {T : ℕ}

/-- counting function `u ↦ #{p ∈ P : x p < u}` -/
noncomputable def Fc (x : Fin T → ℝ) (P : Finset (Fin T)) (u : ℝ) : ℝ := ∑ p ∈ P, st (x p) u

lemma Fc_meas (x : Fin T → ℝ) (P : Finset (Fin T)) : Measurable (Fc x P) := by
  unfold Fc
  exact Finset.measurable_sum _ (fun p _ => st_meas _)

lemma Fc_nonneg (x : Fin T → ℝ) (P : Finset (Fin T)) (u : ℝ) : 0 ≤ Fc x P u :=
  Finset.sum_nonneg (fun p _ => st_nonneg _ _)

lemma Fc_le (x : Fin T → ℝ) (P : Finset (Fin T)) (u : ℝ) : Fc x P u ≤ T := by
  unfold Fc
  calc ∑ p ∈ P, st (x p) u ≤ ∑ p ∈ P, (1 : ℝ) := Finset.sum_le_sum (fun p _ => st_le_one _ _)
    _ = P.card := by simp
    _ ≤ T := by
      have := Finset.card_le_univ P
      simp only [Fintype.card_fin] at this
      exact_mod_cast this

lemma absFc_ii (x : Fin T → ℝ) (P Q : Finset (Fin T)) (a b : ℝ) :
    IntervalIntegrable (fun u => |Fc x P u - Fc x Q u|) volume a b :=
  ii_gen _ ((Fc_meas x P).sub (Fc_meas x Q)).abs (2 * T) (fun u => by
    simp only [abs_abs, Pi.sub_apply]
    rw [abs_le]
    have := Fc_nonneg x P u; have := Fc_nonneg x Q u
    have := Fc_le x P u; have := Fc_le x Q u
    constructor <;> linarith) a b

lemma Fc_zero (x : Fin T → ℝ) (P : Finset (Fin T)) (u : ℝ) (h : ∀ p ∈ P, u ≤ x p) :
    Fc x P u = 0 :=
  Finset.sum_eq_zero (fun p hp => by simp [st, not_lt.2 (h p hp)])

/-- one step of the greedy (sorted) matching -/
lemma match_step (x : Fin T → ℝ) (hx : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1) (n : ℕ)
    (IH : ∀ P Q : Finset (Fin T), P.card = n → Q.card = n → ∃ f g : Fin T → Fin T,
      (∀ p ∈ P, f p ∈ Q) ∧ (∀ q ∈ Q, g q ∈ P) ∧ (∀ p ∈ P, g (f p) = p) ∧ (∀ q ∈ Q, f (g q) = q) ∧
      ∑ p ∈ P, |x p - x (f p)| ≤ ∫ u in (0 : ℝ)..1, |Fc x P u - Fc x Q u|)
    (P Q : Finset (Fin T)) (hP : P.card = n + 1) (hQ : Q.card = n + 1) (m : Fin T) (hm : m ∈ P)
    (hmin : ∀ t ∈ P ∪ Q, x m ≤ x t) : ∃ f g : Fin T → Fin T,
      (∀ p ∈ P, f p ∈ Q) ∧ (∀ q ∈ Q, g q ∈ P) ∧ (∀ p ∈ P, g (f p) = p) ∧ (∀ q ∈ Q, f (g q) = q) ∧
      ∑ p ∈ P, |x p - x (f p)| ≤ ∫ u in (0 : ℝ)..1, |Fc x P u - Fc x Q u| := by
  have hQne : Q.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨b, hb, hbmin⟩ := Finset.exists_min_image Q x hQne
  obtain ⟨f', g', hf'1, hg'1, hfg', hgf', hsum'⟩ :=
    IH (P.erase m) (Q.erase b) (by rw [Finset.card_erase_of_mem hm]; omega)
      (by rw [Finset.card_erase_of_mem hb]; omega)
  have hmb : x m ≤ x b := hmin b (Finset.mem_union_right _ hb)
  refine ⟨Function.update f' m b, Function.update g' b m, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    by_cases h : p = m
    · subst h; simp [hb]
    · rw [Function.update_of_ne h]
      exact Finset.mem_of_mem_erase (hf'1 p (Finset.mem_erase.2 ⟨h, hp⟩))
  · intro q hq
    by_cases h : q = b
    · subst h; simp [hm]
    · rw [Function.update_of_ne h]
      exact Finset.mem_of_mem_erase (hg'1 q (Finset.mem_erase.2 ⟨h, hq⟩))
  · intro p hp
    by_cases h : p = m
    · subst h; simp
    · have h1 := hf'1 p (Finset.mem_erase.2 ⟨h, hp⟩)
      rw [Function.update_of_ne h, Function.update_of_ne (Finset.ne_of_mem_erase h1)]
      exact hfg' p (Finset.mem_erase.2 ⟨h, hp⟩)
  · intro q hq
    by_cases h : q = b
    · subst h; simp
    · have h1 := hg'1 q (Finset.mem_erase.2 ⟨h, hq⟩)
      rw [Function.update_of_ne h, Function.update_of_ne (Finset.ne_of_mem_erase h1)]
      exact hgf' q (Finset.mem_erase.2 ⟨h, hq⟩)
  · rw [← Finset.add_sum_erase P _ hm]
    have hs : ∑ p ∈ P.erase m, |x p - x (Function.update f' m b p)| =
        ∑ p ∈ P.erase m, |x p - x (f' p)| := by
      apply Finset.sum_congr rfl; intro p hp
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hp)]
    rw [hs, Function.update_self]
    have hpt : ∀ u, |Fc x P u - Fc x Q u| =
        |Fc x (P.erase m) u - Fc x (Q.erase b) u| + (st (x m) u - st (x b) u) := by
      intro u
      have eP : Fc x P u = st (x m) u + Fc x (P.erase m) u := by
        unfold Fc; rw [Finset.add_sum_erase P (fun p => st (x p) u) hm]
      have eQ : Fc x Q u = st (x b) u + Fc x (Q.erase b) u := by
        unfold Fc; rw [Finset.add_sum_erase Q (fun p => st (x p) u) hb]
      rw [eP, eQ]
      by_cases h1 : u ≤ x m
      · have z1 : Fc x (P.erase m) u = 0 := Fc_zero x _ u (fun p hp =>
          h1.trans (hmin p (Finset.mem_union_left _ (Finset.mem_of_mem_erase hp))))
        have z2 : Fc x (Q.erase b) u = 0 := Fc_zero x _ u (fun p hp =>
          h1.trans (hmin p (Finset.mem_union_right _ (Finset.mem_of_mem_erase hp))))
        rw [z1, z2]; simp [st, not_lt.2 h1, not_lt.2 (h1.trans hmb)]
      · push Not at h1
        by_cases h2 : u ≤ x b
        · have z2 : Fc x (Q.erase b) u = 0 := Fc_zero x _ u (fun p hp =>
            h2.trans (hbmin p (Finset.mem_of_mem_erase hp)))
          have := Fc_nonneg x (P.erase m) u
          rw [z2]; simp only [st, if_pos h1, if_neg (not_lt.2 h2)]
          rw [show (1 : ℝ) + Fc x (P.erase m) u - (0 + 0) = Fc x (P.erase m) u + 1 by ring,
            show Fc x (P.erase m) u - 0 = Fc x (P.erase m) u by ring,
            abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          ring
        · push Not at h2
          simp only [st, if_pos h1, if_pos h2]
          rw [show (1 : ℝ) + Fc x (P.erase m) u - (1 + Fc x (Q.erase b) u) =
            Fc x (P.erase m) u - Fc x (Q.erase b) u by ring]
          ring
    have hA : ∫ u in (0 : ℝ)..1, |Fc x P u - Fc x Q u| =
        ∫ u in (0 : ℝ)..1, (|Fc x (P.erase m) u - Fc x (Q.erase b) u| +
          (st (x m) u - st (x b) u)) :=
      intervalIntegral.integral_congr (fun u _ => hpt u)
    have hB : ∫ u in (0 : ℝ)..1, (|Fc x (P.erase m) u - Fc x (Q.erase b) u| +
          (st (x m) u - st (x b) u)) =
        (∫ u in (0 : ℝ)..1, |Fc x (P.erase m) u - Fc x (Q.erase b) u|) +
          ∫ u in (0 : ℝ)..1, (st (x m) u - st (x b) u) :=
      intervalIntegral.integral_add (absFc_ii x _ _ 0 1) ((st_ii _ 0 1).sub (st_ii _ 0 1))
    have hC : ∫ u in (0 : ℝ)..1, (st (x m) u - st (x b) u) =
        (∫ u in (0 : ℝ)..1, st (x m) u) - ∫ u in (0 : ℝ)..1, st (x b) u :=
      intervalIntegral.integral_sub (st_ii _ 0 1) (st_ii _ 0 1)
    have hint : ∫ u in (0 : ℝ)..1, |Fc x P u - Fc x Q u| =
        (∫ u in (0 : ℝ)..1, |Fc x (P.erase m) u - Fc x (Q.erase b) u|) + (x b - x m) := by
      rw [hA, hB, hC, st_int _ (hx m), st_int _ (hx b)]; ring
    rw [hint, abs_of_nonpos (by linarith)]
    linarith

lemma match_int (x : Fin T → ℝ) (hx : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1) : ∀ n : ℕ,
    ∀ P Q : Finset (Fin T), P.card = n → Q.card = n → ∃ f g : Fin T → Fin T,
      (∀ p ∈ P, f p ∈ Q) ∧ (∀ q ∈ Q, g q ∈ P) ∧ (∀ p ∈ P, g (f p) = p) ∧ (∀ q ∈ Q, f (g q) = q) ∧
      ∑ p ∈ P, |x p - x (f p)| ≤ ∫ u in (0 : ℝ)..1, |Fc x P u - Fc x Q u| := by
  intro n
  induction n with
  | zero =>
    intro P Q hP hQ
    rw [Finset.card_eq_zero] at hP hQ
    subst hP; subst hQ
    refine ⟨id, id, by simp, by simp, by simp, by simp, ?_⟩
    simp [Fc]
  | succ n ih =>
    intro P Q hP hQ
    have hne : (P ∪ Q).Nonempty := by
      rw [← Finset.card_pos]; have := Finset.card_le_card (Finset.subset_union_left (s₁ := P) (s₂ := Q)); omega
    obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (P ∪ Q) x hne
    rcases Finset.mem_union.1 hm with hmP | hmQ
    · exact match_step x hx n ih P Q hP hQ m hmP hmin
    · obtain ⟨f, g, h1, h2, h3, h4, h5⟩ := match_step x hx n ih Q P hQ hP m hmQ
        (fun t ht => hmin t (by rw [Finset.union_comm]; exact ht))
      refine ⟨g, f, h2, h1, h4, h3, ?_⟩
      have e1 : ∑ p ∈ P, |x p - x (g p)| = ∑ q ∈ Q, |x q - x (f q)| := by
        apply Finset.sum_nbij' g f h2 h1 h4 h3
        intro p hp; rw [h4 p hp, abs_sub_comm]
      have e2 : (fun u => |Fc x P u - Fc x Q u|) = fun u => |Fc x Q u - Fc x P u| :=
        funext (fun u => abs_sub_comm _ _)
      rw [e1, e2]; exact h5

end PartA

lemma discOn_le_int {T : ℕ} (x : Fin T → ℝ) (hx : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1)
    (w : Fin T → Bool) (S : Finset (Fin T))
    (hcard : (S.filter (fun t => w t = false)).card = (S.filter (fun t => w t = true)).card) :
    discrepancyOn x w S ≤ ∫ u in (0 : ℝ)..1,
      |Fc x (S.filter (fun t => w t = false)) u - Fc x (S.filter (fun t => w t = true)) u| := by
  obtain ⟨f, g, hf, hg, hfg, hgf, hsum⟩ := match_int x hx _ (S.filter (fun t => w t = false))
    (S.filter (fun t => w t = true)) rfl hcard.symm
  have mf : ∀ a : {t // t ∈ S ∧ w t = false}, f a.1 ∈ S ∧ w (f a.1) = true := fun a =>
    Finset.mem_filter.1 (hf a.1 (Finset.mem_filter.2 a.2))
  have mg : ∀ b : {t // t ∈ S ∧ w t = true}, g b.1 ∈ S ∧ w (g b.1) = false := fun b =>
    Finset.mem_filter.1 (hg b.1 (Finset.mem_filter.2 b.2))
  let e : {t // t ∈ S ∧ w t = false} ≃ {t // t ∈ S ∧ w t = true} :=
    { toFun := fun a => ⟨f a.1, mf a⟩
      invFun := fun b => ⟨g b.1, mg b⟩
      left_inv := fun a => Subtype.ext (hfg a.1 (Finset.mem_filter.2 a.2))
      right_inv := fun b => Subtype.ext (hgf b.1 (Finset.mem_filter.2 b.2)) }
  have hle : discrepancyOn x w S ≤ ∑ a : {t // t ∈ S ∧ w t = false}, dist (x a) (x (e a)) :=
    ciInf_le ⟨0, by rintro _ ⟨e', rfl⟩; exact Finset.sum_nonneg (fun _ _ => dist_nonneg)⟩ e
  refine hle.trans (le_of_eq_of_le ?_ hsum)
  rw [Finset.sum_subtype (S.filter (fun t => w t = false)) (p := fun t => t ∈ S ∧ w t = false)
    (fun t => by simp)]
  rfl

section PB
variable {ι : Type*} [DecidableEq ι] {T : ℕ} (hole : ℝ → ι) (x : Fin T → ℝ)

def nxtSet (s : Fin T) : Finset (Fin T) :=
  Finset.univ.filter (fun s' => s < s' ∧ hole (x s') = hole (x s))

def prvSet (s : Fin T) : Finset (Fin T) :=
  Finset.univ.filter (fun s' => s' < s ∧ hole (x s') = hole (x s))

lemma cellRank_eq (s : Fin T) : cellRank hole x s = (prvSet hole x s).card := rfl

/-- openers: subjects of even rank in their pigeonhole that have a successor there -/
def Op : Finset (Fin T) :=
  Finset.univ.filter (fun p => Even (cellRank hole x p) ∧ (nxtSet hole x p).Nonempty)

noncomputable def nx (p : Fin T) : Fin T :=
  if h : (nxtSet hole x p).Nonempty then (nxtSet hole x p).min' h else p

lemma nx_spec (p : Fin T) (h : (nxtSet hole x p).Nonempty) :
    p < nx hole x p ∧ hole (x (nx hole x p)) = hole (x p) ∧
      ∀ s, p < s → hole (x s) = hole (x p) → nx hole x p ≤ s := by
  have hm := Finset.min'_mem _ h
  simp only [nxtSet, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  unfold nx; rw [dif_pos h]
  refine ⟨hm.1, hm.2, fun s hs1 hs2 => Finset.min'_le _ _ ?_⟩
  simp [nxtSet, hs1, hs2]

lemma prv_nx (p : Fin T) (h : (nxtSet hole x p).Nonempty) :
    prvSet hole x (nx hole x p) = insert p (prvSet hole x p) := by
  obtain ⟨h1, h2, h3⟩ := nx_spec hole x p h
  ext s
  simp only [prvSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, h2]
  constructor
  · rintro ⟨hs1, hs2⟩
    rcases lt_trichotomy s p with hl | hl | hl
    · exact Or.inr ⟨hl, hs2⟩
    · exact Or.inl hl
    · exact absurd (h3 s hl hs2) (not_le.2 hs1)
  · rintro (rfl | ⟨hs1, hs2⟩)
    · exact ⟨h1, rfl⟩
    · exact ⟨hs1.trans h1, hs2⟩

lemma rank_nx (p : Fin T) (h : (nxtSet hole x p).Nonempty) :
    cellRank hole x (nx hole x p) = cellRank hole x p + 1 := by
  rw [cellRank_eq, cellRank_eq, prv_nx hole x p h, Finset.card_insert_of_notMem]
  simp [prvSet]

lemma nx_inj (p p' : Fin T) (hp : (nxtSet hole x p).Nonempty) (hp' : (nxtSet hole x p').Nonempty)
    (he : nx hole x p = nx hole x p') : p = p' := by
  have a1 : p' ∈ prvSet hole x (nx hole x p) := by
    rw [he, prv_nx hole x p' hp']; simp
  have a2 : p ∈ prvSet hole x (nx hole x p') := by
    rw [← he, prv_nx hole x p hp]; simp
  rw [prv_nx hole x p hp] at a1
  rw [prv_nx hole x p' hp'] at a2
  simp only [prvSet, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at a1 a2
  rcases a1 with h | ⟨h, _⟩
  · exact h.symm
  · rcases a2 with h' | ⟨h', _⟩
    · exact h'
    · exact absurd (h.trans h') (lt_irrefl _)

/-- `matched` for an arbitrary cut-off `τ` -/
def matchedT (τ : ℕ) : Finset (Fin T) :=
  Finset.univ.filter (fun s : Fin T => (s : ℕ) < τ ∧
    cellRank hole x s < 2 * (cellCount hole x τ s / 2))

lemma count_ge (τ : ℕ) (s q : Fin T) (hq : (q : ℕ) < τ) (hc : hole (x q) = hole (x s)) :
    cellRank hole x q + 1 ≤ cellCount hole x τ s := by
  rw [cellRank_eq, ← Finset.card_insert_of_notMem (s := prvSet hole x q) (a := q) (by simp [prvSet])]
  apply Finset.card_le_card
  intro t ht
  simp only [prvSet, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases ht with rfl | ⟨h1, h2⟩
  · exact ⟨hq, hc⟩
  · exact ⟨lt_trans (Fin.lt_def.1 h1) hq, h2.trans hc⟩

lemma mem_matchedT (τ : ℕ) (s : Fin T) : s ∈ matchedT hole x τ ↔
    (s ∈ Op hole x ∧ (nx hole x s : ℕ) < τ) ∨
      (∃ p ∈ Op hole x, nx hole x p = s ∧ (s : ℕ) < τ) := by
  simp only [matchedT, Op, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hs, hr⟩
    rcases Nat.even_or_odd (cellRank hole x s) with he | ho
    · left
      have hc := split_count (fun t => hole (x t)) τ s hs
      have hc' : cellCount hole x τ s = cellRank hole x s + 1 +
          (Finset.univ.filter (fun s' : Fin T => s < s' ∧ (s' : ℕ) < τ ∧
            hole (x s') = hole (x s))).card := hc
      obtain ⟨r, hr'⟩ := he
      have hpos : 0 < (Finset.univ.filter (fun s' : Fin T => s < s' ∧ (s' : ℕ) < τ ∧
            hole (x s') = hole (x s))).card := by
        rw [hc'] at hr; omega
      obtain ⟨t, ht⟩ := Finset.card_pos.1 hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      have hne : (nxtSet hole x s).Nonempty := ⟨t, by simp [nxtSet, ht.1, ht.2.2]⟩
      refine ⟨⟨⟨r, hr'⟩, hne⟩, ?_⟩
      have := (nx_spec hole x s hne).2.2 t ht.1 ht.2.2
      exact lt_of_le_of_lt (Fin.le_def.1 this) ht.2.1
    · right
      have hne : (prvSet hole x s).Nonempty := by
        rw [← Finset.card_pos, ← cellRank_eq]; obtain ⟨r, hr'⟩ := ho; omega
      set p := (prvSet hole x s).max' hne with hpdef
      have hp := Finset.max'_mem _ hne
      rw [← hpdef] at hp
      simp only [prvSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hpn : (nxtSet hole x p).Nonempty := ⟨s, by simp [nxtSet, hp.1, hp.2]⟩
      obtain ⟨n1, n2, n3⟩ := nx_spec hole x p hpn
      have hnx : nx hole x p = s := by
        apply le_antisymm (n3 s hp.1 hp.2.symm)
        by_contra hlt
        push Not at hlt
        have : nx hole x p ∈ prvSet hole x s := by
          simp [prvSet, hlt, n2, hp.2]
        have := (prvSet hole x s).le_max' _ this
        rw [← hpdef] at this
        exact absurd n1 (not_lt.2 this)
      have hr2 := rank_nx hole x p hpn
      rw [hnx] at hr2
      refine ⟨p, ⟨?_, hpn⟩, hnx, hs⟩
      rw [hr2] at ho
      obtain ⟨r, hr'⟩ := ho
      exact ⟨r, by omega⟩
  · rintro (⟨⟨he, hne⟩, hlt⟩ | ⟨p, ⟨he, hne⟩, rfl, hlt⟩)
    · obtain ⟨n1, n2, _⟩ := nx_spec hole x s hne
      refine ⟨lt_trans (Fin.lt_def.1 n1) hlt, ?_⟩
      have h1 := count_ge hole x τ s (nx hole x s) hlt n2
      rw [rank_nx hole x s hne] at h1
      obtain ⟨r, hr⟩ := he
      omega
    · obtain ⟨n1, n2, _⟩ := nx_spec hole x p hne
      refine ⟨hlt, ?_⟩
      have h1 := count_ge hole x τ (nx hole x p) (nx hole x p) hlt rfl
      rw [rank_nx hole x p hne] at h1 ⊢
      obtain ⟨r, hr⟩ := he
      omega

lemma matchedT_eq (τ : ℕ) : matchedT hole x τ =
    ((Op hole x).filter (fun p => (nx hole x p : ℕ) < τ)) ∪
      ((Op hole x).filter (fun p => (nx hole x p : ℕ) < τ)).image (nx hole x) := by
  ext s
  rw [mem_matchedT, Finset.mem_union, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro (h | ⟨p, hp, rfl, hlt⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p, Finset.mem_filter.2 ⟨hp, hlt⟩, rfl⟩
  · rintro (h | ⟨p, hp, rfl⟩)
    · exact Or.inl h
    · rw [Finset.mem_filter] at hp
      exact Or.inr ⟨p, hp.1, rfl, hp.2⟩

lemma op_ne (p : Fin T) (hp : p ∈ Op hole x) : (nxtSet hole x p).Nonempty := by
  simp only [Op, Finset.mem_filter, Finset.mem_univ, true_and] at hp; exact hp.2

lemma op_even (p : Fin T) (hp : p ∈ Op hole x) : Even (cellRank hole x p) := by
  simp only [Op, Finset.mem_filter, Finset.mem_univ, true_and] at hp; exact hp.1

lemma sum_matchedT {M : Type*} [AddCommMonoid M] (τ : ℕ) (g : Fin T → M) :
    ∑ s ∈ matchedT hole x τ, g s =
      ∑ p ∈ (Op hole x).filter (fun p => (nx hole x p : ℕ) < τ), (g p + g (nx hole x p)) := by
  rw [matchedT_eq, Finset.sum_union, Finset.sum_image, Finset.sum_add_distrib]
  · intro p hp p' hp' he
    exact nx_inj hole x p p' (op_ne hole x p (Finset.mem_filter.1 hp).1)
      (op_ne hole x p' (Finset.mem_filter.1 hp').1) he
  · rw [Finset.disjoint_left]
    intro s hs hs'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hs'
    have h1 := op_even hole x _ (Finset.mem_filter.1 hs).1
    have h2 := op_even hole x p (Finset.mem_filter.1 hp).1
    rw [rank_nx hole x p (op_ne hole x p (Finset.mem_filter.1 hp).1)] at h1
    obtain ⟨r, hr⟩ := h1; obtain ⟨r', hr'⟩ := h2; omega

end PB

section PC
variable {ι : Type*} [DecidableEq ι] {T : ℕ} (hole : ℝ → ι) (x : Fin T → ℝ)

lemma cnt_prv (w : Fin T → Bool) (s : Fin T) (b : Bool) :
    cnt (fun t => hole (x t)) w s (hole (x s)) b = ((prvSet hole x s).filter (fun t => w t = b)).card := by
  unfold cnt prvSet
  rw [Finset.filter_filter]
  congr 1; ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨Fin.lt_def.2 h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨Fin.lt_def.1 h1, h2, h3⟩

lemma pa_congr (c c' : Fin T → Bool) (n : ℕ) (h : ∀ i : ℕ, i < n → coinOf c i = coinOf c' i) :
    prefixAssign T (cellOf hole x) (coinOf c) n = prefixAssign T (cellOf hole x) (coinOf c') n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixAssign, prefixAssign, ih (fun i hi => h i (by omega)), h n (by omega)]

lemma T_mem (hT2 : 2 ≤ T) (hTe : Even T) (c : Fin T → Bool) :
    T ∈ {n : ℕ | 1 ≤ n ∧ n ≤ T ∧
      ((prefixAssign T (cellOf hole x) (coinOf c) n).count false = T / 2 ∨
       (prefixAssign T (cellOf hole x) (coinOf c) n).count true = T / 2)} := by
  have hbal := PigeonholeDesign.Upper.assign_balanced hTe hole x c
  refine ⟨by omega, le_rfl, Or.inl ?_⟩
  rw [pa_count hole x c false T le_rfl, ← hbal.1]
  congr 1; ext t; simp

lemma lt_tau_iff (hT2 : 2 ≤ T) (hTe : Even T) (c : Fin T → Bool) (s : ℕ) :
    s < tau hole x c ↔ ∀ n, 1 ≤ n → n ≤ s →
      ¬ ((prefixAssign T (cellOf hole x) (coinOf c) n).count false = T / 2 ∨
       (prefixAssign T (cellOf hole x) (coinOf c) n).count true = T / 2) := by
  have hmem := T_mem hole x hT2 hTe c
  have hτ := Nat.sInf_mem ⟨T, hmem⟩
  unfold tau
  constructor
  · intro h n h1 h2 hf
    have : sInf {n : ℕ | 1 ≤ n ∧ n ≤ T ∧
      ((prefixAssign T (cellOf hole x) (coinOf c) n).count false = T / 2 ∨
       (prefixAssign T (cellOf hole x) (coinOf c) n).count true = T / 2)} ≤ n :=
      Nat.sInf_le ⟨h1, le_trans h2 (le_trans h.le hτ.2.1), hf⟩
    omega
  · intro h
    by_contra hc
    push Not at hc
    exact h _ hτ.1 hc hτ.2.2

lemma tau_congr (hT2 : 2 ≤ T) (hTe : Even T) (c c' : Fin T → Bool) (s : ℕ)
    (h : ∀ i : Fin T, (i : ℕ) < s → c i = c' i) :
    s < tau hole x c ↔ s < tau hole x c' := by
  rw [lt_tau_iff hole x hT2 hTe c, lt_tau_iff hole x hT2 hTe c']
  have key : ∀ n, n ≤ s → prefixAssign T (cellOf hole x) (coinOf c) n =
      prefixAssign T (cellOf hole x) (coinOf c') n := by
    intro n hn
    apply pa_congr
    intro i hi
    unfold coinOf
    split_ifs with hiT
    · exact h ⟨i, hiT⟩ (by simp; omega)
    · rfl
  constructor
  · intro H n h1 h2; rw [← key n h2]; exact H n h1 h2
  · intro H n h1 h2; rw [key n h2]; exact H n h1 h2

variable (coin : Fin T → Bool)

lemma assign_coin (hT2 : 2 ≤ T) (t : Fin T) (ht : (t : ℕ) < tau hole x coin)
    (hbal : cnt (fun t => hole (x t)) (assign hole x coin) t (hole (x t)) false =
      cnt (fun t => hole (x t)) (assign hole x coin) t (hole (x t)) true) :
    assign hole x coin t = coin t := by
  have hspec : ¬ (nCtrl (assign hole x coin) t = T / 2 ∨ nTrt (assign hole x coin) t = T / 2) := by
    rcases Nat.eq_zero_or_pos (t : ℕ) with h0 | h0
    · rw [h0]; simp [nCtrl, nTrt]; omega
    · exact tauU_spec hole x coin t h0 ht
  have heq := assign_eq hole x coin t t.2
  simp only [Fin.eta] at heq
  rw [pa_count hole x coin false t (le_of_lt t.2), pa_count hole x coin true t (le_of_lt t.2),
    pa_countP hole x coin _ false t (le_of_lt t.2),
    pa_countP hole x coin _ true t (le_of_lt t.2)] at heq
  simp only [nCtrl, nTrt] at hspec
  push Not at hspec
  rw [if_neg hspec.1, if_neg hspec.2] at heq
  have hc : cellOf hole x t = some (hole (x t)) := by simp [cellOf, t.2]
  simp only [hc, Option.some.injEq] at heq
  unfold cnt at hbal
  simp only at hbal
  rw [heq, if_neg (by omega), if_neg (by omega)]
  simp [coinOf, t.2]

lemma op_balanced (hT2 : 2 ≤ T) (p : Fin T) (hp : p ∈ Op hole x) (hpt : (p : ℕ) < tau hole x coin) :
    cnt (fun t => hole (x t)) (assign hole x coin) p (hole (x p)) false =
      cnt (fun t => hole (x t)) (assign hole x coin) p (hole (x p)) true := by
  have h1 := inv (fun t => hole (x t)) (assign hole x coin) (tau hole x coin)
    (tauU_le hole x coin) (step2U hole x coin hT2) p (le_of_lt hpt) (hole (x p))
  have h2 := cnt_add (fun t => hole (x t)) (assign hole x coin) p (hole (x p))
  have h3 : (Finset.univ.filter (fun s : Fin T => (s : ℕ) < (p : ℕ) ∧ hole (x s) = hole (x p))).card =
      cellRank hole x p := by
    unfold cellRank; congr 1
  have he := op_even hole x p hp
  rw [h3] at h2
  obtain ⟨r, hr⟩ := he
  omega

lemma cnt_nx (p : Fin T) (hp : p ∈ Op hole x) (w : Fin T → Bool) (b : Bool) :
    cnt (fun t => hole (x t)) w (nx hole x p) (hole (x (nx hole x p))) b =
      cnt (fun t => hole (x t)) w p (hole (x p)) b + if w p = b then 1 else 0 := by
  rw [cnt_prv, cnt_prv, prv_nx hole x p (op_ne hole x p hp), Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [prvSet])]
  · rfl

lemma assign_nx (hT2 : 2 ≤ T) (p : Fin T) (hp : p ∈ Op hole x)
    (hq : (nx hole x p : ℕ) < tau hole x coin) :
    assign hole x coin (nx hole x p) = !assign hole x coin p := by
  have hne := op_ne hole x p hp
  obtain ⟨n1, n2, _⟩ := nx_spec hole x p hne
  have hpt : (p : ℕ) < tau hole x coin := lt_trans (Fin.lt_def.1 n1) hq
  have hb := op_balanced hole x coin hT2 p hp hpt
  have hS := step2U hole x coin hT2 (nx hole x p) hq
  have c0 := cnt_nx hole x p hp (assign hole x coin) false
  have c1 := cnt_nx hole x p hp (assign hole x coin) true
  simp only at hS
  cases hw : assign hole x coin p
  · rw [hw] at c0 c1; simp at c0 c1
    exact hS.2 (by omega)
  · rw [hw] at c0 c1; simp at c0 c1
    exact hS.1 (by omega)

end PC

section PD
variable {ι : Type*} [DecidableEq ι] {T : ℕ} (hole : ℝ → ι) (x : Fin T → ℝ)

def sgn (b : Bool) : ℝ := if b = false then 1 else -1

lemma sgn_not (b : Bool) : sgn (!b) = - sgn b := by cases b <;> simp [sgn]

lemma sgn_sq (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]

lemma abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]

noncomputable def cc (p : Fin T) (u : ℝ) : ℝ := st (x p) u - st (x (nx hole x p)) u

noncomputable def aT (c : Fin T → Bool) (p : Fin T) (u : ℝ) : ℝ :=
  if (p : ℕ) < tau hole x c then sgn (c p) * cc hole x p u else 0

def fl (j : Fin T) (c : Fin T → Bool) : Fin T → Bool := Function.update c j (!c j)

lemma fl_invol (j : Fin T) : Function.Involutive (fl j) := by
  intro c; funext i
  by_cases h : i = j
  · subst h; simp [fl]
  · simp [fl, h]

lemma cross_zero (hT2 : 2 ≤ T) (hTe : Even T) (p p' : Fin T) (hpp : p < p') (u : ℝ) :
    ∑ c : Fin T → Bool, aT hole x c p u * aT hole x c p' u = 0 := by
  have hne : p ≠ p' := ne_of_lt hpp
  have key : ∀ c : Fin T → Bool, aT hole x (fl p' c) p u * aT hole x (fl p' c) p' u =
      -(aT hole x c p u * aT hole x c p' u) := by
    intro c
    have e1 : (p : ℕ) < tau hole x (fl p' c) ↔ (p : ℕ) < tau hole x c :=
      tau_congr hole x hT2 hTe _ _ _ (fun i hi => by
        have : i ≠ p' := fun h => by subst h; exact absurd (lt_trans hi (Fin.lt_def.1 hpp)) (lt_irrefl _)
        simp [fl, this])
    have e2 : (p' : ℕ) < tau hole x (fl p' c) ↔ (p' : ℕ) < tau hole x c :=
      tau_congr hole x hT2 hTe _ _ _ (fun i hi => by
        have : i ≠ p' := fun h => by subst h; exact absurd hi (lt_irrefl _)
        simp [fl, this])
    have f1 : fl p' c p = c p := by simp [fl, hne]
    have f2 : fl p' c p' = !c p' := by simp [fl]
    simp only [aT, e1, e2, f1, f2, sgn_not]
    split_ifs <;> ring
  have hs : ∑ c : Fin T → Bool, aT hole x c p u * aT hole x c p' u =
      ∑ c : Fin T → Bool, aT hole x (fl p' c) p u * aT hole x (fl p' c) p' u :=
    (Equiv.sum_comp (Function.Involutive.toPerm _ (fl_invol p'))
      (fun c => aT hole x c p u * aT hole x c p' u)).symm
  rw [Finset.sum_congr rfl (fun c _ => key c), Finset.sum_neg_distrib] at hs
  linarith

lemma aT_sq_le (c : Fin T → Bool) (p : Fin T) (u : ℝ) :
    aT hole x c p u * aT hole x c p u ≤ cc hole x p u ^ 2 := by
  unfold aT
  split_ifs
  · rw [show sgn (c p) * cc hole x p u * (sgn (c p) * cc hole x p u) =
      (sgn (c p) * sgn (c p)) * cc hole x p u ^ 2 by ring, sgn_sq, one_mul]
  · simp; positivity

lemma sumsq (hT2 : 2 ≤ T) (hTe : Even T) (u : ℝ) :
    ∑ c : Fin T → Bool, (∑ p ∈ Op hole x, aT hole x c p u) ^ 2 ≤
      2 ^ T * ∑ p ∈ Op hole x, cc hole x p u ^ 2 := by
  calc ∑ c : Fin T → Bool, (∑ p ∈ Op hole x, aT hole x c p u) ^ 2
      = ∑ c : Fin T → Bool, ∑ p ∈ Op hole x, ∑ p' ∈ Op hole x, aT hole x c p u * aT hole x c p' u := by
        apply Finset.sum_congr rfl; intro c _
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ p ∈ Op hole x, ∑ p' ∈ Op hole x, ∑ c : Fin T → Bool, aT hole x c p u * aT hole x c p' u := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro p _
        rw [Finset.sum_comm]
    _ = ∑ p ∈ Op hole x, ∑ c : Fin T → Bool, aT hole x c p u * aT hole x c p u := by
        apply Finset.sum_congr rfl; intro p hp
        apply Finset.sum_eq_single p
        · intro p' _ hne
          rcases lt_or_gt_of_ne hne with h | h
          · rw [← cross_zero hole x hT2 hTe p' p h u]
            apply Finset.sum_congr rfl; intro c _; ring
          · exact cross_zero hole x hT2 hTe p p' h u
        · intro h; exact absurd hp h
    _ ≤ ∑ p ∈ Op hole x, ∑ c : Fin T → Bool, cc hole x p u ^ 2 := by
        apply Finset.sum_le_sum; intro p _
        apply Finset.sum_le_sum; intro c _
        exact aT_sq_le hole x c p u
    _ = 2 ^ T * ∑ p ∈ Op hole x, cc hole x p u ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro p _
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

variable (coin : Fin T → Bool)

lemma Fc_filter (S : Finset (Fin T)) (P : Fin T → Prop) [DecidablePred P] (u : ℝ) :
    Fc x (S.filter P) u = ∑ s ∈ S, if P s then st (x s) u else 0 := by
  unfold Fc; rw [Finset.sum_filter]

lemma D_eq (hT2 : 2 ≤ T) (u : ℝ) :
    Fc x ((matched hole x coin).filter (fun t => assign hole x coin t = false)) u -
      Fc x ((matched hole x coin).filter (fun t => assign hole x coin t = true)) u =
    ∑ p ∈ Op hole x, if (nx hole x p : ℕ) < tau hole x coin then sgn (coin p) * cc hole x p u
      else 0 := by
  rw [Fc_filter, Fc_filter, ← Finset.sum_sub_distrib]
  have h1 : ∀ s, ((if assign hole x coin s = false then st (x s) u else 0) -
      if assign hole x coin s = true then st (x s) u else 0) =
      sgn (assign hole x coin s) * st (x s) u := by
    intro s; cases assign hole x coin s <;> simp [sgn]
  simp only [h1]
  change ∑ s ∈ matchedT hole x (tau hole x coin), _ = _
  rw [sum_matchedT, ← Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  have hne := op_ne hole x p hp.1
  have hpt : (p : ℕ) < tau hole x coin :=
    lt_trans (Fin.lt_def.1 (nx_spec hole x p hne).1) hp.2
  rw [assign_nx hole x coin hT2 p hp.1 hp.2, sgn_not,
    assign_coin hole x coin hT2 p hpt (op_balanced hole x coin hT2 p hp.1 hpt)]
  unfold cc; ring

lemma matched_bal (hT2 : 2 ≤ T) :
    ((matched hole x coin).filter (fun t => assign hole x coin t = false)).card =
      ((matched hole x coin).filter (fun t => assign hole x coin t = true)).card := by
  rw [Finset.card_filter, Finset.card_filter]
  change ∑ s ∈ matchedT hole x (tau hole x coin), _ = ∑ s ∈ matchedT hole x (tau hole x coin), _
  rw [sum_matchedT, sum_matchedT]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  rw [assign_nx hole x coin hT2 p hp.1 hp.2]
  cases assign hole x coin p <;> simp

lemma D_le (hT2 : 2 ≤ T) (u : ℝ) :
    |Fc x ((matched hole x coin).filter (fun t => assign hole x coin t = false)) u -
      Fc x ((matched hole x coin).filter (fun t => assign hole x coin t = true)) u| ≤
    |∑ p ∈ Op hole x, aT hole x coin p u| +
      ∑ p ∈ Op hole x, if (p : ℕ) < tau hole x coin ∧ ¬ (nx hole x p : ℕ) < tau hole x coin then
        |cc hole x p u| else 0 := by
  rw [D_eq hole x coin hT2 u]
  have hsplit : (∑ p ∈ Op hole x, if (nx hole x p : ℕ) < tau hole x coin then
      sgn (coin p) * cc hole x p u else 0) =
      (∑ p ∈ Op hole x, aT hole x coin p u) - ∑ p ∈ Op hole x,
        if (p : ℕ) < tau hole x coin ∧ ¬ (nx hole x p : ℕ) < tau hole x coin then
          sgn (coin p) * cc hole x p u else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro p hp
    have hlt : (nx hole x p : ℕ) < tau hole x coin → (p : ℕ) < tau hole x coin := fun h =>
      lt_trans (Fin.lt_def.1 (nx_spec hole x p (op_ne hole x p hp)).1) h
    unfold aT
    by_cases h1 : (nx hole x p : ℕ) < tau hole x coin
    · simp [h1, hlt h1]
    · by_cases h2 : (p : ℕ) < tau hole x coin
      · simp [h1, h2]
      · simp [h1, h2]
  rw [hsplit]
  refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl; intro p _
  split_ifs
  · rw [abs_mul, abs_sgn, one_mul]
  · simp

end PD

section PE
open MeasureTheory
variable {ι : Type*} [DecidableEq ι] {T : ℕ} (hole : ℝ → ι) (x : Fin T → ℝ)

lemma cc_meas (p : Fin T) : Measurable (cc hole x p) := (st_meas _).sub (st_meas _)

lemma cc_abs_le (p : Fin T) (u : ℝ) : |cc hole x p u| ≤ 1 := by
  unfold cc
  have := st_nonneg (x p) u; have := st_le_one (x p) u
  have := st_nonneg (x (nx hole x p)) u; have := st_le_one (x (nx hole x p)) u
  rw [abs_le]; constructor <;> linarith

lemma aT_meas (c : Fin T → Bool) (p : Fin T) : Measurable (aT hole x c p) := by
  unfold aT
  by_cases h : (p : ℕ) < tau hole x c
  · simp only [h, if_true]; exact (cc_meas hole x p).const_mul _
  · simp only [h, if_false]; exact measurable_const

lemma aT_abs_le (c : Fin T → Bool) (p : Fin T) (u : ℝ) : |aT hole x c p u| ≤ 1 := by
  unfold aT
  split_ifs
  · rw [abs_mul, abs_sgn, one_mul]; exact cc_abs_le hole x p u
  · simp

lemma card_le_T (S : Finset (Fin T)) : (S.card : ℝ) ≤ T := by
  have := Finset.card_le_univ S
  simp only [Fintype.card_fin] at this
  exact_mod_cast this

lemma sum_abs_le_T (S : Finset (Fin T)) (f : Fin T → ℝ) (h : ∀ p ∈ S, |f p| ≤ 1) :
    |∑ p ∈ S, f p| ≤ T := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p ∈ S, |f p| ≤ ∑ p ∈ S, (1 : ℝ) := Finset.sum_le_sum h
    _ = S.card := by simp
    _ ≤ T := card_le_T S

noncomputable def Dp (c : Fin T → Bool) (u : ℝ) : ℝ := ∑ p ∈ Op hole x, aT hole x c p u

noncomputable def Rr (c : Fin T → Bool) (u : ℝ) : ℝ :=
  ∑ p ∈ Op hole x, if (p : ℕ) < tau hole x c ∧ ¬ (nx hole x p : ℕ) < tau hole x c then
    |cc hole x p u| else 0

lemma Dp_meas (c : Fin T → Bool) : Measurable (Dp hole x c) := by
  unfold Dp; exact Finset.measurable_sum _ (fun p _ => aT_meas hole x c p)

lemma Dp_abs_le (c : Fin T → Bool) (u : ℝ) : |Dp hole x c u| ≤ T :=
  sum_abs_le_T _ _ (fun p _ => aT_abs_le hole x c p u)

lemma Rr_meas (c : Fin T → Bool) : Measurable (Rr hole x c) := by
  unfold Rr
  refine Finset.measurable_sum _ (fun p _ => ?_)
  by_cases h : (p : ℕ) < tau hole x c ∧ ¬ (nx hole x p : ℕ) < tau hole x c
  · simp only [h, if_true]; exact (cc_meas hole x p).abs
  · simp only [h, if_false]; exact measurable_const

lemma Rr_abs_le (c : Fin T → Bool) (u : ℝ) : |Rr hole x c u| ≤ T := by
  unfold Rr
  apply sum_abs_le_T
  intro p _
  split_ifs
  · rw [abs_abs]; exact cc_abs_le hole x p u
  · simp

lemma st_diff_sq (a b u : ℝ) : (st a u - st b u) ^ 2 = |st a u - st b u| := by
  unfold st; split_ifs <;> norm_num

lemma st_diff_abs_int (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    ∫ u in (0 : ℝ)..1, |st a u - st b u| = |b - a| := by
  rcases le_total a b with hab | hab
  · have e : ∀ u, |st a u - st b u| = st a u - st b u := by
      intro u; apply abs_of_nonneg
      unfold st
      by_cases h2 : b < u
      · rw [if_pos (lt_of_le_of_lt hab h2), if_pos h2]; norm_num
      · rw [if_neg h2]; split_ifs <;> norm_num
    simp only [e]
    rw [intervalIntegral.integral_sub (st_ii _ 0 1) (st_ii _ 0 1), st_int a ha, st_int b hb,
      abs_of_nonneg (by linarith)]
    ring
  · have e : ∀ u, |st a u - st b u| = st b u - st a u := by
      intro u; rw [abs_sub_comm]; apply abs_of_nonneg
      unfold st
      by_cases h2 : a < u
      · rw [if_pos (lt_of_le_of_lt hab h2), if_pos h2]; norm_num
      · rw [if_neg h2]; split_ifs <;> norm_num
    simp only [e]
    rw [intervalIntegral.integral_sub (st_ii _ 0 1) (st_ii _ 0 1), st_int a ha, st_int b hb,
      abs_of_nonpos (by linarith)]
    ring

lemma cc_abs_int (hx : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1) (p : Fin T) :
    ∫ u in (0 : ℝ)..1, |cc hole x p u| = |x (nx hole x p) - x p| :=
  st_diff_abs_int _ _ (hx p) (hx _)

lemma cc_sq_int (hx : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1) (p : Fin T) :
    ∫ u in (0 : ℝ)..1, cc hole x p u ^ 2 = |x (nx hole x p) - x p| := by
  rw [← cc_abs_int hole x hx p]
  apply intervalIntegral.integral_congr
  intro u _
  exact st_diff_sq _ _ u

end PE

lemma cell_dist {m : ℕ} (hm : 1 ≤ m) (z z' : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hz' : z' ∈ Set.Icc (0 : ℝ) 1)
    (h : min ⌊z * m⌋₊ (m - 1) = min ⌊z' * m⌋₊ (m - 1)) : |z - z'| ≤ 1 / m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have key : ∀ y ∈ Set.Icc (0 : ℝ) 1, ((min ⌊y * m⌋₊ (m - 1) : ℕ) : ℝ) ≤ y * m ∧
      y * m ≤ ((min ⌊y * m⌋₊ (m - 1) : ℕ) : ℝ) + 1 := by
    intro y hy
    have hy0 : 0 ≤ y * m := mul_nonneg hy.1 hmpos.le
    constructor
    · calc ((min ⌊y * m⌋₊ (m - 1) : ℕ) : ℝ) ≤ (⌊y * m⌋₊ : ℝ) := by
            exact_mod_cast min_le_left _ _
        _ ≤ y * m := Nat.floor_le hy0
    · rcases le_total ⌊y * m⌋₊ (m - 1) with h1 | h1
      · rw [min_eq_left h1]; exact (Nat.lt_floor_add_one _).le
      · rw [min_eq_right h1]; push_cast [Nat.cast_sub hm]; nlinarith [hy.2]
  obtain ⟨a1, a2⟩ := key z hz
  obtain ⟨b1, b2⟩ := key z' hz'
  rw [h] at a1 a2
  rw [abs_sub_le_iff]
  constructor <;> rw [le_div_iff₀ hmpos] <;> nlinarith

lemma ii_sum {α : Type*} (S : Finset α) (f : α → ℝ → ℝ)
    (h : ∀ i ∈ S, IntervalIntegrable (f i) MeasureTheory.volume 0 1) :
    IntervalIntegrable (fun u => ∑ i ∈ S, f i u) MeasureTheory.volume 0 1 := by
  have e : (fun u => ∑ i ∈ S, f i u) = ∑ i ∈ S, f i := by
    funext u; simp [Finset.sum_apply]
  rw [e]; exact IntervalIntegrable.sum S h

lemma abs_le_quad (y L : ℝ) (hL : 0 < L) : |y| ≤ 1 / (2 * L) * y ^ 2 + L / 2 := by
  have h1 := sq_nonneg (|y| - L)
  have h2 := sq_abs y
  rw [show 1 / (2 * L) * y ^ 2 + L / 2 = (y ^ 2 + L ^ 2) / (2 * L) by field_simp,
    le_div_iff₀ (by positivity)]
  nlinarith

end PHUAux

open MeasureTheory in
open PHUAux in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η < 1 → ∀ T : ℕ, 1 ≤ T → Even T →
      ∀ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) →
        (∑ coin : Fin T → Bool,
            discrepancyOn x (assign (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin)
              (matched (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin)) / 2 ^ T
          ≤ C * (T : ℝ) ^ (1 / 2 - η / 2) := by
  refine ⟨2, by norm_num, ?_⟩
  intro η hη0 hη1 T hT1 hTe x hx
  set K := ⌈(T : ℝ) ^ η⌉₊ with hK
  set hole := uniformHole K with hhole
  have hT2 : 2 ≤ T := by obtain ⟨r, hr⟩ := hTe; omega
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
  have hpos : 0 < (T : ℝ) ^ η := by positivity
  have hK1 : 1 ≤ K := Nat.ceil_pos.2 hpos
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  have hKge : (T : ℝ) ^ η ≤ K := Nat.le_ceil _
  have hdist : ∀ s t : Fin T, hole (x s) = hole (x t) → |x s - x t| ≤ 1 / K := fun s t h =>
    cell_dist hK1 (x s) (x t) (hx s) (hx t) h
  have hnxd : ∀ p ∈ Op hole x, |x (nx hole x p) - x p| ≤ 1 / K := fun p hp =>
    hdist _ _ (nx_spec hole x p (op_ne hole x p hp)).2.1
  set L := Real.sqrt ((T : ℝ) / K) with hLdef
  have hTK : (0 : ℝ) < T / K := div_pos hTpos hKpos
  have hL : 0 < L := Real.sqrt_pos.2 hTK
  have hL2 : L ^ 2 = T / K := Real.sq_sqrt hTK.le
  -- integrability facts
  have iiDp2 : ∀ c, IntervalIntegrable (fun u => Dp hole x c u ^ 2) volume 0 1 := fun c =>
    ii_gen _ ((Dp_meas hole x c).pow_const 2) ((T : ℝ) ^ 2) (fun u => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (Dp_abs_le hole x c u) 2) 0 1
  have iiDp : ∀ c, IntervalIntegrable (fun u => |Dp hole x c u|) volume 0 1 := fun c =>
    ii_gen _ (Dp_meas hole x c).abs T (fun u => by rw [abs_abs]; exact Dp_abs_le hole x c u) 0 1
  have iiRr : ∀ c, IntervalIntegrable (Rr hole x c) volume 0 1 := fun c =>
    ii_gen _ (Rr_meas hole x c) T (Rr_abs_le hole x c) 0 1
  have iicc2 : ∀ p, IntervalIntegrable (fun u => cc hole x p u ^ 2) volume 0 1 := fun p =>
    ii_gen _ ((cc_meas hole x p).pow_const 2) 1 (fun u => by
      rw [abs_pow]
      calc |cc hole x p u| ^ 2 ≤ 1 ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (cc_abs_le hole x p u) 2
        _ = 1 := by norm_num) 0 1
  -- the boundary term
  have hR : ∀ c, ∫ u in (0 : ℝ)..1, Rr hole x c u ≤ 1 := by
    intro c
    have e1 : ∫ u in (0 : ℝ)..1, Rr hole x c u =
        ∑ p ∈ Op hole x, if ((p : ℕ) < tau hole x c ∧ ¬ (nx hole x p : ℕ) < tau hole x c) then |x (nx hole x p) - x p| else 0 := by
      unfold Rr
      rw [intervalIntegral.integral_finset_sum]
      · apply Finset.sum_congr rfl; intro p _
        by_cases hP : ((p : ℕ) < tau hole x c ∧ ¬ (nx hole x p : ℕ) < tau hole x c)
        · rw [if_pos hP, ← cc_abs_int hole x hx p]
          apply intervalIntegral.integral_congr; intro u _; simp only [if_pos hP]
        · rw [if_neg hP]
          simp only [if_neg hP]; simp
      · intro p _
        by_cases hP : ((p : ℕ) < tau hole x c ∧ ¬ (nx hole x p : ℕ) < tau hole x c)
        · simp only [if_pos hP]
          exact ii_gen _ (cc_meas hole x p).abs 1 (fun u => by
            rw [abs_abs]; exact cc_abs_le hole x p u) 0 1
        · simp only [if_neg hP]; exact intervalIntegrable_const
    have hcard : ((Op hole x).filter (fun p : Fin T => ((p : ℕ) < tau hole x c ∧ ¬ (nx hole x p : ℕ) < tau hole x c))).card ≤ K := by
      calc ((Op hole x).filter (fun p : Fin T => ((p : ℕ) < tau hole x c ∧ ¬ (nx hole x p : ℕ) < tau hole x c))).card ≤ (Finset.range K).card := by
            apply Finset.card_le_card_of_injOn (fun p => hole (x p))
            · intro p _
              simp only [Finset.coe_range, Set.mem_Iio, hhole, uniformHole]
              have := min_le_right ⌊x p * K⌋₊ (K - 1)
              omega
            · intro p hp p' hp' hpp
              simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hp'
              by_contra hne
              rcases lt_or_gt_of_ne hne with h | h
              · have := (nx_spec hole x p (op_ne hole x p hp.1)).2.2 p' h hpp.symm
                exact hp.2.2 (lt_of_le_of_lt (Fin.le_def.1 this) hp'.2.1)
              · have := (nx_spec hole x p' (op_ne hole x p' hp'.1)).2.2 p h hpp
                exact hp'.2.2 (lt_of_le_of_lt (Fin.le_def.1 this) hp.2.1)
        _ = K := Finset.card_range K
    rw [e1]
    calc ∑ p ∈ Op hole x, (if ((p : ℕ) < tau hole x c ∧ ¬ (nx hole x p : ℕ) < tau hole x c) then |x (nx hole x p) - x p| else 0)
        ≤ ∑ p ∈ Op hole x, (if ((p : ℕ) < tau hole x c ∧ ¬ (nx hole x p : ℕ) < tau hole x c) then 1 / (K : ℝ) else 0) := by
          apply Finset.sum_le_sum; intro p hp
          split_ifs
          · exact hnxd p hp
          · exact le_rfl
      _ = ((Op hole x).filter (fun p : Fin T => ((p : ℕ) < tau hole x c ∧ ¬ (nx hole x p : ℕ) < tau hole x c))).card * (1 / (K : ℝ)) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (K : ℝ) * (1 / K) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcard
      _ = 1 := by field_simp
  -- per-coin bound
  have hcoin : ∀ c, discrepancyOn x (assign hole x c) (matched hole x c) ≤
      1 / (2 * L) * (∫ u in (0 : ℝ)..1, Dp hole x c u ^ 2) + L / 2 + 1 := by
    intro c
    have h1 := discOn_le_int x hx (assign hole x c) (matched hole x c) (matched_bal hole x c hT2)
    have h2 : ∫ u in (0 : ℝ)..1, |Fc x ((matched hole x c).filter
          (fun t => assign hole x c t = false)) u -
        Fc x ((matched hole x c).filter (fun t => assign hole x c t = true)) u| ≤
        ∫ u in (0 : ℝ)..1, (|Dp hole x c u| + Rr hole x c u) :=
      intervalIntegral.integral_mono_on zero_le_one (absFc_ii x _ _ 0 1)
        ((iiDp c).add (iiRr c)) (fun u _ => D_le hole x c hT2 u)
    have h3 : ∫ u in (0 : ℝ)..1, (|Dp hole x c u| + Rr hole x c u) =
        (∫ u in (0 : ℝ)..1, |Dp hole x c u|) + ∫ u in (0 : ℝ)..1, Rr hole x c u :=
      intervalIntegral.integral_add (iiDp c) (iiRr c)
    have h4 : ∫ u in (0 : ℝ)..1, |Dp hole x c u| ≤
        ∫ u in (0 : ℝ)..1, (1 / (2 * L) * Dp hole x c u ^ 2 + L / 2) :=
      intervalIntegral.integral_mono_on zero_le_one (iiDp c)
        (((iiDp2 c).const_mul _).add intervalIntegrable_const)
        (fun u _ => abs_le_quad _ L hL)
    have h5 : ∫ u in (0 : ℝ)..1, (1 / (2 * L) * Dp hole x c u ^ 2 + L / 2) =
        1 / (2 * L) * (∫ u in (0 : ℝ)..1, Dp hole x c u ^ 2) + L / 2 := by
      rw [intervalIntegral.integral_add ((iiDp2 c).const_mul _) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp
    linarith [hR c]
  -- the second moment
  have hint : ∑ c : Fin T → Bool, ∫ u in (0 : ℝ)..1, Dp hole x c u ^ 2 ≤ 2 ^ T * (T / K) := by
    rw [← intervalIntegral.integral_finset_sum (fun c _ => iiDp2 c)]
    have hiiS : IntervalIntegrable (fun u => ∑ c : Fin T → Bool, Dp hole x c u ^ 2) volume 0 1 :=
      ii_sum _ _ (fun c _ => iiDp2 c)
    have hiiR : IntervalIntegrable (fun u => 2 ^ T * ∑ p ∈ Op hole x, cc hole x p u ^ 2)
        volume 0 1 := (ii_sum _ _ (fun p _ => iicc2 p)).const_mul _
    calc ∫ u in (0 : ℝ)..1, ∑ c : Fin T → Bool, Dp hole x c u ^ 2
        ≤ ∫ u in (0 : ℝ)..1, 2 ^ T * ∑ p ∈ Op hole x, cc hole x p u ^ 2 :=
          intervalIntegral.integral_mono_on zero_le_one hiiS hiiR
            (fun u _ => sumsq hole x hT2 hTe u)
      _ = 2 ^ T * ∑ p ∈ Op hole x, |x (nx hole x p) - x p| := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_finset_sum (fun p _ => iicc2 p)]
          congr 1
          apply Finset.sum_congr rfl; intro p _
          exact cc_sq_int hole x hx p
      _ ≤ 2 ^ T * ∑ p ∈ Op hole x, 1 / (K : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum hnxd
      _ ≤ 2 ^ T * (T / K) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
          exact div_le_div_of_nonneg_right (card_le_T _) hKpos.le
  -- assemble
  have hsum : ∑ c : Fin T → Bool, discrepancyOn x (assign hole x c) (matched hole x c) ≤
      2 ^ T * (L + 1) := by
    calc ∑ c : Fin T → Bool, discrepancyOn x (assign hole x c) (matched hole x c)
        ≤ ∑ c : Fin T → Bool, (1 / (2 * L) * (∫ u in (0 : ℝ)..1, Dp hole x c u ^ 2) + L / 2 + 1) :=
          Finset.sum_le_sum (fun c _ => hcoin c)
      _ = 1 / (2 * L) * (∑ c : Fin T → Bool, ∫ u in (0 : ℝ)..1, Dp hole x c u ^ 2) +
          2 ^ T * (L / 2 + 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
          push_cast; ring
      _ ≤ 1 / (2 * L) * (2 ^ T * (T / K)) + 2 ^ T * (L / 2 + 1) := by
          have : 0 ≤ 1 / (2 * L) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hint this]
      _ = 2 ^ T * (L + 1) := by
          rw [← hL2]; field_simp; ring
  have hLle : L ≤ (T : ℝ) ^ (1 / 2 - η / 2) := by
    have e1 : (T : ℝ) / K ≤ (T : ℝ) ^ (1 - η) := by
      rw [Real.rpow_sub hTpos, Real.rpow_one]
      exact div_le_div_of_nonneg_left hTpos.le hpos hKge
    have e2 : Real.sqrt ((T : ℝ) ^ (1 - η)) = (T : ℝ) ^ (1 / 2 - η / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hTpos.le]
      congr 1; ring
    rw [hLdef, ← e2]
    exact Real.sqrt_le_sqrt e1
  have h1le : (1 : ℝ) ≤ (T : ℝ) ^ (1 / 2 - η / 2) :=
    Real.one_le_rpow (by exact_mod_cast hT1) (by linarith)
  have hpowT : (0 : ℝ) < 2 ^ T := by positivity
  rw [div_le_iff₀ hpowT]
  nlinarith
