-- Prove2me | solution 1 for PigeonholeDesign.Upper.unmatched_imbalance
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:06:41.297131+00:00
-- url     : https://prove2.me/submissions/0e527488-ab36-4b2b-948e-38aaa85e305b

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

end PHUAux

open PHUAux in
theorem solution (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (T : ℕ) (hT1 : 1 ≤ T)
    (hT : Even T) (x : Fin T → ℝ) (hx : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1) (coin : Fin T → Bool) :
    (∀ k : ℕ, ((unmatched (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin).filter
        (fun s => uniformHole ⌈(T : ℝ) ^ η⌉₊ (x s) = k)).card ≤ 1) ∧
    (∀ k : ℕ, ((matched (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin).filter
        (fun s => uniformHole ⌈(T : ℝ) ^ η⌉₊ (x s) = k ∧
          assign (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin s = false)).card =
      ((matched (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin).filter
        (fun s => uniformHole ⌈(T : ℝ) ^ η⌉₊ (x s) = k ∧
          assign (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin s = true)).card) ∧
    H0 (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin + H1 (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin
      ≤ ⌈(T : ℝ) ^ η⌉₊ ∧
    |(H0 (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin : ℤ) - H1 (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin|
      = (T : ℤ) - tau (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin := by
  set K := ⌈(T : ℝ) ^ η⌉₊ with hK
  set hole := uniformHole K with hhole
  have hT2 : 2 ≤ T := by obtain ⟨r, hr⟩ := hT; omega
  set w := assign hole x coin with hw
  set τ := tau hole x coin with hτdef
  have hτT : τ ≤ T := tauU_le hole x coin
  have hmeq := matched_eq hole x coin
  have hS := step2U hole x coin hT2
  rw [← hτdef] at hmeq hS
  have hunm : ∀ s, s ∈ unmatched hole x coin ↔
      (s : ℕ) < τ ∧ s ∉ matchedG (fun t => hole (x t)) τ := by
    intro s
    unfold unmatched
    rw [Finset.mem_filter, ← hmeq, ← hτdef]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter, hunm] at ha hb
    exact unmatched_injG (fun t => hole (x t)) τ a ha.1.1 ha.1.2 b hb.1.1 hb.1.2
      (ha.2.trans hb.2.symm)
  · intro k
    have h := cell_balanced (fun t => hole (x t)) w τ hτT hS k
    rw [hmeq]
    convert h using 2 <;> ext t <;> simp
  · have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
    have hpos : 0 < (T : ℝ) ^ η := by positivity
    have hK1 : 1 ≤ K := Nat.ceil_pos.2 hpos
    have hH : H0 hole x coin + H1 hole x coin = (unmatched hole x coin).card := by
      unfold H0 H1
      rw [← Finset.card_filter_add_card_filter_not (s := unmatched hole x coin)
        (fun s => assign hole x coin s = false)]
      congr 2; ext s; simp
    rw [hH]
    calc (unmatched hole x coin).card ≤ (Finset.range K).card := by
          apply Finset.card_le_card_of_injOn (fun s => hole (x s))
          · intro s _
            simp only [Finset.coe_range, Set.mem_Iio, hhole, uniformHole]
            have := min_le_right ⌊x s * K⌋₊ (K - 1)
            omega
          · intro a ha b hb hab
            rw [Finset.mem_coe, hunm] at ha hb
            exact unmatched_injG (fun t => hole (x t)) τ a ha.1 ha.2 b hb.1 hb.2 hab
      _ = K := Finset.card_range K
  · obtain ⟨e, -⟩ : ∃ e : {t // t ∈ matchedG (fun t => hole (x t)) τ ∧ w t = false} ≃
        {t // t ∈ matchedG (fun t => hole (x t)) τ ∧ w t = true}, True := by
      have hcard : ∀ k : ℕ,
          Fintype.card {a : {t // t ∈ matchedG (fun t => hole (x t)) τ ∧ w t = false} //
            hole (x a.1) = k} =
          Fintype.card {b : {t // t ∈ matchedG (fun t => hole (x t)) τ ∧ w t = true} //
            hole (x b.1) = k} := by
        intro k
        have h := cell_balanced (fun t => hole (x t)) w τ hτT hS k
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
          Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
            (fun t => t ∈ matchedG (fun t => hole (x t)) τ ∧ w t = false) (fun t => hole (x t) = k)),
          Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
            (fun t => t ∈ matchedG (fun t => hole (x t)) τ ∧ w t = true) (fun t => hole (x t) = k)),
          Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
          Fintype.card_subtype, Fintype.card_subtype]
        convert h using 2 <;> ext t <;> simp <;> tauto
      exact ⟨(Equiv.sigmaFiberEquiv (fun a : {t // t ∈ matchedG (fun t => hole (x t)) τ ∧
          w t = false} => hole (x a.1))).symm.trans
        ((Equiv.sigmaCongrRight (fun k => Fintype.equivOfCardEq (hcard k))).trans
          (Equiv.sigmaFiberEquiv (fun b : {t // t ∈ matchedG (fun t => hole (x t)) τ ∧
            w t = true} => hole (x b.1)))), trivial⟩
    have hK := Fintype.card_congr e
    have hm := tauU_mem hole x coin hT2 hT
    rw [← hτdef, ← hw] at hm
    have hc : (Finset.univ.filter (fun t : Fin T => (t : ℕ) < τ)).card = τ := by
      have : (Finset.univ.filter (fun t : Fin T => (t : ℕ) < τ)) =
          (Finset.range τ).attachFin (fun n hn => lt_of_lt_of_le (Finset.mem_range.1 hn) hτT) := by
        ext t; simp
      rw [this, Finset.card_attachFin, Finset.card_range]
    have hsum : nCtrl w τ + nTrt w τ = τ := by
      refine Eq.trans ?_ hc
      unfold nCtrl nTrt
      rw [← Finset.card_filter_add_card_filter_not
        (s := Finset.univ.filter (fun t : Fin T => (t : ℕ) < τ)) (fun t => w t = false),
        Finset.filter_filter, Finset.filter_filter]
      congr 1 <;> (congr 1; ext t; simp)
    have hsplit : ∀ b : Bool, (Finset.univ.filter (fun t : Fin T => (t : ℕ) < τ ∧ w t = b)).card =
        ((unmatched hole x coin).filter (fun s => w s = b)).card +
          Fintype.card {t // t ∈ matchedG (fun t => hole (x t)) τ ∧ w t = b} := by
      intro b
      rw [Fintype.card_subtype, ← Finset.card_filter_add_card_filter_not
        (s := Finset.univ.filter (fun t : Fin T => (t : ℕ) < τ ∧ w t = b))
        (fun t => t ∉ matchedG (fun t => hole (x t)) τ), Finset.filter_filter,
        Finset.filter_filter]
      congr 1
      · congr 1; ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hunm]; tauto
      · congr 1; ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
        constructor
        · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩
          refine ⟨⟨?_, h2⟩, h1⟩
          unfold matchedG at h1
          rw [Finset.mem_filter] at h1
          exact h1.2.1
    have e0 := hsplit false
    have e1 := hsplit true
    have e0' : nCtrl w τ = H0 hole x coin +
        Fintype.card {t // t ∈ matchedG (fun t => hole (x t)) τ ∧ w t = false} := e0
    have e1' : nTrt w τ = H1 hole x coin +
        Fintype.card {t // t ∈ matchedG (fun t => hole (x t)) τ ∧ w t = true} := e1
    have hH0 : H0 hole x coin = ((unmatched hole x coin).filter (fun s => w s = false)).card := rfl
    have hH1 : H1 hole x coin = ((unmatched hole x coin).filter (fun s => w s = true)).card := rfl
    obtain ⟨r, hr⟩ := hT
    have hT2r : T / 2 = r := by omega
    rcases hm.2 with h | h
    · rw [abs_of_nonneg (by omega)]; omega
    · rw [abs_of_nonpos (by omega)]; omega
