-- Prove2me | solution 1 for SetDefinedGraphs.fact_3_2_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:35:27.184612+00:00
-- url     : https://prove2.me/submissions/2cb9dc97-3cb7-46bc-a340-b26ad577c61c

import Mathlib
import Definitions.Def_FASTournament_induce
import Definitions.Def_FASTournament_Isomorphic
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_ShiftDigraph

section
set_option autoImplicit false
namespace SetDefinedGraphs.Dev.F323
open SetDefinedGraphs

variable {n : ℕ}

/-- strict adjacency in the underlying graph -/
def Ed {D : ℕ} (a b : ShiftVertex n D) : Prop :=
  a ≠ b ∧ ((shiftDigraph n D).Adj a b ∨ (shiftDigraph n D).Adj b a)

lemma Ed.symm {D : ℕ} {a b : ShiftVertex n D} (h : Ed a b) : Ed b a :=
  ⟨h.1.symm, h.2.symm⟩

def IsWalk (D L : ℕ) (u : ℕ → ShiftVertex n D) : Prop :=
  u L = u 0 ∧ ∀ i < L, Ed (u i) (u (i + 1))

def pre {D : ℕ} (e : ShiftVertex n (D + 1)) : ShiftVertex n D :=
  ⟨fun i => e.1 i.castSucc, fun _ _ h => e.2 (Fin.castSucc_lt_castSucc_iff.2 h)⟩

def suf {D : ℕ} (e : ShiftVertex n (D + 1)) : ShiftVertex n D :=
  ⟨fun i => e.1 i.succ, fun _ _ h => e.2 (Fin.succ_lt_succ_iff.2 h)⟩

lemma adj_iff {D : ℕ} (a b : ShiftVertex n (D + 1)) :
    (shiftDigraph n (D + 1)).Adj a b ↔ suf a = pre b := by
  constructor
  · intro h
    apply Subtype.ext
    funext k
    exact h k.castSucc k.succ (by simp)
  · intro h i j hij
    have hi : i.val < D := by have := j.2; omega
    have := congrFun (congrArg Subtype.val h) ⟨i.val, hi⟩
    have e1 : i = (⟨i.val, hi⟩ : Fin D).castSucc := Fin.ext rfl
    have e2 : j = (⟨i.val, hi⟩ : Fin D).succ := Fin.ext (by simp; omega)
    rw [e1, e2]
    exact this

lemma adj_pre_suf {D : ℕ} (e : ShiftVertex n (D + 1)) :
    (shiftDigraph n D).Adj (pre e) (suf e) := by
  intro i j hij
  exact congrArg e.1 (Fin.ext (by simp; omega))

lemma pre_ne_suf {D : ℕ} (hD : 1 ≤ D) (e : ShiftVertex n (D + 1)) : pre e ≠ suf e := by
  intro h
  have h1 := congrFun (congrArg Subtype.val h) ⟨0, hD⟩
  have hlt : e.1 (Fin.castSucc ⟨0, hD⟩) < e.1 (Fin.succ ⟨0, hD⟩) :=
    e.2 (by simp [Fin.lt_def])
  exact hlt.ne h1

lemma ed_pre_suf {D : ℕ} (hD : 1 ≤ D) (e : ShiftVertex n (D + 1)) : Ed (pre e) (suf e) :=
  ⟨pre_ne_suf hD e, Or.inl (adj_pre_suf e)⟩

lemma last_lt {D : ℕ} (hD : 1 ≤ D) {a b : ShiftVertex n (D + 1)}
    (h : (shiftDigraph n (D + 1)).Adj a b) : a.1 (Fin.last D) < b.1 (Fin.last D) := by
  have h1 := h ⟨D - 1, by omega⟩ (Fin.last D) (by simp; omega)
  rw [h1]
  exact b.2 (by simp [Fin.lt_def]; omega)

lemma ed_of_adj {D : ℕ} (hD : 1 ≤ D) {a b : ShiftVertex n (D + 1)}
    (h : (shiftDigraph n (D + 1)).Adj a b ∨ (shiftDigraph n (D + 1)).Adj b a) : Ed a b := by
  refine ⟨?_, h⟩
  rintro rfl
  rcases h with h | h <;> exact lt_irrefl _ (last_lt hD h)

lemma normalize {V : Type} [DecidableEq V] (E : V → V → Prop) (t : ℕ → V) (L : ℕ)
    (h : ∀ i < L, t i = t (i + 1) ∨ E (t i) (t (i + 1))) :
    ∃ u : ℕ → V, u 0 = t 0 ∧ u (∑ i ∈ Finset.range L, if t i = t (i + 1) then 0 else 1) = t L ∧
      ∀ i < (∑ i ∈ Finset.range L, if t i = t (i + 1) then 0 else 1), E (u i) (u (i + 1)) := by
  induction L with
  | zero => exact ⟨fun _ => t 0, rfl, by simp, by simp⟩
  | succ L ih =>
    obtain ⟨u, h0, hM, hE⟩ := ih (fun i hi => h i (by omega))
    rw [Finset.sum_range_succ]
    by_cases hc : t L = t (L + 1)
    · simp only [hc, if_true, add_zero] at hM ⊢
      refine ⟨u, h0, ?_, ?_⟩
      · exact hM
      · simpa [hc] using hE
    · set M := ∑ i ∈ Finset.range L, if t i = t (i + 1) then 0 else 1 with hMdef
      simp only [hc, if_false]
      refine ⟨fun i => if i ≤ M then u i else t (L + 1), by simpa using h0, by simp, ?_⟩
      intro i hi
      by_cases hiM : i < M
      · simp only [show i ≤ M by omega, show i + 1 ≤ M by omega, if_true]
        exact hE i hiM
      · have : i = M := by omega
        rw [this]
        simp only [le_refl, if_true, show ¬ (M + 1 ≤ M) by omega, if_false]
        rw [hM]
        exact (h L (by omega)).resolve_left hc

lemma turns_parity (b : ℕ → Bool) (k : ℕ) :
    (∑ i ∈ Finset.range k, if b i = b (i + 1) then 0 else 1) % 2 = if b 0 = b k then 0 else 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    cases h0 : b 0 <;> cases h1 : b k <;> cases h2 : b (k + 1) <;> simp [h0, h1, h2] at ih ⊢ <;> omega

lemma reduce {D : ℕ} (hD : 1 ≤ D) {L : ℕ} (hLodd : L % 2 = 1) (e : ℕ → ShiftVertex n (D + 1))
    (hc : e L = e 0)
    (hs : ∀ i < L, (shiftDigraph n (D + 1)).Adj (e i) (e (i + 1)) ∨
      (shiftDigraph n (D + 1)).Adj (e (i + 1)) (e i)) :
    ∃ M, M % 2 = 1 ∧ M + 2 ≤ L ∧ ∃ u : ℕ → ShiftVertex n D, IsWalk D M u := by
  classical
  have hLpos : 0 < L := by omega
  let b : ℕ → Bool := fun i => decide ((shiftDigraph n (D + 1)).Adj (e (i % L)) (e (i % L + 1)))
  have hb : ∀ i < L, b i = true ↔ (shiftDigraph n (D + 1)).Adj (e i) (e (i + 1)) := by
    intro i hi
    simp [b, Nat.mod_eq_of_lt hi]
  have hbL : b L = b 0 := by simp [b, Nat.mod_self]
  let t : ℕ → ShiftVertex n D := fun i => if b i = true then suf (e i) else pre (e i)
  have htL : t L = t 0 := by simp only [t, hbL, hc]
  have step : ∀ i < L, (b i = b (i + 1) → Ed (t i) (t (i + 1))) ∧ (b i ≠ b (i + 1) → t i = t (i + 1)) := by
    intro i hi
    have hA : b i = true → suf (e i) = pre (e (i + 1)) := fun h => (adj_iff _ _).1 ((hb i hi).1 h)
    have hB : b i = false → suf (e (i + 1)) = pre (e i) := by
      intro h
      have : ¬ (shiftDigraph n (D + 1)).Adj (e i) (e (i + 1)) := by
        rw [← hb i hi, h]; simp
      exact (adj_iff _ _).1 ((hs i hi).resolve_left this)
    cases h1 : b i <;> cases h2 : b (i + 1)
    · have := hB h1
      simp only [t, h1, h2]
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      simp only [Bool.false_eq_true, if_false]
      rw [← this]
      exact (ed_pre_suf hD _).symm
    · have := hB h1
      simp only [t, h1, h2]
      refine ⟨fun h => by simp at h, fun _ => ?_⟩
      simp [this]
    · have := hA h1
      simp only [t, h1, h2]
      refine ⟨fun h => by simp at h, fun _ => ?_⟩
      simp [this]
    · have := hA h1
      simp only [t, h1, h2]
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      simp only [if_true]
      rw [this]
      exact ed_pre_suf hD _
  have hlazy : ∀ i < L, t i = t (i + 1) ∨ Ed (t i) (t (i + 1)) := by
    intro i hi
    by_cases h : b i = b (i + 1)
    · exact Or.inr ((step i hi).1 h)
    · exact Or.inl ((step i hi).2 h)
  obtain ⟨u, hu0, huM, huE⟩ := normalize Ed t L hlazy
  set M := ∑ i ∈ Finset.range L, if t i = t (i + 1) then 0 else 1 with hMdef
  set T := ∑ i ∈ Finset.range L, if b i = b (i + 1) then 0 else 1 with hTdef
  have hterm : ∀ i ∈ Finset.range L, (if t i = t (i + 1) then 0 else 1) +
      (if b i = b (i + 1) then 0 else 1) = 1 := by
    intro i hi
    have hi := Finset.mem_range.1 hi
    by_cases h : b i = b (i + 1)
    · have hne : t i ≠ t (i + 1) := ((step i hi).1 h).1
      simp [h, hne]
    · have := (step i hi).2 h
      simp [h, this]
  have hMT : M + T = L := by
    rw [hMdef, hTdef, ← Finset.sum_add_distrib, Finset.sum_congr rfl hterm]
    simp
  have hTeven : T % 2 = 0 := by
    have := turns_parity b L
    rw [hbL] at this
    simpa using this
  have hTne : T ≠ 0 := by
    intro hT0
    have hall : ∀ i < L, b i = b (i + 1) := by
      intro i hi
      have := (Finset.sum_eq_zero_iff.1 hT0) i (Finset.mem_range.2 hi)
      by_contra hne
      simp [hne] at this
    have hconst : ∀ i ≤ L, b i = b 0 := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih => intro hi; rw [← hall i (by omega)]; exact ih (by omega)
    cases h0 : b 0
    · have hadj : ∀ i < L, (shiftDigraph n (D + 1)).Adj (e (i + 1)) (e i) := by
        intro i hi
        have : ¬ (shiftDigraph n (D + 1)).Adj (e i) (e (i + 1)) := by
          rw [← hb i hi, hconst i hi.le, h0]; simp
        exact (hs i hi).resolve_left this
      have : ∀ k ≤ L, ((e k).1 (Fin.last D)).val + k ≤ ((e 0).1 (Fin.last D)).val := by
        intro k
        induction k with
        | zero => intro _; simp
        | succ k ih =>
          intro hk
          have h1 := last_lt hD (hadj k (by omega))
          have h2 : ((e (k + 1)).1 (Fin.last D)).val < ((e k).1 (Fin.last D)).val := h1
          have := ih (by omega)
          omega
      have h3 := this L le_rfl
      rw [hc] at h3
      omega
    · have hadj : ∀ i < L, (shiftDigraph n (D + 1)).Adj (e i) (e (i + 1)) := by
        intro i hi
        rw [← hb i hi, hconst i hi.le, h0]
      have : ∀ k ≤ L, ((e 0).1 (Fin.last D)).val + k ≤ ((e k).1 (Fin.last D)).val := by
        intro k
        induction k with
        | zero => intro _; simp
        | succ k ih =>
          intro hk
          have h1 := last_lt hD (hadj k (by omega))
          have h2 : ((e k).1 (Fin.last D)).val < ((e (k + 1)).1 (Fin.last D)).val := h1
          have := ih (by omega)
          omega
      have h3 := this L le_rfl
      rw [hc] at h3
      omega
  refine ⟨M, by omega, by omega, u, ?_, huE⟩
  rw [huM, htL, hu0]

theorem no_walk (D : ℕ) (hD : 1 ≤ D) : ∀ L : ℕ, L % 2 = 1 → L + 1 ≤ 2 * D →
    ∀ u : ℕ → ShiftVertex n D, ¬ IsWalk D L u := by
  induction D, hD using Nat.le_induction with
  | base =>
    intro L hL hLD u hw
    have : L = 1 := by omega
    subst this
    exact (hw.2 0 (by omega)).1 (by simpa using hw.1.symm)
  | succ D hD ih =>
    intro L hL hLD e hw
    have hs : ∀ i < L, (shiftDigraph n (D + 1)).Adj (e i) (e (i + 1)) ∨
        (shiftDigraph n (D + 1)).Adj (e (i + 1)) (e i) := fun i hi => (hw.2 i hi).2
    obtain ⟨M, hM, hML, u, hu⟩ := reduce hD hL e hw.1 hs
    exact ih M hM (by omega) u hu

/-! The odd cycle in `S(2d+2, d)`. -/

def hB (d j k : ℕ) : ℕ := if k < j then d - j + k else d + 1 + k - j

def gv (d s k : ℕ) : ℕ :=
  if min s (2 * d + 1) ≤ d then min s (2 * d + 1) + k else hB d (min s (2 * d + 1) - d - 1) k

lemma gv_lt (d s k : ℕ) (hk : k < d) : gv d s k < 2 * d + 2 := by
  unfold gv hB; split_ifs <;> omega

lemma gv_strictMono (d s : ℕ) : StrictMono (gv d s) := by
  apply strictMono_nat_of_lt_succ
  intro k
  unfold gv hB; split_ifs <;> omega

def cyc (d : ℕ) (s : ℕ) : ShiftVertex (2 * d + 2) d :=
  ⟨fun k => ⟨gv d s k, gv_lt d s k k.2⟩, fun i j hij => gv_strictMono d s (show (i : ℕ) < j from hij)⟩

lemma cyc_closed (d : ℕ) (hd : 1 ≤ d) : cyc d (2 * d + 1) = cyc d 0 := by
  apply Subtype.ext
  funext k
  apply Fin.ext
  have := k.2
  simp only [cyc, gv, hB]
  split_ifs <;> omega

lemma cyc_adj (d : ℕ) (s : ℕ) (hs : s ≤ 2 * d) :
    (shiftDigraph (2 * d + 2) d).Adj (cyc d s) (cyc d (s + 1)) ∨
      (shiftDigraph (2 * d + 2) d).Adj (cyc d (s + 1)) (cyc d s) := by
  by_cases h : s ≤ d
  · left
    intro i j hij
    apply Fin.ext
    simp only [cyc, gv, hB]
    split_ifs <;> omega
  · right
    intro i j hij
    apply Fin.ext
    simp only [cyc, gv, hB]
    split_ifs <;> omega

theorem part2 (d : ℕ) (hd : 2 ≤ d) :
    ∃ (W : Type) (G : Digraph W), IsShiftDigraphDim d G ∧ ¬ IsShiftDigraphDim (d + 1) G := by
  refine ⟨(Set.univ : Set (ShiftVertex (2 * d + 2) d)),
    FASTournament.induce (shiftDigraph (2 * d + 2) d) Set.univ, ?_, ?_⟩
  · exact ⟨2 * d + 2, Set.univ, Equiv.refl _, fun a b => Iff.rfl⟩
  · rintro ⟨N, S, e, he⟩
    let w : ℕ → (Set.univ : Set (ShiftVertex (2 * d + 2) d)) := fun s => ⟨cyc d s, trivial⟩
    have hd1 : 1 ≤ d := by omega
    refine no_walk (d + 1) (by omega) (2 * d + 1) (by omega) (by omega) (fun s => (e (w s)).1) ?_
    refine ⟨?_, ?_⟩
    · have : w (2 * d + 1) = w 0 := Subtype.ext (cyc_closed d hd1)
      simp only [this]
    · intro i hi
      have hadj := cyc_adj d i (by omega)
      have hA : (shiftDigraph N (d + 1)).Adj (e (w i)).1 (e (w (i + 1))).1 ∨
          (shiftDigraph N (d + 1)).Adj (e (w (i + 1))).1 (e (w i)).1 := by
        rcases hadj with h | h
        · exact Or.inl ((he (w i) (w (i + 1))).1 h)
        · exact Or.inr ((he (w (i + 1)) (w i)).1 h)
      exact ed_of_adj hd1 hA


/-! Part 1: the inclusion. -/

def code (n : ℕ) (a b : Fin n) : Fin (n * n) :=
  ⟨a.1 * n + b.1, calc a.1 * n + b.1 < a.1 * n + n := by have := b.2; omega
    _ = (a.1 + 1) * n := by ring
    _ ≤ n * n := Nat.mul_le_mul_right n a.2⟩

lemma code_inj {n : ℕ} {a b a' b' : Fin n} (h : code n a b = code n a' b') : a = a' ∧ b = b' := by
  have h1 : a.1 * n + b.1 = a'.1 * n + b'.1 := congrArg Fin.val h
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) b.2
  have hb : b.1 = b'.1 := by
    have e1 : (a.1 * n + b.1) % n = b.1 := by
      rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt b.2
    have e2 : (a'.1 * n + b'.1) % n = b'.1 := by
      rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt b'.2
    rw [← e1, ← e2, h1]
  have ha : a.1 = a'.1 := by
    have : a.1 * n = a'.1 * n := by omega
    exact Nat.eq_of_mul_eq_mul_right hn this
  exact ⟨Fin.ext ha, Fin.ext hb⟩

lemma code_lt {n : ℕ} {a b a' b' : Fin n} (h : a < a') : code n a b < code n a' b' := by
  show a.1 * n + b.1 < a'.1 * n + b'.1
  have h1 : a.1 + 1 ≤ a'.1 := h
  have h2 : (a.1 + 1) * n ≤ a'.1 * n := Nat.mul_le_mul_right n h1
  have := b.2
  nlinarith

def psi {D : ℕ} (u : ShiftVertex n (D + 2)) : ShiftVertex (n * n) (D + 1) :=
  ⟨fun k => code n (u.1 k.castSucc) (u.1 k.succ), fun _ _ h =>
    code_lt (u.2 (Fin.castSucc_lt_castSucc_iff.2 h))⟩

lemma psi_inj {D : ℕ} : Function.Injective (psi (n := n) (D := D)) := by
  intro u w h
  have key : ∀ k : Fin (D + 1), u.1 k.castSucc = w.1 k.castSucc ∧ u.1 k.succ = w.1 k.succ :=
    fun k => code_inj (congrFun (congrArg Subtype.val h) k)
  apply Subtype.ext
  funext i
  by_cases hi : i.val < D + 1
  · exact (key ⟨i.val, hi⟩).1
  · have : i = (Fin.last D).succ := Fin.ext (by simp; omega)
    rw [this]
    exact (key (Fin.last D)).2

lemma adj_psi {D : ℕ} (hD : 1 ≤ D) (u w : ShiftVertex n (D + 2)) :
    (shiftDigraph (n * n) (D + 1)).Adj (psi u) (psi w) ↔ (shiftDigraph n (D + 2)).Adj u w := by
  rw [adj_iff, adj_iff]
  have hu : ∀ x y : Fin (D + 2), x.val = y.val → u.1 x = u.1 y := fun x y h => congrArg u.1 (Fin.ext h)
  have hw : ∀ x y : Fin (D + 2), x.val = y.val → w.1 x = w.1 y := fun x y h => congrArg w.1 (Fin.ext h)
  constructor
  · intro h
    have key : ∀ k : Fin D, u.1 k.succ.castSucc = w.1 k.castSucc.castSucc ∧
        u.1 k.succ.succ = w.1 k.castSucc.succ := fun k =>
      code_inj (congrFun (congrArg Subtype.val h) k)
    apply Subtype.ext
    funext k
    show u.1 k.succ = w.1 k.castSucc
    by_cases hk : k.val < D
    · have := (key ⟨k.val, hk⟩).1
      rw [hu k.succ (Fin.succ (⟨k.val, hk⟩ : Fin D)).castSucc (by simp),
        hw k.castSucc (⟨k.val, hk⟩ : Fin D).castSucc.castSucc (by simp)]
      exact this
    · have := (key ⟨D - 1, by omega⟩).2
      rw [hu k.succ (Fin.succ (⟨D - 1, by omega⟩ : Fin D)).succ (by simp; omega),
        hw k.castSucc (⟨D - 1, by omega⟩ : Fin D).castSucc.succ (by simp; omega)]
      exact this
  · intro h
    apply Subtype.ext
    funext k
    have h1 := congrFun (congrArg Subtype.val h) k.castSucc
    have h2 := congrFun (congrArg Subtype.val h) k.succ
    show code n (u.1 k.succ.castSucc) (u.1 k.succ.succ) =
      code n (w.1 k.castSucc.castSucc) (w.1 k.castSucc.succ)
    have e1 : u.1 k.succ.castSucc = w.1 k.castSucc.castSucc := by
      rw [hu k.succ.castSucc k.castSucc.succ (by simp)]; exact h1
    have e2 : u.1 k.succ.succ = w.1 k.castSucc.succ := by
      rw [hw k.castSucc.succ k.succ.castSucc (by simp)]; exact h2
    rw [e1, e2]

theorem part1 {D : ℕ} (hD : 1 ≤ D) {W : Type} (G : Digraph W) (hG : IsShiftDigraphDim (D + 1 + 1) G) :
    IsShiftDigraphDim (D + 1) G := by
  obtain ⟨n, S, e, he⟩ := hG
  refine ⟨n * n, psi '' S, e.trans (Equiv.Set.image psi S psi_inj), ?_⟩
  intro a b
  rw [he a b]
  exact (adj_psi hD (e a).1 (e b).1).symm

end SetDefinedGraphs.Dev.F323

namespace SetDefinedGraphs
open SetDefinedGraphs.Dev.F323 in
theorem chk_fact_3_2_3 (d : ℕ) (hd : 2 ≤ d) :
    (∀ {W : Type} (G : Digraph W), IsShiftDigraphDim (d + 1) G → IsShiftDigraphDim d G) ∧
      ∃ (W : Type) (G : Digraph W), IsShiftDigraphDim d G ∧ ¬ IsShiftDigraphDim (d + 1) G := by
  refine ⟨?_, part2 d hd⟩
  obtain ⟨D, hD, rfl⟩ : ∃ D, 1 ≤ D ∧ d = D + 1 := ⟨d - 1, by omega, by omega⟩
  intro W G hG
  exact part1 hD G hG
end SetDefinedGraphs
end

theorem solution : type_of% @SetDefinedGraphs.chk_fact_3_2_3 := @SetDefinedGraphs.chk_fact_3_2_3
