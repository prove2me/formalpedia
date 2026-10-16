-- Prove2me | solution 1 for SingleMachinePrec.IntervalChromatic.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T07:44:13.472578+00:00
-- url     : https://prove2.me/submissions/1fc297aa-20db-44b8-bcc9-3b47bd595088

import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalChromatic_CanonicalOrder

set_option autoImplicit false

namespace A79940cfAux
open SingleMachinePrec.IntervalChromatic

def cls {n : ℕ} (b : Fin n) (s : Finset (Fin n)) : ℕ :=
  if ∀ x ∈ s, x < b then 0 else if ∀ x ∈ s, b < x then 2 else 1

def sm {n : ℕ} (s : Finset (Fin n)) : ℤ := ∑ x ∈ s, ((x : ℕ) : ℤ)

def q {n : ℕ} (b : Fin n) (s : Finset (Fin n)) : ℤ :=
  if cls b s = 1 then - sm s else sm s

def key {n : ℕ} (b : Fin n) (s : Interval n) : Lex (ℕ × Lex (ℤ × Colex (Finset (Fin n)))) :=
  toLex (cls b s.1, toLex (q b s.1, toColex s.1))

def Lrel {n : ℕ} (b : Fin n) (s t : Interval n) : Prop := key b s ≤ key b t

lemma key_inj {n : ℕ} (b : Fin n) : Function.Injective (key b) := by
  intro s t h
  simp only [key, toLex_inj, Prod.mk.injEq, toColex_inj] at h
  exact Subtype.ext h.2.2

lemma isLin {n : ℕ} (b : Fin n) : IsLinearOrder (Interval n) (Lrel b) where
  refl := fun s => le_refl (key b s)
  trans := fun _ _ _ h1 h2 => le_trans h1 h2
  antisymm := fun _ _ h1 h2 => key_inj b (le_antisymm h1 h2)
  total := fun s t => le_total (key b s) (key b t)

lemma pair_lt {n : ℕ} (b x1 x2 y1 y2 : Fin n) (hx : x1 ≠ x2) (hy : y1 ≠ y2)
    (h11 : x1 < y1) (h12 : x1 < y2) (h21 : x2 < y1) (h22 : x2 < y2) :
    cls b {x1, x2} < cls b {y1, y2} ∨
      (cls b {x1, x2} = cls b {y1, y2} ∧ q b {x1, x2} < q b {y1, y2}) := by
  have hx' : (x1 : ℕ) ≠ x2 := fun h => hx (Fin.ext h)
  have hy' : (y1 : ℕ) ≠ y2 := fun h => hy (Fin.ext h)
  simp only [q, cls, sm, Finset.sum_pair hx, Finset.sum_pair hy, Finset.mem_insert,
    Finset.mem_singleton, forall_eq_or_imp, forall_eq, Fin.lt_def] at *
  split_ifs <;> first | contradiction | omega

lemma ext_I {n : ℕ} (b : Fin n) (s t : Interval n) (h : I n s t) : Lrel b s t := by
  rcases h with rfl | h
  · exact le_refl (key b s)
  obtain ⟨x1, x2, hx, hs⟩ := Finset.card_eq_two.mp s.2
  obtain ⟨y1, y2, hy, ht⟩ := Finset.card_eq_two.mp t.2
  rw [hs, ht] at h
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] at h
  have hk := pair_lt b x1 x2 y1 y2 hx hy h.1.1 h.1.2 h.2.1 h.2.2
  unfold Lrel key
  rw [hs, ht]
  rcases hk with hk | ⟨he, hk⟩
  · exact le_of_lt (Prod.Lex.toLex_lt_toLex.mpr (Or.inl hk))
  · rw [he]
    exact le_of_lt (Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl hk)⟩))

lemma rev {n : ℕ} (a b c : Fin n) (hab : a < b) (hbc : b < c) :
    Lrel b (endpointPair b c hbc) (endpointPair a b hab) := by
  have hcb : cls b {b, c} = 1 := by
    simp only [cls, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      Fin.lt_def] at *
    split_ifs <;> first | contradiction | omega
  have hab' : cls b {a, b} = 1 := by
    simp only [cls, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      Fin.lt_def] at *
    split_ifs <;> first | contradiction | omega
  have hq : q b {b, c} < q b {a, b} := by
    simp only [q, hcb, hab', ↓reduceIte, sm, Finset.sum_pair (ne_of_lt hab),
      Finset.sum_pair (ne_of_lt hbc)]
    rw [Fin.lt_def] at hab hbc
    omega
  show toLex (cls b {b, c}, toLex (q b {b, c}, toColex ({b, c} : Finset (Fin n)))) ≤
    toLex (cls b {a, b}, toLex (q b {a, b}, toColex ({a, b} : Finset (Fin n))))
  rw [hcb, hab']
  exact le_of_lt (Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl hq)⟩))

lemma inc {n : ℕ} (a b c : Fin n) (hab : a < b) (hbc : b < c) :
    SingleMachinePrec.Framework.Incomparable (I n) (endpointPair a b hab) (endpointPair b c hbc) := by
  constructor
  · rintro (h | h)
    · have ha : a ∈ (endpointPair b c hbc).1 := h ▸ (by simp [endpointPair])
      simp only [endpointPair, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact lt_irrefl _ hab
      · exact lt_asymm hab hbc
    · exact lt_irrefl b (h b (by simp [endpointPair]) b (by simp [endpointPair]))
  · rintro (h | h)
    · have ha : a ∈ (endpointPair b c hbc).1 := h ▸ (by simp [endpointPair])
      simp only [endpointPair, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact lt_irrefl _ hab
      · exact lt_asymm hab hbc
    · exact lt_irrefl b (h b (by simp [endpointPair]) b (by simp [endpointPair]))

end A79940cfAux

namespace C972Aux
open SingleMachinePrec.IntervalChromatic

lemma adj4 {n : ℕ} (i j l m : Fin n)
    (hij : i < j) (hjl : j < l) (hlm : l < m) :
    ∃ h₁ : SingleMachinePrec.Framework.Incomparable (I n) (endpointPair i j hij) (endpointPair j l hjl),
    ∃ h₂ : SingleMachinePrec.Framework.Incomparable (I n) (endpointPair j l hjl) (endpointPair l m hlm),
      G (I n)
        ⟨(endpointPair i j hij, endpointPair j l hjl), h₁⟩
        ⟨(endpointPair j l hjl, endpointPair l m hlm), h₂⟩ := by
  refine ⟨A79940cfAux.inc i j l hij hjl, A79940cfAux.inc j l m hjl hlm, ?_, ?_, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun p : IncomparablePair (I n) => p.1.1) h
    exact (A79940cfAux.inc i j l hij hjl).1 (Or.inl h')
  · exact ⟨A79940cfAux.Lrel j, ⟨A79940cfAux.isLin j, A79940cfAux.ext_I j⟩,
      A79940cfAux.rev i j l hij hjl⟩
  · exact ⟨A79940cfAux.Lrel l, ⟨A79940cfAux.isLin l, A79940cfAux.ext_I l⟩,
      A79940cfAux.rev j l m hjl hlm⟩
  · rintro ⟨L, ⟨hlin, hext⟩, h1, h2⟩
    have := hlin
    have hBA : L (endpointPair j l hjl) (endpointPair i j hij) := h1
    have hCB : L (endpointPair l m hlm) (endpointPair j l hjl) := h2
    have hAC : L (endpointPair i j hij) (endpointPair l m hlm) := by
      apply hext
      right
      intro x hx y hy
      simp only [endpointPair, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact lt_trans hij hjl
      · exact lt_trans (lt_trans hij hjl) hlm
      · exact hjl
      · exact lt_trans hjl hlm
    have hEq := antisymm hAC (_root_.trans hCB hBA)
    have hi : i ∈ (endpointPair l m hlm).1 := hEq ▸ (by simp [endpointPair])
    simp only [endpointPair, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact lt_asymm hij hjl
    · exact lt_asymm (lt_trans hij hjl) hlm

open Classical in
noncomputable def S {n k : ℕ} (color : IncomparablePair (I n) → Fin k) (j l : Fin n) :
    Finset (Fin k) :=
  Finset.univ.filter (fun c => ∃ (i : Fin n) (h1 : i < j) (h2 : j < l),
    color ⟨(endpointPair i j h1, endpointPair j l h2), A79940cfAux.inc i j l h1 h2⟩ = c)

lemma adjc {n k : ℕ} (color : IncomparablePair (I n) → Fin k)
    (hc : ∀ u v, G (I n) u v → color u ≠ color v) (i j l m : Fin n)
    (h1 : i < j) (h2 : j < l) (h3 : l < m) :
    color ⟨(endpointPair i j h1, endpointPair j l h2), A79940cfAux.inc i j l h1 h2⟩ ≠
    color ⟨(endpointPair j l h2, endpointPair l m h3), A79940cfAux.inc j l m h2 h3⟩ := by
  obtain ⟨a, b, hG⟩ := adj4 i j l m h1 h2 h3
  exact hc _ _ hG

lemma S_ne {n k : ℕ} (color : IncomparablePair (I n) → Fin k)
    (hc : ∀ u v, G (I n) u v → color u ≠ color v) (j l m : Fin n)
    (hjl : j < l) (hlm : l < m) : S color l m ≠ S color j l := by
  intro h
  have hmem : color ⟨(endpointPair j l hjl, endpointPair l m hlm),
      A79940cfAux.inc j l m hjl hlm⟩ ∈ S color l m := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨j, hjl, hlm, rfl⟩
  rw [h] at hmem
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨i, h1, h2, he⟩ := hmem
  exact adjc color hc i j l m h1 h2 hlm he

open Classical in
noncomputable def Phi {n k : ℕ} (color : IncomparablePair (I n) → Fin k) (l : Fin n) :
    Finset (Finset (Fin k)) :=
  Finset.univ.filter (fun s => ∃ j : Fin n, j < l ∧ S color j l = s)

lemma Phi_ne {n k : ℕ} (color : IncomparablePair (I n) → Fin k)
    (hc : ∀ u v, G (I n) u v → color u ≠ color v) (l m : Fin n) (hlm : l < m) :
    Phi color l ≠ Phi color m := by
  intro h
  have hmem : S color l m ∈ Phi color m := by
    simp only [Phi, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨l, hlm, rfl⟩
  rw [← h] at hmem
  simp only [Phi, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨j, hj, hS⟩ := hmem
  exact S_ne color hc j l m hj hlm hS.symm

lemma not_col {n k : ℕ} (hn : 2 ^ (2 ^ k) < n) : ¬ Colorable n k := by
  rintro ⟨color, hc⟩
  have hinj : Function.Injective (Phi color) := by
    intro a b hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (Phi_ne color hc a b h)
    · exact h
    · exact absurd hab.symm (Phi_ne color hc b a h)
  have := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin, Fintype.card_finset, Fintype.card_finset, Fintype.card_fin] at this
  exact absurd hn (not_lt.mpr this)

end C972Aux

open SingleMachinePrec.IntervalChromatic in
theorem solution (k : ℕ) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ¬ Colorable n k := by
  refine ⟨2 ^ (2 ^ k) + 2, Nat.le_add_left 2 _, fun n hn => C972Aux.not_col ?_⟩
  exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by norm_num)) hn
