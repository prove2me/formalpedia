-- Prove2me | solution 1 for SteinbergFalse.Counterexample.G_isPlanar
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T15:37:16.588198+00:00
-- url     : https://prove2.me/submissions/3a2144e2-3d18-4453-b031-5ac0750585d9

import Mathlib
import Definitions.Def_opg37357_obstacle_number
import Definitions.Def_SteinbergFalse_Counterexample_G

set_option autoImplicit false

namespace SteinbergAux
open SteinbergFalse.Counterexample

def E1 : List (Sym2 (Fin 15)) := [s(0, 5), s(0, 6), s(5, 6), s(1, 4), s(1, 3), s(3, 4), s(2, 7), s(2, 8), s(7, 8), s(4, 5), s(4, 10), s(5, 10), s(6, 7), s(6, 11), s(7, 11), s(3, 9), s(8, 9), s(9, 12), s(10, 13), s(11, 14), s(12, 13), s(13, 14), s(12, 14)]

theorem G1_adj_mem {u v : Fin 15} (h : G1.Adj u v) : s(u, v) ∈ E1 := by
  simp only [G1, SimpleGraph.fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  simp only [E1, List.mem_cons, List.not_mem_nil, or_false]
  exact h.1

theorem map_adj_mem {V W : Type} {H : SimpleGraph V} (f : V ↪ W) {L : List (Sym2 V)}
    (hL : ∀ u v, H.Adj u v → s(u, v) ∈ L) {x y : W} (h : (H.map f).Adj x y) :
    s(x, y) ∈ L.map (Sym2.map f) := by
  obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj f H x y).1 h
  exact List.mem_map.2 ⟨_, hL u v huv, rfl⟩

def E2s : List (Sym2 (Fin 42)) :=
  E1.map (Sym2.map (copy2 0)) ++ E1.map (Sym2.map (copy2 1)) ++ E1.map (Sym2.map (copy2 2)) ++
    [s(3, 4), s(4, 5), s(3, 5)]

theorem G2_adj_mem {u v : Fin 42} (h : G2.Adj u v) : s(u, v) ∈ E2s := by
  rw [G2, SimpleGraph.sup_adj, SimpleGraph.iSup_adj] at h
  rcases h with ⟨k, hk⟩ | h
  · have := map_adj_mem (copy2 k) (fun a b hab => G1_adj_mem hab) hk
    fin_cases k <;> simp only [E2s, List.mem_append] <;> tauto
  · simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    simp only [E2s, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto

def EGs : List (Sym2 (Fin 166)) :=
  E2s.map (Sym2.map (copyG 0)) ++ E2s.map (Sym2.map (copyG 1)) ++ E2s.map (Sym2.map (copyG 2)) ++
    E2s.map (Sym2.map (copyG 3)) ++
    [s(6, 4), s(4, 7), s(6, 7), s(4, 0), s(0, 1), s(1, 2), s(1, 3), s(2, 3), s(8, 5), s(5, 9), s(8, 9), s(5, 0)]

theorem G_adj_mem {u v : Fin 166} (h : G.Adj u v) : s(u, v) ∈ EGs := by
  rw [G, SimpleGraph.sup_adj, SimpleGraph.iSup_adj] at h
  rcases h with ⟨k, hk⟩ | h
  · have := map_adj_mem (copyG k) (fun a b hab => G2_adj_mem hab) hk
    fin_cases k <;> simp only [EGs, List.mem_append] <;> tauto
  · simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    simp only [EGs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto

end SteinbergAux

namespace SteinbergAux
open OPG37357

def toPt (a : ℕ × ℕ) : Point := ((a.1 : ℝ), (a.2 : ℝ))
/-- positive and negative parts of the orientation determinant -/
def oriP (a b c : ℕ × ℕ) : ℕ := b.1 * c.2 + a.1 * b.2 + a.2 * c.1
def oriN (a b c : ℕ × ℕ) : ℕ := b.1 * a.2 + a.1 * c.2 + b.2 * c.1
def rori (a b x : Point) : ℝ := (b.1 - a.1) * (x.2 - a.2) - (b.2 - a.2) * (x.1 - a.1)

theorem rori_cast (a b c : ℕ × ℕ) :
    rori (toPt a) (toPt b) (toPt c) = (oriP a b c : ℝ) - (oriN a b c : ℝ) := by
  simp only [rori, oriP, oriN, toPt]; push_cast; ring

theorem rori_seg_zero {a b x : Point} (h : x ∈ closedSegment a b) : rori a b x = 0 := by
  obtain ⟨t, -, -, rfl⟩ := h
  simp only [rori, affine2]; ring

theorem rori_seg {a b c d x : Point} (h : x ∈ closedSegment c d) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ rori a b x = (1 - t) * rori a b c + t * rori a b d := by
  obtain ⟨t, h0, h1, rfl⟩ := h
  exact ⟨t, h0, h1, by simp only [rori, affine2]; ring⟩

theorem comb_pos {p q t : ℝ} (hp : 0 < p) (hq : 0 < q) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 < (1 - t) * p + t * q := by
  rcases eq_or_lt_of_le h1 with rfl | h
  · linarith
  · have := mul_pos (sub_pos.2 h) hp
    have := mul_nonneg h0 hq.le
    linarith

theorem seg_comp {a b x : Point} (h : x ∈ closedSegment a b) :
    (x.1 ≤ a.1 ∨ x.1 ≤ b.1) ∧ (a.1 ≤ x.1 ∨ b.1 ≤ x.1) ∧
    (x.2 ≤ a.2 ∨ x.2 ≤ b.2) ∧ (a.2 ≤ x.2 ∨ b.2 ≤ x.2) := by
  obtain ⟨t, h0, h1, rfl⟩ := h
  simp only [affine2]
  have h1' : 0 ≤ 1 - t := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases le_total a.1 b.1 with hab | hab
    · right; nlinarith [mul_le_mul_of_nonneg_left hab h1']
    · left; nlinarith [mul_le_mul_of_nonneg_left hab h0]
  · rcases le_total a.1 b.1 with hab | hab
    · left; nlinarith [mul_le_mul_of_nonneg_left hab h0]
    · right; nlinarith [mul_le_mul_of_nonneg_left hab h1']
  · rcases le_total a.2 b.2 with hab | hab
    · right; nlinarith [mul_le_mul_of_nonneg_left hab h1']
    · left; nlinarith [mul_le_mul_of_nonneg_left hab h0]
  · rcases le_total a.2 b.2 with hab | hab
    · left; nlinarith [mul_le_mul_of_nonneg_left hab h0]
    · right; nlinarith [mul_le_mul_of_nonneg_left hab h1']

theorem seg_symm (a b : Point) : closedSegment a b = closedSegment b a := by
  have key : ∀ a b : Point, closedSegment a b ⊆ closedSegment b a := by
    intro a b x ⟨t, h0, h1, hx⟩
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    rw [hx]; simp only [affine2, Prod.mk.injEq]; constructor <;> ring
  exact Set.Subset.antisymm (key a b) (key b a)

/-- `p` avoids the segment `ab` (bounding box first, then orientation). -/
def offB (p a b : ℕ × ℕ) : Bool :=
  (Nat.blt p.1 a.1 && Nat.blt p.1 b.1) || (Nat.blt b.1 p.1 && Nat.blt a.1 p.1) ||
    (Nat.blt p.2 a.2 && Nat.blt p.2 b.2) || (Nat.blt a.2 p.2 && Nat.blt b.2 p.2) ||
    !(Nat.beq (oriP a b p) (oriN a b p))

theorem offB_sound {p a b : ℕ × ℕ} (h : offB p a b = true) :
    toPt p ∉ closedSegment (toPt a) (toPt b) := by
  intro hx
  have hz := rori_seg_zero hx
  have hc := seg_comp hx
  simp only [toPt] at hc
  simp only [offB, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  rcases h with ((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | h)
  · have h1' : (p.1 : ℝ) < a.1 := by exact_mod_cast h1
    have h2' : (p.1 : ℝ) < b.1 := by exact_mod_cast h2
    rcases hc.2.1 with h | h <;> linarith
  · have h1' : (b.1 : ℝ) < p.1 := by exact_mod_cast h1
    have h2' : (a.1 : ℝ) < p.1 := by exact_mod_cast h2
    rcases hc.1 with h | h <;> linarith
  · have h1' : (p.2 : ℝ) < a.2 := by exact_mod_cast h1
    have h2' : (p.2 : ℝ) < b.2 := by exact_mod_cast h2
    rcases hc.2.2.2 with h | h <;> linarith
  · have h1' : (a.2 : ℝ) < p.2 := by exact_mod_cast h1
    have h2' : (b.2 : ℝ) < p.2 := by exact_mod_cast h2
    rcases hc.2.2.1 with h | h <;> linarith
  · rw [rori_cast] at hz
    have h' : oriP a b p = oriN a b p := by exact_mod_cast (sub_eq_zero.1 hz)
    have h2 : Nat.beq (oriP a b p) (oriN a b p) = true := by simpa only [Nat.beq_eq] using h'
    rw [h2] at h
    exact Bool.noConfusion h

def ltx (a b c d : ℕ × ℕ) : Bool :=
  Nat.blt b.1 c.1 && Nat.blt a.1 c.1 && Nat.blt a.1 d.1 && Nat.blt b.1 d.1
def lty (a b c d : ℕ × ℕ) : Bool :=
  Nat.blt a.2 c.2 && Nat.blt a.2 d.2 && Nat.blt b.2 c.2 && Nat.blt b.2 d.2
def sideB (a b c d : ℕ × ℕ) : Bool :=
  (Nat.blt (oriN a b c) (oriP a b c) && Nat.blt (oriN a b d) (oriP a b d)) ||
    (Nat.blt (oriP a b c) (oriN a b c) && Nat.blt (oriP a b d) (oriN a b d))

def sepB (a b c d : ℕ × ℕ) : Bool :=
  ltx a b c d || ltx c d a b || lty a b c d || lty c d a b || sideB a b c d || sideB c d a b

theorem ltx_sound {a b c d : ℕ × ℕ} (h : ltx a b c d = true) :
    Disjoint (closedSegment (toPt a) (toPt b)) (closedSegment (toPt c) (toPt d)) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have h1 := (seg_comp hx).1
  have h2 := (seg_comp hy).2.1
  simp only [ltx, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨hc, ha⟩, hb⟩, hd⟩ := h
  simp only [toPt] at h1 h2
  have ha' : (a.1 : ℝ) < c.1 := by exact_mod_cast ha
  have hb' : (a.1 : ℝ) < d.1 := by exact_mod_cast hb
  have hc' : (b.1 : ℝ) < c.1 := by exact_mod_cast hc
  have hd' : (b.1 : ℝ) < d.1 := by exact_mod_cast hd
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> linarith

theorem lty_sound {a b c d : ℕ × ℕ} (h : lty a b c d = true) :
    Disjoint (closedSegment (toPt a) (toPt b)) (closedSegment (toPt c) (toPt d)) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have h1 := (seg_comp hx).2.2.1
  have h2 := (seg_comp hy).2.2.2
  simp only [lty, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := h
  simp only [toPt] at h1 h2
  have ha' : (a.2 : ℝ) < c.2 := by exact_mod_cast ha
  have hb' : (a.2 : ℝ) < d.2 := by exact_mod_cast hb
  have hc' : (b.2 : ℝ) < c.2 := by exact_mod_cast hc
  have hd' : (b.2 : ℝ) < d.2 := by exact_mod_cast hd
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> linarith

theorem sideB_sound {a b c d : ℕ × ℕ} (h : sideB a b c d = true) :
    Disjoint (closedSegment (toPt a) (toPt b)) (closedSegment (toPt c) (toPt d)) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hz := rori_seg_zero hx
  obtain ⟨t, h0, h1, ht⟩ := rori_seg (a := toPt a) (b := toPt b) hy
  rw [hz, rori_cast, rori_cast] at ht
  simp only [sideB, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
  rcases h with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · have hp' : (oriN a b c : ℝ) < oriP a b c := by exact_mod_cast hp
    have hq' : (oriN a b d : ℝ) < oriP a b d := by exact_mod_cast hq
    have := comb_pos (sub_pos.2 hp') (sub_pos.2 hq') h0 h1
    linarith
  · have hp' : (oriP a b c : ℝ) < oriN a b c := by exact_mod_cast hp
    have hq' : (oriP a b d : ℝ) < oriN a b d := by exact_mod_cast hq
    have := comb_pos (sub_pos.2 hp') (sub_pos.2 hq') h0 h1
    linarith

theorem sepB_sound {a b c d : ℕ × ℕ} (h : sepB a b c d = true) :
    Disjoint (closedSegment (toPt a) (toPt b)) (closedSegment (toPt c) (toPt d)) := by
  simp only [sepB, Bool.or_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · exact ltx_sound h
  · exact (ltx_sound h).symm
  · exact lty_sound h
  · exact (lty_sound h).symm
  · exact sideB_sound h
  · exact (sideB_sound h).symm

abbrev Q := (ℕ × ℕ) × (ℕ × ℕ)

/-- the meaning of a pair check: an x-coordinate is shared, or the segments are disjoint -/
def Sem (e f : Q) : Prop :=
  (e.1.1 = f.1.1 ∨ e.1.1 = f.2.1 ∨ e.2.1 = f.1.1 ∨ e.2.1 = f.2.1) ∨
    Disjoint (closedSegment (toPt e.1) (toPt e.2)) (closedSegment (toPt f.1) (toPt f.2))

theorem sem_symm {e f : Q} (h : Sem e f) : Sem f e := by
  rcases h with (h | h | h | h) | h
  · exact Or.inl (Or.inl h.symm)
  · exact Or.inl (Or.inr (Or.inr (Or.inl h.symm)))
  · exact Or.inl (Or.inr (Or.inl h.symm))
  · exact Or.inl (Or.inr (Or.inr (Or.inr h.symm)))
  · exact Or.inr h.symm

def pairS (e f : Q) : Bool :=
  Nat.beq e.1.1 f.1.1 || Nat.beq e.1.1 f.2.1 || Nat.beq e.2.1 f.1.1 || Nat.beq e.2.1 f.2.1 ||
    sepB e.1 e.2 f.1 f.2

theorem pairS_sem {e f : Q} (h : pairS e f = true) : Sem e f := by
  simp only [pairS, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with ((((h | h) | h) | h) | h)
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inr (sepB_sound h)

/-! Kernel-friendly merge sort with fuel (only its permutation property is proved; sortedness of the
result is checked by `sortedB`). -/

def mergeF {α : Type} (key : α → ℕ) : ℕ → List α → List α → List α
  | 0, as, bs => as ++ bs
  | _ + 1, [], bs => bs
  | _ + 1, a :: as, [] => a :: as
  | n + 1, a :: as, b :: bs =>
    cond (Nat.ble (key a) (key b)) (a :: mergeF key n as (b :: bs)) (b :: mergeF key n (a :: as) bs)

theorem mergeF_perm {α : Type} (key : α → ℕ) :
    ∀ (n : ℕ) (as bs : List α), (mergeF key n as bs).Perm (as ++ bs)
  | 0, as, bs => List.Perm.refl _
  | _ + 1, [], bs => List.Perm.refl _
  | _ + 1, a :: as, [] => by simp only [mergeF, List.append_nil]; exact List.Perm.refl _
  | n + 1, a :: as, b :: bs => by
    simp only [mergeF]
    cases Nat.ble (key a) (key b)
    · exact ((mergeF_perm key n (a :: as) bs).cons b).trans List.perm_middle.symm
    · exact (mergeF_perm key n as (b :: bs)).cons a

def msortF {α : Type} (key : α → ℕ) : ℕ → List α → List α
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, [a] => [a]
  | n + 1, a :: b :: rest =>
    mergeF key (rest.length + 2) (msortF key n ((a :: b :: rest).take ((rest.length + 2) / 2)))
      (msortF key n ((a :: b :: rest).drop ((rest.length + 2) / 2)))

theorem msortF_perm {α : Type} (key : α → ℕ) : ∀ (n : ℕ) (l : List α), (msortF key n l).Perm l
  | 0, l => List.Perm.refl l
  | _ + 1, [] => List.Perm.refl _
  | _ + 1, [_] => List.Perm.refl _
  | n + 1, a :: b :: rest => by
    simp only [msortF]
    refine (mergeF_perm key _ _ _).trans ?_
    have h := (msortF_perm key n (List.take ((rest.length + 2) / 2) (a :: b :: rest))).append
      (msortF_perm key n (List.drop ((rest.length + 2) / 2) (a :: b :: rest)))
    rw [List.take_append_drop] at h
    exact h

def sortedB {α : Type} (key : α → ℕ) : List α → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => Nat.blt (key a) (key b) && sortedB key (b :: l)

def sortedLE {α : Type} (key : α → ℕ) : List α → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => Nat.ble (key a) (key b) && sortedLE key (b :: l)

theorem sortedB_pw {α : Type} (key : α → ℕ) :
    ∀ l : List α, sortedB key l = true → l.Pairwise (fun x y => key x < key y)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ a
  | a :: b :: l, h => by
    simp only [sortedB, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := sortedB_pw key (b :: l) h.2
    refine List.Pairwise.cons ?_ ih
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

theorem sortedLE_pw {α : Type} (key : α → ℕ) :
    ∀ l : List α, sortedLE key l = true → l.Pairwise (fun x y => key x ≤ key y)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ a
  | a :: b :: l, h => by
    simp only [sortedLE, Bool.and_eq_true, Nat.ble_eq] at h
    have ih := sortedLE_pw key (b :: l) h.2
    refine List.Pairwise.cons ?_ ih
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact le_trans h.1 (List.rel_of_pairwise_cons ih hc)

/-! Edge sweep: edges sorted by left x; `e` is compared only with edges starting left of its right end. -/

def scanE (e : Q) : List Q → Bool
  | [] => true
  | f :: fs => Nat.blt e.2.1 f.1.1 || (pairS e f && scanE e fs)

def chkES : List Q → Bool
  | [] => true
  | e :: rest => scanE e rest && chkES rest

def orientB (E : List Q) : Bool := E.all fun q => Nat.ble q.1.1 q.2.1

theorem ltx_of {e g : Q} (h1 : e.1.1 ≤ e.2.1) (h2 : e.2.1 < g.1.1) (h3 : g.1.1 ≤ g.2.1) :
    ltx e.1 e.2 g.1 g.2 = true := by
  simp only [ltx, Bool.and_eq_true, Nat.blt_eq]
  omega

theorem scanE_sound (e : Q) (he : e.1.1 ≤ e.2.1) :
    ∀ l : List Q, l.Pairwise (fun x y => x.1.1 ≤ y.1.1) → (∀ g ∈ l, g.1.1 ≤ g.2.1) →
      scanE e l = true → ∀ f ∈ l, Sem e f
  | [], _, _, _, f, hf => by simp at hf
  | f :: fs, hs, ho, h, g, hg => by
    simp only [scanE, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · have hfg : f.1.1 ≤ g.1.1 := by
        rcases List.mem_cons.1 hg with rfl | hg'
        · exact le_refl _
        · exact List.rel_of_pairwise_cons hs hg'
      exact Or.inr (ltx_sound (ltx_of he (lt_of_lt_of_le h hfg) (ho g hg)))
    · rcases List.mem_cons.1 hg with rfl | hg'
      · exact pairS_sem h1
      · exact scanE_sound e he fs (List.Pairwise.of_cons hs)
          (fun x hx => ho x (List.mem_cons_of_mem _ hx)) h2 g hg'

theorem chkES_sound : ∀ l : List Q, l.Pairwise (fun x y => x.1.1 ≤ y.1.1) →
    (∀ g ∈ l, g.1.1 ≤ g.2.1) → chkES l = true → ∀ e ∈ l, ∀ f ∈ l, Sem e f
  | [], _, _, _, e, he, _, _ => by simp at he
  | x :: rest, hs, ho, h, e, he, f, hf => by
    simp only [chkES, Bool.and_eq_true] at h
    have hs' := List.Pairwise.of_cons hs
    have ho' : ∀ g ∈ rest, g.1.1 ≤ g.2.1 := fun g hg => ho g (List.mem_cons_of_mem _ hg)
    have hx := scanE_sound x (ho x List.mem_cons_self) rest hs' ho' h.1
    rcases List.mem_cons.1 he with rfl | he'
    · rcases List.mem_cons.1 hf with rfl | hf'
      · exact Or.inl (Or.inl rfl)
      · exact hx f hf'
    · rcases List.mem_cons.1 hf with rfl | hf'
      · exact sem_symm (hx e he')
      · exact chkES_sound rest hs' ho' h.2 e he' f hf'

/-! Vertex sweep: points sorted by x; for each edge only the points strictly inside its x-range are tested. -/

def scanV (e : Q) : List (ℕ × ℕ) → Bool
  | [] => true
  | p :: ps => Nat.ble e.2.1 p.1 || (offB p e.1 e.2 && scanV e ps)

def chkVS : ℕ → List Q → List (ℕ × ℕ) → Bool
  | 0, _, _ => false
  | _ + 1, [], _ => true
  | _ + 1, _ :: _, [] => true
  | n + 1, e :: es, p :: ps =>
    cond (Nat.ble p.1 e.1.1) (chkVS n (e :: es) ps) (scanV e (p :: ps) && chkVS n es (p :: ps))

theorem offB_right {p a b : ℕ × ℕ} (h1 : b.1 < p.1) (h2 : a.1 < p.1) : offB p a b = true := by
  have h1' : Nat.blt b.1 p.1 = true := Nat.blt_eq.mpr h1
  have h2' : Nat.blt a.1 p.1 = true := Nat.blt_eq.mpr h2
  simp only [offB, h1', h2', Bool.and_self, Bool.true_or, Bool.or_true]

theorem offB_left {p a b : ℕ × ℕ} (h1 : p.1 < a.1) (h2 : p.1 < b.1) : offB p a b = true := by
  have h1' : Nat.blt p.1 a.1 = true := Nat.blt_eq.mpr h1
  have h2' : Nat.blt p.1 b.1 = true := Nat.blt_eq.mpr h2
  simp only [offB, h1', h2', Bool.and_self, Bool.true_or]

theorem scanV_sound (e : Q) (he : e.1.1 ≤ e.2.1) :
    ∀ l : List (ℕ × ℕ), l.Pairwise (fun x y => x.1 ≤ y.1) → scanV e l = true →
      ∀ q ∈ l, q.1 ≠ e.2.1 → offB q e.1 e.2 = true
  | [], _, _, q, hq, _ => by simp at hq
  | p :: ps, hs, h, q, hq, hne => by
    simp only [scanV, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · have hpq : p.1 ≤ q.1 := by
        rcases List.mem_cons.1 hq with rfl | hq'
        · exact le_refl _
        · exact List.rel_of_pairwise_cons hs hq'
      exact offB_right (by omega) (by omega)
    · rcases List.mem_cons.1 hq with rfl | hq'
      · exact h1
      · exact scanV_sound e he ps (List.Pairwise.of_cons hs) h2 q hq' hne

theorem chkVS_sound : ∀ (n : ℕ) (es : List Q) (ps : List (ℕ × ℕ)),
    es.Pairwise (fun x y => x.1.1 ≤ y.1.1) → (∀ g ∈ es, g.1.1 ≤ g.2.1) →
    ps.Pairwise (fun x y => x.1 ≤ y.1) → chkVS n es ps = true →
    ∀ e ∈ es, ∀ q ∈ ps, e.1.1 < q.1 → q.1 ≠ e.2.1 → offB q e.1 e.2 = true
  | 0, _, _, _, _, _, h, _, _, _, _, _, _ => by simp [chkVS] at h
  | _ + 1, [], _, _, _, _, _, e, he, _, _, _, _ => by simp at he
  | _ + 1, _ :: _, [], _, _, _, _, _, _, q, hq, _, _ => by simp at hq
  | n + 1, x :: es, p :: ps, hes, ho, hps, h, e, he, q, hq, hlt, hne => by
    simp only [chkVS] at h
    cases hb : Nat.ble p.1 x.1.1
    · rw [hb] at h
      simp only [cond, Bool.and_eq_true] at h
      rcases List.mem_cons.1 he with rfl | he'
      · exact scanV_sound e (ho e List.mem_cons_self) (p :: ps) hps h.1 q hq hne
      · exact chkVS_sound n es (p :: ps) (List.Pairwise.of_cons hes)
          (fun g hg => ho g (List.mem_cons_of_mem _ hg)) hps h.2 e he' q hq hlt hne
    · rw [hb] at h
      simp only [cond] at h
      have hpx : p.1 ≤ x.1.1 := Nat.ble_eq.mp hb
      rcases List.mem_cons.1 hq with rfl | hq'
      · have hxe : x.1.1 ≤ e.1.1 := by
          rcases List.mem_cons.1 he with rfl | he'
          · exact le_refl _
          · exact List.rel_of_pairwise_cons hes he'
        omega
      · exact chkVS_sound n (x :: es) ps hes ho (List.Pairwise.of_cons hps) h e he q hq' hlt hne

/-! Points of the drawing stored in a binary tree (cheap kernel lookup by the bits of the index). -/

inductive PT where
  | leaf (p : ℕ × ℕ)
  | node (l r : PT)

def PT.get : PT → ℕ → ℕ × ℕ
  | leaf p, _ => p
  | node l r, i => cond (Nat.beq (i % 2) 0) (l.get (i / 2)) (r.get (i / 2))

theorem planar_of_checks {n : ℕ} (H : SimpleGraph (Fin n)) (T : PT) (E ES : List Q)
    (PS : List (ℕ × ℕ))
    (hE : ∀ u v, H.Adj u v → (T.get u.val, T.get v.val) ∈ E ∨ (T.get v.val, T.get u.val) ∈ E)
    (hES : msortF (fun q : Q => q.1.1) 12 E = ES)
    (hPS : msortF Prod.fst 12 ((List.range n).map T.get) = PS)
    (hsE : sortedLE (fun q : Q => q.1.1) ES = true) (hoE : orientB ES = true)
    (hsP : sortedB Prod.fst PS = true)
    (hX : chkES ES = true) (hV : chkVS 1000 ES PS = true) : IsPlanar H := by
  have permE : ∀ e ∈ E, e ∈ ES := fun e he => by
    rw [← hES]; exact (msortF_perm _ 12 E).symm.subset he
  have permP : ∀ p ∈ (List.range n).map T.get, p ∈ PS := fun p hp => by
    rw [← hPS]; exact (msortF_perm _ 12 _).symm.subset hp
  have pwE := sortedLE_pw _ ES hsE
  have hoE' : ∀ g ∈ ES, g.1.1 ≤ g.2.1 := fun g hg => Nat.ble_eq.mp (List.all_eq_true.1 hoE g hg)
  have pwP := sortedB_pw _ PS hsP
  have pwP' : PS.Pairwise (fun x y => x.1 ≤ y.1) := pwP.imp (fun h => le_of_lt h)
  -- injectivity of the x-coordinate
  have hnd : ((List.range n).map (fun i => (T.get i).1)).Nodup := by
    have h1 : (PS.map Prod.fst).Nodup :=
      List.Pairwise.map _ (fun a b (h : a.1 < b.1) => ne_of_lt h) pwP
    rw [← hPS] at h1
    have h2 := ((msortF_perm Prod.fst 12 ((List.range n).map T.get)).map Prod.fst).nodup_iff.1 h1
    rw [List.map_map] at h2
    exact h2
  have hinj : ∀ u v : Fin n, (T.get u.val).1 = (T.get v.val).1 → u = v := by
    intro u v h
    exact Fin.ext (List.inj_on_of_nodup_map hnd (List.mem_range.2 u.isLt)
      (List.mem_range.2 v.isLt) h)
  have hpts : ∀ v : Fin n, T.get v.val ∈ PS := fun v =>
    permP _ (List.mem_map.2 ⟨v.val, List.mem_range.2 v.isLt, rfl⟩)
  have hX' := chkES_sound ES pwE hoE' hX
  have hV' := chkVS_sound 1000 ES PS pwE hoE' pwP' hV
  have segE : ∀ u v, H.Adj u v → ∃ e ∈ ES, closedSegment (toPt (T.get u.val)) (toPt (T.get v.val)) =
      closedSegment (toPt e.1) (toPt e.2) ∧
      (e.1.1 = (T.get u.val).1 ∨ e.1.1 = (T.get v.val).1) ∧
      (e.2.1 = (T.get u.val).1 ∨ e.2.1 = (T.get v.val).1) := by
    intro u v huv
    rcases hE u v huv with h | h
    · exact ⟨_, permE _ h, rfl, Or.inl rfl, Or.inr rfl⟩
    · exact ⟨_, permE _ h, seg_symm _ _, Or.inr rfl, Or.inl rfl⟩
  refine ⟨fun v => toPt (T.get v.val), ?_, ?_, ?_⟩
  · intro u v huv
    apply hinj
    simp only [toPt, Prod.mk.injEq, Nat.cast_inj] at huv
    exact huv.1
  · intro a b v hab hva hvb
    obtain ⟨e, he, hseg, h1e, h2e⟩ := segE a b hab
    show toPt (T.get v.val) ∉ _
    rw [hseg]
    have hne : ∀ s : ℕ, (s = (T.get a.val).1 ∨ s = (T.get b.val).1) → (T.get v.val).1 ≠ s := by
      rintro s (rfl | rfl) h
      · exact hva (hinj _ _ h)
      · exact hvb (hinj _ _ h)
    have n1 := hne _ h1e
    have n2 := hne _ h2e
    apply offB_sound
    rcases Nat.lt_or_gt_of_ne n1 with hl | hl
    · exact offB_left hl (lt_of_lt_of_le hl (hoE' e he))
    · exact hV' e he _ (hpts v) hl n2
  · intro a b c d hab hcd hac had hbc hbd
    obtain ⟨e, he, hseg, h1e, h2e⟩ := segE a b hab
    obtain ⟨f, hf, hseg', h1f, h2f⟩ := segE c d hcd
    show Disjoint (closedSegment (toPt (T.get a.val)) (toPt (T.get b.val)))
      (closedSegment (toPt (T.get c.val)) (toPt (T.get d.val)))
    rw [hseg, hseg']
    have hne : ∀ s t : ℕ, (s = (T.get a.val).1 ∨ s = (T.get b.val).1) →
        (t = (T.get c.val).1 ∨ t = (T.get d.val).1) → s ≠ t := by
      rintro s t (rfl | rfl) (rfl | rfl) h
      · exact hac (hinj _ _ h)
      · exact had (hinj _ _ h)
      · exact hbc (hinj _ _ h)
      · exact hbd (hinj _ _ h)
    rcases hX' e he f hf with (h | h | h | h) | h
    · exact absurd h (hne _ _ h1e h1f)
    · exact absurd h (hne _ _ h1e h2f)
    · exact absurd h (hne _ _ h2e h1f)
    · exact absurd h (hne _ _ h2e h2f)
    · exact h

end SteinbergAux

namespace SteinbergAux

def TG : PT := PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.leaf (8454131, 5549494)) (PT.leaf (8182474, 5716196))) (PT.leaf (8380190, 8235486))) (PT.node (PT.node (PT.leaf (5430717, 3754592)) (PT.leaf (8107987, 5761904))) (PT.leaf (8030230, 5805411)))) (PT.node (PT.node (PT.node (PT.leaf (6556227, 5231279)) (PT.leaf (8304128, 5641494))) (PT.leaf (8081664, 13554607))) (PT.node (PT.leaf (3782194, 3270727)) (PT.leaf (8312388, 5635718))))) (PT.node (PT.node (PT.node (PT.node (PT.leaf (8244408, 5677609)) (PT.leaf (8194666, 5708809))) (PT.leaf (8275572, 11899217))) (PT.node (PT.leaf (3762200, 3135354)) (PT.leaf (8363404, 5604581)))) (PT.node (PT.node (PT.node (PT.leaf (7035810, 5531453)) (PT.leaf (8318462, 5632670))) (PT.leaf (8179190, 5714995))) (PT.node (PT.leaf (7481275, 6993706)) (PT.leaf (8176621, 5719148)))))) (PT.node (PT.node (PT.node (PT.node (PT.node (PT.leaf (16777216, 0)) (PT.leaf (8235135, 5683930))) (PT.leaf (8308401, 13405323))) (PT.node (PT.node (PT.leaf (4254186, 2959967)) (PT.leaf (8112533, 5759127))) (PT.leaf (8132507, 5739268)))) (PT.node (PT.node (PT.node (PT.leaf (7131725, 5335973)) (PT.leaf (8328018, 5626787))) (PT.leaf (7941790, 12118979))) (PT.node (PT.leaf (8122345, 6236757)) (PT.leaf (8036925, 5805066))))) (PT.node (PT.node (PT.node (PT.node (PT.leaf (4959816, 3735671)) (PT.leaf (8210853, 5698857))) (PT.leaf (7430786, 8860575))) (PT.node (PT.leaf (4795222, 4173003)) (PT.leaf (8278396, 5656650)))) (PT.node (PT.node (PT.node (PT.leaf (4064817, 2936111)) (PT.leaf (8119353, 5754960))) (PT.leaf (8255857, 5663898))) (PT.node (PT.leaf (7669917, 7204372)) (PT.leaf (8111216, 5759254))))))) (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.leaf (7058706, 6468243)) (PT.leaf (8321685, 5630813))) (PT.leaf (8229965, 9729978))) (PT.node (PT.node (PT.leaf (4448595, 3065259)) (PT.leaf (8159907, 5729995))) (PT.leaf (8200561, 5698680)))) (PT.node (PT.node (PT.node (PT.leaf (7101347, 6006228)) (PT.leaf (8272940, 5660540))) (PT.leaf (7763024, 11295429))) (PT.node (PT.leaf (7911743, 10058962)) (PT.leaf (8301045, 5642591))))) (PT.node (PT.node (PT.node (PT.node (PT.leaf (5766123, 4480332)) (PT.leaf (8140583, 5742005))) (PT.leaf (8300746, 10438186))) (PT.node (PT.leaf (2019392, 1759429)) (PT.leaf (8267009, 5663132)))) (PT.node (PT.node (PT.node (PT.leaf (6373719, 4317795)) (PT.leaf (8026220, 5812191))) (PT.leaf (8227275, 5686873))) (PT.node (PT.leaf (7790489, 6589198)) (PT.leaf (8084651, 5775491)))))) (PT.node (PT.node (PT.node (PT.node (PT.node (PT.leaf (0, 0)) (PT.leaf (8075073, 5782243))) (PT.leaf (8347933, 10910325))) (PT.node (PT.leaf (5505841, 4889207)) (PT.leaf (8129883, 5742198)))) (PT.node (PT.node (PT.node (PT.leaf (7169296, 5586412)) (PT.leaf (8285469, 5652889))) (PT.leaf (7753325, 10798608))) (PT.node (PT.leaf (7941558, 7494338)) (PT.leaf (8153171, 5733038))))) (PT.node (PT.node (PT.node (PT.node (PT.leaf (7535502, 5409129)) (PT.leaf (8383367, 5592874))) (PT.leaf (7738777, 10053377))) (PT.node (PT.leaf (3913821, 3417354)) (PT.leaf (8323712, 5628689)))) (PT.node (PT.node (PT.node (PT.leaf (2289940, 1581300)) (PT.leaf (8187646, 5712918))) (PT.leaf (8130423, 5744133))) (PT.node (PT.leaf (7850916, 6951254)) (PT.leaf (8123491, 5751624)))))))) (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.leaf (7885605, 5845689)) (PT.leaf (8242196, 5679521))) (PT.leaf (8338506, 8246640))) (PT.node (PT.node (PT.leaf (3602797, 2554702)) (PT.leaf (8091120, 5772304))) (PT.leaf (8113322, 5748891)))) (PT.node (PT.node (PT.node (PT.leaf (6885535, 5807271)) (PT.leaf (8276183, 5658611))) (PT.leaf (8077765, 13875751))) (PT.node (PT.leaf (7919198, 8781557)) (PT.leaf (8312382, 5635666))))) (PT.node (PT.node (PT.node (PT.node (PT.leaf (8247341, 5676163)) (PT.leaf (8254082, 5672308))) (PT.leaf (8315294, 10797867))) (PT.node (PT.leaf (2262652, 1917312)) (PT.leaf (8295350, 5645819)))) (PT.node (PT.node (PT.node (PT.leaf (6402761, 4281053)) (PT.leaf (8307284, 5639517))) (PT.leaf (8167553, 5723548))) (PT.node (PT.leaf (7443490, 6683716)) (PT.leaf (8103704, 5764015)))))) (PT.node (PT.node (PT.node (PT.node (PT.node (PT.leaf (8315293, 5634422)) (PT.leaf (8164198, 5727490))) (PT.leaf (8348314, 13697621))) (PT.node (PT.node (PT.leaf (5453357, 4906142)) (PT.leaf (8129730, 5748549))) (PT.leaf (8154317, 5726715)))) (PT.node (PT.node (PT.node (PT.leaf (6825857, 5523334)) (PT.leaf (8330181, 5625501))) (PT.leaf (7780520, 11149963))) (PT.node (PT.leaf (8122416, 6571578)) (PT.leaf (8110575, 5759286))))) (PT.node (PT.node (PT.node (PT.node (PT.leaf (7808760, 5636870)) (PT.leaf (8182478, 5716282))) (PT.leaf (7470628, 8818052))) (PT.node (PT.leaf (3269015, 2774464)) (PT.leaf (8323736, 5628898)))) (PT.node (PT.node (PT.node (PT.leaf (2489389, 1768028)) (PT.leaf (8162345, 5728517))) (PT.leaf (8191507, 5705427))) (PT.node (PT.leaf (7805631, 6847123)) (PT.leaf (8106453, 5762123))))))) (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.leaf (7929199, 5871844)) (PT.leaf (8316258, 5634136))) (PT.leaf (8221110, 11247238))) (PT.node (PT.node (PT.leaf (4711166, 3259939)) (PT.leaf (8116750, 5756527))) (PT.leaf (8102825, 5760610)))) (PT.node (PT.node (PT.node (PT.leaf (7359801, 5743170)) (PT.leaf (8282766, 5654497))) (PT.leaf (7654244, 9890012))) (PT.node (PT.leaf (8070504, 9954434)) (PT.leaf (8023276, 5813641))))) (PT.node (PT.node (PT.node (PT.node (PT.leaf (4801055, 3840200)) (PT.leaf (8195999, 5707983))) (PT.leaf (8297204, 11045090))) (PT.node (PT.leaf (3795523, 3360975)) (PT.leaf (8267045, 5663445)))) (PT.node (PT.node (PT.node (PT.leaf (5207267, 3686043)) (PT.leaf (8041473, 5802825))) (PT.leaf (8177229, 5701993))) (PT.node (PT.leaf (7971630, 7005723)) (PT.leaf (8152804, 5733495)))))) (PT.node (PT.node (PT.node (PT.node (PT.node (PT.leaf (8388608, 16777216)) (PT.leaf (8066313, 5787632))) (PT.leaf (8289739, 9471601))) (PT.node (PT.leaf (4716080, 4009441)) (PT.leaf (8380424, 5594324)))) (PT.node (PT.node (PT.node (PT.leaf (7112277, 5484613)) (PT.leaf (8317922, 5632991))) (PT.leaf (7825212, 11355850))) (PT.node (PT.leaf (7752987, 7618493)) (PT.leaf (8181751, 5715822))))) (PT.node (PT.node (PT.node (PT.node (PT.leaf (6747394, 5114178)) (PT.leaf (8367952, 5602341))) (PT.leaf (7918494, 11446481))) (PT.node (PT.leaf (4163746, 3620361)) (PT.leaf (8278366, 5656389)))) (PT.node (PT.node (PT.node (PT.leaf (4380432, 2975871)) (PT.leaf (8180991, 5716995))) (PT.leaf (8048169, 5795500))) (PT.node (PT.leaf (7775488, 7000916)) (PT.leaf (8206001, 5701784))))))))

def EcG : List Q := [((5766123, 4480332), (6747394, 5114178)), ((5766123, 4480332), (6556227, 5231279)), ((6556227, 5231279), (6747394, 5114178)), ((7535502, 5409129), (8454131, 5549494)), ((7808760, 5636870), (8454131, 5549494)), ((7535502, 5409129), (7808760, 5636870)), ((6885535, 5807271), (7058706, 6468243)), ((7058706, 6468243), (7101347, 6006228)), ((6885535, 5807271), (7101347, 6006228)), ((6747394, 5114178), (7535502, 5409129)), ((7131725, 5335973), (7535502, 5409129)), ((6747394, 5114178), (7131725, 5335973)), ((6556227, 5231279), (6885535, 5807271)), ((6556227, 5231279), (6825857, 5523334)), ((6825857, 5523334), (6885535, 5807271)), ((7359801, 5743170), (7808760, 5636870)), ((7101347, 6006228), (7359801, 5743170)), ((7169296, 5586412), (7359801, 5743170)), ((7112277, 5484613), (7131725, 5335973)), ((6825857, 5523334), (7035810, 5531453)), ((7112277, 5484613), (7169296, 5586412)), ((7035810, 5531453), (7112277, 5484613)), ((7035810, 5531453), (7169296, 5586412)), ((4959816, 3735671), (5207267, 3686043)), ((4064817, 2936111), (4959816, 3735671)), ((4064817, 2936111), (5207267, 3686043)), ((6373719, 4317795), (8454131, 5549494)), ((6402761, 4281053), (8454131, 5549494)), ((6373719, 4317795), (6402761, 4281053)), ((0, 0), (2489389, 1768028)), ((0, 0), (2289940, 1581300)), ((2289940, 1581300), (2489389, 1768028)), ((5207267, 3686043), (6373719, 4317795)), ((5430717, 3754592), (6373719, 4317795)), ((5207267, 3686043), (5430717, 3754592)), ((2489389, 1768028), (4064817, 2936111)), ((3602797, 2554702), (4064817, 2936111)), ((2489389, 1768028), (3602797, 2554702)), ((4380432, 2975871), (6402761, 4281053)), ((2289940, 1581300), (4380432, 2975871)), ((4380432, 2975871), (4448595, 3065259)), ((4711166, 3259939), (5430717, 3754592)), ((3602797, 2554702), (4254186, 2959967)), ((4448595, 3065259), (4711166, 3259939)), ((4254186, 2959967), (4711166, 3259939)), ((4254186, 2959967), (4448595, 3065259)), ((4716080, 4009441), (4801055, 3840200)), ((3762200, 3135354), (4801055, 3840200)), ((3762200, 3135354), (4716080, 4009441)), ((5505841, 4889207), (7058706, 6468243)), ((5453357, 4906142), (7058706, 6468243)), ((5453357, 4906142), (5505841, 4889207)), ((0, 0), (2262652, 1917312)), ((0, 0), (2019392, 1759429)), ((2019392, 1759429), (2262652, 1917312)), ((4716080, 4009441), (5505841, 4889207)), ((4795222, 4173003), (5505841, 4889207)), ((4716080, 4009441), (4795222, 4173003)), ((2262652, 1917312), (3762200, 3135354)), ((3269015, 2774464), (3762200, 3135354)), ((2262652, 1917312), (3269015, 2774464)), ((3795523, 3360975), (5453357, 4906142)), ((2019392, 1759429), (3795523, 3360975)), ((3795523, 3360975), (3913821, 3417354)), ((4163746, 3620361), (4795222, 4173003)), ((3269015, 2774464), (3782194, 3270727)), ((3913821, 3417354), (4163746, 3620361)), ((3782194, 3270727), (4163746, 3620361)), ((3782194, 3270727), (3913821, 3417354)), ((4801055, 3840200), (5766123, 4480332)), ((4801055, 3840200), (4959816, 3735671)), ((4959816, 3735671), (5766123, 4480332)), ((7919198, 8781557), (7941558, 7494338)), ((7752987, 7618493), (7919198, 8781557)), ((7752987, 7618493), (7941558, 7494338)), ((8122416, 6571578), (8454131, 5549494)), ((8122345, 6236757), (8454131, 5549494)), ((8122345, 6236757), (8122416, 6571578)), ((7058706, 6468243), (7481275, 6993706)), ((7058706, 6468243), (7443490, 6683716)), ((7443490, 6683716), (7481275, 6993706)), ((7941558, 7494338), (8122416, 6571578)), ((7971630, 7005723), (8122416, 6571578)), ((7941558, 7494338), (7971630, 7005723)), ((7481275, 6993706), (7752987, 7618493)), ((7669917, 7204372), (7752987, 7618493)), ((7481275, 6993706), (7669917, 7204372)), ((7790489, 6589198), (8122345, 6236757)), ((7443490, 6683716), (7790489, 6589198)), ((7790489, 6589198), (7805631, 6847123)), ((7850916, 6951254), (7971630, 7005723)), ((7669917, 7204372), (7775488, 7000916)), ((7805631, 6847123), (7850916, 6951254)), ((7775488, 7000916), (7850916, 6951254)), ((7775488, 7000916), (7805631, 6847123)), ((8070504, 9954434), (8229965, 9729978)), ((8070504, 9954434), (8221110, 11247238)), ((8221110, 11247238), (8229965, 9729978)), ((8338506, 8246640), (8454131, 5549494)), ((8380190, 8235486), (8454131, 5549494)), ((8338506, 8246640), (8380190, 8235486)), ((8308401, 13405323), (8388608, 16777216)), ((8348314, 13697621), (8388608, 16777216)), ((8308401, 13405323), (8348314, 13697621)), ((8229965, 9729978), (8338506, 8246640)), ((8289739, 9471601), (8338506, 8246640)), ((8229965, 9729978), (8289739, 9471601)), ((8221110, 11247238), (8308401, 13405323)), ((8221110, 11247238), (8275572, 11899217)), ((8275572, 11899217), (8308401, 13405323)), ((8347933, 10910325), (8380190, 8235486)), ((8347933, 10910325), (8348314, 13697621)), ((8315294, 10797867), (8347933, 10910325)), ((8289739, 9471601), (8300746, 10438186)), ((8275572, 11899217), (8297204, 11045090)), ((8300746, 10438186), (8315294, 10797867)), ((8297204, 11045090), (8300746, 10438186)), ((8297204, 11045090), (8315294, 10797867)), ((7738777, 10053377), (7911743, 10058962)), ((7911743, 10058962), (7918494, 11446481)), ((7738777, 10053377), (7918494, 11446481)), ((7058706, 6468243), (7470628, 8818052)), ((7058706, 6468243), (7430786, 8860575)), ((7430786, 8860575), (7470628, 8818052)), ((8081664, 13554607), (8388608, 16777216)), ((8077765, 13875751), (8388608, 16777216)), ((8077765, 13875751), (8081664, 13554607)), ((7470628, 8818052), (7738777, 10053377)), ((7470628, 8818052), (7654244, 9890012)), ((7654244, 9890012), (7738777, 10053377)), ((7918494, 11446481), (8081664, 13554607)), ((7918494, 11446481), (7941790, 12118979)), ((7941790, 12118979), (8081664, 13554607)), ((7430786, 8860575), (7763024, 11295429)), ((7763024, 11295429), (8077765, 13875751)), ((7763024, 11295429), (7780520, 11149963)), ((7654244, 9890012), (7753325, 10798608)), ((7825212, 11355850), (7941790, 12118979)), ((7753325, 10798608), (7780520, 11149963)), ((7753325, 10798608), (7825212, 11355850)), ((7780520, 11149963), (7825212, 11355850)), ((7911743, 10058962), (7919198, 8781557)), ((7911743, 10058962), (8070504, 9954434)), ((7919198, 8781557), (8070504, 9954434)), ((8179190, 5714995), (8191507, 5705427)), ((8130423, 5744133), (8179190, 5714995)), ((8130423, 5744133), (8191507, 5705427)), ((8255857, 5663898), (8454131, 5549494)), ((8177229, 5701993), (8454131, 5549494)), ((8177229, 5701993), (8255857, 5663898)), ((7929199, 5871844), (8048169, 5795500)), ((7929199, 5871844), (8030230, 5805411)), ((8030230, 5805411), (8048169, 5795500)), ((8191507, 5705427), (8255857, 5663898)), ((8200561, 5698680), (8255857, 5663898)), ((8191507, 5705427), (8200561, 5698680)), ((8048169, 5795500), (8130423, 5744133)), ((8102825, 5760610), (8130423, 5744133)), ((8048169, 5795500), (8102825, 5760610)), ((8113322, 5748891), (8177229, 5701993)), ((8030230, 5805411), (8113322, 5748891)), ((8113322, 5748891), (8132507, 5739268)), ((8154317, 5726715), (8200561, 5698680)), ((8102825, 5760610), (8129883, 5742198)), ((8132507, 5739268), (8154317, 5726715)), ((8129883, 5742198), (8154317, 5726715)), ((8129883, 5742198), (8132507, 5739268)), ((8227275, 5686873), (8295350, 5645819)), ((8227275, 5686873), (8267009, 5663132)), ((8267009, 5663132), (8295350, 5645819)), ((8363404, 5604581), (8454131, 5549494)), ((8380424, 5594324), (8454131, 5549494)), ((8363404, 5604581), (8380424, 5594324)), ((8244408, 5677609), (8267045, 5663445)), ((8244408, 5677609), (8278396, 5656650)), ((8267045, 5663445), (8278396, 5656650)), ((8295350, 5645819), (8363404, 5604581)), ((8323712, 5628689), (8363404, 5604581)), ((8295350, 5645819), (8323712, 5628689)), ((8267009, 5663132), (8267045, 5663445)), ((8267009, 5663132), (8278366, 5656389)), ((8267045, 5663445), (8278366, 5656389)), ((8323736, 5628898), (8380424, 5594324)), ((8278396, 5656650), (8323736, 5628898)), ((8312388, 5635718), (8323736, 5628898)), ((8312382, 5635666), (8323712, 5628689)), ((8278366, 5656389), (8301045, 5642591)), ((8312382, 5635666), (8312388, 5635718)), ((8301045, 5642591), (8312382, 5635666)), ((8301045, 5642591), (8312388, 5635718)), ((8110575, 5759286), (8167553, 5723548)), ((8153171, 5733038), (8167553, 5723548)), ((8110575, 5759286), (8153171, 5733038)), ((7929199, 5871844), (8036925, 5805066)), ((7929199, 5871844), (8023276, 5813641)), ((8023276, 5813641), (8036925, 5805066)), ((8181751, 5715822), (8244408, 5677609)), ((8176621, 5719148), (8244408, 5677609)), ((8176621, 5719148), (8181751, 5715822)), ((8036925, 5805066), (8110575, 5759286)), ((8036925, 5805066), (8084651, 5775491)), ((8084651, 5775491), (8110575, 5759286)), ((8153171, 5733038), (8181751, 5715822)), ((8152804, 5733495), (8153171, 5733038)), ((8152804, 5733495), (8181751, 5715822)), ((8023276, 5813641), (8103704, 5764015)), ((8103704, 5764015), (8176621, 5719148)), ((8103704, 5764015), (8111216, 5759254)), ((8084651, 5775491), (8106453, 5762123)), ((8123491, 5751624), (8152804, 5733495)), ((8106453, 5762123), (8111216, 5759254)), ((8106453, 5762123), (8123491, 5751624)), ((8111216, 5759254), (8123491, 5751624)), ((8167553, 5723548), (8179190, 5714995)), ((8167553, 5723548), (8227275, 5686873)), ((8179190, 5714995), (8227275, 5686873)), ((8206001, 5701784), (8235135, 5683930)), ((8164198, 5727490), (8206001, 5701784)), ((8164198, 5727490), (8235135, 5683930)), ((8316258, 5634136), (8454131, 5549494)), ((8321685, 5630813), (8454131, 5549494)), ((8316258, 5634136), (8321685, 5630813)), ((7929199, 5871844), (8075073, 5782243)), ((7929199, 5871844), (8066313, 5787632)), ((8066313, 5787632), (8075073, 5782243)), ((8235135, 5683930), (8316258, 5634136)), ((8254082, 5672308), (8316258, 5634136)), ((8235135, 5683930), (8254082, 5672308)), ((8075073, 5782243), (8164198, 5727490)), ((8140583, 5742005), (8164198, 5727490)), ((8075073, 5782243), (8140583, 5742005)), ((8194666, 5708809), (8321685, 5630813)), ((8066313, 5787632), (8194666, 5708809)), ((8194666, 5708809), (8195999, 5707983)), ((8210853, 5698857), (8254082, 5672308)), ((8140583, 5742005), (8182478, 5716282)), ((8195999, 5707983), (8210853, 5698857)), ((8182478, 5716282), (8210853, 5698857)), ((8182478, 5716282), (8195999, 5707983)), ((8242196, 5679521), (8304128, 5641494)), ((8242196, 5679521), (8276183, 5658611)), ((8276183, 5658611), (8304128, 5641494)), ((8367952, 5602341), (8454131, 5549494)), ((8383367, 5592874), (8454131, 5549494)), ((8367952, 5602341), (8383367, 5592874)), ((8247341, 5676163), (8272940, 5660540)), ((8247341, 5676163), (8282766, 5654497)), ((8272940, 5660540), (8282766, 5654497)), ((8304128, 5641494), (8367952, 5602341)), ((8330181, 5625501), (8367952, 5602341)), ((8304128, 5641494), (8330181, 5625501)), ((8272940, 5660540), (8276183, 5658611)), ((8276183, 5658611), (8285469, 5652889)), ((8272940, 5660540), (8285469, 5652889)), ((8328018, 5626787), (8383367, 5592874)), ((8282766, 5654497), (8328018, 5626787)), ((8317922, 5632991), (8328018, 5626787)), ((8318462, 5632670), (8330181, 5625501)), ((8285469, 5652889), (8307284, 5639517)), ((8317922, 5632991), (8318462, 5632670)), ((8307284, 5639517), (8318462, 5632670)), ((8307284, 5639517), (8317922, 5632991)), ((8119353, 5754960), (8182474, 5716196)), ((8162345, 5728517), (8182474, 5716196)), ((8119353, 5754960), (8162345, 5728517)), ((7929199, 5871844), (8041473, 5802825)), ((7929199, 5871844), (8026220, 5812191)), ((8026220, 5812191), (8041473, 5802825)), ((8187646, 5712918), (8247341, 5676163)), ((8180991, 5716995), (8247341, 5676163)), ((8180991, 5716995), (8187646, 5712918)), ((8041473, 5802825), (8119353, 5754960)), ((8041473, 5802825), (8091120, 5772304)), ((8091120, 5772304), (8119353, 5754960)), ((8162345, 5728517), (8187646, 5712918)), ((8159907, 5729995), (8162345, 5728517)), ((8159907, 5729995), (8187646, 5712918)), ((8026220, 5812191), (8107987, 5761904)), ((8107987, 5761904), (8180991, 5716995)), ((8107987, 5761904), (8116750, 5756527)), ((8091120, 5772304), (8112533, 5759127)), ((8129730, 5748549), (8159907, 5729995)), ((8112533, 5759127), (8116750, 5756527)), ((8112533, 5759127), (8129730, 5748549)), ((8116750, 5756527), (8129730, 5748549)), ((8182474, 5716196), (8206001, 5701784)), ((8182474, 5716196), (8242196, 5679521)), ((8206001, 5701784), (8242196, 5679521)), ((0, 0), (16777216, 0)), ((8388608, 16777216), (16777216, 0)), ((0, 0), (8388608, 16777216)), ((8454131, 5549494), (16777216, 0)), ((7885605, 5845689), (8454131, 5549494)), ((7058706, 6468243), (7885605, 5845689)), ((7885605, 5845689), (7929199, 5871844)), ((7058706, 6468243), (7929199, 5871844)), ((8244408, 5677609), (8315293, 5634422)), ((8247341, 5676163), (8315293, 5634422)), ((8244408, 5677609), (8247341, 5676163)), ((8315293, 5634422), (8454131, 5549494))]

def EcSG : List Q := [((0, 0), (2489389, 1768028)), ((0, 0), (2289940, 1581300)), ((0, 0), (2262652, 1917312)), ((0, 0), (2019392, 1759429)), ((0, 0), (16777216, 0)), ((0, 0), (8388608, 16777216)), ((2019392, 1759429), (2262652, 1917312)), ((2019392, 1759429), (3795523, 3360975)), ((2262652, 1917312), (3762200, 3135354)), ((2262652, 1917312), (3269015, 2774464)), ((2289940, 1581300), (2489389, 1768028)), ((2289940, 1581300), (4380432, 2975871)), ((2489389, 1768028), (4064817, 2936111)), ((2489389, 1768028), (3602797, 2554702)), ((3269015, 2774464), (3762200, 3135354)), ((3269015, 2774464), (3782194, 3270727)), ((3602797, 2554702), (4064817, 2936111)), ((3602797, 2554702), (4254186, 2959967)), ((3762200, 3135354), (4801055, 3840200)), ((3762200, 3135354), (4716080, 4009441)), ((3782194, 3270727), (4163746, 3620361)), ((3782194, 3270727), (3913821, 3417354)), ((3795523, 3360975), (5453357, 4906142)), ((3795523, 3360975), (3913821, 3417354)), ((3913821, 3417354), (4163746, 3620361)), ((4064817, 2936111), (4959816, 3735671)), ((4064817, 2936111), (5207267, 3686043)), ((4163746, 3620361), (4795222, 4173003)), ((4254186, 2959967), (4711166, 3259939)), ((4254186, 2959967), (4448595, 3065259)), ((4380432, 2975871), (6402761, 4281053)), ((4380432, 2975871), (4448595, 3065259)), ((4448595, 3065259), (4711166, 3259939)), ((4711166, 3259939), (5430717, 3754592)), ((4716080, 4009441), (4801055, 3840200)), ((4716080, 4009441), (5505841, 4889207)), ((4716080, 4009441), (4795222, 4173003)), ((4795222, 4173003), (5505841, 4889207)), ((4801055, 3840200), (5766123, 4480332)), ((4801055, 3840200), (4959816, 3735671)), ((4959816, 3735671), (5207267, 3686043)), ((4959816, 3735671), (5766123, 4480332)), ((5207267, 3686043), (6373719, 4317795)), ((5207267, 3686043), (5430717, 3754592)), ((5430717, 3754592), (6373719, 4317795)), ((5453357, 4906142), (7058706, 6468243)), ((5453357, 4906142), (5505841, 4889207)), ((5505841, 4889207), (7058706, 6468243)), ((5766123, 4480332), (6747394, 5114178)), ((5766123, 4480332), (6556227, 5231279)), ((6373719, 4317795), (8454131, 5549494)), ((6373719, 4317795), (6402761, 4281053)), ((6402761, 4281053), (8454131, 5549494)), ((6556227, 5231279), (6747394, 5114178)), ((6556227, 5231279), (6885535, 5807271)), ((6556227, 5231279), (6825857, 5523334)), ((6747394, 5114178), (7535502, 5409129)), ((6747394, 5114178), (7131725, 5335973)), ((6825857, 5523334), (6885535, 5807271)), ((6825857, 5523334), (7035810, 5531453)), ((6885535, 5807271), (7058706, 6468243)), ((6885535, 5807271), (7101347, 6006228)), ((7035810, 5531453), (7112277, 5484613)), ((7035810, 5531453), (7169296, 5586412)), ((7058706, 6468243), (7101347, 6006228)), ((7058706, 6468243), (7481275, 6993706)), ((7058706, 6468243), (7443490, 6683716)), ((7058706, 6468243), (7470628, 8818052)), ((7058706, 6468243), (7430786, 8860575)), ((7058706, 6468243), (7885605, 5845689)), ((7058706, 6468243), (7929199, 5871844)), ((7101347, 6006228), (7359801, 5743170)), ((7112277, 5484613), (7131725, 5335973)), ((7112277, 5484613), (7169296, 5586412)), ((7131725, 5335973), (7535502, 5409129)), ((7169296, 5586412), (7359801, 5743170)), ((7359801, 5743170), (7808760, 5636870)), ((7430786, 8860575), (7470628, 8818052)), ((7430786, 8860575), (7763024, 11295429)), ((7443490, 6683716), (7481275, 6993706)), ((7443490, 6683716), (7790489, 6589198)), ((7470628, 8818052), (7738777, 10053377)), ((7470628, 8818052), (7654244, 9890012)), ((7481275, 6993706), (7752987, 7618493)), ((7481275, 6993706), (7669917, 7204372)), ((7535502, 5409129), (8454131, 5549494)), ((7535502, 5409129), (7808760, 5636870)), ((7654244, 9890012), (7738777, 10053377)), ((7654244, 9890012), (7753325, 10798608)), ((7669917, 7204372), (7752987, 7618493)), ((7669917, 7204372), (7775488, 7000916)), ((7738777, 10053377), (7911743, 10058962)), ((7738777, 10053377), (7918494, 11446481)), ((7752987, 7618493), (7919198, 8781557)), ((7752987, 7618493), (7941558, 7494338)), ((7753325, 10798608), (7780520, 11149963)), ((7753325, 10798608), (7825212, 11355850)), ((7763024, 11295429), (8077765, 13875751)), ((7763024, 11295429), (7780520, 11149963)), ((7775488, 7000916), (7850916, 6951254)), ((7775488, 7000916), (7805631, 6847123)), ((7780520, 11149963), (7825212, 11355850)), ((7790489, 6589198), (8122345, 6236757)), ((7790489, 6589198), (7805631, 6847123)), ((7805631, 6847123), (7850916, 6951254)), ((7808760, 5636870), (8454131, 5549494)), ((7825212, 11355850), (7941790, 12118979)), ((7850916, 6951254), (7971630, 7005723)), ((7885605, 5845689), (8454131, 5549494)), ((7885605, 5845689), (7929199, 5871844)), ((7911743, 10058962), (7918494, 11446481)), ((7911743, 10058962), (7919198, 8781557)), ((7911743, 10058962), (8070504, 9954434)), ((7918494, 11446481), (8081664, 13554607)), ((7918494, 11446481), (7941790, 12118979)), ((7919198, 8781557), (7941558, 7494338)), ((7919198, 8781557), (8070504, 9954434)), ((7929199, 5871844), (8048169, 5795500)), ((7929199, 5871844), (8030230, 5805411)), ((7929199, 5871844), (8036925, 5805066)), ((7929199, 5871844), (8023276, 5813641)), ((7929199, 5871844), (8075073, 5782243)), ((7929199, 5871844), (8066313, 5787632)), ((7929199, 5871844), (8041473, 5802825)), ((7929199, 5871844), (8026220, 5812191)), ((7941558, 7494338), (8122416, 6571578)), ((7941558, 7494338), (7971630, 7005723)), ((7941790, 12118979), (8081664, 13554607)), ((7971630, 7005723), (8122416, 6571578)), ((8023276, 5813641), (8036925, 5805066)), ((8023276, 5813641), (8103704, 5764015)), ((8026220, 5812191), (8041473, 5802825)), ((8026220, 5812191), (8107987, 5761904)), ((8030230, 5805411), (8048169, 5795500)), ((8030230, 5805411), (8113322, 5748891)), ((8036925, 5805066), (8110575, 5759286)), ((8036925, 5805066), (8084651, 5775491)), ((8041473, 5802825), (8119353, 5754960)), ((8041473, 5802825), (8091120, 5772304)), ((8048169, 5795500), (8130423, 5744133)), ((8048169, 5795500), (8102825, 5760610)), ((8066313, 5787632), (8075073, 5782243)), ((8066313, 5787632), (8194666, 5708809)), ((8070504, 9954434), (8229965, 9729978)), ((8070504, 9954434), (8221110, 11247238)), ((8075073, 5782243), (8164198, 5727490)), ((8075073, 5782243), (8140583, 5742005)), ((8077765, 13875751), (8388608, 16777216)), ((8077765, 13875751), (8081664, 13554607)), ((8081664, 13554607), (8388608, 16777216)), ((8084651, 5775491), (8110575, 5759286)), ((8084651, 5775491), (8106453, 5762123)), ((8091120, 5772304), (8119353, 5754960)), ((8091120, 5772304), (8112533, 5759127)), ((8102825, 5760610), (8130423, 5744133)), ((8102825, 5760610), (8129883, 5742198)), ((8103704, 5764015), (8176621, 5719148)), ((8103704, 5764015), (8111216, 5759254)), ((8106453, 5762123), (8111216, 5759254)), ((8106453, 5762123), (8123491, 5751624)), ((8107987, 5761904), (8180991, 5716995)), ((8107987, 5761904), (8116750, 5756527)), ((8110575, 5759286), (8167553, 5723548)), ((8110575, 5759286), (8153171, 5733038)), ((8111216, 5759254), (8123491, 5751624)), ((8112533, 5759127), (8116750, 5756527)), ((8112533, 5759127), (8129730, 5748549)), ((8113322, 5748891), (8177229, 5701993)), ((8113322, 5748891), (8132507, 5739268)), ((8116750, 5756527), (8129730, 5748549)), ((8119353, 5754960), (8182474, 5716196)), ((8119353, 5754960), (8162345, 5728517)), ((8122345, 6236757), (8454131, 5549494)), ((8122345, 6236757), (8122416, 6571578)), ((8122416, 6571578), (8454131, 5549494)), ((8123491, 5751624), (8152804, 5733495)), ((8129730, 5748549), (8159907, 5729995)), ((8129883, 5742198), (8154317, 5726715)), ((8129883, 5742198), (8132507, 5739268)), ((8130423, 5744133), (8179190, 5714995)), ((8130423, 5744133), (8191507, 5705427)), ((8132507, 5739268), (8154317, 5726715)), ((8140583, 5742005), (8164198, 5727490)), ((8140583, 5742005), (8182478, 5716282)), ((8152804, 5733495), (8153171, 5733038)), ((8152804, 5733495), (8181751, 5715822)), ((8153171, 5733038), (8167553, 5723548)), ((8153171, 5733038), (8181751, 5715822)), ((8154317, 5726715), (8200561, 5698680)), ((8159907, 5729995), (8162345, 5728517)), ((8159907, 5729995), (8187646, 5712918)), ((8162345, 5728517), (8182474, 5716196)), ((8162345, 5728517), (8187646, 5712918)), ((8164198, 5727490), (8206001, 5701784)), ((8164198, 5727490), (8235135, 5683930)), ((8167553, 5723548), (8179190, 5714995)), ((8167553, 5723548), (8227275, 5686873)), ((8176621, 5719148), (8244408, 5677609)), ((8176621, 5719148), (8181751, 5715822)), ((8177229, 5701993), (8454131, 5549494)), ((8177229, 5701993), (8255857, 5663898)), ((8179190, 5714995), (8191507, 5705427)), ((8179190, 5714995), (8227275, 5686873)), ((8180991, 5716995), (8247341, 5676163)), ((8180991, 5716995), (8187646, 5712918)), ((8181751, 5715822), (8244408, 5677609)), ((8182474, 5716196), (8206001, 5701784)), ((8182474, 5716196), (8242196, 5679521)), ((8182478, 5716282), (8210853, 5698857)), ((8182478, 5716282), (8195999, 5707983)), ((8187646, 5712918), (8247341, 5676163)), ((8191507, 5705427), (8255857, 5663898)), ((8191507, 5705427), (8200561, 5698680)), ((8194666, 5708809), (8321685, 5630813)), ((8194666, 5708809), (8195999, 5707983)), ((8195999, 5707983), (8210853, 5698857)), ((8200561, 5698680), (8255857, 5663898)), ((8206001, 5701784), (8235135, 5683930)), ((8206001, 5701784), (8242196, 5679521)), ((8210853, 5698857), (8254082, 5672308)), ((8221110, 11247238), (8229965, 9729978)), ((8221110, 11247238), (8308401, 13405323)), ((8221110, 11247238), (8275572, 11899217)), ((8227275, 5686873), (8295350, 5645819)), ((8227275, 5686873), (8267009, 5663132)), ((8229965, 9729978), (8338506, 8246640)), ((8229965, 9729978), (8289739, 9471601)), ((8235135, 5683930), (8316258, 5634136)), ((8235135, 5683930), (8254082, 5672308)), ((8242196, 5679521), (8304128, 5641494)), ((8242196, 5679521), (8276183, 5658611)), ((8244408, 5677609), (8267045, 5663445)), ((8244408, 5677609), (8278396, 5656650)), ((8244408, 5677609), (8315293, 5634422)), ((8244408, 5677609), (8247341, 5676163)), ((8247341, 5676163), (8272940, 5660540)), ((8247341, 5676163), (8282766, 5654497)), ((8247341, 5676163), (8315293, 5634422)), ((8254082, 5672308), (8316258, 5634136)), ((8255857, 5663898), (8454131, 5549494)), ((8267009, 5663132), (8295350, 5645819)), ((8267009, 5663132), (8267045, 5663445)), ((8267009, 5663132), (8278366, 5656389)), ((8267045, 5663445), (8278396, 5656650)), ((8267045, 5663445), (8278366, 5656389)), ((8272940, 5660540), (8282766, 5654497)), ((8272940, 5660540), (8276183, 5658611)), ((8272940, 5660540), (8285469, 5652889)), ((8275572, 11899217), (8308401, 13405323)), ((8275572, 11899217), (8297204, 11045090)), ((8276183, 5658611), (8304128, 5641494)), ((8276183, 5658611), (8285469, 5652889)), ((8278366, 5656389), (8301045, 5642591)), ((8278396, 5656650), (8323736, 5628898)), ((8282766, 5654497), (8328018, 5626787)), ((8285469, 5652889), (8307284, 5639517)), ((8289739, 9471601), (8338506, 8246640)), ((8289739, 9471601), (8300746, 10438186)), ((8295350, 5645819), (8363404, 5604581)), ((8295350, 5645819), (8323712, 5628689)), ((8297204, 11045090), (8300746, 10438186)), ((8297204, 11045090), (8315294, 10797867)), ((8300746, 10438186), (8315294, 10797867)), ((8301045, 5642591), (8312382, 5635666)), ((8301045, 5642591), (8312388, 5635718)), ((8304128, 5641494), (8367952, 5602341)), ((8304128, 5641494), (8330181, 5625501)), ((8307284, 5639517), (8318462, 5632670)), ((8307284, 5639517), (8317922, 5632991)), ((8308401, 13405323), (8388608, 16777216)), ((8308401, 13405323), (8348314, 13697621)), ((8312382, 5635666), (8323712, 5628689)), ((8312382, 5635666), (8312388, 5635718)), ((8312388, 5635718), (8323736, 5628898)), ((8315293, 5634422), (8454131, 5549494)), ((8315294, 10797867), (8347933, 10910325)), ((8316258, 5634136), (8454131, 5549494)), ((8316258, 5634136), (8321685, 5630813)), ((8317922, 5632991), (8328018, 5626787)), ((8317922, 5632991), (8318462, 5632670)), ((8318462, 5632670), (8330181, 5625501)), ((8321685, 5630813), (8454131, 5549494)), ((8323712, 5628689), (8363404, 5604581)), ((8323736, 5628898), (8380424, 5594324)), ((8328018, 5626787), (8383367, 5592874)), ((8330181, 5625501), (8367952, 5602341)), ((8338506, 8246640), (8454131, 5549494)), ((8338506, 8246640), (8380190, 8235486)), ((8347933, 10910325), (8380190, 8235486)), ((8347933, 10910325), (8348314, 13697621)), ((8348314, 13697621), (8388608, 16777216)), ((8363404, 5604581), (8454131, 5549494)), ((8363404, 5604581), (8380424, 5594324)), ((8367952, 5602341), (8454131, 5549494)), ((8367952, 5602341), (8383367, 5592874)), ((8380190, 8235486), (8454131, 5549494)), ((8380424, 5594324), (8454131, 5549494)), ((8383367, 5592874), (8454131, 5549494)), ((8388608, 16777216), (16777216, 0)), ((8454131, 5549494), (16777216, 0))]

def PSG : List (ℕ × ℕ) := [(0, 0), (2019392, 1759429), (2262652, 1917312), (2289940, 1581300), (2489389, 1768028), (3269015, 2774464), (3602797, 2554702), (3762200, 3135354), (3782194, 3270727), (3795523, 3360975), (3913821, 3417354), (4064817, 2936111), (4163746, 3620361), (4254186, 2959967), (4380432, 2975871), (4448595, 3065259), (4711166, 3259939), (4716080, 4009441), (4795222, 4173003), (4801055, 3840200), (4959816, 3735671), (5207267, 3686043), (5430717, 3754592), (5453357, 4906142), (5505841, 4889207), (5766123, 4480332), (6373719, 4317795), (6402761, 4281053), (6556227, 5231279), (6747394, 5114178), (6825857, 5523334), (6885535, 5807271), (7035810, 5531453), (7058706, 6468243), (7101347, 6006228), (7112277, 5484613), (7131725, 5335973), (7169296, 5586412), (7359801, 5743170), (7430786, 8860575), (7443490, 6683716), (7470628, 8818052), (7481275, 6993706), (7535502, 5409129), (7654244, 9890012), (7669917, 7204372), (7738777, 10053377), (7752987, 7618493), (7753325, 10798608), (7763024, 11295429), (7775488, 7000916), (7780520, 11149963), (7790489, 6589198), (7805631, 6847123), (7808760, 5636870), (7825212, 11355850), (7850916, 6951254), (7885605, 5845689), (7911743, 10058962), (7918494, 11446481), (7919198, 8781557), (7929199, 5871844), (7941558, 7494338), (7941790, 12118979), (7971630, 7005723), (8023276, 5813641), (8026220, 5812191), (8030230, 5805411), (8036925, 5805066), (8041473, 5802825), (8048169, 5795500), (8066313, 5787632), (8070504, 9954434), (8075073, 5782243), (8077765, 13875751), (8081664, 13554607), (8084651, 5775491), (8091120, 5772304), (8102825, 5760610), (8103704, 5764015), (8106453, 5762123), (8107987, 5761904), (8110575, 5759286), (8111216, 5759254), (8112533, 5759127), (8113322, 5748891), (8116750, 5756527), (8119353, 5754960), (8122345, 6236757), (8122416, 6571578), (8123491, 5751624), (8129730, 5748549), (8129883, 5742198), (8130423, 5744133), (8132507, 5739268), (8140583, 5742005), (8152804, 5733495), (8153171, 5733038), (8154317, 5726715), (8159907, 5729995), (8162345, 5728517), (8164198, 5727490), (8167553, 5723548), (8176621, 5719148), (8177229, 5701993), (8179190, 5714995), (8180991, 5716995), (8181751, 5715822), (8182474, 5716196), (8182478, 5716282), (8187646, 5712918), (8191507, 5705427), (8194666, 5708809), (8195999, 5707983), (8200561, 5698680), (8206001, 5701784), (8210853, 5698857), (8221110, 11247238), (8227275, 5686873), (8229965, 9729978), (8235135, 5683930), (8242196, 5679521), (8244408, 5677609), (8247341, 5676163), (8254082, 5672308), (8255857, 5663898), (8267009, 5663132), (8267045, 5663445), (8272940, 5660540), (8275572, 11899217), (8276183, 5658611), (8278366, 5656389), (8278396, 5656650), (8282766, 5654497), (8285469, 5652889), (8289739, 9471601), (8295350, 5645819), (8297204, 11045090), (8300746, 10438186), (8301045, 5642591), (8304128, 5641494), (8307284, 5639517), (8308401, 13405323), (8312382, 5635666), (8312388, 5635718), (8315293, 5634422), (8315294, 10797867), (8316258, 5634136), (8317922, 5632991), (8318462, 5632670), (8321685, 5630813), (8323712, 5628689), (8323736, 5628898), (8328018, 5626787), (8330181, 5625501), (8338506, 8246640), (8347933, 10910325), (8348314, 13697621), (8363404, 5604581), (8367952, 5602341), (8380190, 8235486), (8380424, 5594324), (8383367, 5592874), (8388608, 16777216), (8454131, 5549494), (16777216, 0)]

theorem mapG : EGs.map (Sym2.map (fun v : Fin 166 => TG.get v.val)) =
    EcG.map (fun q => s(q.1, q.2)) := by decide +kernel
theorem sortEG : msortF (fun q : Q => q.1.1) 12 EcG = EcSG := by decide +kernel
theorem sortPG : msortF Prod.fst 12 ((List.range 166).map TG.get) = PSG := by
  decide +kernel
theorem sortedEG : sortedLE (fun q : Q => q.1.1) EcSG = true := by decide +kernel
theorem orientG : orientB EcSG = true := by decide +kernel
theorem sortedPG : sortedB Prod.fst PSG = true := by decide +kernel
theorem chkVG : chkVS 1000 EcSG PSG = true := by decide +kernel
theorem chkEG : chkES EcSG = true := by decide +kernel

theorem PG_E {u v : Fin 166} (h : s(u, v) ∈ EGs) :
    (TG.get u.val, TG.get v.val) ∈ EcG ∨ (TG.get v.val, TG.get u.val) ∈ EcG := by
  have h2 : Sym2.map (fun v : Fin 166 => TG.get v.val) s(u, v) ∈ EcG.map (fun q => s(q.1, q.2)) := by
    rw [← mapG]; exact List.mem_map_of_mem h
  obtain ⟨q, hq, hq'⟩ := List.mem_map.1 h2
  simp only [Sym2.map_mk, Sym2.eq_iff] at hq'
  rcases hq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; rw [← h1, ← h2]; exact hq
  · right; rw [← h1, ← h2]; exact hq

end SteinbergAux

open SteinbergFalse.Counterexample in
theorem solution : OPG37357.IsPlanar G := by
  exact SteinbergAux.planar_of_checks _ SteinbergAux.TG SteinbergAux.EcG SteinbergAux.EcSG
    SteinbergAux.PSG (fun u v h => SteinbergAux.PG_E (SteinbergAux.G_adj_mem h)) SteinbergAux.sortEG
    SteinbergAux.sortPG SteinbergAux.sortedEG SteinbergAux.orientG SteinbergAux.sortedPG
    SteinbergAux.chkEG SteinbergAux.chkVG
