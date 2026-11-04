-- Prove2me | solution 1 for SnarkGen.Zhang.observation_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T14:28:44.428489+00:00
-- url     : https://prove2.me/submissions/818783a0-1f96-4394-a835-ad70c2a9d8f0

import Mathlib
import Definitions.Def_SnarkGen_Zhang_ZhangConjecture
import Definitions.Def_SnarkGen_Zhang_g1

set_option autoImplicit false

namespace SnarkLib

open SimpleGraph

/-! ### A generic exhaustive search over assignments, and its soundness -/

/-- `srch alph ok Q r i asg`: extend the reversed partial assignment `asg` (positions `< i`) by `r`
more positions, each value taken from `alph` and accepted by `ok`; `Q` must hold at every leaf. -/
def srch {α : Type} (alph : ℕ → List α) (ok : ℕ → List α → α → Bool) (Q : List α → Bool) :
    ℕ → ℕ → List α → Bool
  | 0, _, asg => Q asg
  | r+1, i, asg => (alph i).all fun c => !(ok i asg c) || srch alph ok Q r (i+1) (c :: asg)

/-- the reversed prefix `[f (i-1), ..., f 0]` -/
def pre {α : Type} (f : ℕ → α) : ℕ → List α
  | 0 => []
  | i+1 => f i :: pre f i

theorem srch_sound {α : Type} (alph : ℕ → List α) (ok : ℕ → List α → α → Bool)
    (Q : List α → Bool) (f : ℕ → α) : ∀ r i, srch alph ok Q r i (pre f i) = true →
    (∀ t, i ≤ t → t < i + r → f t ∈ alph t ∧ ok t (pre f t) (f t) = true) →
    Q (pre f (i + r)) = true := by
  intro r
  induction r with
  | zero => intro i h _; simpa [srch] using h
  | succ r ih =>
    intro i h hf
    have h1 := hf i le_rfl (by omega)
    simp only [srch, List.all_eq_true] at h
    have h2 := h (f i) h1.1
    rw [h1.2] at h2
    simp only [Bool.not_true, Bool.false_or] at h2
    have := ih (i+1) h2 (fun t ht1 ht2 => hf t (by omega) (by omega))
    rwa [show i + 1 + r = i + (r+1) by omega] at this

theorem pre_getD {α : Type} (f : ℕ → α) (d : α) :
    ∀ i j, j < i → (pre f i).getD (i - 1 - j) d = f j := by
  intro i
  induction i with
  | zero => intro j h; omega
  | succ i ih =>
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · rw [show i + 1 - 1 - j = (i - 1 - j) + 1 by omega]
      simp only [pre, List.getD_cons_succ]
      exact ih j h
    · subst h
      simp [pre]

/-! ### Vertices as natural numbers -/

def toF {n : ℕ} (hn : 0 < n) (x : ℕ) : Fin n := ⟨x % n, Nat.mod_lt _ hn⟩

theorem toF_val {n : ℕ} (hn : 0 < n) {x : ℕ} (h : x < n) : (toF hn x).val = x :=
  Nat.mod_eq_of_lt h

theorem toF_eq {n : ℕ} (hn : 0 < n) (v : Fin n) : toF hn v.val = v :=
  Fin.ext (toF_val hn v.isLt)

theorem adjN {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) (nb : ℕ → List ℕ)
    (hadj : ∀ a b : Fin n, G.Adj a b ↔ b.val ∈ nb a.val) {a b : ℕ} (ha : a < n) (hb : b < n) :
    G.Adj (toF hn a) (toF hn b) ↔ b ∈ nb a := by
  rw [hadj, toF_val hn ha, toF_val hn hb]

theorem ncard_val {n : ℕ} (l : List ℕ) (hl : ∀ x ∈ l, x < n) (hnd : l.Nodup) :
    ({w : Fin n | w.val ∈ l} : Set (Fin n)).ncard = l.length := by
  have h : (Fin.val '' {w : Fin n | w.val ∈ l}) = ↑l.toFinset := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Finset.coe_sort_coe, List.coe_toFinset]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hx; exact ⟨⟨x, hl x hx⟩, hx, rfl⟩
  rw [← Set.ncard_image_of_injective _ Fin.val_injective, h, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

theorem degree_eq {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) {inst : Fintype (G.neighborSet v)}
    (l : List ℕ) (hl : ∀ x ∈ l, x < n) (hnd : l.Nodup) (hadj : ∀ b : Fin n, G.Adj v b ↔ b.val ∈ l) :
    @SimpleGraph.degree _ G v inst = l.length := by
  rw [← @SimpleGraph.card_neighborSet_eq_degree _ G v inst, Fintype.card_eq_nat_card,
    Nat.card_coe_set_eq, ← ncard_val l hl hnd]
  congr 1
  ext b
  simp [hadj]

/-! ### Girth -/

theorem girth5 {n : ℕ} (G : SimpleGraph (Fin n)) (nb : ℕ → List ℕ)
    (hadj : ∀ a b : Fin n, G.Adj a b ↔ b.val ∈ nb a.val)
    (h3 : ∀ a < n, ∀ x ∈ nb a, ∀ y ∈ nb x, a ∉ nb y)
    (h4 : ∀ a < n, ∀ x ∈ nb a, ∀ y ∈ nb x, ∀ z ∈ nb y, a ∈ nb z → x = z ∨ a = y) :
    5 ≤ G.egirth := by
  rw [SimpleGraph.le_egirth]
  intro a w hw
  have h3l := hw.three_le_length
  by_contra hlt
  push_neg at hlt
  have hlt' : w.length < 5 := by exact_mod_cast hlt
  have hnd := hw.support_nodup
  rcases w with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3', _ | ⟨h4', _ | ⟨h5, w5⟩⟩⟩⟩⟩
  · simp at h3l
  · simp at h3l
  · simp at h3l
  · rename_i x y
    exact h3 a.val a.isLt x.val ((hadj _ _).1 h1) y.val ((hadj _ _).1 h2) ((hadj _ _).1 h3')
  · rename_i x y z
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons,
      List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true] at hnd
    rcases h4 a.val a.isLt x.val ((hadj _ _).1 h1) y.val ((hadj _ _).1 h2) z.val ((hadj _ _).1 h3')
      ((hadj _ _).1 h4') with h | h
    · exact hnd.1.2.1 (Fin.ext h)
    · exact hnd.2.1.2 (Fin.ext h).symm
  · simp at hlt'
    omega


/-! ### Search over a data list (one entry per position) -/

def srchD {α β : Type} (alph : β → List α) (ok : β → List α → α → Bool) (Q : List α → Bool) :
    List β → List α → Bool
  | [], asg => Q asg
  | d :: ds, asg => (alph d).all fun c => !(ok d asg c) || srchD alph ok Q ds (c :: asg)

theorem srchD_sound {α β : Type} (alph : β → List α) (ok : β → List α → α → Bool)
    (Q : List α → Bool) (f : ℕ → α) (d0 : β) : ∀ (ds : List β) (i : ℕ),
    srchD alph ok Q ds (pre f i) = true →
    (∀ t, i ≤ t → t < i + ds.length →
      f t ∈ alph (ds.getD (t - i) d0) ∧ ok (ds.getD (t - i) d0) (pre f t) (f t) = true) →
    Q (pre f (i + ds.length)) = true := by
  intro ds
  induction ds with
  | nil => intro i h _; simpa [srchD] using h
  | cons d ds ih =>
    intro i h hf
    have h1 := hf i le_rfl (by simp)
    simp only [Nat.sub_self, List.getD_cons_zero] at h1
    simp only [srchD, List.all_eq_true] at h
    have h2 := h (f i) h1.1
    rw [h1.2] at h2
    simp only [Bool.not_true, Bool.false_or] at h2
    have := ih (i+1) h2 (fun t ht1 ht2 => by
      have := hf t (by omega) (by simp; omega)
      rwa [show t - i = (t - (i+1)) + 1 by omega, List.getD_cons_succ] at this)
    rwa [show i + 1 + ds.length = i + (d :: ds).length by simp; omega] at this

/-! ### Bit masks -/

def maskOf : List ℕ → ℕ
  | [] => 0
  | v :: r => maskOf r ||| 2 ^ v

theorem testBit_maskOf (w : ℕ) : ∀ l : List ℕ, (maskOf l).testBit w = decide (w ∈ l)
  | [] => by simp [maskOf]
  | v :: r => by
    simp only [maskOf, Nat.testBit_lor, testBit_maskOf w r, Nat.testBit_two_pow, List.mem_cons]
    by_cases h : w = v
    · subst h; simp
    · simp [h, Ne.symm h]

def nodupM : ℕ → List ℕ → Bool
  | _, [] => true
  | m, v :: r => !(m.testBit v) && nodupM (m ||| 2 ^ v) r

theorem nodupM_spec : ∀ (l : List ℕ) (m : ℕ), nodupM m l = true →
    l.Nodup ∧ ∀ v ∈ l, m.testBit v = false
  | [], _, _ => ⟨List.nodup_nil, by simp⟩
  | v :: r, m, h => by
    simp only [nodupM, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, h2⟩ := nodupM_spec r _ h.2
    refine ⟨List.nodup_cons.2 ⟨fun hv => ?_, h1⟩, ?_⟩
    · have := h2 v hv
      simp [Nat.testBit_lor, Nat.testBit_two_pow] at this
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h.1
      · have := h2 x hx
        simp only [Nat.testBit_lor, Bool.or_eq_false_iff] at this
        exact this.1

/-! ### Paths, edge-disjointness and crossing edges -/

def edgs : List ℕ → List (ℕ × ℕ)
  | a :: b :: r => (a, b) :: edgs (b :: r)
  | _ => []

theorem edgs_mem : ∀ (p : List ℕ), ∀ x ∈ edgs p, x.1 ∈ p ∧ x.2 ∈ p
  | [], x, hx => by simp [edgs] at hx
  | [_], x, hx => by simp [edgs] at hx
  | a :: b :: r, x, hx => by
    simp only [edgs, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · obtain ⟨h1, h2⟩ := edgs_mem (b :: r) x hx
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

def lastN : List ℕ → ℕ
  | [a] => a
  | _ :: b :: r => lastN (b :: r)
  | [] => 0

def pathB (nb : ℕ → List ℕ) (A H : List ℕ) (p : List ℕ) : Bool :=
  A.contains (p.headD 0) && H.contains (lastN p) && (edgs p).all fun x => (nb x.1).contains x.2

def sameE (x y : ℕ × ℕ) : Bool := (x.1 == y.1 && x.2 == y.2) || (x.1 == y.2 && x.2 == y.1)

def ekey (x : ℕ × ℕ) : ℕ := min x.1 x.2 * 64 + max x.1 x.2

theorem ekey_of_same {x y : ℕ × ℕ} (h : sameE x y = true) : ekey x = ekey y := by
  obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
  simp only [sameE, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · simp [ekey, min_comm, max_comm]

theorem sameE_comm (x y : ℕ × ℕ) : sameE x y = sameE y x := by
  rw [Bool.eq_iff_iff]
  simp only [sameE, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor <;> intro h <;> omega

def sysB (nb : ℕ → List ℕ) (k : ℕ) (A H : List ℕ) (ps : List (List ℕ)) : Bool :=
  decide (k ≤ ps.length) && ps.all (pathB nb A H) && nodupM 0 (ps.flatMap fun p => (edgs p).map ekey)

theorem cross (nb : ℕ → List ℕ) (X : ℕ → Prop) (bad : ℕ → ℕ → Prop)
    (hcl : ∀ u w, X u → w ∈ nb u → ¬ X w → bad u w) :
    ∀ p : List ℕ, (∀ x ∈ edgs p, x.2 ∈ nb x.1) → X (p.headD 0) → ¬ X (lastN p) →
      ∃ x ∈ edgs p, bad x.1 x.2
  | [], _, h1, h2 => absurd h1 h2
  | [_], _, h1, h2 => absurd h1 h2
  | a :: b :: r, hc, h1, h2 => by
    by_cases hb : X b
    · obtain ⟨x, hx, hbad⟩ := cross nb X bad hcl (b :: r)
        (fun x hx => hc x (by simp only [edgs]; exact List.mem_cons_of_mem _ hx)) hb h2
      exact ⟨x, by simp only [edgs]; exact List.mem_cons_of_mem _ hx, hbad⟩
    · exact ⟨(a, b), by simp [edgs], hcl a b h1 (hc (a, b) (by simp [edgs])) hb⟩

theorem crossList (nb : ℕ → List ℕ) (X : ℕ → Prop) (bad : ℕ → ℕ → Prop)
    (hcl : ∀ u w, X u → w ∈ nb u → ¬ X w → bad u w) (A H : List ℕ)
    (hA : ∀ a ∈ A, X a) (hH : ∀ h ∈ H, ¬ X h) :
    ∀ ps : List (List ℕ), (∀ p ∈ ps, pathB nb A H p = true) →
      ps.Pairwise (fun p q => List.Disjoint ((edgs p).map ekey) ((edgs q).map ekey)) →
      ∃ L : List (ℕ × ℕ), L.length = ps.length ∧ (∀ x ∈ L, bad x.1 x.2) ∧
        (∀ x ∈ L, ∃ q ∈ ps, x ∈ edgs q) ∧ L.Pairwise (fun x y => ekey x ≠ ekey y)
  | [], _, _ => ⟨[], rfl, by simp, by simp, List.Pairwise.nil⟩
  | p :: ps, hp, hpair => by
    rw [List.pairwise_cons] at hpair
    obtain ⟨L, hlen, hbad, hmem, hpw⟩ := crossList nb X bad hcl A H hA hH ps
      (fun q hq => hp q (List.mem_cons_of_mem _ hq)) hpair.2
    have hpp := hp p List.mem_cons_self
    simp only [pathB, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true] at hpp
    obtain ⟨⟨hhead, hlast⟩, hch⟩ := hpp
    obtain ⟨x, hx, hxb⟩ := cross nb X bad hcl p (fun x hx => hch x hx) (hA _ hhead) (hH _ hlast)
    refine ⟨x :: L, by simp [hlen], ?_, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hxb
      · exact hbad y hy
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨p, List.mem_cons_self, hx⟩
      · obtain ⟨q, hq, hyq⟩ := hmem y hy
        exact ⟨q, List.mem_cons_of_mem _ hq, hyq⟩
    · refine List.Pairwise.cons ?_ hpw
      intro y hy heq
      obtain ⟨q, hq, hyq⟩ := hmem y hy
      exact hpair.1 q hq (List.mem_map_of_mem hx) (heq ▸ List.mem_map_of_mem hyq)

theorem sym_inj {n : ℕ} (hn : 0 < n) {a b c d : ℕ} (ha : a < n) (hb : b < n) (hc : c < n)
    (hd : d < n) (h : s(toF hn a, toF hn b) = s(toF hn c, toF hn d)) :
    sameE (a, b) (c, d) = true := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2
    rw [toF_val hn ha, toF_val hn hc] at e1; rw [toF_val hn hb, toF_val hn hd] at e2
    simp [sameE, e1, e2]
  · have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2
    rw [toF_val hn ha, toF_val hn hd] at e1; rw [toF_val hn hb, toF_val hn hc] at e2
    simp [sameE, e1, e2]

theorem two_le_length {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    2 ≤ l.length := by
  match l, ha, hb with
  | [_], ha, hb =>
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | _ :: _ :: _, _, _ => simp

/-- every cycle of a subgraph `H` of `G` meets the feedback set `W`, certified by a leaf order -/
theorem cycle_hits {n : ℕ} (H : SimpleGraph (Fin n)) (nb : ℕ → List ℕ)
    (hHG : ∀ a b : Fin n, H.Adj a b → b.val ∈ nb a.val) (W : List ℕ) (rank : ℕ → ℕ)
    (hrank : ∀ u < n, u ∉ W →
      ((nb u).filter fun w => !(W.contains w) && decide (rank u < rank w)).length ≤ 1)
    (hrinj : ∀ u < n, ∀ w < n, rank u = rank w → u = w)
    {v : Fin n} (p : H.Walk v v) (hp : p.IsCycle) : ∃ x ∈ p.support, x.val ∈ W := by
  by_contra hall
  push_neg at hall
  obtain ⟨x, hx, hmin⟩ := p.support.toFinset.exists_min_image (fun x => rank x.val)
    ⟨v, List.mem_toFinset.2 p.start_mem_support⟩
  rw [List.mem_toFinset] at hx
  let q := p.rotate x hx
  have hq : q.IsCycle := (SimpleGraph.Walk.isCycle_rotate hx).2 hp
  have hnil := hq.not_nil
  have hy : H.Adj x q.snd := q.adj_snd hnil
  have hz : H.Adj q.penultimate x := q.adj_penultimate hnil
  have hyz := hq.snd_ne_penultimate
  have hys : q.snd ∈ p.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff p x hx).1 (q.getVert_mem_support 1)
  have hzs : q.penultimate ∈ p.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff p x hx).1 (q.getVert_mem_support _)
  have hlt : ∀ y : Fin n, y ∈ p.support → y ≠ x → rank x.val < rank y.val := by
    intro y hy hyx
    have h1 := hmin y (List.mem_toFinset.2 hy)
    rcases Nat.lt_or_eq_of_le h1 with h | h
    · exact h
    · exact absurd (Fin.ext (hrinj _ x.isLt _ y.isLt h)).symm hyx
  have hmemf : ∀ y : Fin n, y ∈ p.support → H.Adj x y →
      y.val ∈ (nb x.val).filter fun w => !(W.contains w) && decide (rank x.val < rank w) := by
    intro y hy hxy
    rw [List.mem_filter]
    refine ⟨hHG _ _ hxy, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    refine ⟨?_, hlt y hy hxy.ne.symm⟩
    simpa using hall y hy
  have := two_le_length (hmemf _ hys hy) (hmemf _ hzs hz.symm) (fun h => hyz (Fin.ext h))
  have := hrank x.val x.isLt (hall x hx)
  omega

/-! ### Cyclic edge-connectivity from anchor-to-hub Menger certificates -/

theorem cycConn {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) (nb : ℕ → List ℕ)
    (hadj : ∀ a b : Fin n, G.Adj a b ↔ b.val ∈ nb a.val)
    (hlt : ∀ a < n, ∀ b ∈ nb a, b < n) (hn64 : n ≤ 64)
    (W : List ℕ) (rank : ℕ → ℕ)
    (hrank : ∀ u < n, u ∉ W →
      ((nb u).filter fun w => !(W.contains w) && decide (rank u < rank w)).length ≤ 1)
    (hrinj : ∀ u < n, ∀ w < n, rank u = rank w → u = w)
    (k : ℕ) (anc : ℕ → ℕ → List ℕ) (ha hb hc : ℕ → ℕ) (cert : ℕ → ℕ → ℕ → List (List ℕ))
    (hanc : ∀ v < n, ∀ y ∈ nb v, ∀ z ∈ nb v, y ≠ z → ∃ e < 3, ∀ t ∈ anc v e,
      t = v ∨ t = y ∨ t = z)
    (hhub : ∀ j < k, ha j < n ∧ hb j ∈ nb (ha j) ∧ hc j ∈ nb (hb j))
    (hhubd : ∀ i < k, ∀ j < k, i ≠ j → ∀ x ∈ [ha i, hb i, hc i], x ∉ [ha j, hb j, hc j])
    (hcert : ∀ v < n, v ∈ W → ∀ e < 3, ∀ j < k, (∀ x ∈ anc v e, x ∉ [ha j, hb j, hc j]) →
      sysB nb k (anc v e) [ha j, hb j, hc j] (cert v e j) = true) :
    SnarkGen.Zhang.CyclicallyEdgeConnected G k := by
  intro S hS hcard c1 c2 hc1 hc2
  by_contra hne
  let H := G.deleteEdges ↑S
  let side : H.ConnectedComponent → ℕ → Prop := fun c x => x < n ∧ toF hn x ∈ c.supp
  let bad : ℕ → ℕ → Prop := fun u w => u < n ∧ w < n ∧ s(toF hn u, toF hn w) ∈ S
  have hHadj : ∀ u w, u < n → w < n → w ∈ nb u → s(toF hn u, toF hn w) ∉ S →
      H.Adj (toF hn u) (toF hn w) := by
    intro u w hu hw hm hS'
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨(adjN hn G nb hadj hu hw).2 hm, hS'⟩
  have hsame : ∀ (c : H.ConnectedComponent) (x y : Fin n), H.Adj x y → x ∈ c.supp →
      y ∈ c.supp := by
    intro c x y hxy hx
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
    rw [← hx]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
  have hcl : ∀ c : H.ConnectedComponent, ∀ u w, side c u → w ∈ nb u → ¬ side c w → bad u w := by
    rintro c u w ⟨hu, hcu⟩ hw hnw
    have hwn : w < n := hlt u hu w hw
    refine ⟨hu, hwn, ?_⟩
    by_contra hS'
    exact hnw ⟨hwn, hsame c _ _ (hHadj u w hu hwn hw hS') hcu⟩
  -- the counting core
  have key : ∀ c : H.ConnectedComponent, ∀ (A Hb : List ℕ) (ps : List (List ℕ)),
      (∀ a ∈ A, side c a) → (∀ h ∈ Hb, ¬ side c h) → sysB nb k A Hb ps = true → False := by
    intro c A Hb ps hA hH hs
    simp only [sysB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs
    obtain ⟨⟨hk, hp⟩, hnd⟩ := hs
    have hpair := (List.nodup_flatMap.1 (nodupM_spec _ 0 hnd).1).2
    obtain ⟨L, hlen, hbad, -, hpw⟩ := crossList nb (side c) bad (hcl c) A Hb hA hH ps hp hpair
    have hsub : (L.map fun x => s(toF hn x.1, toF hn x.2)).toFinset ⊆ S := by
      intro e he
      simp only [List.mem_toFinset, List.mem_map] at he
      obtain ⟨x, hx, rfl⟩ := he
      exact (hbad x hx).2.2
    have hnd' : (L.map fun x => s(toF hn x.1, toF hn x.2)).Nodup := by
      rw [List.Nodup, List.pairwise_map]
      refine hpw.imp_of_mem ?_
      intro x y hx hy hxy heq
      exact hxy (ekey_of_same (sym_inj hn (hbad x hx).1 (hbad x hx).2.1 (hbad y hy).1
        (hbad y hy).2.1 heq))
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd', List.length_map] at this
    omega
  -- an anchor centred in W inside each cyclic component
  have anchor : ∀ c : H.ConnectedComponent, (∃ v ∈ c.supp, ∃ p : H.Walk v v, p.IsCycle) →
      ∃ v < n, v ∈ W ∧ ∃ e < 3, ∀ t ∈ anc v e, side c t := by
    rintro c ⟨v0, hv0, p0, hp0⟩
    obtain ⟨v, hvs, hvW⟩ := cycle_hits H nb (fun a b h => (hadj a b).1 (SimpleGraph.deleteEdges_adj.1 h).1)
      W rank hrank hrinj p0 hp0
    have hv : v ∈ c.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hv0 ⊢
      rw [← hv0]
      exact SimpleGraph.ConnectedComponent.eq.2 (p0.takeUntil v hvs).reachable.symm
    let p := p0.rotate v hvs
    have hp : p.IsCycle := (SimpleGraph.Walk.isCycle_rotate hvs).2 hp0
    have hnil := hp.not_nil
    have hy : H.Adj v p.snd := p.adj_snd hnil
    have hz : H.Adj p.penultimate v := p.adj_penultimate hnil
    have hyz := hp.snd_ne_penultimate
    have hyG : G.Adj v p.snd := (SimpleGraph.deleteEdges_adj.1 hy).1
    have hzG : G.Adj v p.penultimate := (SimpleGraph.deleteEdges_adj.1 hz).1.symm
    obtain ⟨e, he, hsub⟩ := hanc v.val v.isLt p.snd.val ((hadj _ _).1 hyG) p.penultimate.val
      ((hadj _ _).1 hzG) (fun h => hyz (Fin.ext h))
    refine ⟨v.val, v.isLt, hvW, e, he, fun t ht => ?_⟩
    rcases hsub t ht with rfl | rfl | rfl
    · exact ⟨v.isLt, by rw [toF_eq]; exact hv⟩
    · exact ⟨p.snd.isLt, by rw [toF_eq]; exact hsame c _ _ hy hv⟩
    · exact ⟨p.penultimate.isLt, by rw [toF_eq]; exact hsame c _ _ hz.symm hv⟩
  obtain ⟨v1, hv1, hW1, e1, he1, hA1⟩ := anchor c1 hc1
  obtain ⟨v2, hv2, hW2, e2, he2, hA2⟩ := anchor c2 hc2
  -- an unbroken hub
  have hgood : ∃ j < k, s(toF hn (ha j), toF hn (hb j)) ∉ S ∧
      s(toF hn (hb j), toF hn (hc j)) ∉ S := by
    by_contra hall
    push_neg at hall
    classical
    let g : Fin k → Sym2 (Fin n) := fun j =>
      if s(toF hn (ha j), toF hn (hb j)) ∈ S then s(toF hn (ha j), toF hn (hb j))
      else s(toF hn (hb j), toF hn (hc j))
    have hgS : ∀ j : Fin k, g j ∈ S := by
      intro j
      simp only [g]
      split_ifs with h
      · exact h
      · exact hall j j.isLt h
    have hgmem : ∀ j : Fin k, ∀ x ∈ g j, x.val ∈ [ha j, hb j, hc j] := by
      intro j x hx
      obtain ⟨h1, h2, h3⟩ := hhub j j.isLt
      have hbn : hb j < n := hlt _ h1 _ h2
      have hcn : hc j < n := hlt _ hbn _ h3
      simp only [g] at hx
      split_ifs at hx
      · rcases Sym2.mem_iff.1 hx with rfl | rfl
        · simp [toF_val hn h1]
        · simp [toF_val hn hbn]
      · rcases Sym2.mem_iff.1 hx with rfl | rfl
        · simp [toF_val hn hbn]
        · simp [toF_val hn hcn]
    have hinj : Set.InjOn g (Finset.univ : Finset (Fin k)) := by
      intro i _ j _ hij
      by_contra hne'
      have hx : toF hn (hb i) ∈ g i := by
        simp only [g]; split_ifs
        · exact Sym2.mem_mk_right _ _
        · exact Sym2.mem_mk_left _ _
      have hxi := hgmem i _ hx
      have hxj := hgmem j _ (hij ▸ hx)
      exact hhubd i i.isLt j j.isLt (fun h => hne' (Fin.ext h)) _ hxi hxj
    have := Finset.card_le_card_of_injOn g (fun j _ => hgS j) hinj
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨j, hj, hab, hbc⟩ := hgood
  obtain ⟨h1, h2, h3⟩ := hhub j hj
  have hbn : hb j < n := hlt _ h1 _ h2
  have hcn : hc j < n := hlt _ hbn _ h3
  let cj := H.connectedComponentMk (toF hn (hb j))
  have hbj : toF hn (hb j) ∈ cj.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have haj : toF hn (ha j) ∈ cj.supp :=
    hsame cj _ _ (hHadj _ _ h1 hbn h2 hab).symm hbj
  have hcj : toF hn (hc j) ∈ cj.supp := hsame cj _ _ (hHadj _ _ hbn hcn h3 hbc) hbj
  have hhubside : ∀ x ∈ [ha j, hb j, hc j], side cj x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨h1, haj⟩
    · exact ⟨hbn, hbj⟩
    · exact ⟨hcn, hcj⟩
  have hother : ∀ c : H.ConnectedComponent, c ≠ cj → ∀ x, side c x → side cj x → False := by
    rintro c hc x ⟨_, hx1⟩ ⟨_, hx2⟩
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx1 hx2
    exact hc (hx1.symm.trans hx2)
  by_cases hcj1 : cj = c1
  · have hne2 : c2 ≠ cj := fun h => hne (hcj1 ▸ h).symm
    have hpre : ∀ x ∈ anc v2 e2, x ∉ [ha j, hb j, hc j] := fun x hx hx' =>
      hother c2 hne2 x (hA2 x hx) (hhubside x hx')
    exact key c2 _ _ _ hA2 (fun x hx hx' => hother c2 hne2 x hx' (hhubside x hx))
      (hcert v2 hv2 hW2 e2 he2 j hj hpre)
  · have hne1 : c1 ≠ cj := fun h => hcj1 h.symm
    have hpre : ∀ x ∈ anc v1 e1, x ∉ [ha j, hb j, hc j] := fun x hx hx' =>
      hother c1 hne1 x (hA1 x hx) (hhubside x hx')
    exact key c1 _ _ _ hA1 (fun x hx hx' => hother c1 hne1 x hx' (hhubside x hx))
      (hcert v1 hv1 hW1 e1 he1 j hj hpre)

/-! ### No 3-edge-colouring, by exhaustive search (colours of the first two edges fixed) -/

def colOk (d : List ℕ × List ℕ) (asg : List ℕ) (c : ℕ) : Bool :=
  d.2.all fun o => asg.getD o 9 != c

def sharesB (x y : ℕ × ℕ) : Bool := x.1 == y.1 || x.1 == y.2 || x.2 == y.1 || x.2 == y.2

def perm3 (a b x : Fin 3) : ℕ := if x = a then 0 else if x = b then 1 else 2

theorem perm3_inj : ∀ a b x y : Fin 3, a ≠ b → perm3 a b x = perm3 a b y → x = y := by decide

theorem perm3_mem : ∀ a b x : Fin 3, perm3 a b x ∈ ([0, 1, 2] : List ℕ) := by decide

theorem notColourable {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) (nb : ℕ → List ℕ)
    (hadj : ∀ a b : Fin n, G.Adj a b ↔ b.val ∈ nb a.val)
    (EL : List (ℕ × ℕ)) (D : List (List ℕ × List ℕ))
    (hlen : D.length = EL.length) (h2 : 2 ≤ EL.length)
    (hEL : ∀ x ∈ EL, x.1 < n ∧ x.2 < n ∧ x.2 ∈ nb x.1)
    (hal : ∀ t < EL.length, (D.getD t ([], [])).1 =
      if t = 0 then [0] else if t = 1 then [1] else [0, 1, 2])
    (h01 : sharesB (EL.getD 1 (0, 0)) (EL.getD 0 (0, 0)) = true ∧
      sameE (EL.getD 1 (0, 0)) (EL.getD 0 (0, 0)) = false)
    (hconf : ∀ t < EL.length, ∀ o ∈ (D.getD t ([], [])).2, o < t ∧
      sharesB (EL.getD t (0, 0)) (EL.getD (t - 1 - o) (0, 0)) = true ∧
      sameE (EL.getD t (0, 0)) (EL.getD (t - 1 - o) (0, 0)) = false)
    (hs : srchD (fun d => d.1) colOk (fun _ => false) D [] = true) :
    ¬ SnarkGen.EdgeInsertion.Colourable G := by
  rintro ⟨C⟩
  have hget : ∀ t < EL.length, EL.getD t (0, 0) ∈ EL := by
    intro t ht
    rw [List.getD_eq_getElem _ _ ht]
    exact List.getElem_mem ht
  have hmem : ∀ t < EL.length,
      s(toF hn (EL.getD t (0, 0)).1, toF hn (EL.getD t (0, 0)).2) ∈ G.edgeSet := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := hEL _ (hget t ht)
    rw [SimpleGraph.mem_edgeSet, adjN hn G nb hadj h1 h2]
    exact h3
  let col : ℕ → Fin 3 := fun t => if h : t < EL.length then C ⟨_, hmem t h⟩ else 0
  -- adjacent edges get different colours
  have hvalid : ∀ t < EL.length, ∀ j < EL.length,
      sharesB (EL.getD t (0, 0)) (EL.getD j (0, 0)) = true →
      sameE (EL.getD t (0, 0)) (EL.getD j (0, 0)) = false → col j ≠ col t := by
    intro t ht j hjl hsh hsm
    simp only [col, dif_pos ht, dif_pos hjl]
    intro heq
    refine C.valid ?_ heq
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    obtain ⟨i1, i2, i3⟩ := hEL _ (hget t ht)
    obtain ⟨j1, j2, j3⟩ := hEL _ (hget j hjl)
    constructor
    · intro hq
      have hq' := congrArg Subtype.val hq
      simp only at hq'
      have := sym_inj hn j1 j2 i1 i2 hq'
      rw [sameE_comm, hsm] at this
      exact Bool.false_ne_true this
    · simp only [sharesB, Bool.or_eq_true, beq_iff_eq] at hsh
      rcases hsh with ((h | h) | h) | h
      · exact ⟨toF hn (EL.getD j (0, 0)).1, Sym2.mem_mk_left _ _, by
          rw [← h]; exact Sym2.mem_mk_left _ _⟩
      · exact ⟨toF hn (EL.getD j (0, 0)).2, Sym2.mem_mk_right _ _, by
          rw [← h]; exact Sym2.mem_mk_left _ _⟩
      · exact ⟨toF hn (EL.getD j (0, 0)).1, Sym2.mem_mk_left _ _, by
          rw [← h]; exact Sym2.mem_mk_right _ _⟩
      · exact ⟨toF hn (EL.getD j (0, 0)).2, Sym2.mem_mk_right _ _, by
          rw [← h]; exact Sym2.mem_mk_right _ _⟩
  have hab : col 0 ≠ col 1 := by
    have := hvalid 1 (by omega) 0 (by omega) h01.1 h01.2
    exact this
  let f : ℕ → ℕ := fun t => perm3 (col 0) (col 1) (col t)
  have := srchD_sound (fun d => d.1) colOk (fun _ => false) f ([], []) D 0 hs ?_
  · simp at this
  intro t _ ht
  simp only [zero_add, hlen, Nat.sub_zero] at ht ⊢
  refine ⟨?_, ?_⟩
  · rw [hal t ht]
    split_ifs with h0 h1
    · subst h0; simp [f, perm3]
    · subst h1; simp [f, perm3, Ne.symm hab]
    · exact perm3_mem _ _ _
  · simp only [colOk, List.all_eq_true, bne_iff_ne, ne_eq]
    intro o ho
    obtain ⟨hot, hsh, hsm⟩ := hconf t ht o ho
    have hj : t - 1 - o < t := by omega
    have e := pre_getD f 9 t (t - 1 - o) hj
    rw [show t - 1 - (t - 1 - o) = o by omega] at e
    rw [e]
    intro heq
    exact hvalid t ht (t - 1 - o) (by omega) hsh hsm (perm3_inj _ _ _ _ hab heq)

end SnarkLib

namespace Snark207

open SimpleGraph SnarkLib

-- colouring search nodes (python, symmetric): 3545; FVS size 9

def NBT : ℕ := 8594523473646791584945873474625228344836675395426945318332306662965169818581471934384641338692326877978012459643622644581532797886387817564322538486429186009871992489408592355777643144

def EL : List (ℕ × ℕ) :=
  [(4, 20), (4, 25), (4, 26), (5, 26), (26, 27), (1, 5), (5, 15), (1, 9), (1, 24), (24, 25), (24, 27), (18, 25), (27, 32), (3, 15), (14, 15), (3, 7), (3, 8), (8, 9), (0, 8), (9, 11), (0, 10), (0, 16), (14, 16), (14, 28), (16, 19), (18, 19), (12, 18), (12, 28), (12, 23), (19, 29), (28, 29), (29, 31), (2, 7), (2, 11), (2, 30), (7, 22), (11, 17), (17, 31), (30, 31), (20, 30), (17, 21), (20, 21), (13, 21), (10, 13), (6, 10), (6, 22), (6, 32), (22, 23), (13, 33), (23, 33), (32, 33)]

def colD : List (List ℕ × List ℕ) :=
  [([0], []), ([1], [0]), ([0, 1, 2], [1, 0]), ([0, 1, 2], [0]), ([0, 1, 2], [1, 0]), ([0, 1, 2], [1]), ([0, 1, 2], [2, 0]), ([0, 1, 2], [1]), ([0, 1, 2], [2, 0]), ([0, 1, 2], [7, 0]), ([0, 1, 2], [5, 1, 0]), ([0, 1, 2], [9, 1]), ([0, 1, 2], [7, 1]), ([0, 1, 2], [6]), ([0, 1, 2], [7, 0]), ([0, 1, 2], [1]), ([0, 1, 2], [2, 0]), ([0, 1, 2], [9, 0]), ([0, 1, 2], [1, 0]), ([0, 1, 2], [11, 1]), ([0, 1, 2], [1]), ([0, 1, 2], [2, 0]), ([0, 1, 2], [7, 0]), ([0, 1, 2], [8, 0]), ([0, 1, 2], [2, 1]), ([0, 1, 2], [13, 0]), ([0, 1, 2], [14, 0]), ([0, 1, 2], [3, 0]), ([0, 1, 2], [1, 0]), ([0, 1, 2], [4, 3]), ([0, 1, 2], [6, 2, 0]), ([0, 1, 2], [1, 0]), ([0, 1, 2], [16]), ([0, 1, 2], [13, 0]), ([0, 1, 2], [1, 0]), ([0, 1, 2], [19, 2]), ([0, 1, 2], [16, 2]), ([0, 1, 2], [5, 0]), ([0, 1, 2], [6, 3, 0]), ([0, 1, 2], [38, 4, 0]), ([0, 1, 2], [3, 2]), ([0, 1, 2], [40, 1, 0]), ([0, 1, 2], [1, 0]), ([0, 1, 2], [22, 0]), ([0, 1, 2], [23, 0]), ([0, 1, 2], [9, 0]), ([0, 1, 2], [33, 1, 0]), ([0, 1, 2], [18, 11, 1]), ([0, 1, 2], [5, 4]), ([0, 1, 2], [20, 1, 0]), ([0, 1, 2], [37, 3, 1, 0])]

def hubData : List (List ℕ) :=
  [[8, 0, 10], [5, 1, 9], [7, 2, 11], [20, 4, 25], [18, 12, 23]]

def Wl : List ℕ := [3, 16, 18, 21, 22, 24, 28, 30, 32]

def rankData : List ℕ := [21, 14, 2, 25, 10, 13, 0, 1, 20, 19, 22, 18, 3, 23, 4, 5, 26, 17, 27, 6, 7, 28, 29, 8, 30, 9, 12, 11, 31, 15, 32, 16, 33, 24]

def certData : List (List (List ℕ)) :=
  [[[0, 96697245727345760198979679524079968840294584275155022473, 1509855883461799273980435276655043201622638976483246729, 96677083816042465023395524682237991186099349698797380233, 97134821327146439095685542807699893518410790992198509193], [369135048458533406072876791261336755102633989239364, 1512362181165339265684787102021541050489927161085731396, 0, 397564665897636085516793898831501754385723585320484141048388, 6216621420303528841248535765995071087503362503690791686724], [0, 1512362181165339265684787102003977045000175026912621193, 0, 97061686010165059940623510456891974623373194898251719305, 6216621420303528841248535735797032182808927991636783538825]],
   [[6192916341381692414882373254263339228214713452633489928273, 6188606098953610548882976797096665989468930521512546963537, 6191383845836901884772018504573973525379111064878801522769, 395989335033291451074618522866652782975130868386235990716497, 1517664959072447101575351406157628469463671367402041425], [0, 1509447139567795372314702383626241702837066116177134545, 96630776540419209326197662251204340534946347655179076561, 1518391044335316664711845249025837254356207488254673873, 97010032116140155068069399387535476201374154453318751185], [0, 96696970301521154149603566918701315079735385424455611665, 6191383845842502251966806123035008910581966994309586171153, 96677083748360461430091046647461218118160361034984535313, 97134821327146181991380129819557364755101042987308496145]],
   [[6180969437455133869998513342217131783653046207132264310362, 23630382380710252636823266158561538636388433269630554, 96740330324969902158822400339832929358161179008781788762, 0, 0], [96813372426936836296283143020060921673472244277936924250, 1512362180280912946457092060049317359303034002076345946, 96747527920523595464113359645735793554609951710745470554, 0, 0], [6196055835323957522962121153284734369596566084366642026131, 6188874187674971342489957507654337002203363086894688212627, 6191841786913510109703254974904065855665753646380621256339, 397551146334075172858179171117524816467711919712905601480339, 0]],
   [[96815989150179782198459494212658476786698494315160791058, 1623867502920327180420125882578635048171475393212131034162128914, 96747428286122162046942937356662396351620097740153153554, 0, 397863771163168292898073747774574037098111838086963137734674], [1511977180207025056399280298495420287467111819178285198, 96791268563583659230950957787273562267141443216441743502, 6197851582218609289131607375080772940235018622840704698510, 0, 396777253179118848144010424136615426013820271958227142150286], [23624089337028038597374986269318497159249048932313106, 96701023611885981752026004630112164485836973810153547794, 6191383789930137485847063861481531190634147643421495261202, 1516541705397227828353017564832224060313011667835680786, 6208764007949450479162816974186863654117019128769765566482]],
   [[90120861440070966971753690517042977775433869464, 396456671620114067693270025264820350810050802363812883785880, 0, 1516588843901554579174361392869882872312023453986777240, 0], [369314593854540416712950300516475282853396302588056, 25372929730745242703184702638601260696570294899546917564901528, 396248392974813206914919494862391579913664579329725820364952, 395989334964016810448541163834661372043004997347899294148760, 0], [5770540540249206905591756473868568213253714120968, 96790045664769144833315649543636392823750503409460510984, 0, 1516537237678093917377485447897336043888460098401009928, 1515777516655653119156119369215993339960024558116602120]],
   [[1511942452515811173641843217242932166563425338047897753, 96701161888144077022222039967609396059213722792223305881, 6191383789963895717937586874771033714770973732133458190489, 0, 25393744204325325767731236191941838564264775867342796307603609], [1512749770400296248542940034948179905014300922052949657, 0, 6184369698691958304740038718396881757248317882320156702361, 1510581510333005298200630182417632329134801266391381657, 25462192815686326204566849771001784654391619051023136389412505], [23636715162502079552950241489878682671660772072757017, 0, 96630776541397411235588811285205643151901716784065943321, 0, 397846762745098836601981346768301758036335976681855240509209]],
   [[396346645847528983677465487114471248980850510842789309023069, 6188606099292687704297547586149011846840282038505304589149, 6191383845842315672763043990799567529751062777018007257949, 395989335033284242933035410641854756707004307967877088641885, 1517664959072448043960264698338818690010366522978726749], [396558275811709973798127266281460689153346468297861678311454, 6182695483030198956960746050148679150845612883858129233950, 6184369698586673270296568920061940888519925006070185011230, 398036934308689774745833758643256862590445951529868879853598, 0], [96764317833869380777883221265109181157777129452249679773, 96696970301448245379649181025533896949858536679656785821, 96740372591286182386922562356243242172910260902976685981, 6187333359895178779493119010522836694383975646555738605469, 0]],
   [[96766539547522080551378417545700408331599471867947967893, 1623888034930144811704799833021856918782536148923592557422503317, 96841489426393292268287477541715866108955295876744275349, 0, 396777253190272788916952562868058188996697955225341738411413], [96815985070916259658907095021280744240328295627197031171, 395692564160753179081056624540032582144047098786313832014595, 0, 23695900535337740240715318944997546108136852369744643, 397863770901338588106521217248765376321295909362998394266371], [1509025694989601722509526589704587496010390699161985795, 6188605902388853769847898187759820004095835012161936859907, 0, 0, 6208629755231029465066817696867085959309796829587877438211]],
   [[23624629326454413896197901569755031546527556128518625, 1509447384729746244654955550570888196528341100431454689, 396649748273698507121483901687530698379492334083092301050337, 5792338755673242881064738614878540895044369478113, 23684583799109358918765628655700466462652846313664993], [369314593822380648181982855935023608889921103304481, 25372929730745954333635923021176849111217755240666483032430369, 396248392974813122272211266466538846088459606309792616388385, 395989334964016810448123258978079880654352404529785422321441, 23684023697744579750195819615399501781147557103769377], [369314593822380648171484397751059174333777072416929, 1512344463512060304500813659284770139932203836564146337, 96740330316116484929739036591301161422510921592480524449, 370248349042496868033853480765810277254653877258401, 370062870277259058596817049575677147959840653281441]]]

def pmD : List (ℕ × List (ℕ × ℕ)) :=
  [(0, []), (1, []), (2, []), (3, []), (4, []), (5, [(1, 3)]), (6, []), (7, [(2, 4), (3, 3)]), (8, [(0, 7), (3, 4)]), (9, [(1, 7), (8, 0)]), (10, [(0, 9), (6, 3)]), (11, [(2, 8), (9, 1)]), (12, []), (13, [(10, 2)]), (14, []), (15, [(3, 11), (5, 9), (14, 0)]), (16, [(0, 15), (14, 1)]), (17, [(11, 5)]), (18, [(12, 5)]), (19, [(16, 2), (18, 0)]), (20, [(4, 15)]), (21, [(13, 7), (17, 3), (20, 0)]), (22, [(6, 15), (7, 14)]), (23, [(12, 10), (22, 0)]), (24, [(1, 22)]), (25, [(4, 20), (18, 6), (24, 0)]), (26, [(4, 21), (5, 20)]), (27, [(24, 2), (26, 0)]), (28, [(12, 15), (14, 13)]), (29, [(19, 9), (28, 0)]), (30, [(2, 27), (20, 9)]), (31, [(17, 13), (29, 1), (30, 0)]), (32, [(6, 25), (27, 4)]), (33, [(13, 19), (23, 9), (32, 0)])]

def nb (v : ℕ) : List ℕ := [NBT / 64 ^ (3 * v) % 64, NBT / 64 ^ (3 * v + 1) % 64, NBT / 64 ^ (3 * v + 2) % 64]

def anc (v e : ℕ) : List ℕ := v :: (nb v).eraseIdx e

def ha (j : ℕ) : ℕ := (hubData.getD j []).getD 0 0
def hb (j : ℕ) : ℕ := (hubData.getD j []).getD 1 0
def hc (j : ℕ) : ℕ := (hubData.getD j []).getD 2 0

def rank (u : ℕ) : ℕ := rankData.getD u 0

def dec : ℕ → ℕ → List ℕ → List (List ℕ)
  | 0, _, _ => []
  | f+1, x, cur =>
    if x = 0 then [] else if x % 64 = 63 then cur.reverse :: dec f (x / 64) []
      else dec f (x / 64) ((x % 64 - 1) :: cur)

def cert (v e j : ℕ) : List (List ℕ) :=
  dec 400 (((certData.getD (Wl.idxOf v) []).getD e []).getD j 0) []

def ordA : List ℕ := [0, 8, 9, 1, 5, 26, 4, 20, 30, 31, 29, 28, 12, 23, 22, 6, 10]

def ordB : List ℕ := [2, 7, 3, 15, 14, 16, 19, 18, 25, 24, 27, 32, 33, 13, 21, 17, 11]

def chainB (nb : ℕ → List ℕ) : List ℕ → Bool
  | a :: b :: l => (nb a).contains b && chainB nb (b :: l)
  | _ => true

theorem degree_gen {W : Type*} (H : SimpleGraph W) (v : W) {inst : Fintype (H.neighborSet v)}
    (ψ : W → ℕ) (hψ : Function.Injective ψ) (l : List ℕ) (hnd : l.Nodup)
    (hsurj : ∀ x ∈ l, ∃ w, ψ w = x) (hadj : ∀ w, H.Adj v w ↔ ψ w ∈ l) :
    @SimpleGraph.degree _ H v inst = l.length := by
  rw [← @SimpleGraph.card_neighborSet_eq_degree _ H v inst, Fintype.card_eq_nat_card,
    Nat.card_coe_set_eq]
  have h : ψ '' (H.neighborSet v) = ↑l.toFinset := by
    ext x
    simp only [Set.mem_image, SimpleGraph.mem_neighborSet, List.coe_toFinset, Set.mem_setOf_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hadj w).1 hw
    · intro hx
      obtain ⟨w, rfl⟩ := hsurj x hx
      exact ⟨w, (hadj w).2 hx, rfl⟩
  rw [← Set.ncard_image_of_injective _ hψ, h, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem reach_chain {n : ℕ} (G : SimpleGraph (Fin n)) (nb : ℕ → List ℕ)
    (hadj : ∀ a b : Fin n, G.Adj a b ↔ b.val ∈ nb a.val) (S : Set (Fin n)) (ord : List ℕ)
    (hS : ∀ v : Fin n, v ∈ S ↔ v.val ∈ ord) (hlt : ∀ x ∈ ord, x < n) :
    ∀ l : List ℕ, (∀ z ∈ l, z ∈ ord) → chainB nb l = true → ∀ a ∈ l, ∀ b ∈ l, ∀ v w : S,
      v.val.val = a → w.val.val = b → (G.induce S).Reachable v w
  | [], _, _, a, ha, _, _, _, _, _, _ => by simp at ha
  | [x], _, _, a, ha, b, hb, v, w, hv, hw => by
    rw [List.mem_singleton] at ha hb
    have : v = w := Subtype.ext (Fin.ext (by rw [hv, hw, ha, hb]))
    rw [this]
  | x :: y :: l, hl, h, a, ha, b, hb, v, w, hv, hw => by
    simp only [chainB, Bool.and_eq_true, List.contains_iff_mem] at h
    obtain ⟨hxy, hrest⟩ := h
    have hl' : ∀ z ∈ y :: l, z ∈ ord := fun z hz => hl z (List.mem_cons_of_mem _ hz)
    have IH := reach_chain G nb hadj S ord hS hlt (y :: l) hl' hrest
    have hyo : y ∈ ord := hl' y List.mem_cons_self
    let u : S := ⟨⟨y, hlt y hyo⟩, (hS _).2 hyo⟩
    have step : ∀ v : S, v.val.val = x → (G.induce S).Reachable v u := by
      intro v hv
      apply SimpleGraph.Adj.reachable
      show G.Adj v.val u.val
      rw [hadj, hv]
      exact hxy
    rcases List.mem_cons.1 ha with hax | ha'
    · rcases List.mem_cons.1 hb with hbx | hb'
      · have : v = w := Subtype.ext (Fin.ext (by rw [hv, hw, hax, hbx]))
        rw [this]
      · exact (step v (hv.trans hax)).trans (IH y List.mem_cons_self b hb' u w rfl hw)
    · rcases List.mem_cons.1 hb with hbx | hb'
      · exact (IH a ha' y List.mem_cons_self v u hv rfl).trans (step w (hw.trans hbx)).symm
      · exact IH a ha' b hb' v w hv hw

theorem induce_cycle {n : ℕ} (G : SimpleGraph (Fin n)) (nb : ℕ → List ℕ)
    (hadj : ∀ a b : Fin n, G.Adj a b ↔ b.val ∈ nb a.val) (hnd : ∀ a < n, (nb a).Nodup)
    (S : Set (Fin n)) (ord : List ℕ) (hS : ∀ v : Fin n, v ∈ S ↔ v.val ∈ ord)
    (hlt : ∀ x ∈ ord, x < n) (x0 : ℕ) (hx0 : x0 ∈ ord) (hch : chainB nb ord = true)
    (hdeg : ∀ x ∈ ord, ((nb x).filter (fun y => decide (y ∈ ord))).length = 2)
    {inst : Fintype S} : @SnarkGen.Zhang.IsCycleGraph S inst (G.induce S) := by
  unfold SnarkGen.Zhang.IsCycleGraph
  have hv : ∀ v : S, v.val.val ∈ ord := fun v => (hS _).1 v.2
  refine ⟨?_, fun v => ?_⟩
  · have : Nonempty S := ⟨⟨⟨x0, hlt x0 hx0⟩, (hS _).2 hx0⟩⟩
    exact SimpleGraph.Connected.mk (fun v w => reach_chain G nb hadj S ord hS hlt ord
      (fun z hz => hz) hch _ (hv v) _ (hv w) v w rfl rfl)
  refine (degree_gen _ v (fun w : S => w.val.val) ?_ _ ((hnd _ v.val.isLt).filter _) ?_ ?_).trans
    (hdeg _ (hv v))
  · intro a b h
    exact Subtype.ext (Fin.ext h)
  · intro x hx
    rw [List.mem_filter, decide_eq_true_eq] at hx
    exact ⟨⟨⟨x, hlt x hx.2⟩, (hS _).2 hx.2⟩, rfl⟩
  · intro w
    show G.Adj v.val w.val ↔ _
    rw [hadj, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => ⟨h, hv w⟩, fun h => h.1⟩

theorem hE1 : (SnarkGen.Zhang.g1Edges.all fun p =>
    (nb p.1.val).contains p.2.val && (nb p.2.val).contains p.1.val) = true := by decide +kernel

theorem hE2 : ((List.range 34).all fun a => (nb a).all fun b =>
    SnarkGen.Zhang.g1Edges.any fun p =>
      (p.1.val == a && p.2.val == b) || (p.1.val == b && p.2.val == a)) = true := by decide +kernel

theorem hirr : ∀ a < 34, a ∉ nb a := by decide +kernel

theorem hadj : ∀ a b : Fin 34, SnarkGen.Zhang.g1.Adj a b ↔ b.val ∈ nb a.val := by
  intro a b
  show (a ≠ b ∧ ((a, b) ∈ SnarkGen.Zhang.g1Edges ∨ (b, a) ∈ SnarkGen.Zhang.g1Edges)) ↔ _
  have e1 := hE1
  have e2 := hE2
  simp only [List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem, List.any_eq_true,
    Bool.or_eq_true, beq_iff_eq, List.mem_range] at e1 e2
  constructor
  · rintro ⟨-, h | h⟩
    · exact (e1 _ h).1
    · exact (e1 _ h).2
  · intro h
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact hirr a.val a.isLt h
    obtain ⟨p, hp, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ := e2 a.val a.isLt b.val h
    · left
      have : p = (a, b) := Prod.ext (Fin.ext h1) (Fin.ext h2)
      rwa [this] at hp
    · right
      have : p = (b, a) := Prod.ext (Fin.ext h1) (Fin.ext h2)
      rwa [this] at hp

theorem hlt : ∀ a < 34, ∀ b ∈ nb a, b < 34 := by decide +kernel
theorem hnd : ∀ a < 34, (nb a).Nodup := by decide +kernel
theorem hlen : ∀ a < 34, (nb a).length = 3 := by decide +kernel
theorem h3 : ∀ a < 34, ∀ x ∈ nb a, ∀ y ∈ nb x, a ∉ nb y := by decide +kernel
theorem h4 : ∀ a < 34, ∀ x ∈ nb a, ∀ y ∈ nb x, ∀ z ∈ nb y, a ∈ nb z → x = z ∨ a = y := by
  decide +kernel
theorem hanc : ∀ v < 34, ∀ y ∈ nb v, ∀ z ∈ nb v, y ≠ z → ∃ e < 3, ∀ t ∈ anc v e,
    t = v ∨ t = y ∨ t = z := by decide +kernel
theorem hhub : ∀ j < 5, ha j < 34 ∧ hb j ∈ nb (ha j) ∧ hc j ∈ nb (hb j) := by decide +kernel
theorem hhubdB : ((List.range 5).all fun i => (List.range 5).all fun j => i == j ||
    [ha i, hb i, hc i].all fun x => !(decide (x ∈ [ha j, hb j, hc j]))) = true := by decide +kernel
theorem hhubd : ∀ i < 5, ∀ j < 5, i ≠ j → ∀ x ∈ [ha i, hb i, hc i], x ∉ [ha j, hb j, hc j] := by
  have h := hhubdB
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  intro i hi j hj hij x hx
  rcases h i hi j hj with h | h
  · exact absurd h hij
  · exact h x hx
theorem hrank : ∀ u < 34, u ∉ Wl →
    ((nb u).filter fun w => !(Wl.contains w) && decide (rank u < rank w)).length ≤ 1 := by
  decide +kernel
theorem hrinj : ∀ u < 34, ∀ w < 34, rank u = rank w → u = w := by decide +kernel
theorem hcertB : ((List.range 34).all fun v => !(decide (v ∈ Wl)) || (List.range 3).all fun e =>
    (List.range 5).all fun j => ((anc v e).any fun x => decide (x ∈ [ha j, hb j, hc j])) ||
      sysB nb 5 (anc v e) [ha j, hb j, hc j] (cert v e j)) = true := by decide +kernel
theorem hcert : ∀ v < 34, v ∈ Wl → ∀ e < 3, ∀ j < 5, (∀ x ∈ anc v e, x ∉ [ha j, hb j, hc j]) →
    sysB nb 5 (anc v e) [ha j, hb j, hc j] (cert v e j) = true := by
  have h := hcertB
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, List.any_eq_true, decide_eq_true_eq] at h
  intro v hv hW e he j hj hpre
  rcases h v hv with h | h
  · exact absurd hW h
  · rcases h e he j hj with ⟨x, hx, hx'⟩ | h
    · exact absurd hx' (hpre x hx)
    · exact h
theorem hEL : ∀ x ∈ EL, x.1 < 34 ∧ x.2 < 34 ∧ x.2 ∈ nb x.1 := by decide +kernel
theorem hal : ∀ t < EL.length, (colD.getD t ([], [])).1 =
    if t = 0 then [0] else if t = 1 then [1] else [0, 1, 2] := by decide +kernel
theorem h01 : sharesB (EL.getD 1 (0, 0)) (EL.getD 0 (0, 0)) = true ∧
    sameE (EL.getD 1 (0, 0)) (EL.getD 0 (0, 0)) = false := by decide +kernel
theorem hconf : ∀ t < EL.length, ∀ o ∈ (colD.getD t ([], [])).2, o < t ∧
    sharesB (EL.getD t (0, 0)) (EL.getD (t - 1 - o) (0, 0)) = true ∧
    sameE (EL.getD t (0, 0)) (EL.getD (t - 1 - o) (0, 0)) = false := by decide +kernel
theorem hcol : srchD (fun d => d.1) colOk (fun _ => false) colD [] = true := by decide +kernel

theorem hltA : ∀ x ∈ ordA, x < 34 := by decide +kernel
theorem hltB : ∀ x ∈ ordB, x < 34 := by decide +kernel
theorem hchA : chainB nb ordA = true := by decide +kernel
theorem hchB : chainB nb ordB = true := by decide +kernel
theorem hdegA : ∀ x ∈ ordA, ((nb x).filter (fun y => decide (y ∈ ordA))).length = 2 := by
  decide +kernel
theorem hdegB : ∀ x ∈ ordB, ((nb x).filter (fun y => decide (y ∈ ordB))).length = 2 := by
  decide +kernel
theorem hAB : ∀ x < 34, (x ∈ ordB ↔ x ∉ ordA) := by decide +kernel

theorem reg {inst : SnarkGen.Zhang.g1.LocallyFinite} :
    @SimpleGraph.IsRegularOfDegree _ SnarkGen.Zhang.g1 inst 3 := by
  intro v
  rw [degree_eq _ v (nb v.val) (hlt _ v.isLt) (hnd _ v.isLt) (fun b => hadj v b), hlen _ v.isLt]

theorem perm : SnarkGen.Zhang.IsPermutationGraph SnarkGen.Zhang.g1 := by
  unfold SnarkGen.Zhang.IsPermutationGraph
  refine ⟨reg, {v | v.val ∈ ordA},
    induce_cycle _ nb hadj hnd _ ordA (fun v => Iff.rfl) hltA 0 (by decide) hchA hdegA,
    induce_cycle _ nb hadj hnd _ ordB (fun v => ?_) hltB 2 (by decide) hchB hdegB⟩
  show v.val ∉ ordA ↔ v.val ∈ ordB
  exact (hAB _ v.isLt).symm

theorem main : ¬ SnarkGen.Zhang.ZhangConjecture := by
  intro h
  have c5 : SnarkGen.Zhang.CyclicallyEdgeConnected SnarkGen.Zhang.g1 5 :=
    cycConn (by norm_num) _ nb hadj hlt (by norm_num) Wl rank hrank hrinj 5 anc ha hb hc cert hanc
      hhub hhubd hcert
  have c4 : SnarkGen.Zhang.CyclicallyEdgeConnected SnarkGen.Zhang.g1 4 :=
    fun S hS hc => c5 S hS (by omega)
  have hs : SnarkGen.Zhang.IsSnark SnarkGen.Zhang.g1 := by
    unfold SnarkGen.Zhang.IsSnark
    exact ⟨reg, notColourable (by norm_num) _ nb hadj EL colD (by decide) (by decide) hEL hal h01
      hconf hcol, c4, girth5 _ nb hadj h3 h4⟩
  obtain ⟨e⟩ := h (Fin 34) SnarkGen.Zhang.g1 reg c5 perm hs
  have := Fintype.card_congr e.toEquiv
  simp at this

end Snark207

open SnarkGen.Zhang in
theorem solution : ¬ ZhangConjecture := by
  exact Snark207.main
