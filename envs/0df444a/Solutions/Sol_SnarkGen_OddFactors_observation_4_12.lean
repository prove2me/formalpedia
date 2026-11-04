-- Prove2me | solution 1 for SnarkGen.OddFactors.observation_4_12
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T14:19:45.185558+00:00
-- url     : https://prove2.me/submissions/99b64a14-d275-49a9-9ca3-f9a2b53b2364

import Mathlib
import Definitions.Def_SnarkGen_OddFactors_Snark
import Definitions.Def_SnarkGen_OddFactors_TwoFactor
import Definitions.Def_SnarkGen_OddFactors_G81

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

namespace SnarkOdd

open SimpleGraph SnarkLib

/-! ### Every 2-factor has only odd components: enumerate the complementary perfect matchings -/

/-- data per vertex `t`: `(t, [(u, offset of u in the reversed assignment)])` for earlier neighbours -/
def pmOk (d : ℕ × List (ℕ × ℕ)) (asg : List ℕ) (c : ℕ) : Bool :=
  d.2.all fun x => (c == x.1) == (asg.getD x.2 99 == d.1)

def enc : List ℕ → ℕ
  | [] => 0
  | c :: r => c + 64 * enc r

theorem enc_dig : ∀ (l : List ℕ), (∀ x ∈ l, x < 64) → ∀ k, enc l / 64 ^ k % 64 = l.getD k 0
  | [], _, k => by simp [enc]
  | c :: r, h, 0 => by
    simp only [enc, pow_zero, Nat.div_one, List.getD_cons_zero]
    have := h c List.mem_cons_self
    omega
  | c :: r, h, k+1 => by
    have hc := h c List.mem_cons_self
    simp only [enc, List.getD_cons_succ]
    rw [pow_succ, mul_comm (64 ^ k) 64, ← Nat.div_div_eq_div_mul,
      show (c + 64 * enc r) / 64 = enc r by omega]
    exact enc_dig r (fun x hx => h x (List.mem_cons_of_mem _ hx)) k

def fnbP (nb : ℕ → List ℕ) (n P u : ℕ) : List ℕ :=
  (nb u).filter fun w => w != P / 64 ^ (n - 1 - u) % 64

def walkP (nb : ℕ → List ℕ) (n P start : ℕ) : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | f+1, prev, cur =>
    if cur = start then [] else
      cur :: walkP nb n P start f cur (((fnbP nb n P cur).filter fun w => w != prev).headD cur)

def cycP (nb : ℕ → List ℕ) (n P v : ℕ) : List ℕ :=
  v :: walkP nb n P v n v ((fnbP nb n P v).headD v)

def cycChk (nb : ℕ → List ℕ) (n P : ℕ) (C : List ℕ) : Bool :=
  nodupM 0 C && (C.all fun u => decide (u < n) && (fnbP nb n P u).all fun w => (maskOf C).testBit w) &&
    ((edgs C).all fun x => (fnbP nb n P x.1).contains x.2) && (C.length % 2 == 1)

def compsP (nb : ℕ → List ℕ) (n P : ℕ) : ℕ → ℕ → List (List ℕ)
  | 0, _ => []
  | f+1, vis =>
    if Nat.log2 ((vis + 1) ^^^ vis) < n then
      cycP nb n P (Nat.log2 ((vis + 1) ^^^ vis)) ::
        compsP nb n P f (vis ||| maskOf (cycP nb n P (Nat.log2 ((vis + 1) ^^^ vis))))
    else []

def orAll : List (List ℕ) → ℕ
  | [] => 0
  | C :: cs => maskOf C ||| orAll cs

theorem testBit_orAll (w : ℕ) : ∀ cs : List (List ℕ), (orAll cs).testBit w = true → ∃ C ∈ cs, w ∈ C
  | [], h => by simp [orAll] at h
  | C :: cs, h => by
    simp only [orAll, Nat.testBit_lor, Bool.or_eq_true, testBit_maskOf, decide_eq_true_eq] at h
    rcases h with h | h
    · exact ⟨C, List.mem_cons_self, h⟩
    · obtain ⟨C', hC', hw⟩ := testBit_orAll w cs h
      exact ⟨C', List.mem_cons_of_mem _ hC', hw⟩

def QoddP (nb : ℕ → List ℕ) (n P : ℕ) : Bool :=
  ((compsP nb n P n 0).all fun C => cycChk nb n P C) && (orAll (compsP nb n P n 0) == 2 ^ n - 1)

def Qodd (nb : ℕ → List ℕ) (n : ℕ) (asg : List ℕ) : Bool := QoddP nb n (enc asg)

theorem chain_reach {n : ℕ} (hn : 0 < n) (F : SimpleGraph (Fin n)) (R : ℕ → ℕ → Prop)
    (hR : ∀ a b, R a b → F.Adj (toF hn a) (toF hn b)) :
    ∀ p : List ℕ, (∀ x ∈ edgs p, R x.1 x.2) → ∀ x ∈ p, F.Reachable (toF hn (p.headD 0)) (toF hn x)
  | [], _, x, hx => absurd hx List.not_mem_nil
  | [a], _, x, hx => by rw [List.mem_singleton.1 hx]; exact SimpleGraph.Reachable.refl _
  | a :: b :: r, hc, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact SimpleGraph.Reachable.refl _
    · have h1 : F.Adj (toF hn a) (toF hn b) := hR a b (hc (a, b) (by simp [edgs]))
      have h2 := chain_reach hn F R hR (b :: r)
        (fun y hy => hc y (by simp only [edgs]; exact List.mem_cons_of_mem _ hy)) x hx
      exact h1.reachable.trans h2

theorem walk_closed {V : Type} (F : SimpleGraph V) (P : V → Prop)
    (hP : ∀ u w, P u → F.Adj u w → P w) : ∀ {u w : V} (_ : F.Walk u w), P u → P w
  | _, _, .nil, h => h
  | _, _, .cons h' p, h => walk_closed F P hP p (hP _ _ h h')

theorem allOdd {n : ℕ} (hn : 0 < n) (hn64 : n ≤ 64) (G : SimpleGraph (Fin n)) (nb : ℕ → List ℕ)
    (hadj : ∀ a b : Fin n, G.Adj a b ↔ b.val ∈ nb a.val) (hlt : ∀ a < n, ∀ b ∈ nb a, b < n)
    (hnd : ∀ a < n, (nb a).Nodup) (hlen : ∀ a < n, (nb a).length = 3)
    (D : List (ℕ × List (ℕ × ℕ))) (hDlen : D.length = n)
    (hD1 : ∀ t < n, (D.getD t (0, [])).1 = t)
    (hD2 : ∀ t < n, ∀ x ∈ (D.getD t (0, [])).2, x.1 ∈ nb t ∧ x.1 < t ∧ x.2 = t - 1 - x.1)
    (hs : srchD (fun d => nb d.1) pmOk (Qodd nb n) D [] = true) :
    SnarkGen.OddFactors.AllTwoFactorsOdd G := by
  classical
  intro F hF c
  obtain ⟨hle, hreg⟩ := hF
  have hsymm : ∀ a b, a < n → b < n → (b ∈ nb a ↔ a ∈ nb b) := by
    intro a b ha hb
    rw [← adjN hn G nb hadj ha hb, ← adjN hn G nb hadj hb ha]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hm : ∀ v, v < n → ∃ m ∈ nb v, ∀ x ∈ nb v, (F.Adj (toF hn v) (toF hn x) ↔ x ≠ m) := by
    intro v hv
    let l := (nb v).filter fun x => decide (F.Adj (toF hn v) (toF hn x))
    have hl : ∀ x ∈ l, x < n := fun x hx => hlt v hv x (List.mem_filter.1 hx).1
    have hlnd : l.Nodup := (hnd v hv).filter _
    have hFadj : ∀ b : Fin n, F.Adj (toF hn v) b ↔ b.val ∈ l := by
      intro b
      simp only [l, List.mem_filter, decide_eq_true_eq, toF_eq]
      constructor
      · intro h
        refine ⟨?_, h⟩
        have := hle h
        rw [hadj, toF_val hn hv] at this
        exact this
      · exact fun h => h.2
    have hdeg := hreg (toF hn v)
    rw [degree_eq F (toF hn v) l hl hlnd hFadj] at hdeg
    have hsplit := List.length_eq_length_filter_add (l := nb v)
      (fun x => decide (F.Adj (toF hn v) (toF hn x)))
    have hdeg' : ((nb v).filter fun x => decide (F.Adj (toF hn v) (toF hn x))).length = 2 := hdeg
    have h1 : ((nb v).filter fun x => !decide (F.Adj (toF hn v) (toF hn x))).length = 1 := by
      have := hlen v hv
      omega
    obtain ⟨m, hmeq⟩ := List.length_eq_one_iff.1 h1
    have hmmem : m ∈ (nb v).filter fun x => !decide (F.Adj (toF hn v) (toF hn x)) := by
      rw [hmeq]; exact List.mem_singleton_self _
    rw [List.mem_filter] at hmmem
    refine ⟨m, hmmem.1, fun x hx => ?_⟩
    constructor
    · rintro h rfl
      simp [h] at hmmem
    · intro hxm
      by_contra hF'
      have : x ∈ (nb v).filter fun x => !decide (F.Adj (toF hn v) (toF hn x)) :=
        List.mem_filter.2 ⟨hx, by simp [hF']⟩
      rw [hmeq, List.mem_singleton] at this
      exact hxm this
  choose m hmnb hmadj using hm
  let f : ℕ → ℕ := fun v => if h : v < n then m v h else 0
  have hf : ∀ v (hv : v < n), f v ∈ nb v ∧
      ∀ x ∈ nb v, (F.Adj (toF hn v) (toF hn x) ↔ x ≠ f v) := by
    intro v hv
    simp only [f, dif_pos hv]
    exact ⟨hmnb v hv, hmadj v hv⟩
  have hQ := srchD_sound (fun d => nb d.1) pmOk (Qodd nb n) f (0, []) D 0 hs (by
    intro t _ ht
    simp only [zero_add, hDlen, Nat.sub_zero] at ht ⊢
    rw [hD1 t ht]
    refine ⟨(hf t ht).1, ?_⟩
    simp only [pmOk, List.all_eq_true]
    intro x hx
    obtain ⟨hu, hut, hoff⟩ := hD2 t ht x hx
    rw [hD1 t ht, hoff, pre_getD f 99 t x.1 hut]
    have hun : x.1 < n := by omega
    have htu : t ∈ nb x.1 := (hsymm t x.1 ht hun).1 hu
    have key : f t = x.1 ↔ f x.1 = t := by
      have e1 := (hf t ht).2 x.1 hu
      have e2 := (hf x.1 hun).2 t htu
      constructor
      · intro h
        by_contra h'
        have : F.Adj (toF hn x.1) (toF hn t) := e2.2 (Ne.symm h')
        exact (e1.1 this.symm) h.symm
      · intro h
        by_contra h'
        have : F.Adj (toF hn t) (toF hn x.1) := e1.2 (Ne.symm h')
        exact (e2.1 this.symm) h.symm
    have hb : (f t == x.1) = (f x.1 == t) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact key
    simp [hb])
  simp only [zero_add, hDlen] at hQ
  have h64 : ∀ x ∈ pre f n, x < 64 := by
    have : ∀ i, ∀ x ∈ pre f i, i ≤ n → x < 64 := by
      intro i
      induction i with
      | zero => simp [pre]
      | succ i ih =>
        intro x hx hi
        simp only [pre, List.mem_cons] at hx
        rcases hx with rfl | hx
        · have := hlt i (by omega) _ (hf i (by omega)).1; omega
        · exact ih x hx (by omega)
    exact fun x hx => this n x hx le_rfl
  have hmf : ∀ u, u < n → enc (pre f n) / 64 ^ (n - 1 - u) % 64 = f u := by
    intro u hu
    rw [enc_dig _ h64, pre_getD f 0 n u hu]
  have hfnb : ∀ u, u < n → ∀ x, x ∈ fnbP nb n (enc (pre f n)) u ↔ x ∈ nb u ∧ x ≠ f u := by
    intro u hu x
    simp [fnbP, hmf u hu]
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v =>
  simp only [Qodd, QoddP, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hQ
  obtain ⟨hall, hcov⟩ := hQ
  have hbit : (orAll (compsP nb n (enc (pre f n)) n 0)).testBit v.val = true := by
    rw [hcov, Nat.testBit_two_pow_sub_one]
    simpa using v.isLt
  obtain ⟨T, hTc, hvT⟩ := testBit_orAll v.val _ hbit
  have hc := hall T hTc
  simp only [cycChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.contains_iff_mem,
    beq_iff_eq] at hc
  obtain ⟨⟨⟨hTnd, hTcl⟩, hTch⟩, hTodd⟩ := hc
  have hTnd' := (nodupM_spec T 0 hTnd).1
  have hTlt : ∀ x ∈ T, x < n := fun x hx => (hTcl x hx).1
  have hreach : ∀ x ∈ T, F.Reachable (toF hn (T.headD 0)) (toF hn x) :=
    chain_reach hn F (fun a b => a < n ∧ b ∈ fnbP nb n (enc (pre f n)) a) (by
      rintro a b ⟨ha, hab⟩
      rw [hfnb a ha] at hab
      exact ((hf a ha).2 b hab.1).2 hab.2) T
      (fun x hx => ⟨hTlt _ (edgs_mem T x hx).1, hTch x hx⟩)
  have hsupp : (F.connectedComponentMk v).supp = {w : Fin n | w.val ∈ T} := by
    ext w
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq,
      Set.mem_setOf_eq]
    constructor
    · intro h
      obtain ⟨p⟩ := h.symm
      refine walk_closed F (fun u => u.val ∈ T) ?_ p hvT
      intro u w' hu hadj'
      have hG := hle hadj'
      rw [hadj] at hG
      have hw' := (hTcl u.val hu).2 w'.val ((hfnb u.val u.isLt w'.val).2 ⟨hG, ?_⟩)
      · rw [testBit_maskOf] at hw'
        simpa using hw'
      · intro heq
        have := ((hf u.val u.isLt).2 w'.val hG).1
        rw [toF_eq, toF_eq] at this
        exact this hadj' heq
    · intro hw
      have h1 := hreach w.val hw
      have h2 := hreach v.val hvT
      rw [toF_eq] at h1 h2
      exact (h2.symm.trans h1).symm
  rw [hsupp, Nat.card_coe_set_eq, ncard_val T hTlt hTnd']
  exact Nat.odd_iff.2 hTodd

end SnarkOdd

namespace Snark1dd

open SimpleGraph SnarkLib SnarkOdd


def NBT : ℕ := 289960378197705723271752073746270136364516921699141403687715049825921593145876944995168941488807743593074575670067950995523787788520672735361

def EL : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (2, 7), (4, 6), (4, 8), (3, 8), (3, 9), (5, 7), (5, 9), (6, 10), (7, 11), (8, 12), (9, 13), (10, 14), (10, 15), (11, 14), (11, 16), (14, 17), (12, 17), (13, 17), (12, 18), (13, 19), (15, 20), (15, 21), (16, 20), (16, 22), (18, 22), (18, 23), (19, 21), (19, 23), (20, 24), (23, 24), (21, 25), (22, 25), (24, 25)]

def colD : List (List ℕ × List ℕ) :=
  [([0], []), ([1], [0]), ([0, 1, 2], [1, 0]), ([0, 1, 2], [2]), ([0, 1, 2], [3, 0]), ([0, 1, 2], [3]), ([0, 1, 2], [4, 0]), ([0, 1, 2], [3, 1]), ([0, 1, 2], [4, 0]), ([0, 1, 2], [6, 0]), ([0, 1, 2], [7, 0]), ([0, 1, 2], [6, 4]), ([0, 1, 2], [7, 1, 0]), ([0, 1, 2], [7, 5]), ([0, 1, 2], [7, 2]), ([0, 1, 2], [6, 5]), ([0, 1, 2], [5, 3]), ([0, 1, 2], [3]), ([0, 1, 2], [4, 0]), ([0, 1, 2], [4, 1]), ([0, 1, 2], [5, 0]), ([0, 1, 2], [3, 1]), ([0, 1, 2], [6, 0]), ([0, 1, 2], [6, 1, 0]), ([0, 1, 2], [8, 1]), ([0, 1, 2], [8, 1]), ([0, 1, 2], [7]), ([0, 1, 2], [8, 0]), ([0, 1, 2], [7, 1]), ([0, 1, 2], [8, 0]), ([0, 1, 2], [5, 0]), ([0, 1, 2], [6, 0]), ([0, 1, 2], [6, 4]), ([0, 1, 2], [7, 1, 0]), ([0, 1, 2], [7, 5]), ([0, 1, 2], [3, 1, 0]), ([0, 1, 2], [8, 3]), ([0, 1, 2], [7, 6, 0]), ([0, 1, 2], [3, 2, 1, 0])]

def hubData : List (List ℕ) :=
  [[1, 0, 2], [3, 8, 4], [6, 10, 14], [9, 13, 17]]

def Wl : List ℕ := [1, 3, 12, 14, 15, 22, 24]

def rankData : List ℕ := [0, 19, 5, 20, 2, 12, 4, 11, 1, 13, 3, 10, 21, 14, 22, 23, 9, 6, 7, 16, 8, 17, 24, 15, 25, 18]

def certData : List (List (List ℕ)) :=
  [[[0, 0, 20521688693096021758113442151804994, 20495928616444150845734247239008322], [0, 1219853891102814463586726145, 20521688693134703334284578084647105, 20537143158269650349712489848807681], [0, 0, 20480637523966745157856902086684865, 20537141900685163885638659723796737]],
   [[20450134426305218341403424886432585, 0, 1310745735436698923439986759559881545, 0], [0, 0, 1313388075349945160928583189220061377, 0], [0, 0, 1310756582577719708073717620323152065, 20495770159509351478192673026502849]],
   [[21958093108553166521019723297686138113536978, 343788850908024279801042427144983835096018, 83888417382928761651387016666373944274, 0], [5362233667738345352577556206309785477449, 0, 1313418965749055530763103953106006345, 320891374327989077732027794989385], [1309139079052510500261509604539375945, 0, 1313388809607588660219327475282112841, 0]],
   [[83805999969727304751792983244457681810, 1310117786634574437811151245323314066, 0, 0], [83806329558883057137615985860352189330, 1309762200992764154789726924013872018, 0, 0], [21958093094015025065472905321626903910638603, 343787920178741568359436106614991190320139, 0, 84120397134388274409218899237626012683]],
   [[5759104470698667665180563678297796368846193264213, 90030608845128018949384989104947154866321540181, 343962983432263007199164662017081798919765, 344556068901327951025648842904827046233685], [89940354845477840124072921489144241964495979467, 1406346454700662206855254265702158380687500235, 0, 5378479314993158885898635226230988547019], [5756182710109625396229246698400569900103735755723, 1406396407296323097572141461589286183255745483, 0, 344222661135113182684397537164051108144075]],
   [[5759127122017051979524039722810503611183988016538, 90006173100843264327165935508602603341613958554, 1410240496963505922148637368906380720410002842, 1411301743804782017484298209123555251239847322], [5756182356133178811581302820407008409723547223377, 90121946672421611678936877884984438990297695569, 1410272817656204229041813158012632949918074193, 1411291459053427584966612345866581543092028753], [89940349315391911400941533123397134751414158673, 1408155468702293329270969053434217597628122449, 22035512788574660161995305477786927704638801, 22051429862606631766717533422659062876407121]],
   [[368395670792608514532933664707136090175165818537305, 5767804592479501018390093583685375774063005074777, 90257460331326298654460958175078850925473629529, 22051429068478996624731340173201449558017369], [368582685901317985257261158313809133016381465638425, 5761958962593523890603880411439241531638752294425, 90167607738474784941263007381545791668276770329, 22051588396302855977769270899752615827555865], [89940349314601688118392007985122346645172831317, 1408155418085815678317899115787999559855162453, 22035512776202709632436757366945297744053333, 5383649674921630035935527140291439019093]]]

def pmD : List (ℕ × List (ℕ × ℕ)) :=
  [(0, []), (1, [(0, 0)]), (2, [(0, 1)]), (3, [(0, 2)]), (4, [(1, 2)]), (5, [(1, 3)]), (6, [(2, 3), (4, 1)]), (7, [(2, 4), (5, 1)]), (8, [(3, 4), (4, 3)]), (9, [(3, 5), (5, 3)]), (10, [(6, 3)]), (11, [(7, 3)]), (12, [(8, 3)]), (13, [(9, 3)]), (14, [(10, 3), (11, 2)]), (15, [(10, 4)]), (16, [(11, 4)]), (17, [(12, 4), (13, 3), (14, 2)]), (18, [(12, 5)]), (19, [(13, 5)]), (20, [(15, 4), (16, 3)]), (21, [(15, 5), (19, 1)]), (22, [(16, 5), (18, 3)]), (23, [(18, 4), (19, 3)]), (24, [(20, 3), (23, 0)]), (25, [(21, 3), (22, 2), (24, 0)])]

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

theorem hE1 : (SnarkGen.OddFactors.G81Edges.all fun p =>
    (nb p.1.val).contains p.2.val && (nb p.2.val).contains p.1.val) = true := by decide +kernel

theorem hE2 : ((List.range 26).all fun a => (nb a).all fun b =>
    SnarkGen.OddFactors.G81Edges.any fun p =>
      (p.1.val == a && p.2.val == b) || (p.1.val == b && p.2.val == a)) = true := by decide +kernel

theorem hadj : ∀ a b : Fin 26, SnarkGen.OddFactors.G81.Adj a b ↔ b.val ∈ nb a.val := by
  intro a b
  show ((a, b) ∈ SnarkGen.OddFactors.G81Edges ∨ (b, a) ∈ SnarkGen.OddFactors.G81Edges) ↔ _
  have e1 := hE1
  have e2 := hE2
  simp only [List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem, List.any_eq_true,
    Bool.or_eq_true, beq_iff_eq, List.mem_range] at e1 e2
  constructor
  · rintro (h | h)
    · exact (e1 _ h).1
    · exact (e1 _ h).2
  · intro h
    obtain ⟨p, hp, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ := e2 a.val a.isLt b.val h
    · left
      have : p = (a, b) := Prod.ext (Fin.ext h1) (Fin.ext h2)
      rwa [this] at hp
    · right
      have : p = (b, a) := Prod.ext (Fin.ext h1) (Fin.ext h2)
      rwa [this] at hp

theorem hlt : ∀ a < 26, ∀ b ∈ nb a, b < 26 := by decide +kernel
theorem hnd : ∀ a < 26, (nb a).Nodup := by decide +kernel
theorem hlen : ∀ a < 26, (nb a).length = 3 := by decide +kernel
theorem h3 : ∀ a < 26, ∀ x ∈ nb a, ∀ y ∈ nb x, a ∉ nb y := by decide +kernel
theorem h4 : ∀ a < 26, ∀ x ∈ nb a, ∀ y ∈ nb x, ∀ z ∈ nb y, a ∈ nb z → x = z ∨ a = y := by
  decide +kernel
theorem hanc : ∀ v < 26, ∀ y ∈ nb v, ∀ z ∈ nb v, y ≠ z → ∃ e < 3, ∀ t ∈ anc v e,
    t = v ∨ t = y ∨ t = z := by decide +kernel
theorem hhub : ∀ j < 4, ha j < 26 ∧ hb j ∈ nb (ha j) ∧ hc j ∈ nb (hb j) := by decide +kernel
theorem hhubdB : ((List.range 4).all fun i => (List.range 4).all fun j => i == j ||
    [ha i, hb i, hc i].all fun x => !(decide (x ∈ [ha j, hb j, hc j]))) = true := by decide +kernel
theorem hhubd : ∀ i < 4, ∀ j < 4, i ≠ j → ∀ x ∈ [ha i, hb i, hc i], x ∉ [ha j, hb j, hc j] := by
  have h := hhubdB
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  intro i hi j hj hij x hx
  rcases h i hi j hj with h | h
  · exact absurd h hij
  · exact h x hx
theorem hrank : ∀ u < 26, u ∉ Wl →
    ((nb u).filter fun w => !(Wl.contains w) && decide (rank u < rank w)).length ≤ 1 := by
  decide +kernel
theorem hrinj : ∀ u < 26, ∀ w < 26, rank u = rank w → u = w := by decide +kernel
theorem hcertB : ((List.range 26).all fun v => !(decide (v ∈ Wl)) || (List.range 3).all fun e =>
    (List.range 4).all fun j => ((anc v e).any fun x => decide (x ∈ [ha j, hb j, hc j])) ||
      sysB nb 4 (anc v e) [ha j, hb j, hc j] (cert v e j)) = true := by decide +kernel
theorem hcert : ∀ v < 26, v ∈ Wl → ∀ e < 3, ∀ j < 4, (∀ x ∈ anc v e, x ∉ [ha j, hb j, hc j]) →
    sysB nb 4 (anc v e) [ha j, hb j, hc j] (cert v e j) = true := by
  have h := hcertB
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, List.any_eq_true, decide_eq_true_eq] at h
  intro v hv hW e he j hj hpre
  rcases h v hv with h | h
  · exact absurd hW h
  · rcases h e he j hj with ⟨x, hx, hx'⟩ | h
    · exact absurd hx' (hpre x hx)
    · exact h
theorem hEL : ∀ x ∈ EL, x.1 < 26 ∧ x.2 < 26 ∧ x.2 ∈ nb x.1 := by decide +kernel
theorem hal : ∀ t < EL.length, (colD.getD t ([], [])).1 =
    if t = 0 then [0] else if t = 1 then [1] else [0, 1, 2] := by decide +kernel
theorem h01 : sharesB (EL.getD 1 (0, 0)) (EL.getD 0 (0, 0)) = true ∧
    sameE (EL.getD 1 (0, 0)) (EL.getD 0 (0, 0)) = false := by decide +kernel
theorem hconf : ∀ t < EL.length, ∀ o ∈ (colD.getD t ([], [])).2, o < t ∧
    sharesB (EL.getD t (0, 0)) (EL.getD (t - 1 - o) (0, 0)) = true ∧
    sameE (EL.getD t (0, 0)) (EL.getD (t - 1 - o) (0, 0)) = false := by decide +kernel
theorem hcol : srchD (fun d => d.1) colOk (fun _ => false) colD [] = true := by decide +kernel
theorem hD1 : ∀ t < 26, (pmD.getD t (0, [])).1 = t := by decide +kernel
theorem hD2 : ∀ t < 26, ∀ x ∈ (pmD.getD t (0, [])).2, x.1 ∈ nb t ∧ x.1 < t ∧ x.2 = t - 1 - x.1 := by
  decide +kernel
theorem hpm : srchD (fun d => nb d.1) pmOk (Qodd nb 26) pmD [] = true := by decide +kernel

theorem reg : SnarkGen.OddFactors.G81.IsRegularOfDegree 3 := by
  intro v
  rw [degree_eq _ v (nb v.val) (hlt _ v.isLt) (hnd _ v.isLt) (fun b => hadj v b), hlen _ v.isLt]

theorem main : SnarkGen.OddFactors.IsSnark SnarkGen.OddFactors.G81 ∧
    SnarkGen.OddFactors.AllTwoFactorsOdd SnarkGen.OddFactors.G81 := by
  refine ⟨?_, allOdd (by norm_num) (by norm_num) _ nb hadj hlt hnd hlen pmD (by decide) hD1 hD2 hpm⟩
  unfold SnarkGen.OddFactors.IsSnark
  exact ⟨reg, notColourable (by norm_num) _ nb hadj EL colD (by decide) (by decide) hEL hal h01 hconf hcol,
    cycConn (by norm_num) _ nb hadj hlt (by norm_num) Wl rank hrank hrinj 4 anc ha hb hc cert hanc
      hhub hhubd hcert,
    girth5 _ nb hadj h3 h4⟩

end Snark1dd

open SnarkGen.OddFactors in
theorem solution : IsSnark G81 ∧ AllTwoFactorsOdd G81 := by
  exact Snark1dd.main
