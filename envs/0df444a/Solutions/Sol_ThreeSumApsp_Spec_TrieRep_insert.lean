-- Prove2me | solution 1 for ThreeSumApsp.Spec.TrieRep.insert
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:04:32.56912+00:00
-- url     : https://prove2.me/submissions/5838940d-411d-41ac-87ed-b7bd5ce819c4

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_Trie
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# Tries in one array (Section 4.3)

"for each tile we store its boxes, with their values, in a standard trie on their strings of L
symbols.  Thus […] looking up or inserting a box, takes O(L) operations."  Here a string is a list
of L digits below 11, for the ten terms and the star.

All tries live in one array of integers and are numbered; the number of a trie is the number of its
tile.  A vertex is a block of eleven consecutive cells, one for each symbol, holding the address of
the child, or 0 if there is none; a vertex at depth L holds the value of its box in its first cell.
A box is stored if the pointers for its L symbols lead from the root of the trie to such a vertex
(`trieWalk`).  A new vertex is appended at the end of the array (`trieNew`).  The two operations
are `trieInsert` and `trieLookup`.

The interface is `TrieRep`: "the array holds tries with these roots and these stored values".  It
holds for an array without tries (`TrieRep.empty`), it is kept by a new trie (`TrieRep.new`) and by
an insertion (`TrieRep.insert`), and it says what a lookup returns (`TrieRep.lookup`).  `WalkOK` and
`InsertOK` say in addition that every address met on the way lies inside the array
(`TrieRep.walkOK`, `TrieRep.insertOK`).

The proof.  The pair (i, w) names the vertex of trie number i to which the prefix w leads.  The
invariant `TrieInv` gives every vertex its address nd (i, w), 0 if there is none.  `TrieRep` says
that such an nd exists, with nd (i, []) = roots i and the value v in the cell nd x for every entry
f x = some v.
1. Three steps keep the invariant: a new root, a new child, a value written at depth L
   (`TrieInv.newRoot`, `TrieInv.newChild`, `TrieInv.setVal`).  The first gives `TrieRep.new`.
2. An insertion is a sequence of new children and then one write.  Each step extends the tries
   (`TrieExt`): no vertex moves, no root appears, no value of another string changes.  `Inserted`
   collects what holds at the end, and `trieInsert_spec` proves it by induction on the rest of the
   string.  This gives `TrieRep.insert` and `TrieRep.insertOK`.
3. A lookup goes from the vertex of a prefix to the vertex of the next prefix (`trieWalk_spec`).
   This gives `TrieRep.lookup` and `TrieRep.walkOK`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The operations -/


































/-- A vertex has eleven cells. -/
theorem length_trieNew (T : List ℤ) : (trieNew T).length = T.length + 11 := by
  simp [trieNew]
















end ThreeSumApsp.Spec

end

namespace ThreeSumApsp.Spec

/-! ## Arrays as functions -/




private theorem cells_set (T : List ℤ) (a : ℕ) (z : ℤ) (ha : a < T.length) :
    cells (T.set a z) = Function.update (cells T) a z := by
  funext x
  by_cases hx : x = a
  · subst hx
    simp [cells, ha]
  · rw [Function.update_of_ne hx]
    simp only [cells, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hx)]

private theorem cells_trieNew (T : List ℤ) : cells (trieNew T) = cells T := by
  funext x
  simp only [cells, trieNew, List.getD_eq_getElem?_getD]
  by_cases hx : x < T.length
  · rw [List.getElem?_append_left hx]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by omega : T.length ≤ x),
      List.getElem?_replicate]
    split_ifs <;> rfl




/-! ## The invariant -/




















namespace TrieInv

variable {L lo fr : ℕ} {μ : ℕ → ℤ} {nd : ℕ × List ℕ → ℕ}

/-- A vertex lies below the first free cell, and its address is not 0. -/
private theorem inside (h : TrieInv L lo μ nd fr) {x : ℕ × List ℕ} (hx : nd x ≠ 0) :
    0 < nd x ∧ nd x + 11 ≤ fr :=
  ⟨Nat.pos_of_ne_zero hx, (h.range x hx).2.1⟩

/-- The blocks of different vertices are disjoint. -/
private theorem cell_inj (h : TrieInv L lo μ nd fr) {x y : ℕ × List ℕ} {a b : ℕ} (hx : nd x ≠ 0)
    (hy : nd y ≠ 0) (ha : a < 11) (hb : b < 11) (hcell : nd x + b = nd y + a) :
    x = y ∧ b = a := by
  have hrx := h.range x hx
  have hry := h.range y hy
  -- both addresses are lo plus a multiple of 11, and a, b < 11
  exact ⟨h.inj x y hx (by omega), by omega⟩










/-- A new vertex x at the address fr; its parent, if x is not a root, is a vertex already.  The
cells may change, as long as those from fr on stay free and the cells of the old vertices point to
the children, x among them. -/
private theorem addVertex (h : TrieInv L lo μ nd fr) {x : ℕ × List ℕ} {μ' : ℕ → ℤ} (hx : nd x = 0)
    (hparent : ∀ i w a, (i, w ++ [a]) = x → nd (i, w) ≠ 0) (hfresh : ∀ c, fr ≤ c → μ' c = 0)
    (hchild : ∀ i w a, w.length < L → a < 11 → nd (i, w) ≠ 0 →
      μ' (nd (i, w) + a) = Function.update nd x fr (i, w ++ [a])) :
    TrieInv L lo μ' (Function.update nd x fr) (fr + 11) := by
  have hlo := h.lo_pos
  have hfr := h.fr_aligned
  refine { child := fun i w a hw ha hnd => ?_, range := fun y hnd => ?_,
           inj := fun y y' hnd heq => ?_, closed := fun i w a hnd => ?_,
           fresh := fun c hc => hfresh c (by omega), lo_pos := hlo,
           fr_aligned := ⟨by omega, by omega⟩ }
  · -- child
    by_cases hwx : (i, w) = x
    · -- the new vertex has no children
      have hne : (i, w ++ [a]) ≠ x := fun happ => by simp [← hwx] at happ
      have hnone : nd (i, w ++ [a]) = 0 := by
        by_contra hc
        exact h.closed _ _ _ hc (by rw [hwx, hx])
      rw [hwx, Function.update_self, Function.update_of_ne hne, hfresh _ (by omega), hnone]
      rfl
    · rw [Function.update_of_ne hwx] at hnd ⊢
      exact hchild i w a hw ha hnd
  · -- range
    rw [Function.update_apply] at hnd ⊢
    split_ifs at hnd ⊢
    · omega
    · have := h.range y hnd
      omega
  · -- inj: the new address is above all the old ones
    rw [Function.update_apply] at hnd
    rw [Function.update_apply, Function.update_apply] at heq
    split_ifs at hnd heq with hyx hyx'
    · rw [hyx, hyx']
    · have := h.range y' (by omega)
      omega
    · have := h.range y hnd
      omega
    · exact h.inj y y' hnd heq
  · -- closed
    by_cases hwx : (i, w) = x
    · rw [hwx, Function.update_self]
      omega
    · rw [Function.update_of_ne hwx]
      by_cases happ : (i, w ++ [a]) = x
      · exact hparent i w a happ
      · exact h.closed i w a (by rwa [Function.update_of_ne happ] at hnd)










/-- A new vertex for the prefix w ++ [a], at the address fr, with the pointer to it in the vertex
of w. -/
private theorem newChild (h : TrieInv L lo μ nd fr) {i : ℕ} {w : List ℕ} {a : ℕ} (ha : a < 11)
    (hw : nd (i, w) ≠ 0) (hwa : nd (i, w ++ [a]) = 0) :
    TrieInv L lo (Function.update μ (nd (i, w) + a) fr) (Function.update nd (i, w ++ [a]) fr)
      (fr + 11) := by
  have hin := h.inside hw
  refine h.addVertex hwa (fun j u b happ => ?_) (fun c hc => ?_) fun j u b hu hb hnd => ?_
  · obtain ⟨rfl, happ'⟩ := Prod.mk.inj happ
    rwa [(List.append_inj' happ' rfl).1]
  · rw [Function.update_of_ne (by omega), h.fresh c hc]
  · by_cases hcell : nd (j, u) + b = nd (i, w) + a
    · obtain ⟨hju, rfl⟩ := h.cell_inj hnd hw ha hb hcell
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hju
      rw [Function.update_self, Function.update_self]
    · have hne : (j, u ++ [b]) ≠ (i, w ++ [a]) := fun happ => by
        obtain ⟨rfl, happ'⟩ := Prod.mk.inj happ
        obtain ⟨rfl, hba⟩ := List.append_inj' happ' rfl
        exact hcell (by rw [List.singleton_inj.mp hba])
      rw [Function.update_of_ne hcell, Function.update_of_ne hne, h.child j u b hu hb hnd]

/-- Writing a value into the vertex of a string of full length. -/
private theorem setVal (h : TrieInv L lo μ nd fr) {i : ℕ} {w : List ℕ} (hL : w.length = L)
    (hw : nd (i, w) ≠ 0) (z : ℤ) : TrieInv L lo (Function.update μ (nd (i, w)) z) nd fr := by
  have hin := h.inside hw
  refine { h with child := fun j u b hu hb hnd => ?_, fresh := fun c hc => ?_ }
  · rw [Function.update_of_ne, h.child j u b hu hb hnd]
    intro hcell
    obtain ⟨hju, -⟩ := h.cell_inj (a := 0) hnd hw (by omega) hb hcell
    obtain ⟨-, rfl⟩ := Prod.mk.inj hju
    -- a vertex at depth L is not above depth L
    omega
  · rw [Function.update_of_ne (by omega), h.fresh c hc]

end TrieInv

/-! ## Insertion -/









private theorem TrieExt.trans {L : ℕ} {x : ℕ × List ℕ} {μ μ₁ μ₂ : ℕ → ℤ}
    {nd nd₁ nd₂ : ℕ × List ℕ → ℕ} (h : TrieExt L x μ nd μ₁ nd₁) (h' : TrieExt L x μ₁ nd₁ μ₂ nd₂) :
    TrieExt L x μ nd μ₂ nd₂ := by
  have hne : ∀ y, nd y ≠ 0 → nd₁ y ≠ 0 := fun y hy => by rwa [h.old_vertex y hy]
  refine { old_vertex := fun y hy => ?_, old_root := fun i hi => h.old_root i (h'.old_root i hi),
           old_value := fun i w hL hw hx => ?_ }
  · rw [h'.old_vertex y (hne y hy), h.old_vertex y hy]
  · rw [← h.old_value i w hL hw hx, ← h.old_vertex _ hw, h'.old_value i w hL (hne _ hw) hx]










/-- An insertion after a step that extends the tries. -/
private theorem Inserted.of_step {L lo : ℕ} {x : ℕ × List ℕ} {v : ℤ} {T T₁ T₂ : List ℤ}
    {nd nd₁ nd₂ : ℕ × List ℕ → ℕ} (h : Inserted L lo x v T₁ nd₁ T₂ nd₂)
    (hstep : TrieExt L x (cells T) nd (cells T₁) nd₁) : Inserted L lo x v T nd T₂ nd₂ :=
  { h with ext := hstep.trans h.ext }

section

variable {L lo i : ℕ} {T : List ℤ} {nd : ℕ × List ℕ → ℕ} {w : List ℕ}

/-- The end of an insertion: the value is written into the vertex of the string. -/
private theorem TrieInv.inserted_set (h : TrieInv L lo (cells T) nd T.length) (hL : w.length = L)
    (hw : nd (i, w) ≠ 0) (v : ℤ) : Inserted L lo (i, w) v T nd (T.set (nd (i, w)) v) nd := by
  have hin := h.inside hw
  have hcells : cells (T.set (nd (i, w)) v) = Function.update (cells T) (nd (i, w)) v :=
    cells_set T _ _ (by omega)
  refine { inv := ?_, vertex := hw, value := ?_,
           ext := { old_vertex := fun _ _ => rfl, old_root := fun _ hi => hi,
                    old_value := fun j u _ hu hne => ?_ } }
  · rw [hcells, List.length_set]
    exact h.setVal hL hw v
  · rw [hcells, Function.update_self]
  · rw [hcells, Function.update_of_ne fun hnd => hne (h.inj _ _ hu hnd)]

/-- A step of an insertion where there is no child: a new vertex at the end of the array keeps the
invariant and extends the tries. -/
private theorem TrieInv.step_newChild (h : TrieInv L lo (cells T) nd T.length) {d : ℕ}
    (hd : d < 11) (hw : nd (i, w) ≠ 0) (hlen : w.length < L) (hnone : nd (i, w ++ [d]) = 0)
    (x : ℕ × List ℕ) :
    TrieInv L lo (cells (trieNew (T.set (nd (i, w) + d) T.length)))
        (Function.update nd (i, w ++ [d]) T.length)
        (trieNew (T.set (nd (i, w) + d) T.length)).length ∧
      TrieExt L x (cells T) nd (cells (trieNew (T.set (nd (i, w) + d) T.length)))
        (Function.update nd (i, w ++ [d]) T.length) := by
  have hin := h.inside hw
  rw [cells_trieNew, cells_set T _ _ (by omega), length_trieNew, List.length_set]
  refine ⟨h.newChild hd hw hnone,
    { old_vertex := fun y hy => ?_, old_root := fun j hj => ?_,
      old_value := fun j u hL hu _ => ?_ }⟩
  · exact Function.update_of_ne (fun hyw => hy (by rw [hyw, hnone])) _ _
  · rwa [Function.update_of_ne (by simp)] at hj
  · refine Function.update_of_ne (fun hcell => ?_) _ _
    obtain ⟨hju, -⟩ := h.cell_inj (b := 0) hu hw hd (by omega) hcell
    obtain ⟨-, rfl⟩ := Prod.mk.inj hju
    -- a vertex at depth L is not above depth L
    omega

/-- **Insertion.**  Below the vertex of the prefix w, the insertion of the rest of a string meets
only addresses inside the array, and it achieves what `Inserted` says. -/
private theorem trieInsert_spec (v : ℤ) (key : List ℕ) (hinv : TrieInv L lo (cells T) nd T.length)
    (hw : nd (i, w) ≠ 0) (hlen : w.length + key.length = L) (hkey : ∀ d ∈ key, d < 11) :
    InsertOK T (nd (i, w)) key ∧
      ∃ nd', Inserted L lo (i, w ++ key) v T nd (trieInsert T (nd (i, w)) key v) nd' := by
  induction key generalizing T nd w with
  | nil =>
    rw [List.append_nil]
    exact ⟨hinv.inside hw, nd, hinv.inserted_set hlen hw v⟩
  | cons d l ih =>
    obtain ⟨hpos, hin⟩ := hinv.inside hw
    have hd : d < 11 := hkey d (by simp)
    have hl : ∀ x ∈ l, x < 11 := fun x hx => hkey x (by simp [hx])
    rw [List.length_cons] at hlen
    have hchild : T.getD (nd (i, w) + d) 0 = nd (i, w ++ [d]) := hinv.child i w d (by omega) hd hw
    have hlen' : (w ++ [d]).length + l.length = L := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [List.append_cons, trieInsert, InsertOK, hchild]
    by_cases hz : nd (i, w ++ [d]) = 0
    · -- there is no child: a new vertex at the end of the array
      obtain ⟨hinv₁, hstep⟩ := hinv.step_newChild hd hw (by omega) hz (i, w ++ [d] ++ l)
      obtain ⟨hok, nd', hins⟩ :=
        ih hinv₁ (w := w ++ [d]) (by rw [Function.update_self]; omega) hlen' hl
      rw [Function.update_self] at hok hins
      rw [hz, Int.natCast_zero, if_pos rfl, if_pos rfl]
      exact ⟨⟨hpos, hin, hok⟩, nd', hins.of_step hstep⟩
    · -- the child exists
      obtain ⟨hok, nd', hins⟩ := ih hinv (w := w ++ [d]) hz hlen' hl
      have hz' : (nd (i, w ++ [d]) : ℤ) ≠ 0 := by exact_mod_cast hz
      rw [if_neg hz', if_neg hz', Int.toNat_natCast]
      exact ⟨⟨hpos, hin, by omega, hok⟩, nd', hins⟩

/-! ## Lookup -/
























end

/-! ## The interface -/

public section









namespace TrieRep













variable {L lo : ℕ} {T : List ℤ} {roots : ℕ → ℕ} {f : ℕ × List ℕ → Option ℤ}


























/-- What `trieInsert_spec` says about an insertion from the root of trie number i. -/
private theorem insert_spec (nd : ℕ × List ℕ → ℕ) (hinv : TrieInv L lo (cells T) nd T.length)
    (hroots : ∀ i, nd (i, []) = roots i) (i : ℕ) (hi : roots i ≠ 0) (key : List ℕ)
    (hk : key.length = L) (hd : ∀ d ∈ key, d < 11) (v : ℤ) :
    InsertOK T (roots i) key ∧
      ∃ nd', Inserted L lo (i, key) v T nd (trieInsert T (roots i) key v) nd' := by
  have h := trieInsert_spec (i := i) (w := []) v key hinv (by rwa [hroots]) (by simpa using hk) hd
  rwa [hroots] at h

/-- Storing a value. -/
theorem insert_sourceProof (h : TrieRep L lo T roots f) (i : ℕ) (hi : roots i ≠ 0) (key : List ℕ)
    (hk : key.length = L) (hd : ∀ d ∈ key, d < 11) (v : ℤ) :
    TrieRep L lo (trieInsert T (roots i) key v) roots (Function.update f (i, key) (some v)) := by
  obtain ⟨nd, hinv, hroots, hval⟩ := h
  obtain ⟨-, nd', hins⟩ := insert_spec nd hinv hroots i hi key hk hd v
  refine ⟨nd', hins.inv, fun j => ?_, fun j key' v' hf => ?_⟩
  · by_cases hz : roots j = 0
    · -- a trie that does not exist still does not exist
      by_contra hc
      exact hins.ext.old_root j (fun hnd => hc (by rw [hnd, hz])) (by rw [hroots, hz])
    · rw [hins.ext.old_vertex (j, []) (by rwa [hroots]), hroots]
  · by_cases hkey : (j, key') = (i, key)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
      rw [Function.update_self] at hf
      obtain rfl := Option.some.inj hf
      exact ⟨hk, hins.vertex, hins.value⟩
    · rw [Function.update_of_ne hkey] at hf
      obtain ⟨hlen, hne, hv⟩ := hval j key' v' hf
      rw [hins.ext.old_vertex _ hne]
      exact ⟨hlen, hne, (hins.ext.old_value j key' hlen hne hkey).trans hv⟩




























end TrieRep

end

end ThreeSumApsp.Spec



theorem solution : ∀ {L lo : Nat} {T : List.{0} Int} {roots : Nat → Nat} {f : Prod.{0, 0} Nat (List.{0} Nat) → Option.{0} Int},
  ThreeSumApsp.Spec.TrieRep L lo T roots f →
    ∀ (i : Nat),
      @Ne.{1} Nat (roots i) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        ∀ (key : List.{0} Nat),
          @Eq.{1} Nat (@List.length.{0} Nat key) L →
            (∀ (d : Nat),
                @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) key d →
                  @LT.lt.{0} Nat instLTNat d (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))) →
              ∀ (v : Int),
                ThreeSumApsp.Spec.TrieRep L lo (ThreeSumApsp.Spec.trieInsert T (roots i) key v) roots
                  (@Function.update.{1, 1} (Prod.{0, 0} Nat (List.{0} Nat))
                    (fun (a : Prod.{0, 0} Nat (List.{0} Nat)) => Option.{0} Int)
                    (fun (a b : Prod.{0, 0} Nat (List.{0} Nat)) =>
                      @instDecidableEqProd.{0, 0} Nat (List.{0} Nat) instDecidableEqNat
                        (fun (a b : List.{0} Nat) => @instDecidableEqList.{0} Nat instDecidableEqNat a b) a b)
                    f (@Prod.mk.{0, 0} Nat (List.{0} Nat) i key) (@Option.some.{0} Int v)) := by
  exact @ThreeSumApsp.Spec.TrieRep.insert_sourceProof

#print axioms solution
