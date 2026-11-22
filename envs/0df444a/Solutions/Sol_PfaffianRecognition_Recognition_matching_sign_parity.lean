-- Prove2me | solution 1 for PfaffianRecognition.Recognition.matching_sign_parity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:35:29.955834+00:00
-- url     : https://prove2.me/submissions/be1bd173-f74b-46b7-afea-dfc50003e1bd

import Definitions.Def_PfaffianRecognition_Recognition_graph_model

namespace PfaffianRecognition.Recognition.SignParityAux

open PfaffianRecognition.Recognition
open Classical

def inv {α : Type*} [LinearOrder α] : List α → ℕ
  | [] => 0
  | x :: l => l.countP (fun y => decide (y < x)) + inv l

theorem inv_cons {α : Type*} [LinearOrder α] (x : α) (l : List α) :
    inv (x :: l) = l.countP (fun y => decide (y < x)) + inv l := rfl

theorem inv_append {α : Type*} [LinearOrder α] (l₁ l₂ : List α) :
    inv (l₁ ++ l₂) = inv l₁ + inv l₂ +
      (l₁.map fun x => l₂.countP (fun y => decide (y < x))).sum := by
  induction l₁ with
  | nil => simp [inv]
  | cons x l ih =>
    rw [List.cons_append, inv_cons, inv_cons, ih, List.countP_append, List.map_cons,
      List.sum_cons]
    ring

theorem countP_ofFn' {α : Type*} (p : α → Bool) : ∀ (n : ℕ) (g : Fin n → α),
    (List.ofFn g).countP p = ∑ i, if p (g i) then 1 else 0
  | 0, g => by simp
  | n + 1, g => by
    rw [List.ofFn_succ, List.countP_cons, countP_ofFn' p n, Fin.sum_univ_succ]
    ring

theorem inv_ofFn {α : Type*} [LinearOrder α] : ∀ (n : ℕ) (f : Fin n → α),
    inv (List.ofFn f) = ∑ i, ∑ j, if i < j ∧ f j < f i then 1 else 0
  | 0, f => by simp [inv]
  | n + 1, f => by
    rw [List.ofFn_succ, inv_cons, inv_ofFn n, Fin.sum_univ_succ]
    congr 1
    · rw [Fin.sum_univ_succ, countP_ofFn']
      simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.sum_univ_succ]
      simp [Fin.succ_lt_succ_iff]

theorem sign_eq_inv {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign p : ℤˣ) : ℤ) = (-1) ^ inv (List.ofFn p) := by
  rw [inv_ofFn, Equiv.Perm.sign_eq_prod_prod_Ioi, ← Finset.prod_pow_eq_pow_sum]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  have hI : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by ext; simp
  rw [hI, Finset.prod_filter]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hij : i < j
  · have hne : p i ≠ p j := fun h => hij.ne (p.injective h)
    rcases lt_or_gt_of_ne hne with h | h
    · simp [hij, h, h.not_gt]
    · simp [hij, h, h.not_gt]
  · simp [hij]


variable {N : ℕ} {G : SimpleGraph (Fin N)}

theorem val_eq (e : G.edgeSet) : e.val = s(edgeLo e, edgeHi e) := by
  unfold edgeLo edgeHi
  have h := Quot.out_eq e.val
  rcases le_total e.val.out.1 e.val.out.2 with h1 | h1
  · rw [min_eq_left h1, max_eq_right h1]
    exact h.symm
  · rw [min_eq_right h1, max_eq_left h1, Sym2.eq_swap]
    exact h.symm

theorem adj (e : G.edgeSet) : G.Adj (edgeLo e) (edgeHi e) := by
  have := e.prop
  rw [val_eq e, SimpleGraph.mem_edgeSet] at this
  exact this

theorem lo_lt_hi (e : G.edgeSet) : edgeLo e < edgeHi e := by
  have h1 : edgeLo e ≤ edgeHi e := by unfold edgeLo edgeHi; exact min_le_max
  exact lt_of_le_of_ne h1 (adj e).ne

theorem mem_iff (e : G.edgeSet) (v : Fin N) : v ∈ e.val ↔ v = edgeLo e ∨ v = edgeHi e := by
  rw [val_eq e, Sym2.mem_iff]

/-- The block of the one-line sequence contributed by one edge. -/
noncomputable def blk (D : Orientation G) (e : G.edgeSet) : List (Fin N) :=
  if D.val (edgeLo e) (edgeHi e) then [edgeLo e, edgeHi e] else [edgeHi e, edgeLo e]

theorem seq_eq (D : Orientation G) (M : Finset G.edgeSet) :
    matchingSequence D M = (matchingEdgeOrder M).flatMap (blk D) := rfl

theorem mem_blk (D : Orientation G) (e : G.edgeSet) (v : Fin N) :
    v ∈ blk D e ↔ v ∈ e.val := by
  rw [mem_iff]; unfold blk; split_ifs <;> simp [or_comm]

theorem countP_blk (D : Orientation G) (e : G.edgeSet) (P : Fin N → Bool) :
    (blk D e).countP P = (if P (edgeLo e) then 1 else 0) + (if P (edgeHi e) then 1 else 0) := by
  unfold blk
  by_cases hD : D.val (edgeLo e) (edgeHi e) <;>
    simp only [hD, if_true, if_false, List.countP_cons, List.countP_nil] <;>
    cases P (edgeLo e) <;> cases P (edgeHi e) <;> simp

theorem inv_blk (D : Orientation G) (e : G.edgeSet) :
    inv (blk D e) = if D.val (edgeHi e) (edgeLo e) then 1 else 0 := by
  have hlt := lo_lt_hi e
  have hor := D.prop.2 _ _ (adj e)
  unfold blk
  by_cases h : D.val (edgeLo e) (edgeHi e)
  · have : ¬ D.val (edgeHi e) (edgeLo e) := fun h' => hor.2 ⟨h, h'⟩
    simp [h, this, inv, hlt.not_gt]
  · have : D.val (edgeHi e) (edgeLo e) := hor.1.resolve_left h
    simp [h, this, inv, hlt]

theorem sum_blk (D : Orientation G) (e : G.edgeSet) (l : List (Fin N)) :
    ((blk D e).map fun x => l.countP (fun y => decide (y < x))).sum =
      l.countP (fun y => decide (y < edgeLo e)) + l.countP (fun y => decide (y < edgeHi e)) := by
  unfold blk; split_ifs <;> simp [add_comm]

theorem sum_cast_eq_countP {α : Type*} (l : List α) (h : α → ℕ) (Q : α → Prop)
    [DecidablePred Q] (hh : ∀ a ∈ l, (h a : ZMod 2) = if Q a then 1 else 0) :
    ((l.map h).sum : ZMod 2) = (l.countP (fun a => decide (Q a)) : ZMod 2) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, Nat.cast_add]
    rw [ih (fun b hb => hh b (List.mem_cons_of_mem _ hb)), hh a List.mem_cons_self]
    split_ifs <;> simp_all [add_comm]

/-- Edge `e` precedes `f`, and they are vertex-disjoint. -/
def Prec (e f : G.edgeSet) : Prop := edgeLo e < edgeLo f ∧ ∀ v, v ∈ e.val → v ∉ f.val

theorem parity_cross (g f : G.edgeSet) (h : Prec g f) :
    (((if edgeLo f < edgeHi g then 1 else 0) + (if edgeHi f < edgeHi g then 1 else 0) : ℕ) :
      ZMod 2) = if edgeLo g < edgeLo f ∧ Crosses g f then 1 else 0 := by
  have h1 := lo_lt_hi g
  have h2 := lo_lt_hi f
  have hne : edgeHi f ≠ edgeHi g := by
    intro heq
    exact h.2 (edgeHi g) ((mem_iff g _).2 (Or.inr rfl)) ((mem_iff f _).2 (Or.inr heq.symm))
  have hlo := h.1
  by_cases ha : edgeLo f < edgeHi g <;> by_cases hb : edgeHi f < edgeHi g
  · have : ¬ (edgeLo g < edgeLo f ∧ Crosses g f) := by
      rintro ⟨_, (⟨_, _, h3⟩ | ⟨h3, _, _⟩)⟩
      · exact absurd hb (not_lt.2 h3.le)
      · exact absurd hlo (not_lt.2 h3.le)
    rw [if_neg this, if_pos ha, if_pos hb]; decide
  · have h4 : edgeHi g < edgeHi f := lt_of_le_of_ne (not_lt.1 hb) (Ne.symm hne)
    have : edgeLo g < edgeLo f ∧ Crosses g f := ⟨hlo, Or.inl ⟨hlo, ha, h4⟩⟩
    rw [if_pos this, if_pos ha, if_neg hb]; simp
  · exact absurd (lt_trans h2 hb) ha
  · have : ¬ (edgeLo g < edgeLo f ∧ Crosses g f) := by
      rintro ⟨_, (⟨_, h3, _⟩ | ⟨h3, _, _⟩)⟩
      · exact ha h3
      · exact absurd hlo (not_lt.2 h3.le)
    rw [if_neg this, if_neg ha, if_neg hb]; simp

theorem main_ind (D : Orientation G) : ∀ (L : List G.edgeSet), L.Pairwise Prec →
    (inv (L.flatMap (blk D)) : ZMod 2) =
      ((∑ e ∈ L.toFinset,
          (L.toFinset.filter fun f => edgeLo e < edgeLo f ∧ Crosses e f).card : ℕ) : ZMod 2) +
      ((L.toFinset.filter fun e => D.val (edgeHi e) (edgeLo e)).card : ZMod 2)
  | [], _ => by simp [inv]
  | g :: L, hP => by
    rw [List.pairwise_cons] at hP
    obtain ⟨hg, hP⟩ := hP
    have ih := main_ind D L hP
    have hgL : g ∉ L := fun h => lt_irrefl _ (hg g h).1
    have hnd : L.Nodup := hP.imp fun h => fun heq => lt_irrefl _ (heq ▸ h.1)
    rw [List.flatMap_cons, inv_append, inv_blk, sum_blk]
    have h0 : (L.flatMap (blk D)).countP (fun y => decide (y < edgeLo g)) = 0 := by
      rw [List.countP_eq_zero]
      intro a ha
      obtain ⟨f, hf, ha⟩ := List.mem_flatMap.1 ha
      rw [mem_blk, mem_iff] at ha
      have := (hg f hf).1
      have := lo_lt_hi f
      simp only [decide_eq_true_eq, not_lt]
      rcases ha with rfl | rfl <;> order
    have h1 : ((L.flatMap (blk D)).countP (fun y => decide (y < edgeHi g)) : ZMod 2) =
        ((L.toFinset.filter fun f => edgeLo g < edgeLo f ∧ Crosses g f).card : ZMod 2) := by
      rw [List.countP_flatMap, sum_cast_eq_countP _ _ (fun f => edgeLo g < edgeLo f ∧ Crosses g f)]
      · rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter _),
          List.toFinset_filter]
        simp
      · intro f hf
        rw [Function.comp_apply, countP_blk, ← parity_cross g f (hg f hf)]
        simp
    rw [List.toFinset_cons, Finset.sum_insert (by simpa using hgL), Finset.filter_insert,
      if_neg (show ¬(edgeLo g < edgeLo g ∧ Crosses g g) from fun h => lt_irrefl _ h.1)]
    have h2 : ∑ e ∈ L.toFinset, ((insert g L.toFinset).filter
        fun f => edgeLo e < edgeLo f ∧ Crosses e f).card =
        ∑ e ∈ L.toFinset, (L.toFinset.filter fun f => edgeLo e < edgeLo f ∧ Crosses e f).card := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [Finset.filter_insert, if_neg]
      have := (hg e (by simpa using he)).1
      intro h; exact absurd h.1 (not_lt.2 this.le)
    rw [h2]
    push_cast
    rw [h0, h1, ih]
    rw [Finset.filter_insert]
    by_cases hb : D.val (edgeHi g) (edgeLo g)
    · rw [if_pos hb, if_pos hb, Finset.card_insert_of_notMem (by simp [hgL])]
      push_cast; ring
    · rw [if_neg hb, if_neg hb]
      push_cast; ring

theorem exists_perm_ofFn {N : ℕ} (l : List (Fin N)) (hnd : l.Nodup) (hall : ∀ v, v ∈ l) :
    ∃ p : Equiv.Perm (Fin N), List.ofFn p = l := by
  have hlen : l.length = N := by
    apply le_antisymm
    · simpa using hnd.length_le_card
    · have : (Finset.univ : Finset (Fin N)) ⊆ l.toFinset := fun v _ => by simpa using hall v
      simpa using (Finset.card_le_card this).trans (List.toFinset_card_le l)
  refine ⟨(finCongr hlen.symm).trans (hnd.getEquivOfForallMemList l hall), ?_⟩
  apply List.ext_get (by simp [hlen])
  intro n h1 h2
  simp [List.Nodup.getEquivOfForallMemList]

theorem order_perm (M : Finset G.edgeSet) : (matchingEdgeOrder M).Perm M.toList := by
  unfold matchingEdgeOrder; exact List.mergeSort_perm _ _

theorem order_sorted (M : Finset G.edgeSet) :
    (matchingEdgeOrder M).Pairwise (fun e f => edgeLo e ≤ edgeLo f) := by
  unfold matchingEdgeOrder
  have := List.pairwise_mergeSort (le := fun e f : G.edgeSet => decide (edgeLo e ≤ edgeLo f))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; exact le_trans h1 h2)
    (fun a b => by simpa using le_total _ _) M.toList
  simpa using this

end PfaffianRecognition.Recognition.SignParityAux

namespace PfaffianRecognition.Recognition

open PfaffianRecognition.Recognition.SignParityAux

/-- Lemma 2.1 (mission milestone, exact statement). -/
theorem matching_sign_parity {N : ℕ} (G : SimpleGraph (Fin N)) (D : Orientation G)
    (M : Finset G.edgeSet) (hM : MulmuleyVV.Matching.IsPerfectMatchingEdges G M) :
    matchingSign D M = (-1 : ℤ) ^ (crossingParity M + backwardParity D M) := by
  classical
  have hcommon : ∀ e f : G.edgeSet, e ∈ M → f ∈ M → ∀ v, v ∈ e.val → v ∈ f.val → e = f :=
    fun e f he hf v hv hv' => (hM v).unique ⟨he, hv⟩ ⟨hf, hv'⟩
  set L := matchingEdgeOrder M with hLdef
  have hnd : L.Nodup := (order_perm M).nodup_iff.mpr M.nodup_toList
  have hmem : ∀ e, e ∈ L ↔ e ∈ M := fun e => (order_perm M).mem_iff.trans (Finset.mem_toList)
  have hP : L.Pairwise Prec := by
    have h2 : L.Pairwise (fun e f => edgeLo e ≤ edgeLo f ∧ e ≠ f) := (order_sorted M).and hnd
    refine h2.imp_of_mem fun {e f} he hf h => ?_
    have he' := (hmem e).1 he
    have hf' := (hmem f).1 hf
    refine ⟨lt_of_le_of_ne h.1 fun heq => h.2 ?_, fun v hv hv' => h.2 ?_⟩
    · exact hcommon e f he' hf' (edgeLo e) ((mem_iff e _).2 (Or.inl rfl))
        ((mem_iff f _).2 (Or.inl heq))
    · exact hcommon e f he' hf' v hv hv'
  have hseq_nd : (matchingSequence D M).Nodup := by
    rw [seq_eq, List.nodup_flatMap]
    refine ⟨fun e _ => ?_, hP.imp fun {e f} h => ?_⟩
    · have := lo_lt_hi e
      unfold blk; split_ifs <;> simp [this.ne, this.ne']
    · intro a ha hb
      rw [mem_blk] at ha hb
      exact h.2 a ha hb
  have hseq_all : ∀ v, v ∈ matchingSequence D M := by
    intro v
    obtain ⟨e, ⟨he, hv⟩, _⟩ := hM v
    rw [seq_eq, List.mem_flatMap]
    exact ⟨e, (hmem e).2 he, (mem_blk D e v).2 hv⟩
  have hex := exists_perm_ofFn _ hseq_nd hseq_all
  have hσ : List.ofFn (matchingPermutation D M) = matchingSequence D M := by
    unfold matchingPermutation
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  unfold matchingSign
  rw [sign_eq_inv, hσ, seq_eq, neg_one_pow_eq_pow_mod_two,
    neg_one_pow_eq_pow_mod_two (n := crossingParity M + backwardParity D M)]
  congr 1
  have key := main_ind D L hP
  have hLM : L.toFinset = M := by ext e; simp [hmem]
  rw [hLM] at key
  have hA : ((crossingPairs G).filter fun ef => ef.1 ∈ M ∧ ef.2 ∈ M).card =
      ∑ e ∈ M, (M.filter fun f => edgeLo e < edgeLo f ∧ Crosses e f).card := by
    have : ((crossingPairs G).filter fun ef => ef.1 ∈ M ∧ ef.2 ∈ M) =
        (M ×ˢ M).filter fun ef => edgeLo ef.1 < edgeLo ef.2 ∧ Crosses ef.1 ef.2 := by
      ext ef; simp [crossingPairs]; tauto
    rw [this, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.card_filter]
  have hB : (M ∩ backwardEdges D).card =
      (M.filter fun e => D.val (edgeHi e) (edgeLo e)).card := by
    congr 1; ext e; simp [backwardEdges]
  unfold crossingParity backwardParity
  rw [← Nat.add_mod]
  apply (ZMod.natCast_eq_natCast_iff' _ _ 2).1
  push_cast
  rw [key, hA, hB]

end PfaffianRecognition.Recognition


theorem solution {N : ℕ} (G : SimpleGraph (Fin N)) (D : PfaffianRecognition.Recognition.Orientation G)
    (M : Finset G.edgeSet) (hM : MulmuleyVV.Matching.IsPerfectMatchingEdges G M) :
    PfaffianRecognition.Recognition.matchingSign D M =
      (-1 : ℤ) ^ (PfaffianRecognition.Recognition.crossingParity M +
        PfaffianRecognition.Recognition.backwardParity D M) :=
  PfaffianRecognition.Recognition.matching_sign_parity G D M hM
