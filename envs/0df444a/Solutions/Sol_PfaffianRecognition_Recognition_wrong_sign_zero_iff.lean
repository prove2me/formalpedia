-- Prove2me | solution 1 for PfaffianRecognition.Recognition.wrong_sign_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:35:31.289771+00:00
-- url     : https://prove2.me/submissions/54712c73-5013-41d3-b248-0eeb80a0a727

import Definitions.Def_PfaffianRecognition_Recognition_polynomial_model

namespace PfaffianRecognition.CoRP.DetAux

open Finset

theorem det_char_two_symm {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CharP R 2]
    (B : Matrix ι ι R) (hB : ∀ i j, B i j = B j i) (hd : ∀ i, B i i = 0) :
    B.det = ∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => ∀ i, σ (σ i) = i ∧ σ i ≠ i),
      ∏ i, B (σ i) i := by
  rw [Matrix.det_apply]
  have hsign : ∀ σ : Equiv.Perm ι, (Equiv.Perm.sign σ • ∏ i, B (σ i) i) = ∏ i, B (σ i) i := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
    · simp
    · rw [Units.neg_smul, one_smul, CharTwo.neg_eq]
  simp_rw [hsign]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun σ : Equiv.Perm ι => ∀ i, σ (σ i) = i ∧ σ i ≠ i)]
  have hinv : ∀ σ : Equiv.Perm ι, ∏ i, B (σ⁻¹ i) i = ∏ i, B (σ i) i := by
    intro σ
    rw [← Equiv.prod_comp σ (fun i => B (σ⁻¹ i) i)]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [show σ⁻¹ (σ i) = i from Equiv.Perm.inv_eq_iff_eq.mpr rfl]
    exact hB _ _
  rw [add_eq_left]
  refine Finset.sum_involution (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_
  · intro σ _
    rw [hinv, CharTwo.add_self_eq_zero]
  · intro σ hσ hne heq
    simp only [mem_filter, mem_univ, true_and, not_forall] at hσ
    obtain ⟨i, hi⟩ := hσ
    have hinvol : ∀ j, σ (σ j) = j := by
      intro j
      have : σ⁻¹ (σ j) = σ (σ j) := by rw [heq]
      simpa using this.symm
    have hfix : σ i = i := by
      by_contra h
      exact hi ⟨hinvol i, h⟩
    apply hne
    exact Finset.prod_eq_zero (mem_univ i) (by rw [hfix, hd])
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    intro h
    apply hσ
    have hinvol : ∀ j, σ⁻¹ (σ⁻¹ j) = j := fun j => (h j).1
    have heq : σ = σ⁻¹ := by
      ext j
      have h1 : σ⁻¹ (σ j) = j := Equiv.Perm.inv_eq_iff_eq.mpr rfl
      have := hinvol (σ j)
      rw [h1] at this
      exact this.symm
    intro j
    constructor
    · rw [heq]
      exact hinvol j
    · intro hj
      apply (h j).2
      rw [← heq, hj]
  · intro σ _
    exact inv_inv σ

variable {N : ℕ}

def IsPMOn (G : SimpleGraph (Fin N)) (p : Fin N → Prop) (M : Finset G.edgeSet) : Prop :=
  (∀ e ∈ M, ∀ v ∈ (e : Sym2 (Fin N)), p v) ∧
    ∀ v, p v → ∃! e, e ∈ M ∧ v ∈ (e : Sym2 (Fin N))

section partner

variable {G : SimpleGraph (Fin N)} {p : Fin N → Prop} {M : Finset G.edgeSet}

theorem exists_partner (hM : IsPMOn G p M) (i : {v // p v}) :
    ∃ j : {v // p v}, ∃ e ∈ M, (e : Sym2 (Fin N)) = s(i.val, j.val) := by
  obtain ⟨e, ⟨heM, hie⟩, _⟩ := hM.2 i.val i.2
  exact ⟨⟨Sym2.Mem.other hie, hM.1 e heM _ (Sym2.other_mem hie)⟩, e, heM,
    (Sym2.other_spec hie).symm⟩

noncomputable def partner (hM : IsPMOn G p M) (i : {v // p v}) : {v // p v} :=
  Classical.choose (exists_partner hM i)

theorem partner_spec (hM : IsPMOn G p M) (i : {v // p v}) :
    ∃ e ∈ M, (e : Sym2 (Fin N)) = s(i.val, (partner hM i).val) :=
  Classical.choose_spec (exists_partner hM i)

theorem partner_eq (hM : IsPMOn G p M) {i j : {v // p v}} (e : G.edgeSet) (he : e ∈ M)
    (h : (e : Sym2 (Fin N)) = s(i.val, j.val)) : partner hM i = j := by
  obtain ⟨e', he', h'⟩ := partner_spec hM i
  obtain ⟨_, _, huniq⟩ := hM.2 i.val i.2
  have h1 : e = e' := by
    have a := huniq e ⟨he, by rw [h]; exact Sym2.mem_mk_left _ _⟩
    have b := huniq e' ⟨he', by rw [h']; exact Sym2.mem_mk_left _ _⟩
    rw [a, b]
  subst h1
  rw [h] at h'
  exact Subtype.ext (Sym2.congr_right.mp h').symm

theorem partner_invol (hM : IsPMOn G p M) : Function.Involutive (partner hM) := by
  intro i
  obtain ⟨e, he, h⟩ := partner_spec hM i
  exact partner_eq hM e he (by rw [h, Sym2.eq_swap])

theorem partner_adj (hM : IsPMOn G p M) (i : {v // p v}) :
    G.Adj i.val (partner hM i).val := by
  obtain ⟨e, he, h⟩ := partner_spec hM i
  have := e.2
  rw [h] at this
  exact G.mem_edgeSet.mp this

theorem partner_ne (hM : IsPMOn G p M) (i : {v // p v}) : partner hM i ≠ i := by
  intro h
  have := partner_adj hM i
  rw [h] at this
  exact G.loopless.irrefl _ this

end partner

open Classical in
theorem det_submatrix_eq {R : Type*} [CommRing R] [CharP R 2] (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (w : G.edgeSet → R) (p : Fin N → Prop) [DecidablePred p] :
    ((Matrix.of fun i j : Fin N => if h : G.Adj i j then w ⟨s(i, j), G.mem_edgeSet.mpr h⟩ else 0).submatrix
      (Subtype.val : {v // p v} → Fin N) Subtype.val).det =
    ∑ M ∈ univ.filter (fun M : Finset G.edgeSet => IsPMOn G p M), ∏ e ∈ M, w e ^ 2 := by
  set A := (Matrix.of fun i j : Fin N => if h : G.Adj i j then w ⟨s(i, j), G.mem_edgeSet.mpr h⟩ else 0).submatrix
      (Subtype.val : {v // p v} → Fin N) Subtype.val with hA
  have hsymm : ∀ i j, A i j = A j i := by
    intro i j
    simp only [hA, Matrix.submatrix_apply, Matrix.of_apply]
    by_cases h : G.Adj i.val j.val
    · rw [dif_pos h, dif_pos h.symm]
      congr 2
      exact Sym2.eq_swap
    · rw [dif_neg h, dif_neg (fun h' => h h'.symm)]
  have hdiag : ∀ i, A i i = 0 := by
    intro i
    simp only [hA, Matrix.submatrix_apply, Matrix.of_apply]
    rw [dif_neg (G.loopless.irrefl _)]
  rw [det_char_two_symm A hsymm hdiag]
  rw [← Finset.sum_filter_of_ne (p := fun σ : Equiv.Perm {v // p v} => ∀ i, G.Adj (σ i).val i.val)]
  swap
  · intro σ _ hne i
    by_contra h
    apply hne
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hA, h])
  rw [Finset.filter_filter]
  refine Finset.sum_bij'
    (fun σ _ => univ.filter (fun e : G.edgeSet => ∃ i : {v // p v}, (e : Sym2 (Fin N)) = s(i.val, (σ i).val)))
    (fun M hM => Function.Involutive.toPerm (partner (mem_filter.mp hM).2) (partner_invol _))
    ?_ ?_ ?_ ?_ ?_
  · -- forward lands in matchings
    intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    obtain ⟨h1, h2⟩ := hσ
    refine ⟨?_, ?_⟩
    · intro e he v hv
      simp only [mem_filter, mem_univ, true_and] at he
      obtain ⟨i, hi⟩ := he
      rw [hi, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact i.2
      · exact (σ i).2
    · intro v hv
      refine ⟨⟨s(v, (σ ⟨v, hv⟩).val), G.mem_edgeSet.mpr (h2 ⟨v, hv⟩).symm⟩,
        ⟨by simp only [mem_filter, mem_univ, true_and]; exact ⟨⟨v, hv⟩, rfl⟩,
          Sym2.mem_mk_left _ _⟩, ?_⟩
      rintro e' ⟨he', hve'⟩
      simp only [mem_filter, mem_univ, true_and] at he'
      obtain ⟨i', hi'⟩ := he'
      apply Subtype.ext
      simp only
      rw [hi'] at hve' ⊢
      rw [Sym2.mem_iff] at hve'
      rcases hve' with h | h
      · have : i' = ⟨v, hv⟩ := Subtype.ext h.symm
        rw [this]
      · have : (⟨v, hv⟩ : {v // p v}) = σ i' := Subtype.ext h
        rw [this, (h1 i').1, Sym2.eq_swap, h]
  · -- backward lands in involutions
    intro M hM
    simp only [mem_filter, mem_univ, true_and, Function.Involutive.coe_toPerm]
    refine ⟨fun i => ⟨partner_invol _ i, partner_ne _ i⟩, fun i => (partner_adj _ i).symm⟩
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ
    apply Equiv.ext
    intro i
    simp only [Function.Involutive.coe_toPerm]
    refine (partner_eq _ ⟨s(i.val, (σ i).val), G.mem_edgeSet.mpr (hσ.2 i).symm⟩ ?_ rfl)
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨i, rfl⟩
  · intro M hM
    have hM' := (mem_filter.mp hM).2

    apply Finset.ext
    intro e
    rw [Finset.mem_filter]
    simp only [mem_univ, true_and, Function.Involutive.coe_toPerm]
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨e', he', h'⟩ := partner_spec hM' i
      have : e = e' := Subtype.ext (hi.trans h'.symm)
      rw [this]; exact he'
    · intro he
      have ha : e.val.out.1 ∈ (e : Sym2 (Fin N)) := Sym2.out_fst_mem _
      set i : {v // p v} := ⟨e.val.out.1, hM'.1 e he _ ha⟩
      obtain ⟨e', he', h'⟩ := partner_spec hM' i
      obtain ⟨_, _, huniq⟩ := hM'.2 i.val i.2
      have h1 : e = e' := by
        rw [huniq e ⟨he, ha⟩, huniq e' ⟨he', by rw [h']; exact Sym2.mem_mk_left _ _⟩]
      exact ⟨i, by rw [h1]; exact h'⟩
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ
    obtain ⟨h1, h2⟩ := hσ
    set E : {v // p v} → G.edgeSet :=
      fun i => ⟨s(i.val, (σ i).val), G.mem_edgeSet.mpr (h2 i).symm⟩ with hE
    have step1 : ∏ i, A (σ i) i = ∏ i, w (E i) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      simp only [hA, Matrix.submatrix_apply, Matrix.of_apply, hE]
      rw [dif_pos (h2 i)]
      congr 2
      exact Sym2.eq_swap
    rw [step1, Finset.prod_comp w E]
    have himg : univ.image E =
        univ.filter (fun e : G.edgeSet => ∃ i : {v // p v}, (e : Sym2 (Fin N)) = s(i.val, (σ i).val)) := by
      ext e
      simp only [mem_image, mem_univ, true_and, mem_filter, hE]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
      · rintro ⟨i, hi⟩; exact ⟨i, Subtype.ext hi.symm⟩
    rw [himg]
    refine Finset.prod_congr rfl (fun e he => ?_)
    congr 1
    simp only [mem_filter, mem_univ, true_and] at he
    obtain ⟨i₀, hi₀⟩ := he
    have hfil : univ.filter (fun i => E i = e) = {i₀, σ i₀} := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, hE]
      rw [Subtype.ext_iff, hi₀]
      simp only
      rw [Sym2.eq_iff]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
      · rintro (rfl | rfl)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, by rw [(h1 i₀).1]⟩
    rw [hfil, Finset.card_pair (h1 i₀).2.symm]

end PfaffianRecognition.CoRP.DetAux

namespace PfaffianRecognition.CoRP

open PfaffianRecognition.Recognition

/-- In characteristic two the determinant of an edge-weighted symmetric adjacency matrix is the sum,
over perfect matchings, of the squared weight products. -/
theorem det_weighted_adjacency_char_two {R : Type*} [CommRing R] [CharP R 2] {N : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (w : G.edgeSet → R) :
    (Matrix.of fun i j : Fin N => if h : G.Adj i j then w ⟨s(i, j), G.mem_edgeSet.mpr h⟩ else 0).det =
      ∑ M ∈ MulmuleyVV.Matching.perfectMatchings G, ∏ e ∈ M, w e ^ 2 := by
  classical
  rw [← Matrix.det_submatrix_equiv_self
    (Equiv.subtypeUnivEquiv (p := fun _ : Fin N => True) (fun _ => trivial))]
  have h := DetAux.det_submatrix_eq G w (fun _ => True)
  convert h using 1
  · rfl
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext M
  rw [Finset.mem_filter]
  unfold MulmuleyVV.Matching.perfectMatchings
  rw [Finset.mem_filter]
  simp [DetAux.IsPMOn,
    MulmuleyVV.Matching.IsPerfectMatchingEdges]

end PfaffianRecognition.CoRP

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

namespace PfaffianRecognition.Recognition.MinorAux

open PfaffianRecognition.Recognition PfaffianRecognition.CoRP.DetAux Finset
open Classical

variable {N : ℕ} {G : SimpleGraph (Fin N)}

theorem mem_pm {inst : DecidableRel G.Adj} (M : Finset G.edgeSet) :
    M ∈ @MulmuleyVV.Matching.perfectMatchings N G inst ↔
      MulmuleyVV.Matching.IsPerfectMatchingEdges G M := by
  unfold MulmuleyVV.Matching.perfectMatchings
  rw [Finset.mem_filter]
  simp

theorem skew_eq (K : Type*) [CommRing K] [CharP K 2] (D : Orientation G) :
    skewAdjacency K D = Matrix.of fun i j => if h : G.Adj i j then
      (MvPolynomial.X ⟨s(i, j), G.mem_edgeSet.mpr h⟩ : MvPolynomial G.edgeSet K) else 0 := by
  ext i j
  unfold skewAdjacency
  simp only [Matrix.of_apply]
  split_ifs <;> simp [CharTwo.neg_eq]

theorem principalDet_eq (K : Type*) [CommRing K] [CharP K 2] (D : Orientation G)
    (S : Finset (Fin N)) :
    principalDet K D S = ∑ M ∈ univ.filter (fun M => IsPMOn G (fun v => v ∉ S) M),
      ∏ e ∈ M, (MvPolynomial.X e : MvPolynomial G.edgeSet K) ^ 2 := by
  unfold principalDet
  rw [skew_eq]
  convert det_submatrix_eq G (fun e => (MvPolynomial.X e : MvPolynomial G.edgeSet K))
    (fun v => v ∉ S) using 1

theorem det_skew_eq (K : Type*) [CommRing K] [CharP K 2] (D : Orientation G) :
    (skewAdjacency K D).det = ∑ M ∈ univ.filter (fun M => MulmuleyVV.Matching.IsPerfectMatchingEdges G M),
      ∏ e ∈ M, (MvPolynomial.X e : MvPolynomial G.edgeSet K) ^ 2 := by
  rw [skew_eq, PfaffianRecognition.CoRP.det_weighted_adjacency_char_two]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext M
  rw [mem_pm, Finset.mem_filter]
  simp

theorem sum_superset {R : Type*} [CommRing R] (w : G.edgeSet → R) (T : Finset G.edgeSet)
    (S : Finset (Fin N))
    (hT : ∀ t₁ ∈ T, ∀ t₂ ∈ T, ∀ v, v ∈ (t₁ : Sym2 (Fin N)) → v ∈ (t₂ : Sym2 (Fin N)) → t₁ = t₂)
    (hS : ∀ v, v ∈ S ↔ ∃ t ∈ T, v ∈ (t : Sym2 (Fin N))) :
    ∑ M ∈ univ.filter (fun M => MulmuleyVV.Matching.IsPerfectMatchingEdges G M ∧ T ⊆ M),
      ∏ e ∈ M, w e ^ 2 =
      (∏ t ∈ T, w t ^ 2) *
        ∑ M ∈ univ.filter (fun M => IsPMOn G (fun v => v ∉ S) M), ∏ e ∈ M, w e ^ 2 := by
  have hdisj : ∀ M, IsPMOn G (fun v => v ∉ S) M → Disjoint T M := by
    intro M hM
    rw [Finset.disjoint_left]
    intro t ht htM
    have hv : t.val.out.1 ∈ (t : Sym2 (Fin N)) := Sym2.out_fst_mem _
    exact hM.1 t htM _ hv ((hS _).2 ⟨t, ht, hv⟩)
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_bij' (fun M _ => T ∪ M) (fun M _ => M \ T) ?_ ?_ ?_ ?_ ?_
  · intro M hM
    rw [Finset.mem_filter] at hM ⊢
    obtain ⟨-, hM⟩ := hM
    refine ⟨mem_univ _, ?_, Finset.subset_union_left⟩
    intro v
    by_cases hvS : v ∈ S
    · obtain ⟨t, ht, hvt⟩ := (hS v).1 hvS
      refine ⟨t, ⟨Finset.mem_union_left _ ht, hvt⟩, ?_⟩
      rintro e ⟨he, hve⟩
      rcases Finset.mem_union.1 he with he | he
      · exact hT e he t ht v hve hvt
      · exact absurd hvS (hM.1 e he v hve)
    · obtain ⟨e, ⟨heM, hve⟩, huniq⟩ := hM.2 v hvS
      refine ⟨e, ⟨Finset.mem_union_right _ heM, hve⟩, ?_⟩
      rintro e' ⟨he', hve'⟩
      rcases Finset.mem_union.1 he' with he' | he'
      · exact absurd ((hS v).2 ⟨e', he', hve'⟩) hvS
      · exact huniq e' ⟨he', hve'⟩
  · intro M hM
    rw [Finset.mem_filter] at hM ⊢
    obtain ⟨-, hPM, hTM⟩ := hM
    refine ⟨mem_univ _, ?_, ?_⟩
    · intro e he v hve hvS
      obtain ⟨t, ht, hvt⟩ := (hS v).1 hvS
      rw [Finset.mem_sdiff] at he
      have := (hPM v).unique ⟨he.1, hve⟩ ⟨hTM ht, hvt⟩
      exact he.2 (this ▸ ht)
    · intro v hvS
      obtain ⟨e, ⟨he, hve⟩, huniq⟩ := hPM v
      refine ⟨e, ⟨Finset.mem_sdiff.2 ⟨he, fun heT => hvS ((hS v).2 ⟨e, heT, hve⟩)⟩, hve⟩, ?_⟩
      rintro e' ⟨he', hve'⟩
      exact huniq e' ⟨(Finset.mem_sdiff.1 he').1, hve'⟩
  · intro M hM
    exact Finset.union_sdiff_cancel_left (hdisj M (Finset.mem_filter.1 hM).2)
  · intro M hM
    exact Finset.union_sdiff_of_subset (Finset.mem_filter.1 hM).2.2
  · intro M hM
    rw [Finset.prod_union (hdisj M (Finset.mem_filter.1 hM).2)]

theorem mem_edgeVertices (e : G.edgeSet) (v : Fin N) :
    v ∈ edgeVertices e ↔ v ∈ (e : Sym2 (Fin N)) := by
  rw [SignParityAux.mem_iff]
  simp [edgeVertices]

/-- Sum over perfect matchings containing `e`. -/
theorem sum_containing_one (K : Type*) [CommRing K] [CharP K 2] (D : Orientation G)
    (e : G.edgeSet) :
    ∑ M ∈ univ.filter (fun M => MulmuleyVV.Matching.IsPerfectMatchingEdges G M ∧ e ∈ M),
      ∏ f ∈ M, (MvPolynomial.X f : MvPolynomial G.edgeSet K) ^ 2 =
      (MvPolynomial.X e) ^ 2 * principalDet K D (edgeVertices e) := by
  rw [principalDet_eq]
  have := sum_superset (fun f => (MvPolynomial.X f : MvPolynomial G.edgeSet K)) {e}
    (edgeVertices e) (by simp) (fun v => by simp [mem_edgeVertices])
  rw [Finset.prod_singleton] at this
  rw [← this]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext M
  simp only [Finset.mem_filter, Finset.singleton_subset_iff]

theorem crosses_disjoint {e f : G.edgeSet} (h : Crosses e f) (v : Fin N)
    (he : v ∈ (e : Sym2 (Fin N))) (hf : v ∈ (f : Sym2 (Fin N))) : False := by
  rw [SignParityAux.mem_iff] at he hf
  have h1 := SignParityAux.lo_lt_hi e
  have h2 := SignParityAux.lo_lt_hi f
  rcases h with ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> rcases he with rfl | rfl <;> rcases hf with h | h <;>
    order

theorem sum_containing_two (K : Type*) [CommRing K] [CharP K 2] (D : Orientation G)
    (e f : G.edgeSet) (hlt : edgeLo e < edgeLo f) (hc : Crosses e f) :
    ∑ M ∈ univ.filter (fun M => MulmuleyVV.Matching.IsPerfectMatchingEdges G M ∧ (e ∈ M ∧ f ∈ M)),
      ∏ g ∈ M, (MvPolynomial.X g : MvPolynomial G.edgeSet K) ^ 2 =
      (MvPolynomial.X e) ^ 2 * MvPolynomial.X f ^ 2 *
        principalDet K D (edgeVertices e ∪ edgeVertices f) := by
  have hne : e ≠ f := fun h => lt_irrefl _ (h ▸ hlt)
  rw [principalDet_eq]
  have := sum_superset (fun g => (MvPolynomial.X g : MvPolynomial G.edgeSet K)) {e, f}
    (edgeVertices e ∪ edgeVertices f) ?_ ?_
  · rw [Finset.prod_pair hne] at this
    rw [← this]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext M
    simp only [Finset.mem_filter, Finset.insert_subset_iff, Finset.singleton_subset_iff]
  · intro t₁ ht₁ t₂ ht₂ v hv₁ hv₂
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht₁ ht₂
    rcases ht₁ with rfl | rfl <;> rcases ht₂ with rfl | rfl
    · rfl
    · exact (crosses_disjoint hc v hv₁ hv₂).elim
    · exact (crosses_disjoint hc v hv₂ hv₁).elim
    · rfl
  · intro v
    simp [mem_edgeVertices]

theorem parity_aux (a b c d : ℕ) :
    ((-1 : ℤ) ^ (a % 2 + b % 2) ≠ (-1) ^ (c + d)) ↔ ((c + d) % 2 + b + a) % 2 = 1 := by
  rw [neg_one_pow_eq_pow_mod_two (n := a % 2 + b % 2), neg_one_pow_eq_pow_mod_two (n := c + d)]
  have hx : (a % 2 + b % 2) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hy : (c + d) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have key : ((-1 : ℤ) ^ ((a % 2 + b % 2) % 2) ≠ (-1) ^ ((c + d) % 2)) ↔
      (a % 2 + b % 2) % 2 ≠ (c + d) % 2 := by
    generalize (a % 2 + b % 2) % 2 = x at hx ⊢
    generalize (c + d) % 2 = y at hy ⊢
    interval_cases x <;> interval_cases y <;> simp
  rw [key]
  omega

theorem sum_monomials_ne_zero (K : Type*) [Field K] {σ : Type*} (T : Finset (Finset σ))
    (M₀ : Finset σ) (hM₀ : M₀ ∈ T) :
    ∑ M ∈ T, ∏ e ∈ M, (MvPolynomial.X e : MvPolynomial σ K) ^ 2 ≠ 0 := by
  intro h
  have hmon : ∀ M : Finset σ, ∏ e ∈ M, (MvPolynomial.X e : MvPolynomial σ K) ^ 2 =
      MvPolynomial.monomial (∑ e ∈ M, Finsupp.single e 2) 1 := by
    intro M
    rw [MvPolynomial.monomial_sum_one]
    simp [MvPolynomial.X_pow_eq_monomial]
  have happ : ∀ (M : Finset σ) (x : σ), (∑ e ∈ M, Finsupp.single e 2) x = if x ∈ M then 2 else 0 := by
    intro M x
    rw [Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply]
  have hinj : ∀ M : Finset σ, (∑ e ∈ M, Finsupp.single e 2) = (∑ e ∈ M₀, Finsupp.single e 2) ↔
      M = M₀ := by
    intro M
    constructor
    · intro hM
      ext x
      have := congrArg (fun m => m x) hM
      simp only [happ] at this
      by_cases h1 : x ∈ M <;> by_cases h2 : x ∈ M₀ <;> simp_all
    · rintro rfl; rfl
  have := congrArg (MvPolynomial.coeff (∑ e ∈ M₀, Finsupp.single e 2)) h
  simp only [MvPolynomial.coeff_sum, hmon, MvPolynomial.coeff_monomial, hinj,
    MvPolynomial.coeff_zero] at this
  rw [Finset.sum_ite_eq' T M₀ (fun _ => (1 : K)), if_pos hM₀] at this
  exact one_ne_zero this

end PfaffianRecognition.Recognition.MinorAux

namespace PfaffianRecognition.Recognition

open PfaffianRecognition.Recognition.MinorAux Finset

/-- Lemma 2.3 (mission milestone, exact statement). -/
theorem wrong_sign_minor_identity {N : ℕ} (G : SimpleGraph (Fin N))
    (D : Orientation G) (F : Finset G.edgeSet)
    (hF : MulmuleyVV.Matching.IsPerfectMatchingEdges G F)
    (K : Type*) [Field K] [CharP K 2] :
    wrongSignPolynomial K D F = minorExpression K D F := by
  classical
  set P : Finset G.edgeSet → MvPolynomial G.edgeSet K :=
    fun M => ∏ e ∈ M, (MvPolynomial.X e : MvPolynomial G.edgeSet K) ^ 2 with hP
  set PM := univ.filter (fun M => MulmuleyVV.Matching.IsPerfectMatchingEdges G M) with hPM
  set cA : Finset G.edgeSet → ℕ :=
    fun M => ((crossingPairs G).filter fun ef => ef.1 ∈ M ∧ ef.2 ∈ M).card with hcA
  set bA : Finset G.edgeSet → ℕ := fun M => (M ∩ backwardEdges D).card with hbA
  have hcp : ∀ M, crossingParity M = cA M % 2 := fun M => by
    unfold crossingParity; rw [hcA]
  have hbp : ∀ M, backwardParity D M = bA M % 2 := fun M => by
    unfold backwardParity; rw [hbA]
  have hW : wrongSignPolynomial K D F =
      ∑ M ∈ PM, ((referenceParity D F + bA M + cA M : ℕ) : MvPolynomial G.edgeSet K) * P M := by
    unfold wrongSignPolynomial
    rw [Finset.sum_filter]
    have hpm : MulmuleyVV.Matching.perfectMatchings G = PM := by
      ext M; rw [mem_pm, hPM, Finset.mem_filter]; simp
    rw [hpm]
    refine Finset.sum_congr rfl (fun M hM => ?_)
    have hMpm := (Finset.mem_filter.1 hM).2
    rw [matching_sign_parity G D M hMpm, matching_sign_parity G D F hF, hcp M, hbp M]
    have hr : referenceParity D F = (crossingParity F + backwardParity D F) % 2 := rfl
    have key := parity_aux (cA M) (bA M) (crossingParity F) (backwardParity D F)
    rw [hr, CharP.cast_eq_mod (MvPolynomial G.edgeSet K) 2]
    by_cases h : (-1 : ℤ) ^ (cA M % 2 + bA M % 2) ≠ (-1) ^ (crossingParity F + backwardParity D F)
    · rw [if_pos h, key.1 h]; simp [hP]
    · rw [if_neg h]
      have h0 : ((crossingParity F + backwardParity D F) % 2 + bA M + cA M) % 2 = 0 := by
        have := mt key.2 h
        omega
      rw [h0]; simp
  rw [hW]
  simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib]
  unfold minorExpression
  congr 1
  congr 1
  · rw [det_skew_eq, Finset.mul_sum, map_natCast]
  · have h1 : ∀ M, ((bA M : ℕ) : MvPolynomial G.edgeSet K) * P M =
        ∑ e ∈ backwardEdges D, if e ∈ M then P M else 0 := by
      intro M
      rw [hbA]
      simp only
      rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter, Nat.cast_sum,
        Finset.sum_mul]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun M _ => h1 M), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [← sum_containing_one K D e, ← Finset.sum_filter, hPM, Finset.filter_filter]
  · have h1 : ∀ M, ((cA M : ℕ) : MvPolynomial G.edgeSet K) * P M =
        ∑ ef ∈ crossingPairs G, if (ef.1 ∈ M ∧ ef.2 ∈ M) then P M else 0 := by
      intro M
      rw [hcA]
      simp only
      rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun M _ => h1 M), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ef hef => ?_)
    have hef' : edgeLo ef.1 < edgeLo ef.2 ∧ Crosses ef.1 ef.2 := by
      unfold crossingPairs at hef
      exact (Finset.mem_filter.1 hef).2
    rw [← sum_containing_two K D ef.1 ef.2 hef'.1 hef'.2, ← Finset.sum_filter, hPM,
      Finset.filter_filter]

/-- Proposition 2.2 (mission milestone, exact statement). -/
theorem wrong_sign_zero_iff {N : ℕ} (G : SimpleGraph (Fin N)) (D : Orientation G)
    (F : Finset G.edgeSet) (hF : MulmuleyVV.Matching.IsPerfectMatchingEdges G F)
    (K : Type*) [Field K] [Fintype K] [CharP K 2] :
    IsPfaffianOrientation D ↔ wrongSignPolynomial K D F = 0 := by
  classical
  constructor
  · intro hPf
    unfold wrongSignPolynomial
    apply Finset.sum_eq_zero
    intro M hM
    rw [Finset.mem_filter] at hM
    exact absurd (hPf M F ((mem_pm M).1 hM.1) hF) hM.2
  · intro h0
    have key : ∀ M, MulmuleyVV.Matching.IsPerfectMatchingEdges G M →
        matchingSign D M = matchingSign D F := by
      intro M hM
      by_contra hne
      unfold wrongSignPolynomial at h0
      refine sum_monomials_ne_zero K _ M ?_ h0
      rw [Finset.mem_filter]
      exact ⟨(mem_pm M).2 hM, hne⟩
    intro M₁ M₂ h1 h2
    rw [key M₁ h1, key M₂ h2]

end PfaffianRecognition.Recognition


theorem solution {N : ℕ} (G : SimpleGraph (Fin N)) (D : PfaffianRecognition.Recognition.Orientation G)
    (F : Finset G.edgeSet) (hF : MulmuleyVV.Matching.IsPerfectMatchingEdges G F)
    (K : Type*) [Field K] [Fintype K] [CharP K 2] :
    PfaffianRecognition.Recognition.IsPfaffianOrientation D ↔
      PfaffianRecognition.Recognition.wrongSignPolynomial K D F = 0 :=
  PfaffianRecognition.Recognition.wrong_sign_zero_iff G D F hF K
