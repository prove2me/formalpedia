-- Prove2me | solution 1 for OAI.WLIdentification.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T21:23:22.342042+00:00
-- url     : https://prove2.me/submissions/3236a299-a824-4542-88a9-8a361cac202c

import Mathlib
import Definitions.Def_WLIdentification
import Definitions.Def_OAIQWWLI002

section
-- module Solutions.OAIQW_WLIdentification.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.Refinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

/-- Matching diagonal tuples yields exactly a degree-preserving vertex bijection. -/
theorem round_one_degreeBijection {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    (h : tupleHistogram G k 1 = tupleHistogram H k 1) :
    ∃ e : Fin G.order ≃ Fin H.order, ∀ v, degree G v = degree H (e v) := by
  obtain ⟨E, hE⟩ := tupleRound_bijection h
  let i : Fin k := ⟨0, by omega⟩
  have hdiag (v : Fin k → Fin G.order) :
      (∀ j, v j = v i) ↔ ∀ j, E v j = E v i := by
    apply forall_congr'
    intro j
    exact (round_one_local hk (hE v)).1 j i
  let e := (diagonalEquiv i (Fin G.order)).trans
    ((E.subtypeEquiv hdiag).trans (diagonalEquiv i (Fin H.order)).symm)
  refine ⟨e, ?_⟩
  intro v
  exact (round_one_local hk (hE (fun _ => v))).2.2 i

/-- The needed local reconstruction information follows from the literal r-WL definition. -/
theorem equivalent_degreeBijection {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    (h : Equivalent k G H) :
    ∃ e : Fin G.order ≃ Fin H.order, ∀ v, degree G v = degree H (e v) := by
  have hne : k ≠ 1 := by omega
  rw [Equivalent, ite_eq_right hne] at h
  exact round_one_degreeBijection hk (h 1)

/-- Any at most k distinguished vertices have a simultaneous degree-and-incidence match.
This is enough to recover a whole bounded-size incidence piece, not just one valuation. -/
theorem equivalent_local_match {G H : Graph} {k m : ℕ} (hk : 2 ≤ k)
    (h : Equivalent k G H) (hm : m ≤ k) (hm0 : 0 < m) (v : Fin m → Fin G.order) :
    ∃ w : Fin m → Fin H.order,
      (∀ i j, v i = v j ↔ w i = w j) ∧
      (∀ i j, G.edge (v i) (v j) = H.edge (w i) (w j)) ∧
      (∀ i, degree G (v i) = degree H (w i)) := by
  have hne : k ≠ 1 := by omega
  rw [Equivalent, ite_eq_right hne] at h
  obtain ⟨E, hE⟩ := tupleRound_bijection (h 1)
  let v' : Fin k → Fin G.order := fun j =>
    if hj : j.val < m then v ⟨j.val, hj⟩ else v ⟨0, hm0⟩
  have hv (i : Fin m) : v' (Fin.castLE hm i) = v i := by simp [v', i.isLt]
  let w : Fin m → Fin H.order := fun i => E v' (Fin.castLE hm i)
  refine ⟨w, ?_, ?_, ?_⟩
  · intro i j
    simpa only [hv] using (round_one_local hk (hE v')).1 (Fin.castLE hm i) (Fin.castLE hm j)
  · intro i j
    simpa only [hv] using (round_one_local hk (hE v')).2.1 (Fin.castLE hm i) (Fin.castLE hm j)
  · intro i
    simpa only [hv] using (round_one_local hk (hE v')).2.2 (Fin.castLE hm i)

/-- A second joint round gives a single vertex bijection preserving adjacency to
any distinguished slot and the degrees of all possible next vertices. -/
theorem round_two_neighborBijection {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    {v : Fin k → Fin G.order} {w : Fin k → Fin H.order}
    (h : tupleColor G k 2 v = tupleColor H k 2 w) (i : Fin k) :
    ∃ e : Fin G.order ≃ Fin H.order, ∀ z,
      G.edge (v i) z = H.edge (w i) (e z) ∧ degree G z = degree H (e z) := by
  have hj : ∃ j : Fin k, i ≠ j := by
    let a : Fin k := ⟨0, by omega⟩
    let b : Fin k := ⟨1, by omega⟩
    by_cases hia : i = a
    · refine ⟨b, ?_⟩
      subst i
      intro he
      have := congrArg Fin.val he
      simp [a, b] at this
    · exact ⟨a, hia⟩
  obtain ⟨j, hij⟩ := hj
  have hh := congrArg Prod.snd h
  change Finset.univ.val.map (fun z => fun j => tupleColor G k 1 (Function.update v j z)) =
    Finset.univ.val.map (fun z => fun j => tupleColor H k 1 (Function.update w j z)) at hh
  obtain ⟨e, he⟩ := exists_colorEquiv _ _ hh
  refine ⟨e, ?_⟩
  intro z
  have hz := round_one_local hk (v := Function.update v j z)
    (w := Function.update w j (e z)) (congrFun (he z) j)
  simpa only [Function.update_of_ne hij, Function.update_self] using
    And.intro (hz.2.1 i j) (hz.2.2 j)

theorem round_two_degreeNeighbors {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    {v : Fin k → Fin G.order} {w : Fin k → Fin H.order}
    (h : tupleColor G k 2 v = tupleColor H k 2 w) (i : Fin k) (d : ℕ) :
    degreeNeighbors G (v i) d = degreeNeighbors H (w i) d := by
  obtain ⟨e, he⟩ := round_two_neighborBijection hk h i
  apply Finset.card_equiv e
  intro z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, (he z).1, (he z).2]

theorem equivalent_symm {G H : Graph} {k : ℕ} (h : Equivalent k G H) :
    Equivalent k H G := by
  unfold Equivalent at *
  split_ifs at * <;> exact fun s => (h s).symm

/-- In particular private-leaf counts, rather than just total degrees, are
preserved by a simultaneous local match in every equivalent mate. -/
theorem equivalent_local_neighborhood_match {G H : Graph} {k m : ℕ} (hk : 2 ≤ k)
    (h : Equivalent k G H) (hm : m ≤ k) (hm0 : 0 < m) (v : Fin m → Fin G.order) :
    ∃ w : Fin m → Fin H.order,
      (∀ i j, v i = v j ↔ w i = w j) ∧
      (∀ i j, G.edge (v i) (v j) = H.edge (w i) (w j)) ∧
      (∀ i, degree G (v i) = degree H (w i)) ∧
      (∀ i d, degreeNeighbors G (v i) d = degreeNeighbors H (w i) d) := by
  have hne : k ≠ 1 := by omega
  rw [Equivalent, ite_eq_right hne] at h
  obtain ⟨E, hE⟩ := tupleRound_bijection (h 2)
  let v' : Fin k → Fin G.order := fun j =>
    if hj : j.val < m then v ⟨j.val, hj⟩ else v ⟨0, hm0⟩
  have hv (i : Fin m) : v' (Fin.castLE hm i) = v i := by simp [v', i.isLt]
  let w : Fin m → Fin H.order := fun i => E v' (Fin.castLE hm i)
  have h1 : tupleColor G k 1 v' = tupleColor H k 1 (E v') :=
    congrArg Prod.fst (hE v')
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa only [hv] using (round_one_local hk h1).1 (Fin.castLE hm i) (Fin.castLE hm j)
  · intro i j
    simpa only [hv] using (round_one_local hk h1).2.1 (Fin.castLE hm i) (Fin.castLE hm j)
  · intro i
    simpa only [hv] using (round_one_local hk h1).2.2 (Fin.castLE hm i)
  · intro i d
    simpa only [hv] using round_two_degreeNeighbors hk (hE v') (Fin.castLE hm i) d

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.PrivateLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

/-- The leaf gadget really erases colors: uncolored isomorphism forces one
color-preserving base isomorphism, not a separate choice in each block. -/
theorem taggedIso_iff {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (color : V → ℕ) (color' : W → ℕ)
    (hc : ∀ v, 0 < color v) (hc' : ∀ w, 0 < color' w)
    (hN : Fintype.card V = Fintype.card W) :
    Nonempty (withLeaves G (tagSize color) ≃g withLeaves H (tagSize color')) ↔
      ∃ e : G ≃g H, ∀ v, color v = color' (e v) := by
  constructor
  · rintro ⟨e⟩
    let E := e.toEquiv.subtypeEquiv
      (p := fun x => 1 < (withLeaves G (tagSize color)).degree x)
      (q := fun x => 1 < (withLeaves H (tagSize color')).degree x)
      (fun x => by
        change (1 < (withLeaves G (tagSize color)).degree x) ↔
          (1 < (withLeaves H (tagSize color')).degree (e x))
        rw [e.degree_eq])
    let e0 := (baseDegreeEquiv G color hc).trans (E.trans (baseDegreeEquiv H color' hc').symm)
    have he0 (v : V) : Sum.inl (e0 v) = e (Sum.inl v) := by
      have hh := congrArg Subtype.val ((baseDegreeEquiv H color' hc').apply_symm_apply
        (E (baseDegreeEquiv G color hc v)))
      exact hh
    let e1 : G ≃g H := {
      toEquiv := e0
      map_rel_iff' := by
        intro v w
        have hh := e.map_adj_iff (v := Sum.inl v) (w := Sum.inl w)
        rw [← he0 v, ← he0 w] at hh
        exact hh }
    refine ⟨e1, ?_⟩
    intro v
    have hd := e.degree_eq (Sum.inl v)
    rw [← he0 v] at hd
    have hdiv := congrArg (fun n => n / (Fintype.card V + 1)) hd
    rw [tag_degree_color, hN, tag_degree_color] at hdiv
    exact hdiv.symm
  · rintro ⟨e, he⟩
    refine ⟨withLeavesIso e _ _ ?_⟩
    intro v
    simp only [tagSize, he v, hN]

theorem isomorphic_graphOfSimple_iff {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    Isomorphic (graphOfSimple G) (graphOfSimple H) ↔ Nonempty (G ≃g H) := by
  classical
  constructor
  · rintro ⟨e, he⟩
    let E := (Fintype.equivFin V).trans (e.trans (Fintype.equivFin W).symm)
    refine ⟨{ toEquiv := E, map_rel_iff' := ?_ }⟩
    intro v w
    have hh := he (Fintype.equivFin V v) (Fintype.equivFin V w)
    change H.Adj ((Fintype.equivFin W).symm (e (Fintype.equivFin V v)))
      ((Fintype.equivFin W).symm (e (Fintype.equivFin V w))) ↔ G.Adj v w
    simpa [graphOfSimple, decide_eq_decide] using hh.symm
  · rintro ⟨e⟩
    let E := (Fintype.equivFin V).symm.trans (e.toEquiv.trans (Fintype.equivFin W))
    refine ⟨E, ?_⟩
    intro i j
    change decide (G.Adj ((Fintype.equivFin V).symm i) ((Fintype.equivFin V).symm j)) =
      decide (H.Adj ((Fintype.equivFin W).symm (Fintype.equivFin W
        (e ((Fintype.equivFin V).symm i))))
        ((Fintype.equivFin W).symm (Fintype.equivFin W (e ((Fintype.equivFin V).symm j)))))
    simp
    exact e.map_adj_iff.symm

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.AffineIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace AffineBlocks

variable {C B : Type} [Fintype C] [DecidableEq C]

/-- All-zero valuations extract one global offset from a color-preserving
isomorphism. No agreement between independently chosen block maps is assumed. -/
theorem coloredIso_solution (D : AffineBlocks C B) (beta : B → Bit)
    (e : D.baseGraph 0 ≃g D.baseGraph beta)
    (he : ∀ v, D.colorName (e v) = D.colorName v) :
    ∃ offset, D.Solves beta offset := by
  classical
  have hc (c : C) : ∃ a, e (.inl (c, 0)) = .inl (c, a) :=
    D.exists_bit_of_color _ c (he _)
  choose offset hoff using hc
  refine ⟨offset, ?_⟩
  intro b
  let z : {v // D.Legal 0 b v} := ⟨0, D.legal_zero b⟩
  obtain ⟨w, hw⟩ := D.exists_valuation_of_color (e (.inr ⟨b, z⟩)) b (he _)
  have hval : w.val = D.restrict b offset := by
    funext c
    have hs : (D.baseGraph 0).Adj (.inr ⟨b, z⟩) (.inl (c.val, 0)) := ⟨c.property, rfl⟩
    have ht := e.map_adj_iff.mpr hs
    rw [hw, hoff c.val] at ht
    obtain ⟨hc, hvalue⟩ := ht
    exact hvalue
  rw [← hval]
  exact w.property

theorem coloredIso_iff (D : AffineBlocks C B) (beta : B → Bit) :
    (∃ e : D.baseGraph 0 ≃g D.baseGraph beta,
      ∀ v, D.colorName (e v) = D.colorName v) ↔ ∃ offset, D.Solves beta offset := by
  constructor
  · rintro ⟨e, he⟩
    exact D.coloredIso_solution beta e he
  · rintro ⟨offset, ho⟩
    exact ⟨D.translationIso beta offset ho, D.translationIso_color beta offset ho⟩

variable [Fintype B]

theorem graph_isomorphic_iff (D : AffineBlocks C B) (beta : B → Bit) :
    Isomorphic (D.graph 0) (D.graph beta) ↔ ∃ offset, D.Solves beta offset := by
  unfold graph taggedGraph
  rw [isomorphic_graphOfSimple_iff, taggedIso_iff _ _ _ _ D.colorNat_pos D.colorNat_pos
    (D.vertex_card 0 beta)]
  rw [← D.coloredIso_iff beta]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, fun v => (D.colorNat_eq_iff v (e v)).mp (he v) |>.symm⟩
  · rintro ⟨e, he⟩
    exact ⟨e, fun v => (D.colorNat_eq_iff v (e v)).mpr (he v).symm⟩

omit [Fintype B]

theorem bit_cases (a : Bit) : a = 0 ∨ a = 1 := by
  have hv := ZMod.val_lt a
  have h : a.val = 0 ∨ a.val = 1 := by omega
  rcases h with h | h
  · exact Or.inl ((ZMod.val_injective 2) h)
  · exact Or.inr ((ZMod.val_injective 2) h)

theorem bit_injective_translation (f : Bit → Bit) (hf : Function.Injective f) (a : Bit) :
    f a = a + f 0 := by
  have h01 : f 0 ≠ f 1 := hf.ne (by decide)
  rcases bit_cases a with rfl | rfl
  · simp
  · rcases bit_cases (f 0) with h0 | h0 <;>
      rcases bit_cases (f 1) with h1 | h1 <;> simp_all
    decide

theorem piece_bit_of_color (D : AffineBlocks C B) {beta : B → Bit} (b : B)
    (v : D.Piece beta b) (c : D.coordinates b)
    (h : D.colorName (D.pieceEmbed b v) = .inl c.val) :
    ∃ a, v = .inl (c, a) := by
  cases v with
  | inl p =>
    have hp : p.1.val = c.val := Sum.inl.inj h
    have hp' : p.1 = c := Subtype.ext hp
    exact ⟨p.2, by cases p; simp_all⟩
  | inr w => simp [pieceEmbed, colorName] at h

theorem piece_valuation_of_color (D : AffineBlocks C B) {beta : B → Bit} (b : B)
    (v : D.Piece beta b) (h : D.colorName (D.pieceEmbed b v) = .inr b) :
    ∃ w, v = .inr w := by
  cases v with
  | inl p => simp [pieceEmbed, colorName] at h
  | inr w => exact ⟨w, rfl⟩

/-- One entire incidence piece determines a shifted equation in any fixed
labeling of its bit pairs. Coordinate flips in different pieces need not agree. -/
theorem local_reconstruction (D : AffineBlocks C B) (H : SimpleGraph (D.Vertex 0)) (b : B)
    (e : D.pieceGraph 0 b ≃g H.comap (D.pieceEmbed b))
    (he : ∀ v, D.colorName (D.pieceEmbed b (e v)) = D.colorName (D.pieceEmbed b v)) :
    ∃ offset : D.Local b, ∃ E : {v // D.Legal 0 b v} ≃ {v // D.Legal 0 b v},
      ∀ (v : {v // D.Legal 0 b v}) (c : D.coordinates b) (a : Bit),
        H.Adj (.inl (c.val, a)) (.inr ⟨b, E v⟩) ↔ v.val c + offset c = a := by
  classical
  have hbit (c : D.coordinates b) (a : Bit) : ∃ w, e (.inl (c, a)) = .inl (c, w) :=
    D.piece_bit_of_color b _ c (he _)
  choose f hf using hbit
  have hfinj (c : D.coordinates b) : Function.Injective (f c) := by
    intro a a' h
    have hh : e (.inl (c, a)) = e (.inl (c, a')) := by rw [hf, hf, h]
    have hh' := e.injective hh
    exact (Prod.mk.inj (Sum.inl.inj hh')).2
  have hftrans (c : D.coordinates b) (a : Bit) : f c a = a + f c 0 :=
    bit_injective_translation (f c) (hfinj c) a
  have hval (v : {v // D.Legal 0 b v}) : ∃ w, e (.inr v) = .inr w :=
    D.piece_valuation_of_color b _ (he _)
  choose fv hfv using hval
  have hfvinj : Function.Injective fv := by
    intro v w h
    have hh : e (.inr v) = e (.inr w) := by rw [hfv, hfv, h]
    exact Sum.inr.inj (e.injective hh)
  let E := Equiv.ofBijective fv ((Fintype.bijective_iff_injective_and_card fv).mpr ⟨hfvinj, rfl⟩)
  refine ⟨fun c => f c 0, E, ?_⟩
  intro v c a
  have hh := e.map_adj_iff (v := Sum.inl (c, a - f c 0)) (w := Sum.inr v)
  rw [hf, hfv, hftrans, sub_add_cancel] at hh
  change H.Adj (.inl (c.val, a)) (.inr ⟨b, fv v⟩) ↔
    (∃ h : c.val ∈ D.coordinates b, v.val ⟨c.val, h⟩ = a - f c 0) at hh
  simp only [Subtype.coe_eta, exists_prop_of_true c.property] at hh
  exact hh.trans (eq_sub_iff_add_eq)

theorem base_adj_allowed (D : AffineBlocks C B) {beta : B → Bit} {x y : D.Vertex beta}
    (h : (D.baseGraph beta).Adj x y) : D.Allowed x y := by
  cases x <;> cases y
  · exact h
  · exact h.choose
  · exact h.choose
  · exact h

/-- Combining the independently reconstructed pieces uses a single labeling of
all shared bit pairs, but permits one independent right-hand side per block. -/
theorem base_reconstruction (D : AffineBlocks C B) (H : SimpleGraph (D.Vertex 0))
    (hallowed : ∀ x y, H.Adj x y → D.Allowed x y)
    (hlocal : ∀ b, ∃ e : D.pieceGraph 0 b ≃g H.comap (D.pieceEmbed b),
      ∀ v, D.colorName (D.pieceEmbed b (e v)) = D.colorName (D.pieceEmbed b v)) :
    ∃ beta, ∃ e : D.baseGraph beta ≃g H, ∀ v, D.colorName (e v) = D.colorName v := by
  classical
  have hr (b : B) :
      ∃ offset : D.Local b, ∃ E : {v // D.Legal 0 b v} ≃ {v // D.Legal 0 b v},
        ∀ (v : {v // D.Legal 0 b v}) (c : D.coordinates b) (a : Bit),
          H.Adj (.inl (c.val, a)) (.inr ⟨b, E v⟩) ↔ v.val c + offset c = a := by
    obtain ⟨e, he⟩ := hlocal b
    exact D.local_reconstruction H b e he
  choose offset E hE using hr
  let beta : B → Bit := fun b => D.form b (offset b)
  let T (b : B) : {v // D.Legal 0 b v} ≃ {v // D.Legal beta b v} :=
    D.legalTranslate b (offset b) (fun _ => by simp [beta])
  let eV (b : B) := (T b).symm.trans (E b)
  let e : D.Vertex beta ≃ D.Vertex 0 :=
    Equiv.sumCongr (Equiv.refl _) (Equiv.sigmaCongrRight eV)
  have hbits (b : B) (v : {v // D.Legal beta b v}) (c : D.coordinates b) (a : Bit) :
      H.Adj (.inl (c.val, a)) (.inr ⟨b, eV b v⟩) ↔ v.val c = a := by
    have hh := hE b ((T b).symm v) c a
    change H.Adj (.inl (c.val, a)) (.inr ⟨b, eV b v⟩) ↔
      v.val c - offset b c + offset b c = a at hh
    simpa only [sub_add_cancel] using hh
  refine ⟨beta, { toEquiv := e, map_rel_iff' := ?_ }, ?_⟩
  · intro x y
    cases x with
    | inl p =>
      cases y with
      | inl q =>
        change H.Adj (.inl p) (.inl q) ↔ False
        exact ⟨hallowed _ _, False.elim⟩
      | inr v =>
        change H.Adj (.inl p) (.inr ⟨v.1, eV v.1 v.2⟩) ↔
          (∃ h : p.1 ∈ D.coordinates v.1, v.2.val ⟨p.1, h⟩ = p.2)
        by_cases hc : p.1 ∈ D.coordinates v.1
        · simpa only [exists_prop_of_true hc] using hbits v.1 v.2 ⟨p.1, hc⟩ p.2
        · exact ⟨fun h => False.elim (hc (hallowed _ _ h)), fun h => False.elim (hc h.choose)⟩
    | inr v =>
      cases y with
      | inl p =>
        change H.Adj (.inr ⟨v.1, eV v.1 v.2⟩) (.inl p) ↔
          (∃ h : p.1 ∈ D.coordinates v.1, v.2.val ⟨p.1, h⟩ = p.2)
        rw [H.adj_comm]
        by_cases hc : p.1 ∈ D.coordinates v.1
        · simpa only [exists_prop_of_true hc] using hbits v.1 v.2 ⟨p.1, hc⟩ p.2
        · exact ⟨fun h => False.elim (hc (hallowed _ _ h)), fun h => False.elim (hc h.choose)⟩
      | inr w =>
        change H.Adj (.inr ⟨v.1, eV v.1 v.2⟩) (.inr ⟨w.1, eV w.1 w.2⟩) ↔ False
        exact ⟨hallowed _ _, False.elim⟩
  · intro v
    cases v <;> rfl

end AffineBlocks

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.MateReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

theorem histogram_eq_of_equiv {α β γ : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → γ) (g : β → γ) (h : ∀ a, f a = g (e a)) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  rw [← Multiset.map_univ_val_equiv e, Multiset.map_map]
  exact Multiset.map_congr rfl (fun a _ => h a)

theorem filteredHistogram_eq_of_equiv {α β γ : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (p : α → Prop) (q : β → Prop) [DecidablePred p] [DecidablePred q]
    (f : α → γ) (g : β → γ) (hp : ∀ a, p a ↔ q (e a)) (h : ∀ a, f a = g (e a)) :
    (Finset.univ.filter p).val.map f = (Finset.univ.filter q).val.map g := by
  simp only [Finset.filter_val]
  conv_rhs => rw [← Multiset.map_univ_val_equiv e, Multiset.filter_map, Multiset.map_map]
  apply Multiset.map_congr
  · exact Multiset.filter_congr (fun a _ => hp a)
  · exact fun a _ => h a

theorem isomorphic_symm {G H : Graph} (h : Isomorphic G H) : Isomorphic H G := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  intro v w
  simpa only [e.apply_symm_apply] using (he (e.symm v) (e.symm w)).symm

theorem isomorphic_trans {G H I : Graph} (h : Isomorphic G H) (h' : Isomorphic H I) :
    Isomorphic G I := by
  obtain ⟨e, he⟩ := h
  obtain ⟨f, hf⟩ := h'
  exact ⟨e.trans f, fun v w => (he v w).trans (hf (e v) (e w))⟩

theorem neighborColor_isomorphic {G H : Graph} (e : Fin G.order ≃ Fin H.order)
    (he : ∀ v w, G.edge v w = H.edge (e v) (e w)) (s : ℕ) (v : Fin G.order) :
    neighborColor G s v = neighborColor H s (e v) := by
  induction s generalizing v with
  | zero => rfl
  | succ s ih =>
    change (neighborColor G s v, _) = (neighborColor H s (e v), _)
    apply Prod.ext (ih v)
    exact filteredHistogram_eq_of_equiv e _ _ _ _
      (fun w => by rw [he v w]) ih

theorem tupleColor_isomorphic {G H : Graph} (e : Fin G.order ≃ Fin H.order)
    (he : ∀ v w, G.edge v w = H.edge (e v) (e w)) (k s : ℕ) (v : Fin k → Fin G.order) :
    tupleColor G k s v = tupleColor H k s (e ∘ v) := by
  induction s generalizing v with
  | zero =>
    apply Prod.ext
    · funext i j
      exact decide_eq_decide.mpr e.injective.eq_iff.symm
    · funext i j
      exact he (v i) (v j)
  | succ s ih =>
    change (tupleColor G k s v, _) = (tupleColor H k s (e ∘ v), _)
    apply Prod.ext (ih v)
    apply histogram_eq_of_equiv e
    intro z
    funext i
    simpa only [Function.comp_update] using ih (Function.update v i z)

theorem isomorphic_equivalent {G H : Graph} (h : Isomorphic G H) (k : ℕ) : Equivalent k G H := by
  obtain ⟨e, he⟩ := h
  unfold Equivalent
  split_ifs
  · intro s
    exact histogram_eq_of_equiv e _ _ (neighborColor_isomorphic e he s)
  · intro s
    exact histogram_eq_of_equiv (Equiv.piCongrRight (fun _ : Fin k => e)) _ _
      (tupleColor_isomorphic e he k s)

theorem equivalent_trans {G H I : Graph} {k : ℕ}
    (h : Equivalent k G H) (h' : Equivalent k H I) : Equivalent k G I := by
  unfold Equivalent at *
  split_ifs at * <;> exact fun s => (h s).trans (h' s)

theorem graph_simple_isomorphic (G : Graph) : Isomorphic G (graphOfSimple (simpleOfGraph G)) := by
  refine ⟨Fintype.equivFin (Fin G.order), ?_⟩
  intro v w
  have hh : decide ((simpleOfGraph G).Adj v w) = G.edge v w := by
    cases h : G.edge v w <;> simp [simpleOfGraph, h]
  exact hh.symm.trans (graphOfSimple_edge (simpleOfGraph G) v w).symm

/-- A degree-one vertex has the same unique neighbor in every incident edge. -/
theorem degree_one_neighbors_eq {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v x y : V} (hd : G.degree v = 1)
    (hx : G.Adj v x) (hy : G.Adj v y) : x = y := by
  obtain ⟨w, _, hw⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hd
  exact (hw x hx).trans (hw y hy).symm

/-- Private-leaf reconstruction by exact finite counting. The prescribed leaf
counts exhaust all leaf vertices; no separate leaf-only component can remain. -/
theorem private_leaf_reconstruction {V : Type} [Fintype V] (ell : V → ℕ)
    (H : SimpleGraph (LeafVertex ell)) [DecidableRel H.Adj]
    (hleaf : ∀ (v : V) (j : Fin (ell v)), H.degree (.inr ⟨v, j⟩) = 1)
    (hcount : ∀ v, Fintype.card {l : Σ v, Fin (ell v) // H.Adj (.inl v) (.inr l)} = ell v) :
    ∃ e : withLeaves (H.comap Sum.inl) ell ≃g H, ∀ v, e (.inl v) = .inl v := by
  classical
  let F (v : V) : Fin (ell v) ≃ {l : Σ v, Fin (ell v) // H.Adj (.inl v) (.inr l)} :=
    Classical.choice (Fintype.card_eq.mp (by rw [Fintype.card_fin, hcount]))
  let f : (Σ v, Fin (ell v)) → (Σ v, Fin (ell v)) := fun l => (F l.1 l.2).val
  have hfadj (l : Σ v, Fin (ell v)) : H.Adj (.inl l.1) (.inr (f l)) := (F l.1 l.2).property
  have hfparent (l : Σ v, Fin (ell v)) (v : V) :
      H.Adj (.inl v) (.inr (f l)) ↔ v = l.1 := by
    constructor
    · intro h
      exact Sum.inl.inj (degree_one_neighbors_eq H (hleaf (f l).1 (f l).2)
        h.symm (hfadj l).symm)
    · rintro rfl
      exact hfadj l
  have hfinj : Function.Injective f := by
    intro l m heq
    have hp : l.1 = m.1 := (hfparent m l.1).mp (heq ▸ hfadj l)
    obtain ⟨v, i⟩ := l
    obtain ⟨w, j⟩ := m
    dsimp at hp
    subst w
    have hij : i = j := (F v).injective (Subtype.ext heq)
    subst j
    rfl
  let E := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, rfl⟩)
  refine ⟨{ toEquiv := Equiv.sumCongr (Equiv.refl V) E, map_rel_iff' := ?_ }, fun _ => rfl⟩
  intro x y
  cases x with
  | inl v =>
    cases y with
    | inl w => rfl
    | inr l => exact hfparent l v
  | inr l =>
    cases y with
    | inl v =>
      change H.Adj (.inr (f l)) (.inl v) ↔ l.1 = v
      rw [H.adj_comm, hfparent, eq_comm]
    | inr m =>
      change H.Adj (.inr (f l)) (.inr (f m)) ↔ False
      refine ⟨fun h => ?_, False.elim⟩
      have hf := degree_one_neighbors_eq H (hleaf (f l).1 (f l).2) h (hfadj l).symm
      cases hf

/-- Transfer the literal WL local information to any finite graph vertex types. -/
theorem simple_equivalent_local {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    {k m : ℕ} (hk : 2 ≤ k) (h : Equivalent k (graphOfSimple G) (graphOfSimple H))
    (hm : m ≤ k) (hm0 : 0 < m) (v : Fin m → V) :
    ∃ w : Fin m → W,
      (∀ i j, v i = v j ↔ w i = w j) ∧
      (∀ i j, G.Adj (v i) (v j) ↔ H.Adj (w i) (w j)) ∧
      (∀ i, G.degree (v i) = H.degree (w i)) ∧
      (∀ i d, simpleDegreeNeighbors G (v i) d = simpleDegreeNeighbors H (w i) d) := by
  classical
  obtain ⟨wg, heq, hadj, hd, hn⟩ := equivalent_local_neighborhood_match hk h hm hm0
    (fun i => Fintype.equivFin V (v i))
  let w (i : Fin m) : W := (Fintype.equivFin W).symm (wg i)
  have hw (i : Fin m) : Fintype.equivFin W (w i) = wg i := Equiv.apply_symm_apply _ _
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact (Fintype.equivFin V).injective.eq_iff.symm.trans
      ((heq i j).trans (Fintype.equivFin W).symm.injective.eq_iff.symm)
  · intro i j
    have hh := hadj i j
    rw [← hw i, ← hw j] at hh
    have hv := graphOfSimple_edge G (v i) (v j)
    have hw' := graphOfSimple_edge H (w i) (w j)
    exact decide_eq_decide.mp (hv.symm.trans (hh.trans hw'))
  · intro i
    have hh := hd i
    rw [← hw i] at hh
    exact (graphOfSimple_degree G (v i)).symm.trans (hh.trans (graphOfSimple_degree H (w i)))
  · intro i d
    have hh := hn i d
    rw [← hw i] at hh
    exact (graphOfSimple_degreeNeighbors G (v i) d).symm.trans
      (hh.trans (graphOfSimple_degreeNeighbors H (w i) d))

theorem simple_equivalent_local_finite {A V W : Type}
    [Fintype A] [Nonempty A] [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    {k : ℕ} (hk : 2 ≤ k) (h : Equivalent k (graphOfSimple G) (graphOfSimple H))
    (hA : Fintype.card A ≤ k) (v : A → V) :
    ∃ w : A → W,
      (∀ i j, v i = v j ↔ w i = w j) ∧
      (∀ i j, G.Adj (v i) (v j) ↔ H.Adj (w i) (w j)) ∧
      (∀ i, G.degree (v i) = H.degree (w i)) ∧
      (∀ i d, simpleDegreeNeighbors G (v i) d = simpleDegreeNeighbors H (w i) d) := by
  obtain ⟨w, heq, hadj, hd, hn⟩ := simple_equivalent_local G H hk h hA
    Fintype.card_pos (fun i => v ((Fintype.equivFin A).symm i))
  refine ⟨w ∘ Fintype.equivFin A, ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using heq (Fintype.equivFin A i) (Fintype.equivFin A j)
  · intro i j
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hadj (Fintype.equivFin A i) (Fintype.equivFin A j)
  · intro i
    have hv := congrArg (fun a => G.degree (v a)) ((Fintype.equivFin A).symm_apply_apply i)
    exact hv.symm.trans (hd (Fintype.equivFin A i))
  · intro i d
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hn (Fintype.equivFin A i) d

/-- The diagonal-tuple degree bijection is independent of the chosen finite encoding. -/
theorem simple_equivalent_degreeBijection {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    {k : ℕ} (hk : 2 ≤ k) (h : Equivalent k (graphOfSimple G) (graphOfSimple H)) :
    ∃ e : V ≃ W, ∀ v, G.degree v = H.degree (e v) := by
  obtain ⟨e, he⟩ := equivalent_degreeBijection hk h
  let E := (Fintype.equivFin V).trans (e.trans (Fintype.equivFin W).symm)
  refine ⟨E, ?_⟩
  intro v
  have hh := he (Fintype.equivFin V v)
  exact (graphOfSimple_degree G v).symm.trans (hh.trans (graphOfSimple_degree_at H _))

theorem leaf_count_eq_degreeNeighbors {V : Type} [Fintype V] (ell : V → ℕ)
    (H : SimpleGraph (LeafVertex ell)) [DecidableRel H.Adj]
    (hleaf : ∀ (v : V) (j : Fin (ell v)), H.degree (.inr ⟨v, j⟩) = 1)
    (hbase : ∀ v, 1 < H.degree (.inl v)) (v : V) :
    Fintype.card {l : Σ v, Fin (ell v) // H.Adj (.inl v) (.inr l)} =
      simpleDegreeNeighbors H (.inl v) 1 := by
  classical
  let e : {l : Σ v, Fin (ell v) // H.Adj (.inl v) (.inr l)} ≃
      {x : LeafVertex ell // H.Adj (.inl v) x ∧ H.degree x = 1} := {
    toFun l := ⟨.inr l.val, l.property, hleaf l.val.1 l.val.2⟩
    invFun x := by
      rcases x with ⟨x, hx, hd⟩
      cases x with
      | inl w => exact False.elim (by have := hbase w; omega)
      | inr l => exact ⟨l, hx⟩
    left_inv _ := rfl
    right_inv x := by
      rcases x with ⟨x, hx, hd⟩
      cases x with
      | inl w => exact False.elim (by have := hbase w; omega)
      | inr l => rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  rfl

theorem tagged_degreeNeighbors_one {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (color : V → ℕ) (hc : ∀ v, 0 < color v) (v : V) :
    simpleDegreeNeighbors (withLeaves G (tagSize color)) (.inl v) 1 = tagSize color v := by
  classical
  rw [← leaf_count_eq_degreeNeighbors _ _ (withLeaves_leaf_degree G _) (tag_base_degree_gt_one G color hc)]
  let e : {l : Σ v, Fin (tagSize color v) // (withLeaves G (tagSize color)).Adj (.inl v) (.inr l)} ≃
      Fin (tagSize color v) := {
    toFun l := by
      have hl : v = l.val.1 := l.property
      exact hl.symm ▸ l.val.2
    invFun i := ⟨⟨v, i⟩, rfl⟩
    left_inv l := by
      rcases l with ⟨⟨w, i⟩, hw⟩
      change v = w at hw
      subst w
      rfl
    right_inv _ := rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

/-- An arbitrary WL mate of a leaf-coded graph has exactly the same leaf-coded
shape. This theorem quantifies over all finite mate graphs, with no gadget promise. -/
theorem tagged_arbitrary_mate {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (color : V → ℕ) (hc : ∀ v, 0 < color v) {k : ℕ} (hk : 2 ≤ k)
    (h : Equivalent k (taggedGraph G color) (graphOfSimple H)) :
    ∃ G' : SimpleGraph V, Nonempty (withLeaves G' (tagSize color) ≃g H) := by
  classical
  let T := withLeaves G (tagSize color)
  obtain ⟨e, he⟩ := simple_equivalent_degreeBijection T H hk h
  let H' := H.comap e
  let E : H' ≃g H := SimpleGraph.Iso.comap e H
  have hd (v : LeafVertex (tagSize color)) : H'.degree v = T.degree v :=
    (E.degree_eq v).symm.trans (he v).symm
  have hleaf (v : V) (i : Fin (tagSize color v)) : H'.degree (.inr ⟨v, i⟩) = 1 := by
    rw [hd, withLeaves_leaf_degree]
  have hbase (v : V) : 1 < H'.degree (.inl v) := by
    rw [hd]
    exact tag_base_degree_gt_one G color hc v
  have heq : Equivalent k (graphOfSimple H') (graphOfSimple T) :=
    equivalent_trans (isomorphic_equivalent ((isomorphic_graphOfSimple_iff H' H).mpr ⟨E⟩) k)
      (equivalent_symm h)
  have hn (v : V) : simpleDegreeNeighbors H' (.inl v) 1 = tagSize color v := by
    obtain ⟨w, _, _, hw, hneigh⟩ := simple_equivalent_local H' T hk heq
      (m := 1) (by omega) (by omega) (fun _ => .inl v)
    have hdeg := hw 0
    have hh := hneigh 0 1
    cases hval : w 0 with
    | inr l =>
      rw [hval, withLeaves_leaf_degree] at hdeg
      have := hbase v
      omega
    | inl u =>
      rw [hval] at hdeg hh
      have hcu : color v = color u := by
        rw [hd] at hdeg
        have hdiv := congrArg (fun n => n / (Fintype.card V + 1)) hdeg
        simpa only [T, tag_degree_color] using hdiv
      rw [tagged_degreeNeighbors_one G color hc] at hh
      exact hh.trans (by simp only [tagSize, hcu])
  have hn' (v : V) : Fintype.card {l : Σ v, Fin (tagSize color v) // H'.Adj (.inl v) (.inr l)} =
      tagSize color v := (leaf_count_eq_degreeNeighbors _ H' hleaf hbase v).trans (hn v)
  obtain ⟨F, _⟩ := private_leaf_reconstruction (tagSize color) H' hleaf hn'
  exact ⟨H'.comap Sum.inl, ⟨F.trans E⟩⟩

/-- A bounded set of base vertices of equivalent tagged graphs has a simultaneous
color-preserving induced-graph match. Degree coding recovers the original colors. -/
theorem tagged_equivalent_local {A V W : Type} [Fintype A] [Nonempty A]
    [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (color : V → ℕ) (color' : W → ℕ)
    (hc : ∀ v, 0 < color v)
    (hN : Fintype.card V = Fintype.card W) {k : ℕ} (hk : 2 ≤ k)
    (h : Equivalent k (taggedGraph G color) (taggedGraph H color'))
    (hA : Fintype.card A ≤ k) (v : A → V) :
    ∃ w : A → W, (∀ i j, v i = v j ↔ w i = w j) ∧
      (∀ i j, G.Adj (v i) (v j) ↔ H.Adj (w i) (w j)) ∧
      (∀ i, color (v i) = color' (w i)) := by
  classical
  obtain ⟨w, he, ha, hd, _⟩ := simple_equivalent_local_finite
    (withLeaves G (tagSize color)) (withLeaves H (tagSize color')) hk h hA (fun i => .inl (v i))
  have hw (i : A) : ∃ u, w i = .inl u := by
    cases hh : w i with
    | inl u => exact ⟨u, rfl⟩
    | inr l =>
      have hd' := hd i
      rw [hh, withLeaves_leaf_degree] at hd'
      have := tag_base_degree_gt_one G color hc (v i)
      omega
  choose w' hw' using hw
  refine ⟨w', ?_, ?_, ?_⟩
  · intro i j
    simpa only [hw', Sum.inl.injEq] using he i j
  · intro i j
    simpa only [hw', withLeaves] using ha i j
  · intro i
    have hh := hd i
    rw [hw'] at hh
    have hdiv := congrArg (fun n => n / (Fintype.card V + 1)) hh
    rw [tag_degree_color, hN, tag_degree_color] at hdiv
    exact hdiv

namespace AffineBlocks

variable {C B : Type} [Fintype C] [DecidableEq C]

theorem allowed_name (D : AffineBlocks C B) {beta : B → Bit} (x y : D.Vertex beta) :
    D.Allowed x y ↔ D.AllowedName (D.colorName x) (D.colorName y) := by
  cases x <;> cases y <;> rfl

theorem piece_contains_color (D : AffineBlocks C B) {beta : B → Bit} (b : B)
    (x : D.Piece beta b) (y : D.Vertex beta)
    (h : D.colorName y = D.colorName (D.pieceEmbed b x)) :
    ∃ y' : D.Piece beta b, D.pieceEmbed b y' = y := by
  cases x with
  | inl p =>
    obtain ⟨a, ha⟩ := D.exists_bit_of_color y p.1.val h
    exact ⟨.inl (p.1, a), ha.symm⟩
  | inr v =>
    obtain ⟨u, hu⟩ := D.exists_valuation_of_color y b h
    exact ⟨.inr u, hu.symm⟩

variable [Fintype B]

/-- Bounded local WL information excludes every edge between forbidden colors. -/
theorem tagged_equivalent_allowed (D : AffineBlocks C B) (H : SimpleGraph (D.Vertex 0))
    [DecidableRel H.Adj] {k : ℕ} (hk : 2 ≤ k)
    (h : Equivalent k (D.graph 0) (taggedGraph H D.colorNat)) :
    ∀ x y, H.Adj x y → D.Allowed x y := by
  classical
  intro x y hxy
  obtain ⟨w, _, ha, hc⟩ := tagged_equivalent_local (A := Fin 2) H (D.baseGraph 0)
    D.colorNat D.colorNat D.colorNat_pos rfl hk (equivalent_symm h)
    (by simpa using hk) ![x, y]
  have he : (D.baseGraph 0).Adj (w 0) (w 1) := (ha 0 1).mp hxy
  have hcx := (D.colorNat_eq_iff _ _).mp (hc 0)
  have hcy := (D.colorNat_eq_iff _ _).mp (hc 1)
  change D.colorName x = D.colorName (w 0) at hcx
  change D.colorName y = D.colorName (w 1) at hcy
  have hallow := D.base_adj_allowed he
  rw [D.allowed_name] at hallow ⊢
  rw [hcx, hcy]
  exact hallow

/-- Match a complete incidence piece at once. Finite cardinality upgrades the
injective local match into an isomorphism of the entire piece. -/
theorem tagged_equivalent_piece (D : AffineBlocks C B) (H : SimpleGraph (D.Vertex 0))
    [DecidableRel H.Adj] {k : ℕ} (hk : 2 ≤ k)
    (h : Equivalent k (D.graph 0) (taggedGraph H D.colorNat)) (b : B)
    (hb : Fintype.card (D.Piece 0 b) ≤ k) :
    ∃ e : D.pieceGraph 0 b ≃g H.comap (D.pieceEmbed b),
      ∀ v, D.colorName (D.pieceEmbed b (e v)) = D.colorName (D.pieceEmbed b v) := by
  classical
  let : Nonempty (D.Piece 0 b) := ⟨.inr ⟨0, D.legal_zero b⟩⟩
  obtain ⟨w, he, ha, hc⟩ := tagged_equivalent_local (A := D.Piece 0 b) (D.baseGraph 0) H
    D.colorNat D.colorNat D.colorNat_pos rfl hk h hb (D.pieceEmbed b)
  have hw (x : D.Piece 0 b) : ∃ y : D.Piece 0 b, D.pieceEmbed b y = w x :=
    D.piece_contains_color b x (w x) ((D.colorNat_eq_iff _ _).mp (hc x)).symm
  choose f hf using hw
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply (D.pieceEmbed b).injective
    apply (he x y).mpr
    rw [← hf x, ← hf y, hxy]
  let E := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, rfl⟩)
  refine ⟨{ toEquiv := E, map_rel_iff' := ?_ }, ?_⟩
  · intro x y
    change H.Adj (D.pieceEmbed b (f x)) (D.pieceEmbed b (f y)) ↔
      (D.baseGraph 0).Adj (D.pieceEmbed b x) (D.pieceEmbed b y)
    rw [hf, hf]
    exact (ha x y).symm
  · intro x
    change D.colorName (D.pieceEmbed b (f x)) = _
    rw [hf]
    exact ((D.colorNat_eq_iff _ _).mp (hc x)).symm

/-- Full arbitrary-mate reconstruction, not pair-equivalence hardness: every
finite uncolored WL mate is isomorphic to some affine shift of the same system. -/
theorem graph_arbitrary_mate (D : AffineBlocks C B) {k : ℕ} (hk : 2 ≤ k)
    (hbound : ∀ b, Fintype.card (D.Piece 0 b) ≤ k) (H : Graph)
    (h : Equivalent k (D.graph 0) H) :
    ∃ beta : B → Bit, Isomorphic H (D.graph beta) := by
  classical
  have hS : Equivalent k (D.graph 0) (graphOfSimple (simpleOfGraph H)) :=
    equivalent_trans h (isomorphic_equivalent (graph_simple_isomorphic H) k)
  obtain ⟨H0, ⟨E⟩⟩ := tagged_arbitrary_mate (D.baseGraph 0) (simpleOfGraph H)
    D.colorNat D.colorNat_pos hk hS
  have hE := (isomorphic_graphOfSimple_iff _ _).mpr ⟨E⟩
  have h0 : Equivalent k (D.graph 0) (taggedGraph H0 D.colorNat) :=
    equivalent_trans hS (isomorphic_equivalent (isomorphic_symm hE) k)
  obtain ⟨beta, F, hF⟩ := D.base_reconstruction H0
    (D.tagged_equivalent_allowed H0 hk h0)
    (fun b => D.tagged_equivalent_piece H0 hk h0 b (hbound b))
  have hsize (v : D.Vertex beta) : tagSize D.colorNat v = tagSize D.colorNat (F v) := by
    dsimp only [tagSize]
    rw [D.vertex_card beta 0]
    exact congrArg (fun n => n * (Fintype.card (D.Vertex 0) + 1))
      ((D.colorNat_eq_iff _ _).mpr (hF v).symm)
  let T := withLeavesIso F (tagSize D.colorNat) (tagSize D.colorNat) hsize
  have hT : Isomorphic (D.graph beta) (taggedGraph H0 D.colorNat) :=
    (isomorphic_graphOfSimple_iff _ _).mpr ⟨T⟩
  refine ⟨beta, isomorphic_symm ?_⟩
  exact isomorphic_trans hT (isomorphic_trans hE (isomorphic_symm (graph_simple_isomorphic H)))

end AffineBlocks

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.CycleSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace CycleRows

open scoped BigOperators

/-- The rectangular difference of a vanishing cycle sum isolates one edge.
No finiteness or cardinality assumption on the coordinate alphabets is needed. -/
theorem rectangle {I : Type} [Fintype I] [DecidableEq I]
    (s : Equiv.Perm I) (hs : ∀ i, s i ≠ i) (hs2 : ∀ i, s (s i) ≠ i)
    (A : I → Type) (g : (i : I) → A i → A (s i) → Bit)
    (hzero : ∀ a : (i : I) → A i, ∑ i, g i (a i) (a (s i)) = 0)
    (b : (i : I) → A i) (i : I) (u : A i) (v : A (s i)) :
    g i u v + g i u (b (s i)) + g i (b i) v + g i (b i) (b (s i)) = 0 := by
  let bu := Function.update b i u
  let bv := Function.update b (s i) v
  let buv := Function.update bu (s i) v
  let d (j : I) := g j (buv j) (buv (s j)) + g j (bu j) (bu (s j)) +
    g j (bv j) (bv (s j)) + g j (b j) (b (s j))
  have hd (j : I) (hj : j ≠ i) : d j = 0 := by
    by_cases hj' : j = s i
    · subst j
      have hnext : s (s i) ≠ s i := s.injective.ne (hs i)
      dsimp only [d, buv, bu, bv]
      simp only [Function.update_self, Function.update_of_ne (hs i),
        Function.update_of_ne (hs2 i), Function.update_of_ne hnext]
      rw [add_assoc, CharTwo.add_self_eq_zero]
    · have hnext : s j ≠ s i := s.injective.ne hj
      dsimp only [d, buv, bv]
      simp only [Function.update_of_ne hj', Function.update_of_ne hnext]
      rw [CharTwo.add_self_eq_zero, zero_add, CharTwo.add_self_eq_zero]
  have hsum : ∑ j, d j = 0 := by
    simp only [d, Finset.sum_add_distrib, hzero, add_zero]
  have hdi : d i = 0 := by
    rw [Finset.sum_eq_single i (fun j _ hj => hd j hj) (fun h => (h (Finset.mem_univ i)).elim)] at hsum
    exact hsum
  have hi : i ≠ s i := (hs i).symm
  simpa only [d, buv, bu, bv, Function.update_self, Function.update_of_ne hi,
    Function.update_of_ne (hs i)] using hdi

/-- Varying a single coordinate equates the two adjacent one-coordinate deviations. -/
theorem adjacent_deviation {I : Type} [Fintype I] [DecidableEq I]
    (s : Equiv.Perm I) (hs : ∀ i, s i ≠ i)
    (A : I → Type) (g : (i : I) → A i → A (s i) → Bit)
    (hzero : ∀ a : (i : I) → A i, ∑ i, g i (a i) (a (s i)) = 0)
    (b : (i : I) → A i) (i : I) (v : A (s i)) :
    g i (b i) v + g i (b i) (b (s i)) =
      g (s i) v (b (s (s i))) + g (s i) (b (s i)) (b (s (s i))) := by
  let bv := Function.update b (s i) v
  let d (j : I) := g j (bv j) (bv (s j)) + g j (b j) (b (s j))
  have hd (j : I) (hj : j ≠ i) (hj' : j ≠ s i) : d j = 0 := by
    dsimp only [d, bv]
    simp only [Function.update_of_ne hj', Function.update_of_ne (s.injective.ne hj),
      CharTwo.add_self_eq_zero]
  have hsum : ∑ j, d j = 0 := by
    simp only [d, Finset.sum_add_distrib, hzero, zero_add]
  have hp : ∑ j ∈ {i, s i}, d j = ∑ j, d j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    exact hd j hj.1 hj.2
  rw [Finset.sum_pair (hs i).symm, hsum] at hp
  have hi : i ≠ s i := (hs i).symm
  have hnext : s (s i) ≠ s i := s.injective.ne (hs i)
  simpa only [d, bv, Function.update_self, Function.update_of_ne hi,
    Function.update_of_ne hnext] using CharTwo.add_eq_zero.mp hp

/-- Integrating constants around a finite cycle needs exactly the zero-sum condition. -/
theorem integrate_constants {n : ℕ} (c : Fin n → Bit) (hc : ∑ i, c i = 0) :
    ∃ C : Fin n → Bit, ∀ i, C i + C (finRotate n i) = c i := by
  let f (j : ℕ) : Bit := if h : j < n then c ⟨j, h⟩ else 0
  let C (i : Fin n) : Bit := ∑ j ∈ Finset.range i.val, f j
  have hf (i : Fin n) : f i.val = c i := by simp [f, i.isLt]
  have htotal : ∑ j ∈ Finset.range n, f j = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simpa only [hf] using hc
  refine ⟨C, ?_⟩
  intro i
  have hn := i.isLt
  have hi := rotate_val i
  by_cases hlt : i.val + 1 < n
  · rw [ite_eq_left hlt] at hi
    change C i + (∑ j ∈ Finset.range (finRotate n i).val, f j) = c i
    rw [hi, Finset.sum_range_succ, hf]
    change C i + (C i + c i) = c i
    exact CharTwo.add_cancel_left _ _
  · rw [ite_eq_right hlt] at hi
    have hn' : n = i.val + 1 := by omega
    rw [hn', Finset.sum_range_succ, hf] at htotal
    have hci : C i = c i := CharTwo.add_eq_zero.mp htotal
    change C i + (∑ j ∈ Finset.range (finRotate n i).val, f j) = c i
    rw [hi, Finset.range_zero, Finset.sum_empty, add_zero, hci]

theorem cycle_lifting {r : ℕ} (hr : 3 ≤ r) (A : Fin r → Type)
    (g : (i : Fin r) → A i → A (finRotate r i) → Bit)
    (b : (i : Fin r) → A i)
    (hzero : ∀ a : (i : Fin r) → A i, ∑ i, g i (a i) (a (finRotate r i)) = 0) :
    ∃ Y : (i : Fin r) → A i → Bit,
      ∀ i u v, g i u v = Y i u + Y (finRotate r i) v := by
  let s := finRotate r
  let c (i : Fin r) : Bit := g i (b i) (b (s i))
  let alpha (i : Fin r) (u : A i) : Bit := g i u (b (s i)) + c i
  obtain ⟨C, hC⟩ := integrate_constants c (hzero b)
  refine ⟨fun i u => alpha i u + C i, ?_⟩
  intro i u v
  have hs := fun j => rotate_ne_self (by omega : 2 ≤ r) j
  have hrect := rectangle s hs (rotate_twice_ne_self hr) A g hzero b i u v
  have hdev := adjacent_deviation s hs A g hzero b i v
  have hsep : g i u v = g i u (b (s i)) + g i (b i) v + c i := by
    apply CharTwo.add_eq_zero.mp
    simpa only [c, add_assoc] using hrect
  have hdev' : alpha (s i) v = g i (b i) v + c i := hdev.symm
  have hcc : C i + C (s i) = c i := hC i
  apply Eq.symm
  calc
    (alpha i u + C i) + (alpha (s i) v + C (s i)) =
        (g i u (b (s i)) + g i (b i) v) + (c i + c i) + (C i + C (s i)) := by
      rw [hdev']
      dsimp only [alpha]
      abel
    _ = g i u (b (s i)) + g i (b i) v + c i := by
      rw [CharTwo.add_self_eq_zero, add_zero, hcc]
    _ = g i u v := hsep.symm

end CycleRows

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.BijectionGames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace BijectionSystem

/-- Deleting a slot after an extension simultaneously preserves every possible
replacement, as required by the joint (not independent-marginal) WL update. -/
theorem replace {G H : Graph} {K m : ℕ} (S : BijectionSystem G H K)
    {v : Fin m → Fin G.order} {w : Fin m → Fin H.order}
    {z : Fin G.order} {z' : Fin H.order}
    (h : S.relates (m + 1) (Fin.snoc v z) (Fin.snoc w z')) (i : Fin m) :
    S.relates m (Function.update v i z) (Function.update w i z') := by
  let f (j : Fin m) : Fin (m + 1) := if j = i then Fin.last m else j.castSucc
  have hv : Fin.snoc v z ∘ f = Function.update v i z := by
    funext j
    by_cases hj : j = i
    · subst j; simp [f]
    · simp [f, hj]
  have hw : Fin.snoc w z' ∘ f = Function.update w i z' := by
    funext j
    by_cases hj : j = i
    · subst j; simp [f]
    · simp [f, hj]
  simpa only [hv, hw] using S.restrict h f

/-- Every maintained tuple has equal colors at every actual finite joint round. -/
theorem tupleColor_eq {G H : Graph} {K k : ℕ} (S : BijectionSystem G H K)
    (hk : k < K) {v : Fin k → Fin G.order} {w : Fin k → Fin H.order}
    (h : S.relates k v w) (round : ℕ) : tupleColor G k round v = tupleColor H k round w := by
  induction round generalizing v w with
  | zero =>
    apply Prod.ext
    · funext i j
      exact decide_eq_decide.mpr ((S.atomic h).1 i j)
    · funext i j
      exact (S.atomic h).2 i j
  | succ r ih =>
    obtain ⟨e, he⟩ := S.extend hk h
    apply Prod.ext
    · exact ih h
    · apply histogram_eq_of_equiv e
      intro z
      funext i
      exact ih (S.replace (he z) i)

/-- Sequentially chosen vertex bijections give a bijection of all ordered tuples;
there is no unsupported inference from mere existence of a mate for each tuple. -/
theorem tupleBijection {G H : Graph} {K : ℕ} (S : BijectionSystem G H K)
    (m : ℕ) (hm : m ≤ K) :
    ∃ E : (Fin m → Fin G.order) ≃ (Fin m → Fin H.order), ∀ v, S.relates m v (E v) := by
  induction m with
  | zero => exact ⟨Equiv.ofUnique _ _, fun v => S.empty v _⟩
  | succ m ih =>
    obtain ⟨E, hE⟩ := ih (by omega)
    have hext (v : Fin m → Fin G.order) :
        ∃ e : Fin G.order ≃ Fin H.order, ∀ z,
          S.relates (m + 1) (Fin.snoc v z) (Fin.snoc (E v) (e z)) :=
      S.extend (by omega) (hE v)
    choose e he using hext
    let P := (Equiv.prodCongrRight e).trans (Equiv.prodCongr E (Equiv.refl _))
    let E' := (tupleSnocEquiv (Fin G.order) m).symm.trans
      (P.trans (tupleSnocEquiv (Fin H.order) m))
    refine ⟨E', ?_⟩
    intro v
    change S.relates (m + 1) v (Fin.snoc (E (Fin.init v)) (e (Fin.init v) (v (Fin.last m))))
    simpa only [Fin.snoc_init_self] using he (Fin.init v) (v (Fin.last m))

/-- A genuine k+1-slot system proves equivalence for the literal joint k-WL colors. -/
theorem equivalent {G H : Graph} {K k : ℕ} (S : BijectionSystem G H K)
    (hk : 2 ≤ k) (hkK : k < K) : Equivalent k G H := by
  rw [Equivalent, ite_eq_right (by omega : k ≠ 1)]
  intro round
  obtain ⟨E, hE⟩ := S.tupleBijection k (by omega)
  exact histogram_eq_of_equiv E _ _ (fun v => S.tupleColor_eq hkK (hE v) round)

end BijectionSystem

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.AffineTranslations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace AffineBlocks

variable {C B : Type} [Fintype C] [DecidableEq C] [DecidableEq B]

namespace OwnedTranslations

variable {D : AffineBlocks C B} {beta : B → Bit}
    {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

/-- Exact projection implies the literal joint-WL equivalence. -/
theorem equivalent (T : OwnedTranslations D beta G H) {K k : ℕ}
    (F : OffsetFamily D beta K) (hk : 2 ≤ k) (hkK : k < K) :
    Equivalent k (graphOfSimple G) (graphOfSimple H) :=
  (T.bijectionSystem F).equivalent hk hkK

end OwnedTranslations
end AffineBlocks

namespace AffineBlocks
variable {C B : Type} [Fintype C] [DecidableEq C] [Fintype B] [DecidableEq B]

theorem graph_equivalent_of_offsetFamily (D : AffineBlocks C B) (owner : C → B)
    (ho : ∀ c, c ∈ D.coordinates (owner c)) (beta : B → Bit) {K k : ℕ}
    (F : D.OffsetFamily beta K) (hk : 2 ≤ k) (hkK : k < K) :
    Equivalent k (D.graph 0) (D.graph beta) :=
  (D.taggedTranslations owner ho beta).equivalent F hk hkK

end AffineBlocks

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.RowOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace CycleRows

namespace RowSum
variable {r : ℕ} {A : Fin r → Type} {V W : Type} [AddCommMonoid V] [AddCommMonoid W]

protected theorem zero : RowSum A V (fun _ => 0) := ⟨fun _ _ _ => 0, by simp⟩

protected theorem add {h g : ((i : Fin r) → A i) → V}
    (hh : RowSum A V h) (hg : RowSum A V g) : RowSum A V (fun a => h a + g a) := by
  obtain ⟨f, hf⟩ := hh
  obtain ⟨g, hg⟩ := hg
  exact ⟨fun i u v => f i u v + g i u v, fun a => by
    dsimp only
    rw [Finset.sum_add_distrib, hf, hg]⟩

protected theorem map {h : ((i : Fin r) → A i) → V}
    (hh : RowSum A V h) (L : V →+ W) : RowSum A W (fun a => L (h a)) := by
  obtain ⟨f, hf⟩ := hh
  exact ⟨fun i u v => L (f i u v), fun a => by dsimp only; rw [hf, map_sum]⟩

protected theorem pullback {A' : Fin r → Type} {h : ((i : Fin r) → A i) → V}
    (hh : RowSum A V h) (f : (i : Fin r) → A' i → A i) :
    RowSum A' V (fun a => h (fun i => f i (a i))) := by
  obtain ⟨g, hg⟩ := hh
  exact ⟨fun i u v => g i (f i u) (f (finRotate r i) v), fun a => hg _⟩

/-- Extending the adjacent-coordinate terms, not an arbitrary full-address
function, gives the extension on a product subdomain used by private buffers. -/
theorem extend {A' : Fin r → Type} {h : ((i : Fin r) → A i) → V}
    (hh : RowSum A V h) (f : (i : Fin r) → A i → A' i)
    (hf : ∀ i, Function.Injective (f i)) :
    ∃ h', RowSum A' V h' ∧ ∀ a, h' (fun i => f i (a i)) = h a := by
  classical
  obtain ⟨g, hg⟩ := hh
  let F (i : Fin r) : (A i × A (finRotate r i)) → (A' i × A' (finRotate r i)) :=
    Prod.map (f i) (f (finRotate r i))
  have hF (i : Fin r) : Function.Injective (F i) := by
    intro p q hp
    exact Prod.ext (hf i (congrArg Prod.fst hp))
      (hf (finRotate r i) (congrArg Prod.snd hp))
  let g' (i : Fin r) := Function.extend (F i) (fun p => g i p.1 p.2) (fun _ => (0 : V))
  refine ⟨fun a => ∑ i, g' i (a i, a (finRotate r i)),
    ⟨fun i u v => g' i (u, v), fun _ => rfl⟩, ?_⟩
  intro a
  rw [hg]
  apply Finset.sum_congr rfl
  intro i _
  exact (hF i).extend_apply _ _ (a i, a (finRotate r i))

end RowSum

/-- One link, with arbitrary nonempty coordinate match domains, has legal
vertical offsets exactly when the horizontal ring sums have the required shift.
This is the local-to-global step used independently on every private wire link. -/
theorem square_lifting {r : ℕ} (hr : 3 ≤ r) (A : Fin r → Type)
    (base : (i : Fin r) → A i)
    (left right beta : (i : Fin r) → A i → A (finRotate r i) → Bit) :
    (∃ y : (i : Fin r) → A i → Bit, ∀ i u v,
      left i u v + right i u v + y i u + y (finRotate r i) v = beta i u v) ↔
    ∀ a : (i : Fin r) → A i,
      (∑ i, left i (a i) (a (finRotate r i))) +
        (∑ i, right i (a i) (a (finRotate r i))) =
      ∑ i, beta i (a i) (a (finRotate r i)) := by
  constructor
  · rintro ⟨y, hy⟩ a
    have hh := congrArg (fun f : Fin r → Bit => ∑ i, f i)
      (funext (fun i => hy i (a i) (a (finRotate r i))))
    simp only [Finset.sum_add_distrib] at hh
    rw [Equiv.sum_comp (finRotate r) (fun i => y i (a i))] at hh
    simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero] using hh
  · intro h
    let g (i : Fin r) (u : A i) (v : A (finRotate r i)) :=
      left i u v + right i u v + beta i u v
    have hg (a : (i : Fin r) → A i) : ∑ i, g i (a i) (a (finRotate r i)) = 0 := by
      dsimp only [g]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h a, CharTwo.add_self_eq_zero]
    obtain ⟨y, hy⟩ := cycle_lifting hr A g base hg
    refine ⟨y, ?_⟩
    intro i u v
    have he := hy i u v
    dsimp only [g] at he
    calc
      left i u v + right i u v + y i u + y (finRotate r i) v =
          (left i u v + right i u v) + (y i u + y (finRotate r i) v) := by abel
      _ = beta i u v := by
        rw [← he]
        calc
          _ = ((left i u v + right i u v) + (left i u v + right i u v)) + beta i u v := by abel
          _ = beta i u v := by rw [CharTwo.add_self_eq_zero, zero_add]

end CycleRows

namespace RingLayout
variable {r : ℕ} {T L : Type} [Fintype T] [Fintype L] (R : RingLayout r T L)

theorem solves_iff (hr : 2 ≤ r) (beta : R.Block → Bit) (z : R.Coordinate → Bit) :
    (R.affine hr).Solves beta z ↔ ∀ b : R.Square,
      R.firstForm b.1 (R.horizontal z (R.leftH b)) +
      R.secondForm b.1 (R.horizontal z (R.rightH b)) +
      R.vertical z (R.topV b) + R.vertical z (R.bottomV b) = beta (.inr b) := by
  constructor
  · intro h b
    exact h (.inr b) rfl
  · intro h b
    cases b with
    | inl h => intro hf; cases hf
    | inr b => exact fun _ => h b

omit [Fintype T] [Fintype L] in
theorem ringValue_rowSum (x : R.Horizontal) (t : T) :
    CycleRows.RowSum (R.Label t) (Fin (R.dimension t) → Bit) (R.ringValue x t) :=
  ⟨fun i u v => x ⟨t, i, u, v⟩, fun _ => rfl⟩

omit [Fintype T] [Fintype L] in
theorem linkShift_rowSum (beta : R.Block → Bit) (e : L) :
    CycleRows.RowSum (R.Match e) Bit (R.linkShift beta e) :=
  ⟨fun i u v => beta (.inr ⟨e, i, u, v⟩), fun _ => rfl⟩

/-- All link square equations are lifted simultaneously. No arbitrary-address
assignment substitutes for readouts shared by adjacent-coordinate pairs. -/
theorem offsets_iff_horizontal (hr : 3 ≤ r) (beta : R.Block → Bit) :
    (∃ z, (R.affine (by omega)).Solves beta z) ↔
    ∃ x : R.Horizontal, ∀ e (a : R.MatchAddress e),
      R.firstForm e (R.ringValue x (R.first e) (R.leftAddress e a)) +
      R.secondForm e (R.ringValue x (R.second e) (R.rightAddress e a)) = R.linkShift beta e a := by
  classical
  have hb (e : L) (i : Fin r) : Nonempty (R.Match e i) :=
    ⟨⟨(R.matchLabels_nonempty e i).choose, (R.matchLabels_nonempty e i).choose_spec⟩⟩
  let base (e : L) (i : Fin r) : R.Match e i := Classical.choice (hb e i)
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨R.horizontal z, ?_⟩
    intro e a
    have hsq := (R.solves_iff (by omega) beta z).mp hz
    have hh := (CycleRows.square_lifting hr (R.Match e) (base e)
      (fun i u v => R.firstForm e (R.horizontal z (R.leftH ⟨e, i, u, v⟩)))
      (fun i u v => R.secondForm e (R.horizontal z (R.rightH ⟨e, i, u, v⟩)))
      (fun i u v => beta (.inr ⟨e, i, u, v⟩))).mp
        ⟨fun i u => R.vertical z ⟨e, i, u⟩, fun i u v => hsq ⟨e, i, u, v⟩⟩ a
    simpa only [ringValue, map_sum, linkShift, leftAddress, rightAddress, leftH, rightH] using hh
  · rintro ⟨x, hx⟩
    have he (e : L) : ∃ y : (i : Fin r) → R.Match e i → Bit, ∀ i u v,
        R.firstForm e (x (R.leftH ⟨e, i, u, v⟩)) +
        R.secondForm e (x (R.rightH ⟨e, i, u, v⟩)) +
        y i u + y (finRotate r i) v = beta (.inr ⟨e, i, u, v⟩) := by
      apply (CycleRows.square_lifting hr (R.Match e) (base e) _ _ _).mpr
      intro a
      simpa only [ringValue, map_sum, linkShift, leftAddress, rightAddress, leftH, rightH] using hx e a
    choose y hy using he
    refine ⟨R.pack x (fun v => y v.1 v.2.1 v.2.2), (R.solves_iff (by omega) beta _).mpr ?_⟩
    intro b
    exact hy b.1 b.2.1 b.2.2.1 b.2.2.2

theorem offsets_iff_rowSums (hr : 3 ≤ r) (beta : R.Block → Bit) :
    (∃ z, (R.affine (by omega)).Solves beta z) ↔
    ∃ h : (t : T) → R.Address t → Fin (R.dimension t) → Bit,
      (∀ t, CycleRows.RowSum (R.Label t) (Fin (R.dimension t) → Bit) (h t)) ∧
      ∀ e (a : R.MatchAddress e),
        R.firstForm e (h (R.first e) (R.leftAddress e a)) +
        R.secondForm e (h (R.second e) (R.rightAddress e a)) = R.linkShift beta e a := by
  rw [R.offsets_iff_horizontal hr beta]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨R.ringValue x, R.ringValue_rowSum x, hx⟩
  · rintro ⟨h, hs, he⟩
    choose f hf using hs
    let x : R.Horizontal := fun a => f a.1 a.2.1 a.2.2.1 a.2.2.2
    have hx (t : T) (a : R.Address t) : R.ringValue x t a = h t a := (hf t a).symm
    refine ⟨x, ?_⟩
    intro e a
    rw [hx, hx]
    exact he e a

end RingLayout

namespace AffineBlocks
variable {C B : Type} [Fintype C] [DecidableEq C]

/-- A nonzero scalar equation cuts a binary valuation class exactly in half. -/
theorem constrained_card (D : AffineBlocks C B) (beta : B → Bit) (b : B)
    (hc : D.constrained b = true) :
    2 * Fintype.card {v // D.Legal beta b v} = 2 ^ (D.coordinates b).card := by
  classical
  have hf (c : Bit) : Fintype.card {v : D.Local b // D.form b v = c} =
      Fintype.card {v // D.Legal beta b v} := by
    calc
      _ = Fintype.card {v // D.Legal (fun _ => c) b v} :=
        Fintype.card_congr (Equiv.subtypeEquivRight (fun v => by simp [Legal, hc]))
      _ = _ := D.legal_card _ _ b
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv (D.form b))
  simpa only [Fintype.card_sigma, hf, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Local, Fintype.card_fun, Fintype.card_coe, Bit, ZMod.card] using h

theorem local_card_le (D : AffineBlocks C B) (beta : B → Bit) (b : B) :
    Fintype.card {v // D.Legal beta b v} ≤ 2 ^ (D.coordinates b).card := by
  classical
  simpa only [Local, Fintype.card_fun, Fintype.card_coe, Bit, ZMod.card] using
    Fintype.card_subtype_le (D.Legal beta b)

theorem piece_card_bound (D : AffineBlocks C B) (beta : B → Bit) (b : B)
    (hs : (D.coordinates b).card ≤ 5)
    (hu : D.constrained b ≠ true → (D.coordinates b).card ≤ 2) :
    Fintype.card (D.Piece beta b) ≤ 26 := by
  classical
  have he : Fintype.card (D.Piece beta b) =
      2 * (D.coordinates b).card + Fintype.card {v // D.Legal beta b v} := by
    simp only [Piece, Fintype.card_sum, Fintype.card_prod, Fintype.card_coe, Bit, ZMod.card]
    omega
  rw [he]
  by_cases hc : D.constrained b = true
  · have h := D.constrained_card beta b hc
    have hp := Nat.pow_le_pow_right (by omega : 0 < 2) hs
    norm_num at hp
    omega
  · have h := D.local_card_le beta b
    have hd := hu hc
    have hp := Nat.pow_le_pow_right (by omega : 0 < 2) hd
    norm_num at hp
    omega

end AffineBlocks

namespace RingLayout
variable {r : ℕ} {T L : Type} [Fintype T] [Fintype L] (R : RingLayout r T L)

/-- The advertised 26-vertex bound, including both vertices of every readout bit. -/
theorem piece_card_le (hr : 2 ≤ r) (beta : R.Block → Bit) (b : R.Block) :
    Fintype.card ((R.affine hr).Piece beta b) ≤ 26 := by
  apply AffineBlocks.piece_card_bound
  · exact R.coordinates_card b
  · intro hc
    cases b with
    | inl h =>
      change (R.hCoords h).card ≤ 2
      rw [R.hCoords_card]
      rcases R.dimension_bound h.1 with h | h <;> omega
    | inr b => exact False.elim (hc rfl)

omit [Fintype T] [Fintype L] in
theorem owner_covers (c : R.Coordinate) : c ∈ R.coordinates (R.owner c) := by
  cases c with
  | inl h => exact R.hCoord_mem h.1 h.2
  | inr v => exact R.top_mem _

/-- All-mates reconstruction for the ring construction when r≥32. -/
theorem arbitrary_mate (hr : 32 ≤ r) (H : Graph)
    (h : Equivalent r ((R.affine (by omega)).graph 0) H) :
    ∃ beta, Isomorphic H ((R.affine (by omega)).graph beta) :=
  (R.affine (by omega)).graph_arbitrary_mate (by omega)
    (fun b => (R.piece_card_le (by omega) 0 b).trans (by omega)) H h

end RingLayout

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.ConstraintSchemas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace CycleRows.RowSum
variable {r : ℕ} {A : Fin r → Type} {V : Type} [AddCommMonoid V]

protected theorem sum {I : Type} (s : Finset I)
    (h : I → ((i : Fin r) → A i) → V) (hh : ∀ j ∈ s, RowSum A V (h j)) :
    RowSum A V (fun a => ∑ j ∈ s, h j a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (RowSum.zero (A := A) (V := V))
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj] using
      (hh j (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => hh i (Finset.mem_insert_of_mem hi)))

protected theorem pi {J : Type} {W : J → Type} [∀ j, AddCommMonoid (W j)]
    (h : ((i : Fin r) → A i) → (j : J) → W j)
    (hh : ∀ j, RowSum A (W j) (fun a => h a j)) : RowSum A ((j : J) → W j) h := by
  choose f hf using hh
  refine ⟨fun i u v j => f j i u v, ?_⟩
  intro a
  funext j
  simpa only [Finset.sum_apply] using hf j a

end CycleRows.RowSum

namespace WireAlgebra

theorem sum_adjacent {n : ℕ} (h : Fin (n + 1) → Bit) :
    ∑ i : Fin n, (h i.castSucc + h i.succ) = h 0 + h (Fin.last n) := by
  have ha := Fin.sum_univ_castSucc h
  have hb := Fin.sum_univ_succ h
  have hab : (∑ i : Fin n, h i.castSucc) + h (Fin.last n) =
      h 0 + ∑ i : Fin n, h i.succ := ha.symm.trans hb
  rw [Finset.sum_add_distrib]
  calc
    _ = ((∑ i : Fin n, h i.castSucc) + (∑ i : Fin n, h i.succ)) +
        (h (Fin.last n) + h (Fin.last n)) := by
      rw [CharTwo.add_self_eq_zero, add_zero]
    _ = ((∑ i : Fin n, h i.castSucc) + h (Fin.last n)) +
        (∑ i : Fin n, h i.succ) + h (Fin.last n) := by abel
    _ = _ := by
      rw [hab]
      simp only [add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- A wire's internal scalars cancel; the converse uses explicit prefixSum sums. -/
theorem chain_lifting {n : ℕ} (left right first last : Bit) (middle : Fin n → Bit) :
    (∃ h : Fin (n + 1) → Bit,
      left + h 0 = first ∧
      (∀ i, h i.castSucc + h i.succ = middle i) ∧
      h (Fin.last n) + right = last) ↔
    left + right = first + (∑ i, middle i) + last := by
  constructor
  · rintro ⟨h, hfirst, hmiddle, hlast⟩
    rw [← hfirst, ← hlast, ← funext hmiddle, sum_adjacent]
    symm
    calc
      _ = left + right + (h 0 + h 0) + (h (Fin.last n) + h (Fin.last n)) := by abel
      _ = _ := by simp only [CharTwo.add_self_eq_zero, add_zero]
  · intro he
    refine ⟨fun j => left + first + prefixSum middle j, ?_, ?_, ?_⟩
    · simp only [prefix_zero, add_zero]
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    · intro i
      dsimp only
      rw [prefix_succ]
      calc
        _ = ((left + first + prefixSum middle i.castSucc) +
          (left + first + prefixSum middle i.castSucc)) + middle i := by abel
        _ = middle i := by rw [CharTwo.add_self_eq_zero, zero_add]
    · dsimp only
      rw [prefix_last]
      calc
        _ = (left + right) + first + (∑ i, middle i) := by abel
        _ = last := by
          rw [he]
          calc
            _ = (first + first) + ((∑ i, middle i) + (∑ i, middle i)) + last := by abel
            _ = last := by simp only [CharTwo.add_self_eq_zero, zero_add]

end WireAlgebra

namespace WireAlgebra

theorem prefix_equations {n : ℕ} (left right first last : Bit) (middle : Fin n → Bit)
    (he : left + right = first + (∑ i, middle i) + last) :
    let h := fun j => left + first + prefixSum middle j
    (left + h 0 = first) ∧ (∀ i, h i.castSucc + h i.succ = middle i) ∧
      (h (Fin.last n) + right = last) := by
  dsimp only
  constructor
  · simp only [prefix_zero, add_zero]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  constructor
  · intro i
    rw [prefix_succ]
    calc
      _ = ((left + first + prefixSum middle i.castSucc) +
        (left + first + prefixSum middle i.castSucc)) + middle i := by abel
      _ = middle i := by rw [CharTwo.add_self_eq_zero, zero_add]
  · rw [prefix_last]
    calc
      _ = (left + right) + first + (∑ i, middle i) := by abel
      _ = last := by
        rw [he]
        calc
          _ = (first + first) + ((∑ i, middle i) + (∑ i, middle i)) + last := by abel
          _ = last := by simp only [CharTwo.add_self_eq_zero, zero_add]

end WireAlgebra

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

theorem wireShift_rowSum (n : ℕ) (beta : (S.layout n).Block → Bit) (e : E) :
    CycleRows.RowSum (fun i => {a // a ∈ S.domain e i}) Bit (S.wireShift n beta e) := by
  exact ((S.layout n).linkShift_rowSum beta (.inl e)).add
    (CycleRows.RowSum.sum Finset.univ (S.middleShift n beta e)
      (fun j _ => (S.layout n).linkShift_rowSum beta (.inr (.inl (e, j))))) |>.add
        ((S.layout n).linkShift_rowSum beta (.inr (.inr e)))

variable [Fintype P] [Fintype E]

theorem offsets_iff_real_rowSums (hr : 3 ≤ r) (n : ℕ)
    (beta : (S.layout n).Block → Bit) :
    (∃ z, ((S.layout n).affine (by omega)).Solves beta z) ↔
    ∃ h : (p : P) → S.Address → Fin (S.dimension p) → Bit,
      (∀ p, CycleRows.RowSum (fun _ : Fin r => {a : Bool // a ∈ (Finset.univ : Finset Bool)})
        (Fin (S.dimension p) → Bit) (h p)) ∧
      ∀ e (a : S.DomainAddress e),
        S.left e (h (S.source e) (S.sourceAddress e a)) +
        S.right e (h (S.target e) (S.targetAddress e a)) = S.wireShift n beta e a := by
  rw [(S.layout n).offsets_iff_rowSums hr beta]
  constructor
  · rintro ⟨h, hs, he⟩
    refine ⟨fun p => h (.inl p), fun p => hs (.inl p), ?_⟩
    intro e a
    apply (WireAlgebra.chain_lifting _ _ _ _ _).mp
    refine ⟨fun j => h (.inr (e, j)) a (0 : Fin 1), ?_, ?_, ?_⟩
    · exact he (.inl e) a
    · intro j
      exact he (.inr (.inl (e, j))) a
    · exact he (.inr (.inr e)) a
  · rintro ⟨h, hs, he⟩
    let g (e : E) (j : Fin (n + 1)) (a : S.DomainAddress e) : Bit :=
      S.left e (h (S.source e) (S.sourceAddress e a)) + S.firstShift n beta e a +
        WireAlgebra.prefixSum (fun i => S.middleShift n beta e i a) j
    let q : (t : S.InternalType n) → (S.layout n).Address t →
        Fin ((S.layout n).dimension t) → Bit := fun t => match t with
      | .inl p => h p
      | .inr (e, j) => fun a _ => g e j a
    have hg (e : E) (a : S.DomainAddress e) :
        (S.left e (h (S.source e) (S.sourceAddress e a)) + g e 0 a = S.firstShift n beta e a) ∧
        (∀ j, g e j.castSucc a + g e j.succ a = S.middleShift n beta e j a) ∧
        (g e (Fin.last n) a + S.right e (h (S.target e) (S.targetAddress e a)) = S.lastShift n beta e a) :=
      WireAlgebra.prefix_equations _ _ _ _ _ (he e a)
    refine ⟨q, ?_, ?_⟩
    · intro t
      cases t with
      | inl p => exact hs p
      | inr p =>
        apply CycleRows.RowSum.pi
        intro j
        have hf := ((hs (S.source p.1)).map (S.left p.1).toAddMonoidHom).pullback
          (fun i (a : {a // a ∈ S.domain p.1 i}) => (⟨a.val, Finset.mem_univ _⟩ : {b : Bool // b ∈ (Finset.univ : Finset Bool)}))
        have hb := (S.layout n).linkShift_rowSum beta (.inl p.1)
        have hc : CycleRows.RowSum (fun i => {a // a ∈ S.domain p.1 i}) Bit
            (fun a => WireAlgebra.prefixSum (fun i => S.middleShift n beta p.1 i a) p.2) := by
          apply CycleRows.RowSum.sum
          intro i _
          by_cases hi : i.val < p.2.val
          · simpa only [hi, ite_true, middleShift, RingLayout.Match, layout, wire] using
              (S.layout n).linkShift_rowSum beta (.inr (.inl (p.1, i)))
          · simpa only [hi, ite_false] using
              (CycleRows.RowSum.zero (A := fun i => {a // a ∈ S.domain p.1 i}) (V := Bit))
        exact (hf.add hb).add hc
    · intro l a
      cases l with
      | inl e => exact (hg e a).1
      | inr l => cases l with
        | inl p => exact (hg p.1 a).2.1 p.2
        | inr e => exact (hg e a).2.2

end ComparisonSchemas

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.RejectingMates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace ComparisonSchemas.SpecialImages
variable {r : ℕ} {P E : Type} {S : ComparisonSchemas r P E} {b : E → Bit}
    (I : S.SpecialImages b)

variable [Fintype P] [Fintype E]

include I in
/-- Equivalence of the special twist on the uncolored
leaf-coded graph; the private interior may be arbitrarily longer than K. -/
theorem equivalent_special {n : ℕ} (hr : 32 ≤ r) (hn : r + 1 < n) :
    Equivalent r (((S.layout n).affine (by omega)).graph 0)
      (((S.layout n).affine (by omega)).graph (S.specialTwist n b)) := by
  exact AffineBlocks.graph_equivalent_of_offsetFamily _ (S.layout n).owner
    (S.layout n).owner_covers (S.specialTwist n b) (offsetFamily I (by omega) hn)
    (by omega) (by omega)

end ComparisonSchemas.SpecialImages

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.BufferedCircuits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace BufferAlgebra

theorem determined_comp {V W : Type} {Q : Set V} {R : Set W} {f : V → Bit}
    {g : W → Bit} (d : Bit)
    (he : f '' Q = (fun w => d + g w) '' R) :
    Determined Q f ↔ Determined R g := by
  constructor
  · intro h v hv w hw
    obtain ⟨v', hv', ev⟩ := he.symm ▸ (show d + g v ∈ (fun w => d + g w) '' R from ⟨v, hv, rfl⟩)
    obtain ⟨w', hw', ew⟩ := he.symm ▸ (show d + g w ∈ (fun w => d + g w) '' R from ⟨w, hw, rfl⟩)
    exact add_left_cancel (ev.symm.trans ((h v' hv' w' hw').trans ew))
  · intro h v hv w hw
    obtain ⟨v', hv', ev⟩ := he ▸ (show f v ∈ f '' Q from ⟨v, hv, rfl⟩)
    obtain ⟨w', hw', ew⟩ := he ▸ (show f w ∈ f '' Q from ⟨w, hw, rfl⟩)
    exact ev.symm.trans ((congrArg (d + ·) (h v' hv' w' hw')).trans ew)

theorem determined_zero {V : Type} (Q : Set V) : Determined Q (fun _ => 0) :=
  fun _ _ _ _ => rfl

theorem determined_sum {J V : Type} [Fintype J] {Q : Set V} {f : J → V → Bit}
    (h : ∀ j, Determined Q (f j)) : Determined Q (fun v => ∑ j, f j v) := by
  intro v hv w hw
  exact Finset.sum_congr rfl (fun j _ => h j v hv w hw)

theorem subsingleton_of_coordinates {J : Type} {Q : Set (J → Bit)}
    (h : ∀ j, Determined Q (fun v => v j)) : Q.Subsingleton := by
  intro v hv w hw
  funext j
  exact h j v hv w hw

/-- Arbitrarily shifted private buffers propagate singletonness only forwards. -/
theorem forward {V W : Type} {Q : Set V} {R : Set W} {B : Set Vector}
    {f : V → Bit} {g : W → Bit} (d₁ d₂ d₃ : Bit)
    (h₁ : f '' Q = (fun v => d₁ + v 0) '' B)
    (h₂ : f '' Q = (fun v => d₂ + v 1) '' B)
    (h₃ : (fun v => v 0 + v 1) '' B = (fun w => d₃ + g w) '' R)
    (h : Determined Q f) : Determined R g := by
  apply (determined_comp d₃ h₃).mp
  have ha := (determined_comp d₁ h₁).mp h
  have hb := (determined_comp d₂ h₂).mp h
  intro v hv w hw
  exact congrArg₂ (· + ·) (ha v hv w hw) (hb v hv w hw)

/-- Two copies of one source value cancel, even for nonconstant wire shifts. -/
theorem self_value (x z₁ z₂ d₁ d₂ d₃ : Bit)
    (h₁ : x = d₁ + z₁) (h₂ : x = d₂ + z₂)
    (h₃ : z₁ + z₂ = d₃ + x) : x = d₁ + d₂ + d₃ := by
  linear_combination h₁ + h₂ + h₃

end BufferAlgebra

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} (C : ProductCircuit r P E Z T)

theorem accepted_reseed (zindex : Z ↪ ℕ) :
    ({C with seedIndex := zindex} : ProductCircuit r P E Z T).Accepted ↔ C.Accepted := by
  let D : ProductCircuit r P E Z T := {C with seedIndex := zindex}
  have hp (p : P) (a : Fin r → Bool) (j : Fin (C.dimension p)) :
      D.PortTrue p a j ↔ C.PortTrue p a j := by
    constructor
    · intro h
      induction h using @PortTrue.rec r P E Z T D with
      | seed z a j => exact PortTrue.seed (C := C) z a j
      | edge e a h ih => exact PortTrue.edge (C := C) e a ih
    · intro h
      induction h using @PortTrue.rec r P E Z T C with
      | seed z a j => exact PortTrue.seed (C := D) z a j
      | edge e a h ih => exact PortTrue.edge (C := D) e a ih
  constructor
  · rintro ⟨t,a,h⟩
    exact ⟨t,a,fun j => (hp _ _ j).mp (h j)⟩
  · rintro ⟨t,a,h⟩
    exact ⟨t,a,fun j => (hp _ _ j).mpr (h j)⟩

end ProductCircuit

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.AcceptingBroadcast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} (C : ProductCircuit r P E Z T)

namespace Images
variable {C} {delta : C.Shifts} (I : C.Images delta)
open BufferAlgebra

theorem first_equation (l : C.Connection) (a : (C.connectionMap l).Point) :
    C.sourceForm l '' I.values (.primary (C.connectionSource l)) ((C.connectionMap l).source a) =
      (fun v => delta (.first l) a + v (0 : Fin 2)) '' I.values (.buffer l) ((C.connectionMap l).source a) :=
  I.equation (.first l) a

theorem second_equation (l : C.Connection) (a : (C.connectionMap l).Point) :
    C.sourceForm l '' I.values (.primary (C.connectionSource l)) ((C.connectionMap l).source a) =
      (fun v => delta (.second l) a + v (1 : Fin 2)) '' I.values (.buffer l) ((C.connectionMap l).source a) :=
  I.equation (.second l) a

theorem third_equation (l : C.Connection) (a : (C.connectionMap l).Point) :
    (fun v => v (0 : Fin 2) + v (1 : Fin 2)) '' I.values (.buffer l) ((C.connectionMap l).source a) =
      (fun v => delta (.third l) a + C.targetForm l v) ''
        I.values (.primary (C.connectionTarget l)) ((C.connectionMap l).target a) :=
  I.equation (.third l) a

theorem forward (l : C.Connection) (a : (C.connectionMap l).Point)
    (h : Determined (I.values (.primary (C.connectionSource l)) ((C.connectionMap l).source a))
      (C.sourceForm l)) :
    Determined (I.values (.primary (C.connectionTarget l)) ((C.connectionMap l).target a))
      (C.targetForm l) :=
  BufferAlgebra.forward _ _ _ (I.first_equation l a) (I.second_equation l a) (I.third_equation l a) h

theorem coordinate_eq_sum_of_one {d : ℕ} (hd : d = 1) (v : Fin d → Bit) (j : Fin d) :
    v j = sumForm d v := by
  subst d
  fin_cases j
  simp [sumForm_apply]

theorem seed (z : Z) (a : (C.seedMap z).Point) (j : Fin (C.dimension (C.seedType z))) :
    Determined (I.values (.primary (some (C.seedType z))) ((C.seedMap z).source a))
      (fun v => v j) := by
  have h : Determined (I.values (.primary (some (C.seedType z))) ((C.seedMap z).source a))
      (sumForm (C.dimension (C.seedType z))) :=
    (determined_comp (delta (.seed z) a) (I.equation (.seed z) a)).mpr
      (determined_zero _)
  intro v hv w hw
  dsimp only
  rw [coordinate_eq_sum_of_one (C.seed_scalar z) v j,
    coordinate_eq_sum_of_one (C.seed_scalar z) w j]
  exact h v hv w hw

theorem true_port {p : P} {a : Fin r → Bool} {j : Fin (C.dimension p)}
    (h : C.PortTrue p a j) :
    Determined (I.values (.primary (some p)) a) (fun v => v j) := by
  induction h with
  | seed z a j => exact I.seed z a j
  | edge e a h ih =>
    apply I.forward (.original e) a
    simpa only [sourceForm, BufferAlgebra.Determined, sumForm_apply] using determined_sum ih

theorem true_output {p : P} {a : Fin r → Bool} (h : C.True p a) :
    Determined (I.values (.primary (some p)) a) (sumForm (C.dimension p)) := by
  simpa only [BufferAlgebra.Determined, sumForm_apply] using determined_sum (fun j => I.true_port (h j))

end Images

/-- Coordinate flips connect the entire Boolean address cube, not only the
addresses actually visited by the computation. -/
theorem cube_propagation (Q : (Fin r → Bool) → Prop)
    (hstep : ∀ a i, Q a → Q (fun j => if j = i then !(a j) else a j))
    {a₀ : Fin r → Bool} (h₀ : Q a₀) : ∀ a, Q a := by
  classical
  intro a
  have hp (s : Finset (Fin r)) : Q (fun i => if i ∈ s then a i else a₀ i) := by
    induction s using Finset.induction_on with
    | empty => simpa using h₀
    | @insert i s hi ih =>
      let b : Fin r → Bool := fun j => if j ∈ s then a j else a₀ j
      by_cases he : a i = b i
      · convert ih using 1
        funext j
        by_cases hj : j = i
        · subst j; simpa only [Finset.mem_insert_self, ite_true] using he
        · simp only [Finset.mem_insert, hj, false_or]
      · have hb : a i = !(b i) := by cases ha : a i <;> cases hh : b i <;> simp_all
        convert hstep b i ih using 1
        funext j
        by_cases hj : j = i
        · subst j
          simp only [Finset.mem_insert_self, ite_true]
          exact hb
        · simp only [Finset.mem_insert, hj, false_or, ite_false, b]
  simpa using hp Finset.univ

namespace Images
variable {C} {delta : C.Shifts} (I : C.Images delta)
open BufferAlgebra

include I in
theorem accepted_broadcast (h : C.Accepted) (a : Fin r → Bool) :
    Determined (I.values (.primary none) a) (fun v => v (0 : Fin 1)) := by
  obtain ⟨t, x, ht⟩ := h
  have h₀ : Determined (I.values (.primary none) ((C.testMap t).source x)) (fun v => v (0 : Fin 1)) :=
    I.forward (.test t) x (I.true_output ht)
  apply cube_propagation (fun a => Determined (I.values (.primary none) a) (fun v => v (0 : Fin 1))) _ h₀ a
  intro b i hb
  exact I.forward (.flip i) (ProductMap.ofAddress b) hb

theorem accepted_primary (h : C.Accepted) (p : C.Primary) (a : Fin r → Bool) :
    (I.values (.primary p) a).Subsingleton := by
  apply subsingleton_of_coordinates
  intro j
  cases p with
  | none =>
    have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    subst j
    exact I.accepted_broadcast h a
  | some p =>
    exact I.forward (.broadcast p j) (ProductMap.ofAddress a) (I.accepted_broadcast h a)

theorem primaryValue_mem (p : C.Primary) (a : Fin r → Bool) :
    I.primaryValue p a ∈ I.values (.primary p) a := (I.nonempty (.primary p) a).choose_spec

end Images
end ProductCircuit

namespace ProductCircuit.Images
variable {r : ℕ} {P E Z T : Type} {C : ProductCircuit r P E Z T}
    {delta : C.Shifts} (I : C.Images delta)

theorem bufferValue_mem (l : C.Connection) (a : (C.connectionMap l).Point) :
    I.bufferValue l a ∈ I.values (.buffer l) ((C.connectionMap l).source a) :=
  (I.nonempty (.buffer l) ((C.connectionMap l).source a)).choose_spec

theorem buffer_values (h : C.Accepted) (l : C.Connection) (a : (C.connectionMap l).Point) :
    C.sourceForm l (I.primaryValue (C.connectionSource l) ((C.connectionMap l).source a)) =
      delta (.first l) a + I.bufferValue l a 0 ∧
    C.sourceForm l (I.primaryValue (C.connectionSource l) ((C.connectionMap l).source a)) =
      delta (.second l) a + I.bufferValue l a 1 ∧
    I.bufferValue l a 0 + I.bufferValue l a 1 = delta (.third l) a +
      C.targetForm l (I.primaryValue (C.connectionTarget l) ((C.connectionMap l).target a)) := by
  have hm := I.bufferValue_mem l a
  constructor
  · obtain ⟨v, hv, he⟩ := (I.first_equation l a).symm ▸
      (show delta (.first l) a + I.bufferValue l a 0 ∈
        (fun v : Fin 2 → Bit => delta (.first l) a + v 0) ''
          I.values (.buffer l) ((C.connectionMap l).source a) from ⟨_, hm, rfl⟩)
    rw [(I.accepted_primary h _ _) hv (I.primaryValue_mem _ _)] at he
    exact he
  constructor
  · obtain ⟨v, hv, he⟩ := (I.second_equation l a).symm ▸
      (show delta (.second l) a + I.bufferValue l a 1 ∈
        (fun v : Fin 2 → Bit => delta (.second l) a + v 1) ''
          I.values (.buffer l) ((C.connectionMap l).source a) from ⟨_, hm, rfl⟩)
    rw [(I.accepted_primary h _ _) hv (I.primaryValue_mem _ _)] at he
    exact he
  · obtain ⟨v, hv, he⟩ := (I.third_equation l a) ▸
      (show I.bufferValue l a 0 + I.bufferValue l a 1 ∈
        (fun v : Fin 2 → Bit => v 0 + v 1) ''
          I.values (.buffer l) ((C.connectionMap l).source a) from ⟨_, hm, rfl⟩)
    rw [(I.accepted_primary h _ _) hv (I.primaryValue_mem _ _)] at he
    exact he.symm

theorem primary_rowSum (h : C.Accepted)
    (hd : ∀ e, CycleRows.RowSum (fun i => {x // x ∈ (C.comparisonMap e).domain i}) Bit (delta e))
    (p : C.Primary) :
    CycleRows.RowSum (fun _ : Fin r => Bool) (Fin (C.primaryDimension p) → Bit) (I.primaryValue p) := by
  apply CycleRows.RowSum.pi
  intro j
  have hv (a : Fin r → Bool) : I.primaryValue p a j =
      delta (.first (.self p j)) (ProductMap.ofAddress a) +
      delta (.second (.self p j)) (ProductMap.ofAddress a) +
      delta (.third (.self p j)) (ProductMap.ofAddress a) := by
    obtain ⟨h₁, h₂, h₃⟩ := I.buffer_values h (.self p j) (ProductMap.ofAddress a)
    exact BufferAlgebra.self_value _ _ _ _ _ _ h₁ h₂ h₃
  have ha := (hd (.first (.self p j))).pullback
    (fun _ (x : Bool) => (⟨x, Finset.mem_univ _⟩ : {b : Bool // b ∈ (Finset.univ : Finset Bool)}))
  have hb := (hd (.second (.self p j))).pullback
    (fun _ (x : Bool) => (⟨x, Finset.mem_univ _⟩ : {b : Bool // b ∈ (Finset.univ : Finset Bool)}))
  have hc := (hd (.third (.self p j))).pullback
    (fun _ (x : Bool) => (⟨x, Finset.mem_univ _⟩ : {b : Bool // b ∈ (Finset.univ : Finset Bool)}))
  convert (ha.add hb).add hc using 1
  exact funext hv

theorem solve_shift {x d z : Bit} (h : x = d + z) : z = x + d := by
  rw [h]
  calc z = (d + d) + z := by rw [CharTwo.add_self_eq_zero, zero_add]
    _ = d + z + d := by ac_rfl

theorem buffer_rowSum (h : C.Accepted)
    (hd : ∀ e, CycleRows.RowSum (fun i => {x // x ∈ (C.comparisonMap e).domain i}) Bit (delta e))
    (l : C.Connection) :
    CycleRows.RowSum (fun i => {x // x ∈ (C.connectionMap l).domain i})
      (Fin 2 → Bit) (I.bufferValue l) := by
  apply CycleRows.RowSum.pi
  have hs := ((I.primary_rowSum h hd (C.connectionSource l)).pullback
    (fun i (x : {x // x ∈ (C.connectionMap l).domain i}) => x.val)).map (C.sourceForm l).toAddMonoidHom
  intro j
  fin_cases j
  · change CycleRows.RowSum _ Bit (fun a => I.bufferValue l a 0)
    have he : (fun a => I.bufferValue l a 0) =
        (fun a => C.sourceForm l
          (I.primaryValue (C.connectionSource l) ((C.connectionMap l).source a)) + delta (.first l) a) := by
      funext a
      exact solve_shift (I.buffer_values h l a).1
    rw [he]
    exact hs.add (hd (.first l))
  · change CycleRows.RowSum _ Bit (fun a => I.bufferValue l a 1)
    have he : (fun a => I.bufferValue l a 1) =
        (fun a => C.sourceForm l
          (I.primaryValue (C.connectionSource l) ((C.connectionMap l).source a)) + delta (.second l) a) := by
      funext a
      exact solve_shift (I.buffer_values h l a).2.1
    rw [he]
    exact hs.add (hd (.second l))

theorem buffer_extension (h : C.Accepted)
    (hd : ∀ e, CycleRows.RowSum (fun i => {x // x ∈ (C.comparisonMap e).domain i}) Bit (delta e))
    (l : C.Connection) :
    ∃ f : (Fin r → Bool) → Fin 2 → Bit,
      CycleRows.RowSum (fun _ : Fin r => Bool) (Fin 2 → Bit) f ∧
      ∀ a : (C.connectionMap l).Point, f ((C.connectionMap l).source a) = I.bufferValue l a :=
  (I.buffer_rowSum h hd l).extend (fun _ x => x.val) (fun _ => Subtype.val_injective)

include I in
/-- Acceptance supplies genuine row-sum functions at ALL real types, not merely
pointwise scalar images. No property outside a buffer's active domain is used. -/
theorem rows_of_accepted (h : C.Accepted)
    (hd : ∀ e, CycleRows.RowSum (fun i => {x // x ∈ (C.comparisonMap e).domain i}) Bit (delta e)) :
    ∃ f : (p : C.RealType) → (Fin r → Bool) → Fin (C.realDimension p) → Bit,
      (∀ p, CycleRows.RowSum (fun _ : Fin r => Bool) (Fin (C.realDimension p) → Bit) (f p)) ∧
      ∀ e (a : (C.comparisonMap e).Point),
        C.comparisonLeft e (f (C.comparisonSource e) ((C.comparisonMap e).source a)) +
        C.comparisonRight e (f (C.comparisonTarget e) ((C.comparisonMap e).target a)) = delta e a := by
  choose B hB hBa using I.buffer_extension h hd
  let f (p : C.RealType) : (Fin r → Bool) → Fin (C.realDimension p) → Bit := match p with
    | .primary p => I.primaryValue p
    | .buffer l => B l
    | .dummy => fun _ _ => 0
  refine ⟨f, ?_, ?_⟩
  · intro p
    cases p with
    | primary p => exact I.primary_rowSum h hd p
    | buffer l => exact hB l
    | dummy => exact CycleRows.RowSum.zero
  · intro e a
    cases e with
    | seed z =>
      obtain ⟨v, _, he⟩ := (I.equation (.seed z) a) ▸
        (show C.comparisonLeft (.seed z) (I.primaryValue (some (C.seedType z)) ((C.seedMap z).source a)) ∈
          C.comparisonLeft (.seed z) '' I.values (.primary (some (C.seedType z))) ((C.seedMap z).source a)
          from ⟨_, I.primaryValue_mem _ _, rfl⟩)
      change sumForm (C.dimension (C.seedType z))
        (I.primaryValue (some (C.seedType z)) ((C.seedMap z).source a)) + 0 = _
      simpa only [comparisonRight, LinearMap.zero_apply, add_zero] using he.symm
    | first l =>
      have he := I.buffer_values h l a |>.1
      change C.sourceForm l (I.primaryValue _ ((C.connectionMap l).source a)) +
        B l ((C.connectionMap l).source a) 0 = _
      rw [hBa l a, he, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    | second l =>
      have he := I.buffer_values h l a |>.2.1
      change C.sourceForm l (I.primaryValue _ ((C.connectionMap l).source a)) +
        B l ((C.connectionMap l).source a) 1 = _
      rw [hBa l a, he, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    | third l =>
      have he := I.buffer_values h l a |>.2.2
      change (B l _ 0 + B l _ 1) + C.targetForm l (I.primaryValue _ _) = _
      rw [hBa l a, he, add_assoc, CharTwo.add_self_eq_zero, add_zero]

end ProductCircuit.Images

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} [Fintype P] [Fintype E] [Fintype Z] [Fintype T]
    (C : ProductCircuit r P E Z T)

/-- Acceptance gives identification against every finite
simple uncolored mate; no special-twist condition is imposed on its shifts. -/
theorem identifies_of_accepted (hr : 32 ≤ r) (n : ℕ) (h : C.Accepted) :
    Identifies r (((C.schemas.layout n).affine (by omega)).graph 0) := by
  intro H he
  obtain ⟨beta, hb⟩ := (C.schemas.layout n).arbitrary_mate hr H he
  have he' := equivalent_trans he (isomorphic_equivalent hb r)
  let I := C.imagesOfEquivalent hr n beta he'
  obtain ⟨f, hf, hfe⟩ := I.rows_of_accepted h (fun e => C.schemas.wireShift_rowSum n beta e)
  have hs : ∃ z, ((C.schemas.layout n).affine (by omega)).Solves beta z := by
    apply (C.schemas.offsets_iff_real_rowSums (by omega) n beta).mpr
    refine ⟨fun p a => f p (fun i => (a i).val), ?_, ?_⟩
    · intro p
      exact (hf p).pullback (fun _ (b : {b : Bool // b ∈ (Finset.univ : Finset Bool)}) => b.val)
    · intro e a
      exact hfe e a
  exact isomorphic_trans (((C.schemas.layout n).affine (by omega)).graph_isomorphic_iff beta |>.mpr hs)
    (isomorphic_symm hb)

end ProductCircuit

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.CircuitReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace Marker

theorem sum_delta {r : ℕ} (hr : 0 < r) : ∑ i : Fin r, delta i = 1 := by
  cases r with
  | zero => omega
  | succ n =>
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp [delta]
    · intro i _ hi
      have hn : i.val + 1 ≠ n + 1 := by
        intro he
        exact hi (Fin.ext (Nat.add_right_cancel he))
      exact ite_eq_right hn
    · simp

end Marker

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

theorem wireShift_special (hr : 0 < r) (n : ℕ) (b : E → Bit) (e : E)
    (a : S.DomainAddress e) : S.wireShift n (S.specialTwist n b) e a = b e := by
  dsimp only [wireShift, firstShift, middleShift, lastShift, RingLayout.linkShift,
    specialTwist, linkConstant]
  simp only [mul_zero, Finset.sum_const_zero, zero_add]
  rw [← Finset.sum_mul, Marker.sum_delta hr, one_mul]

end ComparisonSchemas

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} [Fintype P] [Fintype E] [Fintype Z] [Fintype T]
    (C : ProductCircuit r P E Z T)

theorem special_not_isomorphic (hr : 32 ≤ r) (n : ℕ) :
    ¬ Isomorphic (((C.schemas.layout n).affine (by omega)).graph 0)
      (((C.schemas.layout n).affine (by omega)).graph (C.schemas.specialTwist n C.rejectConstant)) := by
  intro hi
  obtain ⟨h, _, he⟩ := (C.schemas.offsets_iff_real_rowSums (by omega) n _).mp
    ((((C.schemas.layout n).affine (by omega)).graph_isomorphic_iff _).mp hi)
  have hc (e : C.Comparison) (a : (C.comparisonMap e).Point) := he e a
  have hc' (e : C.Comparison) (a : (C.comparisonMap e).Point) :
      C.schemas.left e (h (C.schemas.source e) (C.schemas.sourceAddress e a)) +
        C.schemas.right e (h (C.schemas.target e) (C.schemas.targetAddress e a)) = C.rejectConstant e :=
    (hc e a).trans (C.schemas.wireShift_special (by omega) n C.rejectConstant e a)
  let a := ProductMap.ofAddress (fun _ : Fin r => false)
  have h₁ := hc' (.first (.self none 0)) a
  have h₂ := hc' (.second (.self none 0)) a
  have h₃ := hc' (.third (.self none 0)) a
  have g₁ := hc' (.first .conflict) a
  have g₂ := hc' (.second .conflict) a
  have g₃ := hc' (.third .conflict) a
  let x := h (.primary none) a (0 : Fin 1)
  let z : Fin 2 → Bit := h (.buffer (.self none 0)) a
  let v : Fin 2 → Bit := h (.buffer .conflict) a
  change x + z 0 = 0 at h₁
  change x + z 1 = 0 at h₂
  change (z 0 + z 1) + x = 0 at h₃
  change x + v 0 = 0 at g₁
  change x + v 1 = 0 at g₂
  change (v 0 + v 1) + x = 1 at g₃
  rw [← CharTwo.add_eq_zero.mp h₁, ← CharTwo.add_eq_zero.mp h₂,
    CharTwo.add_self_eq_zero, zero_add] at h₃
  rw [← CharTwo.add_eq_zero.mp g₁, ← CharTwo.add_eq_zero.mp g₂,
    CharTwo.add_self_eq_zero, zero_add] at g₃
  exact zero_ne_one (h₃.symm.trans g₃)

/-- Rejection prevents identification for the full least-closure product
circuit, not only for a promised selection of comparison mates. -/
theorem not_identifies_of_rejected (hr : 32 ≤ r) (n : ℕ) (hn : r + 1 < n)
    (h : ¬ C.Accepted) : ¬ Identifies r (((C.schemas.layout n).affine (by omega)).graph 0) := by
  intro hi
  exact C.special_not_isomorphic hr n
    (hi _ ((C.rejectingImages h).equivalent_special hr hn))

theorem identifies_iff_accepted (hr : 32 ≤ r) (n : ℕ) (hn : r + 1 < n) :
    Identifies r (((C.schemas.layout n).affine (by omega)).graph 0) ↔ C.Accepted := by
  constructor
  · intro hi
    by_contra hnacc
    exact C.not_identifies_of_rejected hr n hn hnacc hi
  · exact C.identifies_of_accepted hr n

end ProductCircuit

/-- Retained color history always determines the original atomic type. -/
theorem tupleColor_zero_eq {G H : Graph} {k s : ℕ}
    {v : Fin k → Fin G.order} {w : Fin k → Fin H.order}
    (h : tupleColor G k s v = tupleColor H k s w) :
    tupleColor G k 0 v = tupleColor H k 0 w := by
  induction s with
  | zero => exact h
  | succ s ih => exact ih (congrArg Prod.fst h)

theorem tupleColor_atomic {G H : Graph} {k s : ℕ}
    {v : Fin k → Fin G.order} {w : Fin k → Fin H.order}
    (h : tupleColor G k s v = tupleColor H k s w) :
    (∀ i j, v i = v j ↔ w i = w j) ∧
    (∀ i j, G.edge (v i) (v j) = H.edge (w i) (w j)) := by
  have h0 := tupleColor_zero_eq h
  exact ⟨fun i j => decide_eq_decide.mp (congrFun (congrFun (congrArg Prod.fst h0) i) j),
    fun i j => congrFun (congrFun (congrArg Prod.snd h0) i) j⟩

theorem restrictTupleColor_apply (G : Graph) {j k : ℕ} (q : Fin j → Fin k)
    (hq : Function.Injective q) (s : ℕ) (v : Fin k → Fin G.order) :
    restrictTupleColor q s (tupleColor G k s v) = tupleColor G j s (v ∘ q) := by
  induction s generalizing v with
  | zero => rfl
  | succ s ih =>
    dsimp only [restrictTupleColor, tupleColor]
    apply Prod.ext (ih v)
    dsimp only [Prod.snd]
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro z _
    funext i
    dsimp only [Function.comp_def]
    rw [ih, Function.update_comp_eq_of_injective v hq]
    rfl

theorem tupleHistogram_dimension_mono {G H : Graph} {j k s : ℕ}
    (hj : 0 < j) (hjk : j ≤ k) (h : tupleHistogram G k s = tupleHistogram H k s) :
    tupleHistogram G j s = tupleHistogram H j s := by
  obtain ⟨E, hE⟩ := tupleRound_bijection h
  have hp (v : Fin k → Fin G.order) :
      (∀ i, v i = v (Fin.castLE hjk (padIndex hj hjk i))) ↔
      (∀ i, E v i = E v (Fin.castLE hjk (padIndex hj hjk i))) :=
    forall_congr' (fun i => (tupleColor_atomic (hE v)).1 i _)
  let e := (paddedEquiv hj hjk (Fin G.order)).trans
    ((E.subtypeEquiv hp).trans (paddedEquiv hj hjk (Fin H.order)).symm)
  apply histogram_eq_of_equiv e
  intro v
  have hh := congrArg (restrictTupleColor (Fin.castLE hjk) s) (hE (v ∘ padIndex hj hjk))
  rw [restrictTupleColor_apply _ _ (Fin.castLE_injective _),
    restrictTupleColor_apply _ _ (Fin.castLE_injective _)] at hh
  have hv : (v ∘ padIndex hj hjk) ∘ Fin.castLE hjk = v := by funext i; simp
  rw [hv] at hh
  exact hh

/-- Ordinary neighbor refinement is recoverable from any joint dimension >=2. -/
theorem neighborColor_of_tupleColor {G H : Graph} {k : ℕ} (hk : 2 ≤ k) (s : ℕ)
    {v : Fin k → Fin G.order} {w : Fin k → Fin H.order}
    (h : tupleColor G k s v = tupleColor H k s w) (i : Fin k) :
    neighborColor G s (v i) = neighborColor H s (w i) := by
  induction s generalizing v w i with
  | zero => rfl
  | succ s ih =>
    have hprev := congrArg Prod.fst h
    obtain ⟨e, he⟩ := exists_colorEquiv
      (fun z i => tupleColor G k s (Function.update v i z))
      (fun z i => tupleColor H k s (Function.update w i z)) (congrArg Prod.snd h)
    obtain ⟨j, hij⟩ : ∃ j : Fin k, i ≠ j := by
      by_cases hi : i = ⟨0, by omega⟩
      · refine ⟨⟨1, by omega⟩, ?_⟩
        rw [hi]
        intro he
        have := congrArg Fin.val he
        change (0 : ℕ) = 1 at this
        omega
      · exact ⟨⟨0, by omega⟩, hi⟩
    change (neighborColor G s (v i), _) = (neighborColor H s (w i), _)
    apply Prod.ext (ih hprev i)
    apply filteredHistogram_eq_of_equiv e
    · intro z
      have hz := (tupleColor_atomic (congrFun (he z) j)).2 i j
      simp only [Function.update_of_ne hij, Function.update_self] at hz
      rw [hz]
    · intro z
      simpa only [Function.update_self] using ih (congrFun (he z) j) j

theorem neighborHistogram_of_tupleHistogram {G H : Graph} {k s : ℕ} (hk : 2 ≤ k)
    (h : tupleHistogram G k s = tupleHistogram H k s) :
    neighborHistogram G s = neighborHistogram H s := by
  obtain ⟨E, hE⟩ := tupleRound_bijection h
  let i : Fin k := ⟨0, by omega⟩
  have hp (v : Fin k → Fin G.order) :
      (∀ j, v j = v i) ↔ ∀ j, E v j = E v i :=
    forall_congr' (fun j => (tupleColor_atomic (hE v)).1 j i)
  let e := (diagonalEquiv i (Fin G.order)).trans
    ((E.subtypeEquiv hp).trans (diagonalEquiv i (Fin H.order)).symm)
  exact histogram_eq_of_equiv e _ _ (fun v => neighborColor_of_tupleColor hk s (hE (fun _ => v)) i)

theorem equivalent_dimension_mono {G H : Graph} {j k : ℕ}
    (hj : 0 < j) (hjk : j ≤ k) (h : Equivalent k G H) : Equivalent j G H := by
  by_cases he : j = k
  · simpa only [he] using h
  have hk : 2 ≤ k := by omega
  have hne : k ≠ 1 := by omega
  rw [Equivalent, ite_eq_right hne] at h
  unfold Equivalent
  split_ifs with hj1
  · intro s; exact neighborHistogram_of_tupleHistogram hk (h s)
  · intro s; exact tupleHistogram_dimension_mono hj hjk (h s)

theorem identifies_dimension_mono {G : Graph} {j k : ℕ}
    (hj : 0 < j) (hjk : j ≤ k) (h : Identifies j G) : Identifies k G :=
  fun H hH => h H (equivalent_dimension_mono hj hjk hH)

/-- A finite graph has a positive identifying dimension without any restriction
on the order of its candidate mate. -/
theorem identifies_order (G : Graph) : Identifies (max 2 G.order) G := by
  intro H he
  obtain ⟨e, _⟩ := equivalent_degreeBijection (le_max_left _ _) he
  by_cases hn : 0 < G.order
  · obtain ⟨f, hf, ha, _⟩ := equivalent_local_match (le_max_left _ _) he
      (le_max_right _ _) hn (fun i => i)
    have hfi : Function.Injective f := fun i j h => (hf i j).mpr h
    have hfb : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi, Fintype.card_congr e⟩
    exact ⟨Equiv.ofBijective f hfb, ha⟩
  · exact ⟨e, fun u _ => by have := u.isLt; omega⟩

theorem positive_identifying_nonempty (G : Graph) :
    {k : ℕ | 0 < k ∧ Identifies k G}.Nonempty :=
  ⟨max 2 G.order, by have := le_max_left 2 G.order; omega, identifies_order G⟩

theorem WLdim_spec (G : Graph) : 0 < WLdim G ∧ Identifies (WLdim G) G :=
  Nat.sInf_mem (positive_identifying_nonempty G)

theorem WLdim_le_iff {G : Graph} {k : ℕ} (hk : 0 < k) : WLdim G ≤ k ↔ Identifies k G := by
  constructor
  · intro h; exact identifies_dimension_mono (WLdim_spec G).1 h (WLdim_spec G).2
  · intro h; exact Nat.sInf_le ⟨hk, h⟩

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} [Fintype P] [Fintype E] [Fintype Z] [Fintype T]
    (C : ProductCircuit r P E Z T)

theorem dimension_iff_accepted (hr : 32 ≤ r) (n : ℕ) (hn : r + 1 < n) :
    WLdim (((C.schemas.layout n).affine (by omega)).graph 0) ≤ r ↔ C.Accepted := by
  rw [WLdim_le_iff (by omega), C.identifies_iff_accepted hr n hn]

end ProductCircuit

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.BinaryAddresses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace BinaryAddress

theorem advance_one (d : ℕ) : advance (fun _ : Fin d => true) = fun _ => false := by
  induction d with
  | zero => exact Subsingleton.elim _ _
  | succ d ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [advance]
    · simp [advance, ih]

theorem value_advance {d : ℕ} (v : Bits d) (hv : value v + 1 < 2 ^ d) :
    value (advance v) = value v + 1 := by
  induction d with
  | zero => simp [value] at hv
  | succ d ih =>
    cases hb : v 0 with
    | false => simp [advance, value, hb, Nat.add_comm]
    | true =>
      have ht : value (fun i => v i.succ) + 1 < 2 ^ d := by
        simp only [value, hb, ↓reduceIte, pow_succ] at hv
        omega
      have hit := ih (fun i => v i.succ) ht
      simp only [advance, hb, Bool.not_true, ↓reduceIte, value_cons, Bool.false_eq_true, Nat.zero_add]
      rw [hit]
      simp only [value, hb, ↓reduceIte]
      omega

theorem value_eq_last {d : ℕ} (v : Bits d) : value v + 1 = 2 ^ d ↔ v = fun _ => true := by
  constructor
  · intro h
    apply value_injective d
    have h' := value_one d
    omega
  · rintro rfl; exact value_one d

theorem advance_mod {d : ℕ} (v : Bits d) :
    value (advance v) = (value v + 1) % (2 ^ d) := by
  have h := value_lt v
  by_cases h' : value v + 1 < 2 ^ d
  · rw [value_advance v h', Nat.mod_eq_of_lt h']
  · have he := (value_eq_last v).mp (by omega)
    subst v
    rw [advance_one, value_zero, value_one, Nat.mod_self]

theorem advance_carry {d : ℕ} (h : Fin d) (v : Bits d) (hv : Carry h true v) :
    advance v = flipPrefix h v := by
  induction d with
  | zero => exact Fin.elim0 h
  | succ d ih =>
    cases h using Fin.cases with
    | zero =>
      have h0 : v 0 = false := hv.2
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [advance, flipPrefix]
      · simp [advance, flipPrefix, h0]
    | succ j =>
      have h0 : v 0 = true := hv.1 0 (by simp)
      have ht : Carry j true (fun i => v i.succ) :=
        ⟨fun i hi => hv.1 i.succ (by simpa using hi), hv.2⟩
      funext i
      refine Fin.cases ?_ (fun l => ?_) i
      · simp [advance, flipPrefix]
      · simpa [advance, h0, flipPrefix] using congrFun (ih j _ ht) l

theorem carry_exists {d : ℕ} (v : Bits d) (h : v ≠ fun _ => true) :
    ∃ i, Carry i true v := by
  induction d with
  | zero => exact (h (Subsingleton.elim _ _)).elim
  | succ d ih =>
    cases hb : v 0 with
    | false => exact ⟨0, (by intro i hi; exact (Fin.not_lt_zero _ hi).elim), hb⟩
    | true =>
      have ht : (fun i : Fin d => v i.succ) ≠ fun _ => true := by
        intro he
        apply h
        funext i
        exact Fin.cases hb (fun j => congrFun he j) i
      obtain ⟨i, hi⟩ := ih (fun i => v i.succ) ht
      refine ⟨i.succ, ?_, hi.2⟩
      intro j hj
      cases j using Fin.cases with
      | zero => exact hb
      | succ l => exact hi.1 l (by simpa using hj)

theorem carry_not_last {d : ℕ} {h : Fin d} {v : Bits d} (hv : Carry h true v) :
    value v + 1 < 2 ^ d := by
  have hlt := value_lt v
  by_contra hn
  have he := (value_eq_last v).mp (by omega)
  have hh := hv.2
  rw [he] at hh
  contradiction

end BinaryAddress

namespace BinaryAddress

theorem ofNat_value {d : ℕ} (x : Bits d) : ofNat d (value x) = x :=
  value_injective d (value_ofNat d _ (value_lt x))

end BinaryAddress

namespace ProductMap
variable {r : ℕ}

theorem rel_point (D : ProductMap r) (a : D.Point) : D.Rel (D.source a) (D.target a) :=
  ⟨fun i => (a i).property, fun _ => rfl⟩

theorem rel_iff (D : ProductMap r) (x y : Fin r → Bool) :
    D.Rel x y ↔ ∃ a : D.Point, D.source a = x ∧ D.target a = y := by
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨fun i => ⟨x i, hx i⟩, rfl, funext hy⟩
  · rintro ⟨a, rfl, rfl⟩; exact rel_point D a

end ProductMap

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.AddressArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace BinaryAddress

theorem carryMap_sound {d : ℕ} (h : Fin d) {x y : Bits d}
    (hxy : (carryMap h).Rel x y) : value y = value x + 1 := by
  obtain ⟨hx, rfl⟩ := (carryMap_rel _ _ _).mp hxy
  rw [← advance_carry h x hx]
  exact value_advance x (carry_not_last hx)

theorem carryMap_complete {d : ℕ} (x y : Bits d) (hxy : value y = value x + 1) :
    ∃ h : Fin d, (carryMap h).Rel x y := by
  have hn : x ≠ fun _ => true := by
    intro he
    have h := value_lt y
    rw [hxy, he, value_one] at h
    omega
  obtain ⟨h, hh⟩ := carry_exists x hn
  refine ⟨h, (carryMap_rel _ _ _).mpr ⟨hh, ?_⟩⟩
  apply value_injective d
  rw [← advance_carry h x hh, value_advance x (carry_not_last hh), hxy]

theorem cycleMap_sound {d : ℕ} (h : Option (Fin d)) {x y : Bits d}
    (hxy : (cycleMap d h).Rel x y) : y = advance x := by
  cases h with
  | none =>
    obtain ⟨rfl, rfl⟩ := (ProductMap.singleton_rel _ _ _ _).mp hxy
    exact (advance_one d).symm
  | some h =>
    obtain ⟨hh, rfl⟩ := (carryMap_rel _ _ _).mp hxy
    exact (advance_carry h x hh).symm

theorem cycleMap_complete {d : ℕ} (x : Bits d) :
    ∃ h, (cycleMap d h).Rel x (advance x) := by
  by_cases he : x = fun _ => true
  · exact ⟨none, (ProductMap.singleton_rel _ _ _ _).mpr ⟨he, he ▸ advance_one d⟩⟩
  · obtain ⟨h, hh⟩ := carry_exists x he
    exact ⟨some h, (carryMap_rel _ _ _).mpr ⟨hh, advance_carry h x hh⟩⟩

theorem rotation_advance {d : ℕ} (x : Bits d) : rotation d x = advance x := by
  apply value_injective d
  have h : value (rotation d x) = ((value x + 1) % (2 ^ d)) := by
    change ((equiv d) (rotation d x)).val = _
    simp only [rotation, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [finRotate_apply]
    simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
    rfl
  exact h.trans (advance_mod x).symm

end BinaryAddress

namespace BinaryAddress

/-- The largest differing bit determines strict numeric order. -/
theorem value_lt_iff {d : ℕ} (x y : Bits d) : value x < value y ↔
    ∃ h : Fin d, x h = false ∧ y h = true ∧ ∀ i, h < i → x i = y i := by
  induction d with
  | zero => simp [value]
  | succ d ih =>
    let xt : Bits d := fun i => x i.succ
    let yt : Bits d := fun i => y i.succ
    constructor
    · intro h
      by_cases ht : value xt < value yt
      · obtain ⟨i, hi, hj, hh⟩ := (ih xt yt).mp ht
        refine ⟨i.succ, hi, hj, ?_⟩
        intro j hji
        cases j using Fin.cases with
        | zero => exact (Fin.not_lt_zero _ hji).elim
        | succ j => exact hh j (by simpa using hji)
      · have he : value xt = value yt := by
          change (if x 0 then 1 else 0) + 2 * value xt < (if y 0 then 1 else 0) + 2 * value yt at h
          split_ifs at h <;> omega
        have hev := value_injective d he
        refine ⟨0, ?_, ?_, ?_⟩
        · change (if x 0 then 1 else 0) + 2 * value xt < (if y 0 then 1 else 0) + 2 * value yt at h
          cases hx0 : x 0 <;> cases hy0 : y 0 <;> simp_all
        · change (if x 0 then 1 else 0) + 2 * value xt < (if y 0 then 1 else 0) + 2 * value yt at h
          cases hx0 : x 0 <;> cases hy0 : y 0 <;> simp_all
        · intro i hi
          cases i using Fin.cases with
          | zero => exact (lt_irrefl _ hi).elim
          | succ i => exact congrFun hev i
    · rintro ⟨h, hx, hy, hhigh⟩
      cases h using Fin.cases with
      | zero =>
        have hev : xt = yt := by
          funext i
          exact hhigh i.succ (by simp)
        change (if x 0 then 1 else 0) + 2 * value xt < (if y 0 then 1 else 0) + 2 * value yt
        rw [hx, hy, hev]
        simp
      | succ h =>
        have ht : value xt < value yt := (ih xt yt).mpr
          ⟨h, hx, hy, fun i hi => hhigh i.succ (by simpa using hi)⟩
        change (if x 0 then 1 else 0) + 2 * value xt < (if y 0 then 1 else 0) + 2 * value yt
        split_ifs <;> omega

theorem threshold_sound {d : ℕ} (x : Bits d) (h : ThresholdCase x) {y z : Bits d}
    (hy : (thresholdMap x h).Rel y z) : value x ≤ value y ∧ y = z := by
  cases h with
  | none =>
    obtain ⟨rfl, rfl⟩ := (ProductMap.singleton_rel _ _ _ _).mp hy
    exact ⟨le_rfl, rfl⟩
  | some h =>
    obtain ⟨he, hh, hhi⟩ := (aboveMap_rel _ _ _ _).mp hy
    exact ⟨le_of_lt ((value_lt_iff x y).mpr
      ⟨h.val, h.property, hh, fun i hi => (hhi i hi).symm⟩), he⟩

theorem threshold_complete {d : ℕ} (x y : Bits d) (hxy : value x ≤ value y) :
    ∃ h : ThresholdCase x, (thresholdMap x h).Rel y y := by
  rcases lt_or_eq_of_le hxy with hlt | he
  · obtain ⟨h, hx, hy, hhi⟩ := (value_lt_iff x y).mp hlt
    exact ⟨some ⟨h, hx⟩, (aboveMap_rel _ _ _ _).mpr ⟨rfl, hy, fun i hi => (hhi i hi).symm⟩⟩
  · have he' := value_injective d he
    exact ⟨none, (ProductMap.singleton_rel _ _ _ _).mpr ⟨he'.symm, he'.symm⟩⟩

end BinaryAddress

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} (C : ProductCircuit r P E Z T)

theorem edge_rel (e : E) {x y : Fin r → Bool} (h : (C.edgeMap e).Rel x y)
    (hx : C.True (C.source e) x) : C.PortTrue (C.target e) y (C.port e) := by
  obtain ⟨a, rfl, rfl⟩ := (ProductMap.rel_iff _ _ _).mp h
  exact PortTrue.edge e a hx

theorem seed_rel (z : Z) {x y : Fin r → Bool} (h : (C.seedMap z).Rel x y) :
    C.True (C.seedType z) x := by
  obtain ⟨a, rfl, rfl⟩ := (ProductMap.rel_iff _ _ _).mp h
  exact fun j => PortTrue.seed z a j

end ProductCircuit

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.CellularCircuits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace CellularCircuit
open BinaryAddress
variable {d : ℕ} {A Z : Type}

theorem concat_address (D E : ProductMap d) (t j u v : Bits d) :
    (D.concat E).Rel (address t j) (address u v) ↔ D.Rel t u ∧ E.Rel j v := by
  rw [ProductMap.concat_rel]
  simp only [address, Fin.append_left, Fin.append_right]

variable (F : A → A → A → A) (seedLetter : Z → A) (seedDomain : Z → ProductMap d)
    (accept : A → Prop)

variable [Fintype A] [Fintype Z]

variable (init : Bits d → A)

variable {F init}

omit [Fintype A] in
theorem edge_sound (e : Connection d A) {x y : Address d} (h : (edgeMap e).Rel x y)
    (hx : ∀ i, SemPort F init (source e) x i) : SemPort F init (target F e) y (port F e) := by
  cases e with
  | left a b c hct hcp =>
    obtain ⟨ht, hp⟩ := (ProductMap.concat_rel _ _ _ _).mp h
    have htime : value (time y) = value (time x) + 1 := carryMap_sound hct ht
    have hpos : position y = rotation d (position x) :=
      (cycleMap_sound hcp hp).trans (rotation_advance _).symm
    simpa [SemPort, htime, hpos] using hx 0
  | center a b c hct =>
    obtain ⟨ht, hp⟩ := (ProductMap.concat_rel _ _ _ _).mp h
    have htime : value (time y) = value (time x) + 1 := carryMap_sound hct ht
    have hpos : position x = position y := (ProductMap.identity_rel _ _).mp hp
    simpa [SemPort, htime, hpos] using hx 0
  | right a b c hct hcp =>
    obtain ⟨ht, hp⟩ := (ProductMap.concat_rel _ _ _ _).mp h
    have htime : value (time y) = value (time x) + 1 := carryMap_sound hct ht
    have hpos : position x = rotation d (position y) :=
      (cycleMap_sound hcp ((ProductMap.inverse_rel _ _ _).mp hp)).trans (rotation_advance _).symm
    simpa [SemPort, htime, hpos] using hx 0
  | join a b c =>
    obtain rfl := (ProductMap.identity_rel _ _).mp h
    have h0 := hx 0
    have h1 := hx 1
    simp only [SemPort, ↓reduceIte, show (1 : Fin 2) ≠ 0 from by decide] at h0 h1 ⊢
    exact ⟨h0.1, h0.2, h1.2⟩
  | output a b c =>
    obtain rfl := (ProductMap.identity_rel _ _).mp h
    have h0 := hx 0
    have h1 := hx 1
    simp only [SemPort, ↓reduceIte, show (1 : Fin 2) ≠ 0 from by decide] at h0 h1 ⊢
    have ht : value (time x) = (value (time x) - 1) + 1 := by omega
    conv_rhs => rw [ht]
    dsimp only [evolution]
    rw [h0.2.1, h0.2.2, h1.2]

variable (F init)

variable (hseed : SeedCorrect seedLetter seedDomain init)

include hseed in
theorem port_sound {p : Gate A} {x : Address d} {i : Fin (dimension p)}
    (h : (circuit F seedLetter seedDomain accept).PortTrue p x i) : SemPort F init p x i := by
  apply ProductCircuit.PortTrue.rec (motive := fun p x i _ => SemPort F init p x i) ?_ ?_ h
  · intro z a i
    have hrel := ProductMap.rel_point
      ((circuit F seedLetter seedDomain accept).seedMap z) a
    obtain ⟨ht, hp⟩ := (ProductMap.concat_rel _ _ _ _).mp hrel
    obtain ⟨ht, _⟩ := (ProductMap.singleton_rel _ _ _ _).mp ht
    have hs := (hseed (seedLetter z) _).mp ⟨z, _, rfl, hp⟩
    change time (((circuit F seedLetter seedDomain accept).seedMap z).source a) = (fun _ => false) at ht
    change seedLetter z = evolution F init (value (time (((circuit F seedLetter seedDomain accept).seedMap z).source a))) (position _)
    rw [ht, value_zero]
    exact hs
  · intro e a _ ih
    exact edge_sound e (ProductMap.rel_point (edgeMap e) a) ih

include hseed in
theorem scalar_complete (t j : Bits d) :
    (circuit F seedLetter seedDomain accept).True (.scalar (evolution F init (value t) j)) (address t j) := by
  generalize ht : value t = n
  induction n using Nat.strong_induction_on generalizing t j with
  | h n ih =>
    let C := circuit F seedLetter seedDomain accept
    by_cases hn : n = 0
    · have hzero : t = fun _ => false := value_injective d (by rw [ht, hn, value_zero])
      subst t
      obtain ⟨z, y, hz, hrel⟩ := (hseed (init j) j).mpr rfl
      have hs := C.seed_rel z ((concat_address _ _ _ _ _ _).mpr
        ⟨(ProductMap.singleton_rel _ _ _ _).mpr ⟨rfl, rfl⟩, hrel⟩ :
          (C.seedMap z).Rel (address (fun _ => false) j) (address (fun _ => false) y))
      simpa only [C, circuit, value_zero, evolution, hz, hn] using hs
    · have hnpos : 0 < n := by omega
      obtain ⟨u, hu⟩ := value_surjective d (n - 1) (by have := value_lt t; omega)
      obtain ⟨hct, htime⟩ := carryMap_complete u t (by omega)
      let a := evolution F init (n - 1) ((rotation d).symm j)
      let b := evolution F init (n - 1) j
      let c := evolution F init (n - 1) (rotation d j)
      have ha : C.True (.scalar a) (address u ((rotation d).symm j)) := by
        simpa only [hu] using ih (n - 1) (by omega) u ((rotation d).symm j) hu
      have hb : C.True (.scalar b) (address u j) := by
        simpa only [hu] using ih (n - 1) (by omega) u j hu
      have hc : C.True (.scalar c) (address u (rotation d j)) := by
        simpa only [hu] using ih (n - 1) (by omega) u (rotation d j) hu
      obtain ⟨hleft, hleftrel⟩ := cycleMap_complete ((rotation d).symm j)
      have hleftrel' : (cycleMap d hleft).Rel ((rotation d).symm j) j := by
        simpa only [← rotation_advance, Equiv.apply_symm_apply] using hleftrel
      obtain ⟨hright, hrightrel⟩ := cycleMap_complete j
      have hrightrel' : (cycleMap d hright).inverse.Rel (rotation d j) j := by
        rw [ProductMap.inverse_rel]
        simpa only [← rotation_advance] using hrightrel
      have hp0 : C.PortTrue (.first a b c) (address t j) 0 :=
        C.edge_rel (.left a b c hct hleft)
          ((concat_address _ _ _ _ _ _).mpr ⟨htime, hleftrel'⟩) ha
      have hp1 : C.PortTrue (.first a b c) (address t j) 1 :=
        C.edge_rel (.center a b c hct)
          ((concat_address _ _ _ _ _ _).mpr ⟨htime, (ProductMap.identity_rel _ _).mpr rfl⟩) hb
      have hp : C.True (.first a b c) (address t j) := by
        intro i; fin_cases i <;> assumption
      have hv0 : C.PortTrue (.second a b c) (address t j) 0 :=
        C.edge_rel (.join a b c) ((ProductMap.identity_rel _ _).mpr rfl) hp
      have hv1 : C.PortTrue (.second a b c) (address t j) 1 :=
        C.edge_rel (.right a b c hct hright)
          ((concat_address _ _ _ _ _ _).mpr ⟨htime, hrightrel'⟩) hc
      have hv : C.True (.second a b c) (address t j) := by
        intro i; fin_cases i <;> assumption
      have hs : C.PortTrue (.scalar (F a b c)) (address t j) 0 :=
        C.edge_rel (.output a b c) ((ProductMap.identity_rel _ _).mpr rfl) hv
      have hn' : n = (n - 1) + 1 := by omega
      have hval : evolution F init n j = F a b c := by rw [hn']; rfl
      rw [hval]
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using hs

include hseed in
theorem accepted_iff : (circuit F seedLetter seedDomain accept).Accepted ↔
    ∃ j : Bits d, accept (evolution F init (2 ^ d - 1) j) := by
  constructor
  · rintro ⟨f, a, ha⟩
    have hrel := ProductMap.rel_point ((circuit F seedLetter seedDomain accept).testMap f) a
    obtain ⟨ht, _⟩ := (ProductMap.concat_rel _ _ _ _).mp hrel
    obtain ⟨ht, _⟩ := (ProductMap.singleton_rel _ _ _ _).mp ht
    have hs := port_sound F seedLetter seedDomain accept init hseed (ha 0)
    change f.val = evolution F init (value (time _)) (position _) at hs
    have ht' : value (time ((circuit F seedLetter seedDomain accept).testMap f |>.source a)) = 2 ^ d - 1 := by
      change value (fun i => ((circuit F seedLetter seedDomain accept).testMap f).source a (Fin.castAdd d i)) = _
      rw [ht]; have := value_one d; omega
    rw [ht'] at hs
    exact ⟨_, hs ▸ f.property⟩
  · rintro ⟨j, hj⟩
    let f : {f : A // accept f} := ⟨evolution F init (2 ^ d - 1) j, hj⟩
    let x : Address d := address (fun _ => true) j
    have hrel : ((circuit F seedLetter seedDomain accept).testMap f).Rel x x :=
      (concat_address _ _ _ _ _ _).mpr (by simp only [ProductMap.singleton_rel, ProductMap.identity_rel, and_self])
    obtain ⟨a, ha, _⟩ := (ProductMap.rel_iff _ _ _).mp hrel
    refine ⟨f, a, ?_⟩
    rw [ha]
    have ht : value (fun _ : Fin d => true) = 2 ^ d - 1 := by have := value_one d; omega
    simpa only [ht] using scalar_complete F seedLetter seedDomain accept init hseed (fun _ => true) j

end CellularCircuit

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.MachineCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace Machine

namespace TapeConfig
variable {M : Machine} {X : Type} [DecidableEq X]

/-- The finite local table is an actual one-head machine step, including seam
crossings and halted configurations; no cellular-automaton theorem is assumed. -/
theorem localRule_correct (e : X ≃ X)
    (hfix : ∀ x, e x ≠ x) (htwo : ∀ x, e x ≠ e.symm x)
    (c : M.TapeConfig X) (x : X) :
    M.localRule (c.letter (e.symm x)) (c.letter x) (c.letter (e x)) =
      (c.advance e).letter x := by
  have hfix' (x : X) : e.symm x ≠ x := by
    intro h
    have he := congrArg e h
    exact hfix x (by simpa using he.symm)
  have hL : e.symm x = c.head ↔ x = e c.head := e.symm_apply_eq
  have hR : e x = c.head ↔ x = e.symm c.head := e.eq_symm_apply.symm
  by_cases hc : x = c.head
  · subst x
    have hl := hfix' c.head
    have hr := hfix c.head
    cases hm : (M.action c.state (c.tape c.head)).2.2 <;>
      simp [localRule, letter, advance, hm, Ne.symm hl, Ne.symm hr]
  · by_cases hl : e.symm x = c.head
    · have hr : e x ≠ c.head := by intro he; exact htwo x (he.trans hl.symm)
      have hx := hL.mp hl
      simp only [localRule, letter, hc, hl, hr, ite_true, ite_false]
      cases hm : (M.action c.state (c.tape c.head)).2.2 <;>
        simp [advance, hm, hx, hfix, htwo]
    · by_cases hr : e x = c.head
      · have hx := hR.mp hr
        simp only [localRule, letter, hc, hl, hr, ite_true, ite_false]
        cases hm : (M.action c.state (c.tape c.head)).2.2 <;>
          simp [advance, hm, hx, hfix', Ne.symm (htwo c.head)]
      · cases hm : (M.action c.state (c.tape c.head)).2.2 <;>
          simp [localRule, letter, advance, hm, hc, hl, hr, ← hL, ← hR]

theorem advance_halted (e : X ≃ X) (c : M.TapeConfig X)
    (h : c.state = 1 ∨ c.state = 2) : c.advance e = c := by
  simp only [advance, action_halt M _ _ h]
  cases c
  simp

end TapeConfig

end Machine

namespace Machine
open BinaryAddress

theorem ringInitial_blank (M : Machine) {d : ℕ} (w : Word) (x : Bits d)
    (hx : inputSpan w ≤ value x) : (M.ringInitial w).letter x = (0, none) := by
  have hn : w.length ≤ value x := (le_max_right _ _).trans hx
  have h0 : x ≠ fun _ => false := by
    intro he
    rw [he, value_zero] at hx
    exact Nat.not_succ_le_zero 0 ((le_max_left 1 w.length).trans hx)
  simp only [TapeConfig.letter, ringInitial, h0, ite_false]
  rw [List.getElem?_eq_none (by omega)]
  rfl

theorem initialSeed_correct (M : Machine) {d : ℕ} (w : Word)
    (hsize : inputSpan w < 2 ^ d) :
    CellularCircuit.SeedCorrect (M.initialSeedLetter d w) (initialSeedMap d w)
      (M.ringInitial w).letter := by
  intro f x
  constructor
  · rintro ⟨z, y, rfl, hz⟩
    cases z with
    | inl i =>
      obtain ⟨rfl, _⟩ := (ProductMap.singleton_rel _ _ _ _).mp hz
      rfl
    | inr h =>
      have hs := (threshold_sound _ h hz).1
      rw [value_ofNat _ _ hsize] at hs
      exact (ringInitial_blank M w x hs).symm
  · intro hf
    by_cases hx : value x < inputSpan w
    · let i : Fin (inputSpan w) := ⟨value x, hx⟩
      refine ⟨.inl i, x, ?_, ?_⟩
      · simp only [initialSeedLetter, i, ofNat_value, hf]
      · change (ProductMap.singleton (ofNat d (value x)) (ofNat d (value x))).Rel x x
        simp only [ofNat_value, ProductMap.singleton_rel, and_self]
    · have hle : inputSpan w ≤ value x := by omega
      obtain ⟨h, hh⟩ := threshold_complete (ofNat d (inputSpan w)) x
        (by simpa only [value_ofNat _ _ hsize] using hle)
      refine ⟨.inr h, x, ?_, hh⟩
      exact (ringInitial_blank M w x hle).symm.trans hf.symm

theorem compiledCircuit_iff (M : Machine) {d : ℕ} (w : Word)
    (hsize : inputSpan w < 2 ^ d) : (M.compiledCircuit d w).Accepted ↔
    ∃ j : Bits d,
      (CellularCircuit.evolution M.localRule (M.ringInitial w).letter (2 ^ d - 1) j).2 = some 1 :=
  (ProductCircuit.accepted_reseed _ _).trans
    (CellularCircuit.accepted_iff M.localRule _ _ (fun a => a.2 = some 1) _
      (M.initialSeed_correct w hsize))

end Machine

namespace BinaryAddress

theorem value_rotation {d : ℕ} (x : Bits d) :
    value (rotation d x) = if value x + 1 < 2 ^ d then value x + 1 else 0 := by
  rw [rotation_advance, advance_mod]
  have hx := value_lt x
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have he : value x + 1 = 2 ^ d := by omega
    rw [he, Nat.mod_self]

theorem rotation_ne_self {d : ℕ} (hd : 1 < 2 ^ d) (x : Bits d) : rotation d x ≠ x := by
  intro h
  have he := congrArg value h
  rw [value_rotation] at he
  have hx := value_lt x
  split_ifs at he <;> omega

theorem rotation_ne_symm {d : ℕ} (hd : 2 < 2 ^ d) (x : Bits d) :
    rotation d x ≠ (rotation d).symm x := by
  intro h
  have he := congrArg (rotation d) h
  rw [Equiv.apply_symm_apply] at he
  have hv := congrArg value he
  rw [value_rotation, value_rotation] at hv
  have hx := value_lt x
  split_ifs at hv <;> omega

end BinaryAddress

namespace Machine
open BinaryAddress

theorem evolution_ringRun (M : Machine) {d : ℕ} (hd : 2 < 2 ^ d) (w : Word) (t : ℕ) :
    CellularCircuit.evolution M.localRule (M.ringInitial w).letter t =
      (@ringRun M d w t).letter := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext j
    simp only [CellularCircuit.evolution, ih, ringRun_succ]
    exact TapeConfig.localRule_correct (rotation d) (rotation_ne_self (by omega))
      (rotation_ne_symm hd) _ _

theorem exists_letter_accept {M : Machine} {X : Type} [DecidableEq X]
    (c : M.TapeConfig X) : (∃ x, (c.letter x).2 = some 1) ↔ c.state = 1 := by
  constructor
  · rintro ⟨x, hx⟩
    change (if x = c.head then some c.state else none) = some 1 at hx
    split_ifs at hx with he
    exact Option.some.inj hx
  · intro h
    exact ⟨c.head, by simp [TapeConfig.letter, h]⟩

theorem compiledCircuit_ringRun (M : Machine) {d : ℕ} (hd : 2 < 2 ^ d)
    (w : Word) (hsize : inputSpan w < 2 ^ d) :
    (M.compiledCircuit d w).Accepted ↔ (@ringRun M d w (2 ^ d - 1)).state = 1 := by
  rw [compiledCircuit_iff M w hsize, evolution_ringRun M hd w]
  exact exists_letter_accept _

end Machine

namespace BinaryAddress

theorem value_residue (d : ℕ) (z : ℤ) : value (residue d z) = (z % (2 ^ d : ℕ)).toNat := by
  apply value_ofNat
  exact (Int.toNat_lt (Int.emod_nonneg _ (by positivity))).mpr
    (Int.emod_lt_of_pos _ (by positivity))

theorem residue_add_one (d : ℕ) (z : ℤ) : residue d (z + 1) = rotation d (residue d z) := by
  apply value_injective d
  rw [value_residue, rotation_advance, advance_mod, value_residue]
  apply Int.ofNat_inj.mp
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity)), Int.natCast_emod,
    Nat.cast_add, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity)), Nat.cast_one]
  simp only [Int.add_emod, Int.emod_emod]

theorem residue_sub_one (d : ℕ) (z : ℤ) : residue d (z - 1) = (rotation d).symm (residue d z) := by
  apply (rotation d).injective
  rw [Equiv.apply_symm_apply, ← residue_add_one]
  congr 1
  omega

theorem residue_injective_window {d T : ℕ} (hsize : 2 * T < 2 ^ d) {x y : ℤ}
    (hx : -(T : ℤ) ≤ x ∧ x ≤ T) (hy : -(T : ℤ) ≤ y ∧ y ≤ T)
    (h : residue d x = residue d y) : x = y := by
  have hv := congrArg value h
  rw [value_residue, value_residue] at hv
  have he : x % (2 ^ d : ℕ) = y % (2 ^ d : ℕ) := by
    have hc := congrArg (fun n : ℕ => (n : ℤ)) hv
    simpa only [Int.toNat_of_nonneg (Int.emod_nonneg x (b := (2 ^ d : ℕ)) (by positivity)),
      Int.toNat_of_nonneg (Int.emod_nonneg y (b := (2 ^ d : ℕ)) (by positivity))] using hc
  have hh := (Int.emod_add_cancel_right (m := x) (k := y) (n := (2 ^ d : ℕ)) (i := T)).mpr he
  have hx0 : 0 ≤ x + T := by omega
  have hy0 : 0 ≤ y + T := by omega
  have hxlt : x + T < (2 ^ d : ℕ) := by omega
  have hylt : y + T < (2 ^ d : ℕ) := by omega
  rw [Int.emod_eq_of_lt hx0 hxlt, Int.emod_eq_of_lt hy0 hylt] at hh
  omega

theorem value_residue_of_nonneg {d : ℕ} {z : ℤ} (h0 : 0 ≤ z) (hlt : z < (2 ^ d : ℕ)) :
    value (residue d z) = z.toNat := by rw [value_residue, Int.emod_eq_of_lt h0 hlt]

theorem value_residue_negative {d : ℕ} {z : ℤ} (hlt : -(2 ^ d : ℕ) < z) (h0 : z < 0) :
    (value (residue d z) : ℤ) = z + (2 ^ d : ℕ) := by
  rw [value_residue, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
  have h := (Int.ediv_emod_unique (a := z) (b := (2 ^ d : ℕ))
    (q := -1) (r := z + (2 ^ d : ℕ)) (by positivity)).mpr (by constructor <;> omega)
  exact h.2

end BinaryAddress

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.MachineReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace Machine
open BinaryAddress

theorem step_action (M : Machine) (c : Configuration M) : step M c = M.actionConfig c := by
  by_cases h : c.state = 1 ∨ c.state = 2
  · simp only [step, h, ite_true, actionConfig, action_halt M _ _ h,
      Move.displacement, add_zero, Function.update_eq_self]
  · simp only [step, h, ite_false, actionConfig, action]

theorem displacement_bound (m : Move) : -1 ≤ m.displacement ∧ m.displacement ≤ 1 := by
  cases m <;> simp [Move.displacement]

theorem head_bound (M : Machine) (w : Word) (t : ℕ) :
    -(t : ℤ) ≤ (run M w t).head ∧ (run M w t).head ≤ t := by
  induction t with
  | zero => simp [run, initial]
  | succ t ih =>
    rw [run_succ, step_action]
    have hm := displacement_bound (M.action (run M w t).state ((run M w t).tape (run M w t).head)).2.2
    dsimp only [actionConfig]
    push_cast
    omega

theorem initial_ringAgrees (M : Machine) {d T : ℕ} (w : Word)
    (hsize : 2 * T < 2 ^ d) (hm : w.length ≤ T) :
    RingAgrees M d T (initial M w) (M.ringInitial w) := by
  refine ⟨rfl, residue_zero d, ?_⟩
  intro z hz
  by_cases h0 : 0 ≤ z
  · have hlt : z < (2 ^ d : ℕ) := by omega
    simp only [initial, h0, ite_true, ringInitial, value_residue_of_nonneg h0 hlt]
  · have hneg : z < 0 := by omega
    have hgt : -(2 ^ d : ℕ) < z := by omega
    have hv := value_residue_negative hgt hneg
    have hn : w.length ≤ value (residue d z) := by omega
    simp only [initial, h0, ite_false, ringInitial, List.getElem?_eq_none hn]
    rfl

variable {M : Machine} {d T : ℕ}

theorem RingAgrees.step {c : Configuration M} {q : M.TapeConfig (Bits d)}
    (h : RingAgrees M d T c q) (hsize : 2 * T < 2 ^ d)
    (hc : -(T : ℤ) ≤ c.head ∧ c.head ≤ T) :
    RingAgrees M d T (step M c) (q.advance (rotation d)) := by
  have ha : M.action c.state (c.tape c.head) = M.action q.state (q.tape q.head) := by
    rw [h.state, h.tape _ hc, h.head]
  rw [step_action]
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg Prod.fst ha
  · change residue d (c.head + (M.action c.state (c.tape c.head)).2.2.displacement) = _
    rw [ha]
    cases hm : (M.action q.state (q.tape q.head)).2.2 with
    | left => simp only [TapeConfig.advance, hm, Move.displacement,
        ← sub_eq_add_neg, residue_sub_one, h.head]
    | stay => simp only [TapeConfig.advance, hm, Move.displacement, add_zero, h.head]
    | right => simp only [TapeConfig.advance, hm, Move.displacement, residue_add_one, h.head]
  · intro z hz
    change Function.update c.tape c.head (M.action c.state (c.tape c.head)).2.1 z =
      Function.update q.tape q.head (M.action q.state (q.tape q.head)).2.1 (residue d z)
    rw [ha]
    by_cases he : z = c.head
    · subst z
      rw [h.head, Function.update_self, Function.update_self]
    · have hr : residue d z ≠ q.head := by
        intro hr
        apply he
        exact residue_injective_window hsize hz hc (hr.trans h.head.symm)
      rw [Function.update_of_ne he, Function.update_of_ne hr]
      exact h.tape z hz

theorem run_ringAgrees (M : Machine) {d T : ℕ} (w : Word)
    (hsize : 2 * T < 2 ^ d) (hm : w.length ≤ T) (t : ℕ) (ht : t ≤ T) :
    RingAgrees M d T (run M w t) (M.ringRun w t) := by
  induction t with
  | zero => exact initial_ringAgrees M w hsize hm
  | succ t ih =>
    have hhead := head_bound M w t
    rw [run_succ, ringRun_succ]
    exact (ih (by omega)).step hsize (by constructor <;> omega)

theorem ringRun_halted (M : Machine) {d : ℕ} (w : Word) (t u : ℕ)
    (h : (@ringRun M d w t).state = 1 ∨ (@ringRun M d w t).state = 2) :
    @ringRun M d w (t + u) = M.ringRun w t := by
  induction u with
  | zero => simp only [add_zero]
  | succ u ih =>
    rw [← Nat.add_assoc, ringRun_succ, ih]
    exact TapeConfig.advance_halted _ _ h

theorem compiledCircuit_run (M : Machine) {d T : ℕ} (w : Word)
    (hsize : 2 * T < 2 ^ d) (hT : 0 < T) (hm : w.length ≤ T)
    {t : ℕ} (ht : t ≤ T) (hhalt : Halted (run M w t)) :
    (M.compiledCircuit d w).Accepted ↔ (run M w t).state = 1 := by
  have hd : 2 < 2 ^ d := by omega
  have hi : inputSpan w < 2 ^ d := by dsimp only [inputSpan]; omega
  rw [compiledCircuit_ringRun M hd w hi]
  have hag := run_ringAgrees M w hsize hm t ht
  have hr : (@ringRun M d w t).state = 1 ∨ (@ringRun M d w t).state = 2 := by
    rw [← hag.state]
    exact hhalt
  have ht' : t + (2 ^ d - 1 - t) = 2 ^ d - 1 := by omega
  rw [← ht', ringRun_halted M w t _ hr]
  rw [hag.state]

end Machine

namespace AffineBlocks
variable {C B : Type} [Fintype C] [DecidableEq C] [Fintype B]
theorem graph_nonempty (D : AffineBlocks C B) (c : C) (beta : B → Bit) :
    0 < (D.graph beta).order := by
  classical
  change 0 < Fintype.card (LeafVertex (tagSize D.colorNat))
  exact Fintype.card_pos_iff.mpr ⟨.inl (.inl (c, 0))⟩
end AffineBlocks

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} [Fintype P] [Fintype E] [Fintype Z] [Fintype T]
    (C : ProductCircuit r P E Z T)

theorem outputGraph_correct (hr : 32 ≤ r) : WLdim (C.outputGraph hr) ≤ r ↔ C.Accepted :=
  C.dimension_iff_accepted hr (4 * (r + 1) - 1) (by omega)

theorem outputGraph_nonempty (hr : 32 ≤ r) : 0 < (C.outputGraph hr).order := by
  classical
  let i : Fin r := ⟨0, by omega⟩
  let R := C.schemas.layout (4 * (r + 1) - 1)
  let h : R.HName := ⟨.inl (.primary none), i, ⟨false, by simp [R, ComparisonSchemas.layout,
    ComparisonSchemas.layoutLabels]⟩, ⟨false, by simp [R, ComparisonSchemas.layout,
    ComparisonSchemas.layoutLabels]⟩⟩
  let c : R.Coordinate := .inl ⟨h, ⟨0, by exact Nat.zero_lt_one⟩⟩
  exact (R.affine (by omega)).graph_nonempty c 0

end ProductCircuit

namespace Machine

theorem compiledCircuit_decides {L : BinaryLanguage} {M : Machine} {C e : ℕ}
    (h : DecidesWithin M L (fun m => 2 ^ (C * (m + 1) ^ e))) (w : Word) :
    (M.compiledCircuit (addressWidth C e w.length) w).Accepted ↔ w ∈ L := by
  obtain ⟨t, ht, hhalt, hacc⟩ := h w
  let p := paddedExponent C e w.length
  have hp : C * (w.length + 1) ^ e ≤ p := by dsimp [p, paddedExponent]; omega
  have hm : w.length ≤ 2 ^ p := by
    have hpow : 2 ^ w.length ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (by dsimp [p, paddedExponent]; omega)
    exact (le_of_lt (Nat.lt_two_pow_self (n := w.length))).trans hpow
  have ht' : t ≤ 2 ^ p := ht.trans (Nat.pow_le_pow_right (by decide) hp)
  have hsize : 2 * 2 ^ p < 2 ^ addressWidth C e w.length := by
    change 2 * 2 ^ p < 2 ^ (p + 2)
    rw [pow_add]
    have : 0 < 2 ^ p := by positivity
    norm_num
    omega
  exact (M.compiledCircuit_run w hsize (by positivity) hm ht' hhalt).trans hacc

theorem reductionGraph_correct {L : BinaryLanguage} {M : Machine} {C e : ℕ}
    (h : DecidesWithin M L (fun m => 2 ^ (C * (m + 1) ^ e))) (w : Word) :
    WLdim (M.reductionGraph C e w) ≤ reductionDimension C e w.length ↔ w ∈ L := by
  classical
  exact (ProductCircuit.outputGraph_correct _ _).trans (compiledCircuit_decides h w)

theorem reductionGraph_nonempty (M : Machine) (C e : ℕ) (w : Word) :
    0 < (M.reductionGraph C e w).order := by
  classical
  exact ProductCircuit.outputGraph_nonempty _ _

end Machine

theorem binaryValue_append_bit (l : Word) (b : Bool) :
    binaryValue (l ++ [b]) = 2 * binaryValue l + if b then 1 else 0 := by
  simp [binaryValue, List.foldl_append]

@[simp] theorem binaryValue_binaryWord (n : ℕ) : binaryValue (binaryWord n) = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [binaryWord, Nat.bits_append_bit n b hn, List.reverse_cons, binaryValue_append_bit]
    change 2 * binaryValue (binaryWord n) + (if b then 1 else 0) = Nat.bit b n
    rw [ih, Nat.bit_val]
    cases b <;> rfl

theorem binaryWord_leading {n : ℕ} (hn : 0 < n) : ∃ t, binaryWord n = true :: t := by
  induction n using Nat.binaryRec' with
  | zero => omega
  | bit b n hb ih =>
    by_cases hz : n = 0
    · subst n
      obtain rfl := hb rfl
      exact ⟨[], rfl⟩
    · obtain ⟨t, ht⟩ := ih (by omega)
      refine ⟨t ++ [b], ?_⟩
      rw [binaryWord, Nat.bits_append_bit n b hb, List.reverse_cons]
      change binaryWord n ++ [b] = _
      rw [ht]
      rfl

/-- The order header is genuinely uniquely parsable, including order zero. -/
theorem unary_frame_injective {n m : ℕ} {s t : Word}
    (h : List.replicate n true ++ false :: s = List.replicate m true ++ false :: t) :
    n = m ∧ s = t := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simpa [List.replicate_succ] using h
    | succ m => simp [List.replicate_succ] at h
  | succ n ih =>
    cases m with
    | zero => simp [List.replicate_succ] at h
    | succ m =>
      have h' : List.replicate n true ++ false :: s = List.replicate m true ++ false :: t := by
        simpa [List.replicate_succ] using h
      obtain ⟨hn, ht⟩ := ih h'
      exact ⟨congrArg Nat.succ hn, ht⟩

private theorem split_matrix_length (n m : ℕ) (f : Fin n → Fin m → Bool) :
    ((List.ofFn fun i => List.ofFn (f i)).flatten).length = n * m := by
  simp [List.length_flatten, List.map_ofFn, Function.comp_def]

@[simp] theorem matrixWord_length (G : Graph) : (matrixWord G).length = G.order * G.order :=
  split_matrix_length _ _ _

private theorem split_matrix_injective (n m : ℕ) (f g : Fin n → Fin m → Bool)
    (h : (List.ofFn fun i => List.ofFn (f i)).flatten =
      (List.ofFn fun i => List.ofFn (g i)).flatten) : f = g := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [List.ofFn_succ, List.flatten_cons] at h
    obtain ⟨hh, ht⟩ := List.append_inj h (by simp)
    have hh' : f 0 = g 0 := List.ofFn_inj.mp hh
    have ht' := ih (fun i => f i.succ) (fun i => g i.succ) ht
    funext i
    refine Fin.cases hh' (fun i => congrFun ht' i) i

theorem inputWord_injective {G H : Graph} {u v : Word}
    (h : inputWord G u = inputWord H v) : G = H ∧ u = v := by
  have hh : List.replicate G.order true ++ false :: (matrixWord G ++ u) =
      List.replicate H.order true ++ false :: (matrixWord H ++ v) := by
    simpa only [inputWord, List.append_assoc, List.cons_append, List.nil_append] using h
  obtain ⟨hn, hs⟩ := unary_frame_injective hh
  obtain ⟨hm, hv⟩ := List.append_inj hs (by simp only [matrixWord_length, hn])
  refine ⟨?_, hv⟩
  apply Graph.ext _ _ hn
  cases G with | mk n e hsym hl =>
    cases H with | mk m f hsym' hl' =>
      simp only at hn
      subst m
      have he := split_matrix_injective n n e f hm
      subst f
      intro i j
      rfl

/-- Correctness of serialization includes exclusion of every malformed alternative parse. -/
theorem inputWord_mem_iff (G : Graph) (hn : 0 < G.order) (k : ℕ) (hk : 0 < k) :
    inputWord G (binaryWord k) ∈ dimensionLanguage ↔ WLdim G ≤ k := by
  constructor
  · rintro ⟨H, bits, _, _, _, he, hw⟩
    obtain ⟨rfl, rfl⟩ := inputWord_injective he
    simpa [List.replicate_succ] using hw
  · intro h
    exact ⟨G, binaryWord k, hn, binaryWord_leading hk, by simpa, rfl, by simpa⟩

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.StackMachines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

/- A finite-alphabet parallel-stack interpreter, with local one-tape execution.
All stored registers below range over a fixed finite type; no unbounded value is
hidden in a transition table. The only unbounded data are the literal bit stk. -/
namespace StackModel

variable {K Λ R : Type} [DecidableEq K]

variable [Fintype K] [Fintype Λ] [Fintype R]

@[simp] theorem decode_symbol (input : K) (a : Alphabet K) : decodeSymbol input (symbol input a) = a := by
  classical
  unfold symbol
  split_ifs with h0 h1 h2
  · subst a; simp only [decodeSymbol, Fin.val_zero]; norm_num
  · subst a; simp only [decodeSymbol, Fin.val_one]; norm_num
  · subst a; simp only [decodeSymbol, Fin.val_two]; norm_num
  · dsimp [decodeSymbol]
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega)]
    simp

end StackModel

namespace StackModel
variable {K Λ R : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R]
    (P : Program K Λ R) (input : K)

/-- Literal one-transition equation for every interpreter phase. -/
theorem step_config (p : Phase K Λ R) (z : ℤ) (S : K → Word) :
    WLIdentification.step (compile P input) (config P input p z S) =
      let t := dispatch P input p (tape input S z)
      ⟨t.1, z + t.2.2.displacement, Function.update (tape input S) z t.2.1⟩ := by
  have hn : ¬ ((config P input p z S).state = 1 ∨ (config P input p z S).state = 2) :=
    not_or_intro (state_ne_one p) (state_ne_two p)
  rw [WLIdentification.step, ite_eq_right hn]
  change (let t := (compile P input).transition (state p) (tape input S z)
    ; Configuration.mk (M := compile P input) t.1 (z + t.2.2.displacement)
      (Function.update (tape input S) z t.2.1)) = _
  rw [transition_state]

theorem step_readonly (p q : Phase K Λ R) (z : ℤ) (S : K → Word) (m : Move)
    (h : dispatch P input p (tape input S z) = (state q, tape input S z, m)) :
    WLIdentification.step (compile P input) (config P input p z S) =
      config P input q (z + m.displacement) S := by
  rw [step_config, h]
  change Configuration.mk (M := compile P input) (state q) (z + m.displacement)
    (Function.update (tape input S) z (tape input S z)) = _
  congr 1
  exact Function.update_eq_self z (tape input S)

theorem step_back_nat (label : Λ) (s : R) (S : K → Word) (n : ℕ) :
    WLIdentification.step (compile P input) (config P input (.back label s) n S) =
      config P input (.back label s) ((n : ℤ) - 1) S := by
  simpa only [Move.displacement, sub_eq_add_neg] using
    step_readonly P input (.back label s) (.back label s) n S .left
      (by simp only [tape_nat, dispatch, decode_symbol])

theorem step_back_marker (label : Λ) (s : R) (S : K → Word) :
    WLIdentification.step (compile P input) (config P input (.back label s) (-1) S) =
      config P input (.ready label s) 0 S := by
  simpa only [Move.displacement, neg_add_cancel] using
    step_readonly P input (.back label s) (.ready label s) (-1) S .right
      (by simp only [tape_marker, dispatch, decode_symbol])

theorem back_to_marker (label : Λ) (s : R) (S : K → Word) (n : ℕ) :
    (WLIdentification.step (compile P input))^[n]
      (config P input (.back label s) ((n : ℤ) - 1) S) =
        config P input (.back label s) (-1) S := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have he : ((n + 1 : ℕ) : ℤ) - 1 = n := by omega
    rw [he, step_back_nat, ih]

theorem back_to_ready (label : Λ) (s : R) (S : K → Word) (n : ℕ) :
    (WLIdentification.step (compile P input))^[n + 1]
      (config P input (.back label s) ((n : ℤ) - 1) S) =
        config P input (.ready label s) 0 S := by
  rw [Function.iterate_succ_apply', back_to_marker, step_back_marker]

/-- No random access is used: a full rightward scan costs one transition per cell. -/
theorem scan_push (k : K) (label : Λ) (s : R) (b : Bool) (S : K → Word)
    (n : ℕ) (hn : n ≤ (S k).length) :
    (WLIdentification.step (compile P input))^[n]
      (config P input (.push k label s b) 0 S) =
        config P input (.push k label s b) n S := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hsome : ((column S n) k).isSome = true := by simp [column]; omega
    have hstep := step_readonly P input (.push k label s b) (.push k label s b) n S .right
      (by simp only [tape_nat, dispatch, decode_symbol, hsome, ite_true])
    simpa only [Move.displacement, Nat.cast_add, Nat.cast_one] using hstep

theorem scan_pop (k : K) (label : Λ) (f : Option Bool → R) (S : K → Word)
    (n : ℕ) (hn : n ≤ (S k).length) :
    (WLIdentification.step (compile P input))^[n]
      (config P input (.pop k label f) 0 S) =
        config P input (.pop k label f) n S := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hsome : ((column S n) k).isSome = true := by simp [column]; omega
    have hstep := step_readonly P input (.pop k label f) (.pop k label f) n S .right
      (by simp only [tape_nat, dispatch, decode_symbol, hsome, ite_true])
    simpa only [Move.displacement, Nat.cast_add, Nat.cast_one] using hstep

/-- Erasing the end of a stack, like pushing, only edits one physical cell. -/
theorem tape_push (S : K → Word) (k : K) (b : Bool) :
    tape input (Function.update S k (S k ++ [b])) =
      Function.update (tape input S) ((S k).length : ℤ)
        (symbol input (some (Function.update (column S (S k).length) k (some b)))) := by
  funext z
  by_cases hz : z = ((S k).length : ℤ)
  · subst z
    rw [Function.update_self, tape_nat]
    congr 2
    funext j
    by_cases hj : j = k
    · subst j; simp [column]
    · simp [column, Function.update_of_ne hj]
  · rw [Function.update_of_ne hz]
    unfold tape
    split_ifs with hm hpos
    · rfl
    · congr 2
      funext j
      by_cases hj : j = k
      · subst j
        simp only [column, Function.update_self]
        rw [List.getElem?_append]
        split_ifs with hi
        · rfl
        · have hgt : (S k).length < z.toNat := by omega
          have hn : 1 ≤ z.toNat - (S k).length := by omega
          rw [List.getElem?_eq_none (by simpa using hn), List.getElem?_eq_none (by omega)]
      · simp [column, Function.update_of_ne hj]
    · rfl

end StackModel

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.TapeCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace StackModel
variable {K Λ R : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R]
    (P : Program K Λ R) (input : K)

theorem push_at_end (k : K) (label : Λ) (s : R) (b : Bool) (S : K → Word) :
    WLIdentification.step (compile P input)
      (config P input (.push k label s b) (S k).length S) =
    config P input (.back label s) (((S k).length : ℤ) - 1)
      (Function.update S k (S k ++ [b])) := by
  rw [step_config]
  have hn : column S (S k).length k = none := by simp [column]
  simp only [tape_nat, dispatch, decode_symbol, hn, Option.isSome_none, Bool.false_eq_true,
    ite_false, Move.displacement]
  unfold config
  congr 1
  exact (tape_push input S k b).symm

theorem push_execution (k : K) (label : Λ) (s : R) (b : Bool) (S : K → Word) :
    (WLIdentification.step (compile P input))^[2 * (S k).length + 2]
      (config P input (.push k label s b) 0 S) =
    config P input (.ready label s) 0 (Function.update S k (S k ++ [b])) := by
  have he : 2 * (S k).length + 2 = ((S k).length + 1) + 1 + (S k).length := by omega
  rw [he, Function.iterate_add_apply, scan_push P input _ _ _ _ _ _ (by omega),
    Function.iterate_add_apply, Function.iterate_one, push_at_end, back_to_ready]

theorem ready_push (l : Λ) (s : R) (k : K) (value : R → Bool) (next : Λ)
    (h : P.code l = .push k value next) (S : K → Word) :
    WLIdentification.step (compile P input) (config P input (.ready l s) 0 S) =
      config P input (.push k next s (value s)) 0 S := by
  have he := step_readonly P input (.ready l s) (.push k next s (value s)) 0 S .stay
    (by simp only [dispatch, h])
  exact he

theorem ready_push_execution (l : Λ) (s : R) (k : K) (value : R → Bool) (next : Λ)
    (h : P.code l = .push k value next) (S : K → Word) :
    (WLIdentification.step (compile P input))^[2 * (S k).length + 3]
      (config P input (.ready l s) 0 S) =
    config P input (.ready next s) 0 (Function.update S k (S k ++ [value s])) := by
  rw [show 2 * (S k).length + 3 = (2 * (S k).length + 2) + 1 by omega,
    Function.iterate_add_apply, Function.iterate_one, ready_push P input _ _ _ _ _ h,
    push_execution]

theorem pop_at_end (k : K) (label : Λ) (f : Option Bool → R) (S : K → Word) :
    WLIdentification.step (compile P input) (config P input (.pop k label f) (S k).length S) =
      config P input (.read k label f) (((S k).length : ℤ) - 1) S := by
  have hn : column S (S k).length k = none := by simp [column]
  simpa only [Move.displacement, sub_eq_add_neg] using
    step_readonly P input (.pop k label f) (.read k label f) (S k).length S .left
      (by simp only [tape_nat, dispatch, decode_symbol, hn, Option.isSome_none,
        Bool.false_eq_true, ite_false])

theorem read_empty (k : K) (label : Λ) (f : Option Bool → R) (S : K → Word) :
    WLIdentification.step (compile P input) (config P input (.read k label f) (-1) S) =
      config P input (.ready label (f none)) 0 S := by
  simpa only [Move.displacement, neg_add_cancel] using
    step_readonly P input (.read k label f) (.ready label (f none)) (-1) S .right
      (by simp only [tape_marker, dispatch, decode_symbol])

theorem tape_pop (S : K → Word) (k : K) (l : Word) (b : Bool) (h : S k = l ++ [b]) :
    tape input (Function.update S k l) =
      Function.update (tape input S) (l.length : ℤ)
        (symbol input (some (Function.update (column S l.length) k none))) := by
  let S' := Function.update S k l
  have he : Function.update S' k (S' k ++ [b]) = S := by
    funext j
    by_cases hj : j = k
    · subst j; simp [S', h]
    · simp [S', hj]
  have ht := tape_push input S' k b
  rw [he, show (S' k).length = l.length by simp [S']] at ht
  have hc : Function.update (column S l.length) k none = column S' l.length := by
    funext j
    by_cases hj : j = k
    · subst j; simp [column, S']
    · simp [column, S', hj]
  rw [hc, ← tape_nat input S' l.length, ht, Function.update_idem, Function.update_eq_self]

theorem read_last (k : K) (label : Λ) (f : Option Bool → R) (S : K → Word)
    (l : Word) (b : Bool) (h : S k = l ++ [b]) :
    WLIdentification.step (compile P input) (config P input (.read k label f) l.length S) =
      config P input (.back label (f (some b))) ((l.length : ℤ) - 1)
        (Function.update S k l) := by
  rw [step_config]
  have hc : column S l.length k = some b := by simp [column, h]
  simp only [tape_nat, dispatch, decode_symbol, hc, Move.displacement]
  unfold config
  congr 1
  exact (tape_pop input S k l b h).symm

theorem pop_execution (k : K) (label : Λ) (f : Option Bool → R) (S : K → Word) :
    (WLIdentification.step (compile P input))^[2 * (S k).length + 2]
      (config P input (.pop k label f) 0 S) =
    config P input (.ready label (f (S k).getLast?)) 0
      (Function.update S k (S k).dropLast) := by
  by_cases he : S k = []
  · have hs : Function.update S k (S k).dropLast = S := by
      rw [he, List.dropLast_nil, ← he, Function.update_eq_self]
    simp only [he, List.length_nil, mul_zero, zero_add, List.getLast?_nil]
    rw [show 2 = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]
    have hh := pop_at_end P input k label f S
    simp only [he, List.length_nil, Nat.cast_zero, zero_sub] at hh
    rw [hh, read_empty]
    rw [← he, hs]
  · let l := (S k).dropLast
    let b := (S k).getLast he
    have hs : S k = l ++ [b] := (List.dropLast_append_getLast he).symm
    have hlen : (S k).length = l.length + 1 := by rw [hs]; simp
    have heq : 2 * (S k).length + 2 = (l.length + 1) + 1 + 1 + (S k).length := by omega
    rw [heq, Function.iterate_add_apply, scan_pop P input _ _ _ _ _ (by omega),
      Function.iterate_add_apply, Function.iterate_one, pop_at_end,
      show ((S k).length : ℤ) - 1 = l.length by omega,
      Function.iterate_add_apply, Function.iterate_one, read_last P input k label f S l b hs,
      back_to_ready]
    have hg : (S k).getLast? = some b := List.getLast?_eq_some_getLast he
    rw [hg]

theorem ready_pop (l : Λ) (s : R) (k : K) (store : R → Option Bool → R) (next : Λ)
    (h : P.code l = .pop k store next) (S : K → Word) :
    WLIdentification.step (compile P input) (config P input (.ready l s) 0 S) =
      config P input (.pop k next (store s)) 0 S :=
  step_readonly P input (.ready l s) (.pop k next (store s)) 0 S .stay
    (by simp only [dispatch, h])

theorem ready_pop_execution (l : Λ) (s : R) (k : K) (store : R → Option Bool → R) (next : Λ)
    (h : P.code l = .pop k store next) (S : K → Word) :
    (WLIdentification.step (compile P input))^[2 * (S k).length + 3]
      (config P input (.ready l s) 0 S) =
    config P input (.ready next (store s (S k).getLast?)) 0
      (Function.update S k (S k).dropLast) := by
  rw [show 2 * (S k).length + 3 = (2 * (S k).length + 2) + 1 by omega,
    Function.iterate_add_apply, Function.iterate_one, ready_pop P input _ _ _ _ _ h,
    pop_execution]

end StackModel

namespace StackModel
variable {K Λ R : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R]
    (P : Program K Λ R) (input : K)

theorem initial_tape (w : Word) :
    tape input (Function.update (fun _ => []) input w) =
      Function.update (WLIdentification.initial (compile P input) w).tape (-1) (symbol input none) := by
  funext z
  by_cases hz : z = -1
  · subst z; simp
  · rw [Function.update_of_ne hz]
    unfold tape
    rw [ite_eq_right hz]
    change symbol input (some (if 0 ≤ z then column _ z.toNat else emptyData)) =
      if 0 ≤ z then (w[z.toNat]?).elim 0 (inputSymbol (compile P input)) else 0
    split_ifs with hpos
    · have hc : column (Function.update (fun _ => []) input w) z.toNat =
          match w[z.toNat]? with
          | some b => inputData input b
          | none => emptyData := by
        funext k
        by_cases hk : k = input
        · subst k; cases he : w[z.toNat]? <;> simp [column, he, inputData, emptyData]
        · cases w[z.toNat]? <;> simp [column, inputData, emptyData, hk]
      rw [hc]
      cases h : w[z.toNat]? with
      | none => exact symbol_empty input
      | some b => exact symbol_input input b
    · exact symbol_empty input

theorem initial_execution (w : Word) :
    WLIdentification.run (compile P input) w 2 = encodeConfig P input (initial P input w) := by
  let c := WLIdentification.initial (compile P input) w
  have hs : WLIdentification.step (compile P input) c =
      (⟨state .init, -1, c.tape⟩ : Configuration (compile P input)) := by
    unfold WLIdentification.step
    have hn : ¬ (c.state = 1 ∨ c.state = 2) := by
      change ¬ ((0 : Fin (Fintype.card (Phase K Λ R) + 3)) = 1 ∨ 0 = 2)
      simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two]
      omega
    rw [ite_eq_right hn]
    change (⟨state .init, (0 : ℤ) + -1, Function.update c.tape 0 (c.tape 0)⟩ :
      Configuration (compile P input)) = _
    congr 1
    exact Function.update_eq_self 0 c.tape
  have hs' : WLIdentification.step (compile P input)
      (⟨state .init, -1, c.tape⟩ : Configuration (compile P input)) =
      encodeConfig P input (initial P input w) := by
    unfold WLIdentification.step
    dsimp only
    rw [ite_eq_right (not_or_intro (state_ne_one .init) (state_ne_two .init))]
    change (let t := (compile P input).transition (state (.init : Phase K Λ R)) (c.tape (-1))
      ; Configuration.mk (M := compile P input) t.1 (-1 + t.2.2.displacement)
        (Function.update c.tape (-1) t.2.1)) = _
    rw [transition_state]
    dsimp only [dispatch, Move.displacement]
    change (⟨state (.ready P.main P.initialStore), 0,
      Function.update c.tape (-1) (symbol input none)⟩ : Configuration (compile P input)) = _
    unfold encodeConfig initial
    dsimp only
    congr 1
    exact (initial_tape P input w).symm
  change WLIdentification.step (compile P input) (WLIdentification.step (compile P input) c) = _
  rw [hs, hs']

/-- Uniform interpreter cost for one instruction, including all scans. -/
theorem instruction_execution (c : Config K Λ R) (n : ℕ)
    (hn : ∀ k, (c.stk k).length ≤ n) :
    ∃ t ≤ 2 * n + 3, (WLIdentification.step (compile P input))^[t]
      (encodeConfig P input c) = encodeConfig P input (step P c) := by
  obtain ⟨control, s, S⟩ := c
  cases control with
  | inl b => exact ⟨0, by omega, rfl⟩
  | inr l =>
    cases h : P.code l with
    | push k value next =>
      refine ⟨2 * (S k).length + 3, by have := hn k; dsimp at this; omega, ?_⟩
      simpa only [step, h, encodeConfig, config] using ready_push_execution P input l s k value next h S
    | pop k store next =>
      refine ⟨2 * (S k).length + 3, by have := hn k; dsimp at this; omega, ?_⟩
      simpa only [step, h, encodeConfig, config] using ready_pop_execution P input l s k store next h S
    | modify store next =>
      refine ⟨1, by omega, ?_⟩
      have he := step_readonly P input (.ready l s) (.ready next (store s)) 0 S .stay
        (by simp only [dispatch, h])
      simpa only [step, h, encodeConfig, config, Function.iterate_one, Move.displacement, zero_add] using he
    | branch test yes no =>
      refine ⟨1, by omega, ?_⟩
      have he := step_readonly P input (.ready l s) (.ready (if test s then yes else no) s) 0 S .stay
        (by simp only [dispatch, h])
      simpa only [step, h, encodeConfig, config, Function.iterate_one, Move.displacement, zero_add] using he
    | halt b =>
      refine ⟨1, by omega, ?_⟩
      change WLIdentification.step (compile P input) (config P input (.ready l s) 0 S) = _
      rw [step_config]
      simp only [dispatch, h, Move.displacement, add_zero]
      change (⟨(if b then 1 else 2), 0, Function.update (tape input S) 0 (tape input S 0)⟩ :
        Configuration (compile P input)) = _
      simp only [encodeConfig, step, h]
      congr 1
      exact Function.update_eq_self 0 (tape input S)

omit [Fintype K] [Fintype Λ] [Fintype R] in
theorem step_length (c : Config K Λ R) (n : ℕ) (hn : ∀ k, (c.stk k).length ≤ n) :
    ∀ k, ((step P c).stk k).length ≤ n + 1 := by
  intro k
  obtain ⟨control, s, S⟩ := c
  dsimp only at hn
  cases control with
  | inl b => exact (hn k).trans (Nat.le_succ n)
  | inr l =>
    cases h : P.code l <;> simp only [step, h]
    case push j value next =>
      by_cases hk : k = j
      · subst k; simp only [Function.update_self, List.length_append, List.length_singleton]; exact Nat.add_le_add_right (hn j) 1
      · rw [Function.update_of_ne hk]; exact (hn k).trans (Nat.le_succ n)
    case pop j store next =>
      by_cases hk : k = j
      · subst k; simp only [Function.update_self, List.length_dropLast]; have := hn j; omega
      · rw [Function.update_of_ne hk]; exact (hn k).trans (Nat.le_succ n)
    all_goals exact (hn k).trans (Nat.le_succ n)

omit [Fintype K] [Fintype Λ] [Fintype R] in
theorem run_length (w : Word) (t : ℕ) : ∀ k, ((run P input w t).stk k).length ≤ w.length + t := by
  induction t with
  | zero =>
    intro k
    by_cases hk : k = input
    · subst k; simp [run, initial]
    · simp [run, initial, hk]
  | succ t ih =>
    simpa only [run, Function.iterate_succ_apply', Nat.add_assoc] using
      step_length P (run P input w t) (w.length + t) ih

/-- The compilation preserves a real execution with a quadratic simulation bound. -/
theorem run_execution (w : Word) (t : ℕ) :
    ∃ T ≤ 2 + t * (2 * (w.length + t) + 3),
      WLIdentification.run (compile P input) w T = encodeConfig P input (run P input w t) := by
  induction t with
  | zero => exact ⟨2, by omega, initial_execution P input w⟩
  | succ t ih =>
    obtain ⟨T, hT, he⟩ := ih
    obtain ⟨s, hs, he'⟩ := instruction_execution P input (run P input w t)
      (w.length + t) (run_length P input w t)
    refine ⟨s + T, by nlinarith, ?_⟩
    unfold WLIdentification.run at he ⊢
    rw [Function.iterate_add_apply, he, he']
    simp only [run, Function.iterate_succ_apply']

/-- Only the input track is present at output; the fixed marker is at negative position. -/
theorem output_correct (c : Config K Λ R) (w : Word)
    (h : c.stk = Function.update (fun _ => []) input w) :
    Output (encodeConfig P input c) w := by
  constructor
  · intro i
    change tape input c.stk (i.val : ℤ) = _
    rw [h, initial_tape P input w, Function.update_of_ne (by omega)]
    simp only [WLIdentification.initial, Nat.cast_nonneg, ite_true, Int.toNat_natCast,
      List.getElem?_eq_getElem i.isLt, Option.elim_some]
    rfl
  · change tape input c.stk (w.length : ℤ) = 0
    rw [h, initial_tape P input w, Function.update_of_ne (by omega)]
    simp [WLIdentification.initial]

end StackModel

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.StackCommands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace StackModel

namespace Command
variable {K R : Type}

variable [DecidableEq K] {Λ : Type}

omit [DecidableEq K] in
theorem embeds_seq_left {P : Program K Λ R} {c d : Command K R} {e : Control (.seq c d) → Λ}
    {next : Λ} (h : Embeds P (.seq c d) e next) :
    Embeds P c (e ∘ Sum.inl) (e (.inr d.entry)) := by
  intro x
  rw [Function.comp_apply, h _]
  simp only [code, Instruction.map_map]
  congr 1
  funext a
  cases a <;> rfl

omit [DecidableEq K] in
theorem embeds_seq_right {P : Program K Λ R} {c d : Command K R} {e : Control (.seq c d) → Λ}
    {next : Λ} (h : Embeds P (.seq c d) e next) :
    Embeds P d (e ∘ Sum.inr) next := by
  intro x
  rw [Function.comp_apply, h _]
  simp only [code, Instruction.map_map]
  congr 1
  funext a
  cases a <;> rfl

omit [DecidableEq K] in
theorem embeds_branch_left {P : Program K Λ R} {test : R → Bool} {c d : Command K R}
    {e : Control (.branch test c d) → Λ} {next : Λ} (h : Embeds P (.branch test c d) e next) :
    Embeds P c (e ∘ Sum.inr ∘ Sum.inl) next := by
  intro x
  rw [Function.comp_apply, Function.comp_apply, h _]
  simp only [code, Instruction.map_map]
  congr 1
  funext a
  cases a <;> rfl

omit [DecidableEq K] in
theorem embeds_branch_right {P : Program K Λ R} {test : R → Bool} {c d : Command K R}
    {e : Control (.branch test c d) → Λ} {next : Λ} (h : Embeds P (.branch test c d) e next) :
    Embeds P d (e ∘ Sum.inr ∘ Sum.inr) next := by
  intro x
  rw [Function.comp_apply, Function.comp_apply, h _]
  simp only [code, Instruction.map_map]
  congr 1
  funext a
  cases a <;> rfl

omit [DecidableEq K] in
theorem embeds_while_body {P : Program K Λ R} {test : R → Bool} {c : Command K R}
    {e : Control (.while test c) → Λ} {next : Λ} (h : Embeds P (.while test c) e next) :
    Embeds P c (e ∘ Sum.inr) (e (.inl ())) := by
  intro x
  rw [Function.comp_apply, h _]
  simp only [code, Instruction.map_map]
  congr 1
  funext a
  cases a <;> rfl

/-- This induction supplies every control-flow transition, even nested loops. -/
theorem Exec.execution {c : Command K R} {s S t T n} (h : Exec c s S t T n)
    (P : Program K Λ R) (e : Control c → Λ) (next : Λ) (he : Embeds P c e next) :
    (StackModel.step P)^[n] ⟨.inr (e c.entry), s, S⟩ = ⟨.inr next, t, T⟩ := by
  induction h generalizing next with
  | skip s S => simp only [entry, Function.iterate_one, step, he _, code, Instruction.map, Option.elim_none, id_eq]
  | push k f s S => simp only [entry, Function.iterate_one, step, he _, code, Instruction.map, Option.elim_none]
  | pop k f s S => simp only [entry, Function.iterate_one, step, he _, code, Instruction.map, Option.elim_none]
  | modify f s S => simp only [entry, Function.iterate_one, step, he _, code, Instruction.map, Option.elim_none]
  | @seq c d s S t T u U a b hc hd ihc ihd =>
    rw [Function.iterate_add_apply]
    have h1 := ihc (e ∘ Sum.inl) (e (.inr d.entry)) (embeds_seq_left he)
    have h2 := ihd (e ∘ Sum.inr) next (embeds_seq_right he)
    exact h1 ▸ h2
  | @branch_true test c d s S t T n ht hc ih =>
    rw [Function.iterate_add_apply, Function.iterate_one]
    have hs : StackModel.step P ⟨.inr (e (.inl ())), s, S⟩ =
        ⟨.inr (e (.inr (.inl c.entry))), s, S⟩ := by
      simp only [step, he _, code, Instruction.map, ht, ite_true, Option.elim_some]
    rw [show (.branch test c d : Command K R).entry = .inl () from rfl, hs]
    exact ih (e ∘ Sum.inr ∘ Sum.inl) next (embeds_branch_left he)
  | @branch_false test c d s S t T n ht hd ih =>
    rw [Function.iterate_add_apply, Function.iterate_one]
    have hs : StackModel.step P ⟨.inr (e (.inl ())), s, S⟩ =
        ⟨.inr (e (.inr (.inr d.entry))), s, S⟩ := by
      simp only [step, he _, code, Instruction.map, ht, Bool.false_eq_true, ite_false, Option.elim_some]
    rw [show (.branch test c d : Command K R).entry = .inl () from rfl, hs]
    exact ih (e ∘ Sum.inr ∘ Sum.inr) next (embeds_branch_right he)
  | while_false test c s S ht =>
    simp only [entry, Function.iterate_one, step, he _, code, Instruction.map, ht,
      Bool.false_eq_true, ite_false, Option.elim_none]
  | @while_true test c s S t T u U a b ht hc hw ihc ihw =>
    rw [Function.iterate_add_apply, Function.iterate_one]
    have hs : StackModel.step P ⟨.inr (e (.inl ())), s, S⟩ =
        ⟨.inr (e (.inr c.entry)), s, S⟩ := by
      simp only [step, he _, code, Instruction.map, ht, ite_true, Option.elim_some]
    rw [show (.while test c : Command K R).entry = .inl () from rfl, hs,
      Function.iterate_add_apply]
    have h1 := ihc (e ∘ Sum.inr) (e (.inl ())) (embeds_while_body he)
    dsimp only [Function.comp_apply] at h1
    rw [h1]
    exact ihw e next he

omit [DecidableEq K] in
theorem program_embeds (c : Command K R) (s : R) : Embeds (c.program s) c some none := by
  intro x
  simp only [program]
  have he : (fun a : Option (Control c) => a.elim none some) = id := by funext a; cases a <;> rfl
  rw [he, Instruction.map_id]

theorem Exec.run {c : Command K R} {s S t T n} (h : Exec c s S t T n) (input : K) (w : Word)
    (hS : S = Function.update (fun _ => []) input w) :
    StackModel.run (c.program s) input w (n + 1) = ⟨.inl true, t, T⟩ := by
  unfold StackModel.run
  rw [Function.iterate_succ_apply']
  have he := h.execution (c.program s) some none (program_embeds c s)
  subst S
  change StackModel.step (c.program s) ((StackModel.step (c.program s))^[n]
    ⟨.inr (some c.entry), s, Function.update (fun _ => []) input w⟩) = _
  rw [he]
  rfl

end Command
end StackModel

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.FiniteRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace FiniteRefinement

/-- Only equality kernels matter; no full color trees need be stored. -/
theorem map_eq_of_kernel {A B C : Type} (f : A → B) (g : A → C) (L M : Multiset A)
    (h : ∀ a b, f a = f b → g a = g b) (he : L.map f = M.map f) : L.map g = M.map g := by
  apply Multiset.rel_eq.mp
  rw [Multiset.rel_map]
  have hr : Multiset.Rel (fun a b => f a = f b) L M := by
    rw [← Multiset.rel_map, Multiset.rel_eq]
    exact he
  exact hr.mono (fun a _ b _ hab => h a b hab)

theorem map_eq_iff_kernel {A B C : Type} (f : A → B) (g : A → C) (L M : Multiset A)
    (h : ∀ a b, f a = f b ↔ g a = g b) : L.map f = M.map f ↔ L.map g = M.map g :=
  ⟨map_eq_of_kernel f g L M (fun a b => (h a b).mp),
    map_eq_of_kernel g f L M (fun a b => (h a b).mpr)⟩

variable {A : Type} [Fintype A] {C : ℕ → Type} (color : (s : ℕ) → A → C s)

theorem kernel_eq_iff (s t : ℕ) : kernel color s = kernel color t ↔ KernelEq color s t := by
  classical
  constructor
  · intro h a b
    have := Finset.ext_iff.mp h (a, b)
    simpa only [kernel, Finset.mem_filter, Finset.mem_univ, true_and] using this
  · intro h
    ext ab
    simp only [kernel, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h ab.1 ab.2

theorem kernel_step_subset (h : ∀ s a b, color (s+1) a = color (s+1) b → color s a = color s b)
    (s : ℕ) : kernel color (s + 1) ⊆ kernel color s := by
  classical
  intro ab hab
  simp only [kernel, Finset.mem_filter, Finset.mem_univ, true_and] at hab ⊢
  exact h s ab.1 ab.2 hab

/-- A descending Boolean relation on N objects must settle by N² rounds.
This coarse bound avoids an implicit unit-cost operation on full color names. -/
theorem exists_adjacent (h : ∀ s a b, color (s+1) a = color (s+1) b → color s a = color s b) :
    ∃ s ≤ Fintype.card A ^ 2, KernelEq color s (s+1) := by
  classical
  let N := Fintype.card A ^ 2
  by_contra hn
  have hstrict (s : ℕ) (hs : s ≤ N) : (kernel color (s + 1)).card < (kernel color s).card := by
    apply Finset.card_lt_card
    exact (kernel_step_subset color h s).ssubset_of_ne (by
      intro he
      exact hn ⟨s, hs, (kernel_eq_iff color s (s+1)).mp he.symm⟩)
  have hsum (s : ℕ) (hs : s ≤ N + 1) : (kernel color s).card + s ≤ (kernel color 0).card := by
    induction s with
    | zero => simp
    | succ s ih => have hlt := hstrict s (by omega); have hi := ih (by omega); omega
  have hc : (kernel color 0).card ≤ N := by
    calc
      _ ≤ Fintype.card (A × A) := Finset.card_le_univ _
      _ = N := by simp [N, pow_two]
  have := hsum (N+1) (by omega)
  omega

omit [Fintype A] in
theorem KernelEq.refl (s : ℕ) : KernelEq color s s := fun _ _ => Iff.rfl

omit [Fintype A] in
theorem KernelEq.trans {s t u : ℕ} (h : KernelEq color s t) (h' : KernelEq color t u) :
    KernelEq color s u := fun a b => (h a b).trans (h' a b)

variable (hrefine : ∀ s a b, color (s+1) a = color (s+1) b → color s a = color s b)
    (hstep : ∀ s t, KernelEq color s t → KernelEq color (s+1) (t+1))

omit [Fintype A] in
include hrefine in
theorem earlier {s t : ℕ} (hst : s ≤ t) (a b : A) (h : color t a = color t b) :
    color s a = color s b := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t ht ih => exact ih (hrefine t a b h)

omit [Fintype A] in
include hstep in
theorem stable_tail {s : ℕ} (h : KernelEq color s (s+1)) (u : ℕ) :
    KernelEq color s (s+u) := by
  induction u with
  | zero => exact KernelEq.refl color s
  | succ u ih =>
    have ht : KernelEq color (s+1) (s+u+1) := hstep s (s+u) ih
    exact (h.trans color ht)

include hrefine hstep in
/-- The one stored Boolean relation after the explicit cutoff decides equality
at every refinement depth, including all later rounds. -/
theorem cutoff (a b : A) (s : ℕ) :
    color (Fintype.card A ^ 2) a = color (Fintype.card A ^ 2) b → color s a = color s b := by
  intro he
  let N := Fintype.card A ^ 2
  obtain ⟨t, ht, hstable⟩ := exists_adjacent color hrefine
  by_cases hs : s ≤ N
  · exact earlier color hrefine hs a b he
  · have hte := earlier color hrefine ht a b he
    have hts : t ≤ s := by omega
    have htail := stable_tail color hstep hstable (s-t)
    rw [Nat.add_sub_of_le hts] at htail
    exact (htail a b).mp hte

include hrefine hstep in
theorem histogram_cutoff (L M : Multiset A) :
    (∀ s, L.map (color s) = M.map (color s)) ↔
      L.map (color (Fintype.card A ^ 2)) = M.map (color (Fintype.card A ^ 2)) := by
  constructor
  · exact fun h => h _
  · intro h s
    exact map_eq_of_kernel _ _ L M (fun a b => cutoff color hrefine hstep a b s) h

omit [Fintype A] in
/-- Equality of replacement-vector histograms is determined by the old kernel,
so the same stored relation supports ordinary and joint tuple updates. -/
theorem successor_kernel {I : Type} (N : A → Multiset (I → A))
    (hupdate : ∀ s a b, color (s+1) a = color (s+1) b ↔
      color s a = color s b ∧
        (N a).map (fun v i => color s (v i)) = (N b).map (fun v i => color s (v i))) :
    ∀ s t, KernelEq color s t → KernelEq color (s+1) (t+1) := by
  intro s t h a b
  rw [hupdate, hupdate, h a b]
  apply and_congr Iff.rfl
  apply map_eq_iff_kernel
  intro v w
  simp only [funext_iff]
  exact forall_congr' (fun i => h (v i) (w i))

end FiniteRefinement
namespace FiniteRefinement

theorem successor_kernel_scalar {A : Type} {C : ℕ → Type}
    (color : (s : ℕ) → A → C s) (N : A → Multiset A)
    (hupdate : ∀ s a b, color (s+1) a = color (s+1) b ↔
      color s a = color s b ∧ (N a).map (color s) = (N b).map (color s)) :
    ∀ s t, KernelEq color s t → KernelEq color (s+1) (t+1) := by
  intro s t h a b
  rw [hupdate, hupdate, h a b]
  apply and_congr Iff.rfl
  exact map_eq_iff_kernel _ _ _ _ h

end FiniteRefinement

namespace FiniteWL

theorem neighbor_update (G H : Graph) (s : ℕ) (a b : Fin G.order ⊕ Fin H.order) :
    neighbor G H (s+1) a = neighbor G H (s+1) b ↔
      neighbor G H s a = neighbor G H s b ∧
        (neighbors G H a).map (neighbor G H s) = (neighbors G H b).map (neighbor G H s) := by
  cases a <;> cases b <;>
    dsimp only [neighbor, neighborColor, neighbors, Sum.elim] <;>
    simp only [Multiset.map_map, Function.comp_def, Sum.elim_inl, Sum.elim_inr] <;>
    exact Prod.ext_iff

theorem neighbor_cutoff (G H : Graph) :
    (∀ s, neighborHistogram G s = neighborHistogram H s) ↔
    neighborHistogram G ((G.order + H.order)^2) = neighborHistogram H ((G.order+H.order)^2) := by
  have hr s a b (h : neighbor G H (s+1) a = neighbor G H (s+1) b) :=
    ((neighbor_update G H s a b).mp h).1
  have hs := FiniteRefinement.successor_kernel_scalar (neighbor G H) (neighbors G H)
    (neighbor_update G H)
  have he := FiniteRefinement.histogram_cutoff (neighbor G H) hr hs
    ((Finset.univ : Finset (Fin G.order)).val.map Sum.inl)
    ((Finset.univ : Finset (Fin H.order)).val.map Sum.inr)
  have hc : Fintype.card (Fin G.order ⊕ Fin H.order) = G.order + H.order := by simp
  rw [hc] at he
  simpa only [Multiset.map_map, Function.comp_def, neighbor, Sum.elim_inl,
    Sum.elim_inr, neighborHistogram] using he

theorem tuple_update (G H : Graph) (k s : ℕ)
    (a b : (Fin k → Fin G.order) ⊕ (Fin k → Fin H.order)) :
    tuple G H k (s+1) a = tuple G H k (s+1) b ↔
      tuple G H k s a = tuple G H k s b ∧
        (vectors G H k a).map (fun v i => tuple G H k s (v i)) =
          (vectors G H k b).map (fun v i => tuple G H k s (v i)) := by
  cases a <;> cases b <;>
    dsimp only [tuple, tupleColor, vectors, Sum.elim] <;>
    simp only [Multiset.map_map, Function.comp_def] <;>
    exact Prod.ext_iff

theorem tuple_cutoff (G H : Graph) (k : ℕ) :
    (∀ s, tupleHistogram G k s = tupleHistogram H k s) ↔
    tupleHistogram G k ((G.order^k+H.order^k)^2) = tupleHistogram H k ((G.order^k+H.order^k)^2) := by
  have hr s a b (h : tuple G H k (s+1) a = tuple G H k (s+1) b) :=
    ((tuple_update G H k s a b).mp h).1
  have hs := FiniteRefinement.successor_kernel (tuple G H k) (vectors G H k)
    (tuple_update G H k)
  have he := FiniteRefinement.histogram_cutoff (tuple G H k) hr hs
    ((Finset.univ : Finset (Fin k → Fin G.order)).val.map Sum.inl)
    ((Finset.univ : Finset (Fin k → Fin H.order)).val.map Sum.inr)
  have hc : Fintype.card ((Fin k → Fin G.order) ⊕ (Fin k → Fin H.order)) =
      G.order ^ k + H.order ^ k := by simp
  rw [hc] at he
  simpa only [Multiset.map_map, Function.comp_def, tuple, Sum.elim_inl,
    Sum.elim_inr, tupleHistogram] using he

/-- Explicit finite stopping criteria, retaining neighbor refinement precisely at k=1. -/
theorem equivalent_cutoff (G H : Graph) (k : ℕ) :
    Equivalent k G H ↔
      if k = 1 then
        neighborHistogram G ((G.order+H.order)^2) = neighborHistogram H ((G.order+H.order)^2)
      else tupleHistogram G k ((G.order^k+H.order^k)^2) =
        tupleHistogram H k ((G.order^k+H.order^k)^2) := by
  unfold Equivalent
  split_ifs
  · exact neighbor_cutoff G H
  · exact tuple_cutoff G H k

end FiniteWL
namespace FiniteRefinement

/-- Image multiset equality is checked by finite class counts; there is no
unit-cost comparison of recursively expanded color trees. -/
theorem map_eq_iff_counts {A C : Type} [DecidableEq C] (f : A → C) (L M : Multiset A) :
    L.map f = M.map f ↔ ∀ a, L.countP (fun b => f b = f a) = M.countP (fun b => f b = f a) := by
  constructor
  · intro h a
    have he := congrArg (Multiset.count (f a)) h
    simpa only [Multiset.count_map, ← Multiset.countP_eq_card_filter, eq_comm] using he
  · intro h
    apply Multiset.ext.mpr
    intro c
    by_cases hc : ∃ a, f a = c
    · obtain ⟨a, rfl⟩ := hc
      simpa only [Multiset.count_map, ← Multiset.countP_eq_card_filter, eq_comm] using h a
    · have hL : c ∉ L.map f := by simpa only [Multiset.mem_map, not_exists, not_and] using
        (fun a (_ : a ∈ L) ha => hc ⟨a, ha⟩)
      have hM : c ∉ M.map f := by simpa only [Multiset.mem_map, not_exists, not_and] using
        (fun a (_ : a ∈ M) ha => hc ⟨a, ha⟩)
      rw [Multiset.count_eq_zero_of_notMem hL, Multiset.count_eq_zero_of_notMem hM]

variable {A I : Type} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

omit [DecidableEq A] in
/-- Reusable correctness of a table update, including the joint vector test. -/
theorem tableStep_correct {C D : Type} [DecidableEq C] (old : A → C) (next : A → D)
    (N : A → Multiset (I → A)) (R : A → A → Bool)
    (hR : ∀ a b, R a b = true ↔ old a = old b)
    (hnext : ∀ a b, next a = next b ↔ old a = old b ∧
      (N a).map (fun v i => old (v i)) = (N b).map (fun v i => old (v i))) (a b : A) :
    tableStep N R a b = true ↔ next a = next b := by
  rw [hnext]
  simp only [tableStep, Bool.and_eq_true, decide_eq_true_eq, hR]
  apply and_congr Iff.rfl
  rw [map_eq_iff_counts]
  have hm (w v : I → A) : vectorMatch R w v = true ↔
      (fun i => old (w i)) = (fun i => old (v i)) := by
    simp only [vectorMatch, decide_eq_true_eq, funext_iff]
    exact forall_congr' (fun i => hR (w i) (v i))
  simp only [hm]

omit [DecidableEq A] in
theorem table_correct {C : ℕ → Type} [∀ s, DecidableEq (C s)]
    (color : (s : ℕ) → A → C s) (N : A → Multiset (I → A))
    (hnext : ∀ s a b, color (s+1) a = color (s+1) b ↔ color s a = color s b ∧
      (N a).map (fun v i => color s (v i)) = (N b).map (fun v i => color s (v i)))
    (initial : A → A → Bool) (hinit : ∀ a b, initial a b = true ↔ color 0 a = color 0 b)
    (s : ℕ) (a b : A) : table N initial s a b = true ↔ color s a = color s b := by
  induction s generalizing a b with
  | zero => exact hinit a b
  | succ s ih =>
    simp only [table, Function.iterate_succ_apply']
    exact tableStep_correct (color s) (color (s+1)) N _ (fun a b => ih (a:=a) (b:=b)) (hnext s) a b

end FiniteRefinement

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.WordCommands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace StackModel
namespace Command
variable {K : Type} [DecidableEq K]

/-- Tail traversal is an actual structured loop, not a host-language iteration. -/
theorem drain_exec (k : K) (body : Command K (Option Bool))
    (S : K → Word) (s : Option Bool) (f : Bool → (K → Word) → (K → Word)) (c : ℕ)
    (hbody : ∀ b T, ∃ t, Exec body (some b) T t (f b T) c)
    (hpres : ∀ b T, f b T k = T k) :
    ∃ n ≤ (c + 2) * (S k).length + 2,
      Exec (drain k body) s S none
        ((S k).reverse.foldl (fun T b => f b (Function.update T k (T k).dropLast))
          S) n := by
  generalize hw : S k = w
  induction w using List.reverseRecOn generalizing S s with
  | nil =>
    have hu : Function.update S k [] = S := by
      funext x
      by_cases hx : x = k <;> simp [hx, hw]
    refine ⟨2, by simp, ?_⟩
    simp only [List.reverse_nil, List.foldl_nil]
    have hp : Exec (read k) s S none S 1 := by
      simpa only [read, hw, List.getLast?_nil, List.dropLast_nil, hu] using
        (Exec.pop k (fun _ b => b) s S)
    exact .seq hp (.while_false _ _ _ _ rfl)
  | append_singleton w b ih =>
    let T := Function.update S k w
    have hT : T k = w := by simp [T]
    obtain ⟨t, hb⟩ := hbody b T
    have hU : f b T k = w := (hpres _ _).trans hT
    obtain ⟨n, hn, he⟩ := ih (f b T) t hU
    dsimp only [drain] at he
    cases he with
    | seq hr hwhile =>
      cases hr
      rename_i nr
      have hp : Exec (read k) s S (some b) T 1 := by
        simpa only [read, hw, List.getLast?_append, List.getLast?_singleton,
          Option.some_or, List.dropLast_append_cons, List.dropLast_singleton, List.append_nil] using
          (Exec.pop k (fun _ b => b) s S)
      refine ⟨nr + c + 3, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton] at *
        nlinarith
      · have hh := Exec.seq hp (Exec.while_true (by rfl) (Exec.seq hb
            (Exec.pop k (fun _ b => b) t (f b T))) hwhile)
        convert hh using 1 <;> try omega
        all_goals try simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
          List.foldl_cons, hw, List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, T]
        all_goals rfl

theorem pushMany_exec (ks : List K) (hks : ks.Nodup) (b : Bool) (S : K → Word) :
    Exec (pushMany ks) (some b) S (some b) (appendMany ks b S) (ks.length + 1) := by
  induction ks generalizing S with
  | nil =>
    have h : appendMany [] b S = S := by funext k; simp [appendMany]
    simpa only [pushMany, List.foldr_nil, List.length_nil, Nat.zero_add, h] using Exec.skip (some b) S
  | cons k ks ih =>
    have hi := ih (List.nodup_cons.mp hks).2 (Function.update S k (S k ++ [b]))
    have he := Exec.seq (Exec.push k (fun x : Option Bool => x.getD false) (some b) S) hi
    have hstate : appendMany ks b (Function.update S k (S k ++ [b])) =
        appendMany (k :: ks) b S := by
      funext x
      by_cases hx : x = k
      · subst x
        simp [appendMany, (List.nodup_cons.mp hks).1]
      · simp [appendMany, hx]
    simpa only [pushMany, List.foldr_cons, List.length_cons, Nat.add_assoc, hstate] using he

theorem fan_fold (a : K) (ks : List K) (ha : a ∉ ks) (S : K → Word) :
    (S a).reverse.foldl (fun T b => appendMany ks b (Function.update T a (T a).dropLast)) S =
      fanEffect a ks S := by
  generalize hw : S a = w
  induction w using List.reverseRecOn generalizing S with
  | nil =>
    simp only [List.reverse_nil, List.foldl_nil]
    funext x
    by_cases hx : x = a <;> simp [fanEffect, hx, hw]
  | append_singleton w b ih =>
    let T := appendMany ks b (Function.update S a w)
    have hT : T a = w := by simp [T, appendMany, ha]
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append, List.foldl_cons,
      hw, List.dropLast_append_cons, List.dropLast_singleton, List.append_nil]
    change w.reverse.foldl _ T = _
    rw [ih T hT]
    funext x
    by_cases hx : x = a
    · simp [fanEffect, hx]
    · by_cases hk : x ∈ ks <;>
        simp [fanEffect, hx, T, appendMany, hw, ha, hk, List.reverse_append, List.append_assoc]

theorem fan_exec (a : K) (ks : List K) (hks : ks.Nodup) (ha : a ∉ ks)
    (s : Option Bool) (S : K → Word) :
    ∃ n ≤ (ks.length + 3) * (S a).length + 2,
      Exec (drain a (pushMany ks)) s S none (fanEffect a ks S) n := by
  obtain ⟨n, hn, he⟩ := drain_exec a (pushMany ks) S s (appendMany ks) (ks.length + 1)
    (fun b T => ⟨some b, pushMany_exec ks hks b T⟩)
    (by intro b T; simp [appendMany, ha])
  refine ⟨n, by omega, ?_⟩
  rwa [fan_fold a ks ha S] at he

theorem clear_exec (a : K) (s : Option Bool) (S : K → Word) :
    ∃ n ≤ 3 * (S a).length + 2,
      Exec (clear a) s S none (Function.update S a []) n := by
  have hf : fanEffect a [] S = Function.update S a [] := by
    funext k; by_cases h : k = a <;> simp [fanEffect, h]
  simpa only [clear, pushMany, List.foldr_nil, List.length_nil, Nat.zero_add, hf] using
    fan_exec a [] (by simp) (by simp) s S

theorem move_exec (a b : K) (hab : a ≠ b) (s : Option Bool) (S : K → Word) :
    ∃ n ≤ 4 * (S a).length + 2,
      Exec (drain a (pushMany [b])) s S none
        (Function.update (Function.update S a []) b (S b ++ (S a).reverse)) n := by
  have hf : fanEffect a [b] S = Function.update (Function.update S a []) b
      (S b ++ (S a).reverse) := by
    funext k
    by_cases hb : k = b
    · simp [fanEffect, hb, hab.symm]
    · by_cases ha : k = a <;> simp [fanEffect, ha, hb, hab]
  simpa only [List.length_singleton, hf] using fan_exec a [b] (by simp) (by simp [hab]) s S

theorem copy_exec (a b tmp : K) (hab : a ≠ b) (hat : a ≠ tmp) (hbt : b ≠ tmp)
    (s : Option Bool) (S : K → Word) :
    ∃ n ≤ 3 * (S b).length + 3 * (S tmp).length + 9 * (S a).length + 8,
      Exec (copy a b tmp) s S none (Function.update (Function.update S b (S a)) tmp []) n := by
  obtain ⟨n₁, hn₁, he₁⟩ := clear_exec b s S
  let S₁ := Function.update S b []
  obtain ⟨n₂, hn₂, he₂⟩ := clear_exec tmp none S₁
  let S₂ := Function.update S₁ tmp []
  obtain ⟨n₃, hn₃, he₃⟩ := move_exec a tmp hat none S₂
  let S₃ := Function.update (Function.update S₂ a []) tmp (S₂ tmp ++ (S₂ a).reverse)
  obtain ⟨n₄, hn₄, he₄⟩ := fan_exec tmp [a,b] (by simp [hab]) (by simp [hat.symm,hbt.symm]) none S₃
  have hf : fanEffect tmp [a,b] S₃ = Function.update (Function.update S b (S a)) tmp [] := by
    funext k
    by_cases ht : k = tmp
    · simp [fanEffect, ht]
    · by_cases ha : k = a
      · subst k
        simp [fanEffect, hat, S₃, S₂, S₁, hab]
      · by_cases hb : k = b
        · subst k
          simp [fanEffect, hbt, hab.symm, S₃, S₂, S₁, hat, hab]
        · simp [fanEffect, ht, ha, hb, S₃, S₂, S₁]
  refine ⟨n₄ + n₃ + n₂ + n₁, ?_, ?_⟩
  · simp only [S₁, S₂, S₃, Function.update_self, Function.update_of_ne hat,
      Function.update_of_ne hab, Function.update_of_ne hbt.symm, List.nil_append,
      List.length_reverse, List.length_cons, List.length_nil] at hn₂ hn₃ hn₄
    omega
  · exact Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (hf ▸ he₄)))

end Command
end StackModel

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.WordExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace StackModel.Command
variable {K : Type} [DecidableEq K]

/-- General indexed captured-count iteration, preserving an arbitrary counter
prefix during each body execution. -/
theorem drain_indexed (body : Command K (Option Bool)) (counter : K)
    (X : ℕ → K → Word) (hX : ∀ i, X i counter = []) (cost start : ℕ) (w : Word)
    (hbody : ∀ i, start ≤ i → i < start+w.length → ∀ v s,
      ∃ t ≤ cost, Exec body s (Function.update (X i) counter v) none
        (Function.update (X (i+1)) counter v) t) (s : Option Bool) :
    ∃ n ≤ (cost+2)*w.length+2,
      Exec (drain counter body) s (Function.update (X start) counter w) none
        (X (start+w.length)) n := by
  induction w using List.reverseRecOn generalizing start s with
  | nil =>
    have hu : Function.update (X start) counter [] = X start := by
      rw [← hX start]; exact Function.update_eq_self _ _
    have hr : Exec (StackModel.Command.read counter) s (X start) none (X start) 1 := by
      simpa only [StackModel.Command.read, hX, List.getLast?_nil, List.dropLast_nil,
        hu] using Exec.pop counter (fun _ b => b) s (X start)
    refine ⟨2, by simp, ?_⟩
    simpa only [drain, List.length_nil, Nat.add_zero, hu] using
      Exec.seq hr (Exec.while_false Option.isSome (.seq body (StackModel.Command.read counter)) none (X start) rfl)
  | append_singleton w b ih =>
    obtain ⟨a, ha, hea⟩ := hbody start le_rfl (by simp) w (some b)
    obtain ⟨n, hn, hen⟩ := ih (start+1) (by
      intro i hi hj v s
      apply hbody i (by omega) (by simp only [List.length_append, List.length_singleton]; omega) v s) none
    have hr : Exec (StackModel.Command.read counter) s
        (Function.update (X start) counter (w++[b])) (some b)
        (Function.update (X start) counter w) 1 := by
      simpa only [StackModel.Command.read, Function.update_self, List.getLast?_append,
        List.getLast?_singleton, Option.some_or, List.dropLast_append_cons,
        List.dropLast_singleton, List.append_nil, Function.update_idem] using
        Exec.pop counter (fun _ b => b) s (Function.update (X start) counter (w++[b]))
    dsimp only [drain] at hen
    cases hen with
    | seq hpop hwhile =>
      cases hpop
      rename_i t
      have hex := Exec.seq hr (Exec.while_true (by rfl)
        (Exec.seq hea (Exec.pop counter (fun _ b => b) none (Function.update (X (start+1)) counter w))) hwhile)
      refine ⟨t+1+(a+1+1), ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton] at *
        nlinarith
      · have hl : start+1+w.length = start+(w++[b]).length := by simp; omega
        simpa only [drain, StackModel.Command.read, hl, Nat.add_assoc] using hex

end StackModel.Command
namespace WordExpressions.Expr
open StackModel.Command

theorem Clean.mono {S b c} (h : Clean S b) (hbc : b ≤ c) : Clean S c :=
  fun _ hi => h _ (hbc.trans hi)

theorem update_clean {S b w} (h : Clean S b) : Clean (Function.update S b w) (b+1) :=
  (h.mono (by omega)).update (by omega)

theorem correct_var {n} (i : Fin n) : Correct (.var i) := by
  intro B S env out base ho he hc hb h s
  obtain ⟨t, ht, hex⟩ := copy_exec (env i) out base (he i).2 (by have := (he i).1; omega)
    (by omega) s S
  have htemp := hc base le_rfl
  have hu : Function.update (Function.update S out (S (env i))) base [] =
      Function.update S out (S (env i)) := by
    apply Function.update_eq_self_iff.mpr
    simp only [Function.update_of_ne (by omega : base ≠ out), htemp]
  refine ⟨t, ?_, ?_⟩
  · simp only [htemp, List.length_nil, mul_zero, add_zero] at ht
    exact ht.trans (by dsimp only [cost]; dsimp only [Bounded, Function.comp_apply] at h; omega)
  · simpa only [code, eval, Function.comp_apply, hu] using hex

theorem correct_nil {n} : Correct (.nil : Expr n) := by
  intro B S env out base ho he hc hb _ s
  obtain ⟨t, ht, hex⟩ := clear_exec out s S
  exact ⟨t, ht.trans (by dsimp only [cost]; omega), hex⟩

theorem correct_snoc {n} {e : Expr n} (he : Correct e) (b : Bool) : Correct (.snoc e b) := by
  intro B S env out base ho henv hc hb h s
  obtain ⟨t, ht, hex⟩ := he B S env out base ho henv hc hb h.1 s
  have hx := Exec.seq hex (Exec.push out (fun _ => b) none (Function.update S out (e.eval (S ∘ env))))
  refine ⟨1+t, by dsimp only [cost]; omega, ?_⟩
  simpa only [code, eval, Function.update_self, Function.update_idem] using hx

theorem correct_drop {n} {e : Expr n} (he : Correct e) : Correct (.drop e) := by
  intro B S env out base ho henv hc hb h s
  obtain ⟨t, ht, hex⟩ := he B S env out base ho henv hc hb h s
  have hx := Exec.seq hex (Exec.pop out (fun _ _ => none) none (Function.update S out (e.eval (S ∘ env))))
  refine ⟨1+t, by dsimp only [cost]; omega, ?_⟩
  simpa only [code, eval, Function.update_self, Function.update_idem] using hx

/-- An allocated temporary is invisible to the immutable environment. -/
theorem env_update {n} (S : ℕ → Word) (env : Fin n → ℕ) (base : ℕ) (w : Word)
    (h : ∀ i, env i < base) : Function.update S base w ∘ env = S ∘ env := by
  funext i
  exact Function.update_of_ne (by have := h i; omega) _ _

theorem snoc_env_update {n} (S : ℕ → Word) (env : Fin n → ℕ) (base : ℕ) (w : Word)
    (h : ∀ i, env i < base) : Function.update S base w ∘ Fin.snoc env base = Fin.snoc (S ∘ env) w := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp only [Function.comp_apply, Fin.snoc_castSucc]
    exact Function.update_of_ne (by have := h j; omega) _ _

theorem correct_bind {n} {e : Expr n} {f : Expr (n+1)} (he : Correct e) (hf : Correct f) :
    Correct (.bind e f) := by
  intro B S env out base ho henv hc hb h s
  have hb0 := hc base le_rfl
  obtain ⟨a, ha, hea⟩ := he B S env base (base+1) (by omega)
    (fun i => ⟨by have := (henv i).1; omega, by have := (henv i).1; omega⟩)
    (hc.mono (by omega)) (by simp only [hb0, List.length_nil]; omega) h.1 s
  let v := e.eval (S ∘ env)
  let T := Function.update S base v
  have henv' : ∀ i : Fin (n+1), (Fin.snoc env base : Fin (n+1) → ℕ) i < base+1 ∧ (Fin.snoc env base : Fin (n+1) → ℕ) i ≠ out := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]; omega
    · simp only [Fin.snoc_castSucc]; have := henv j; omega
  have henvEq : T ∘ Fin.snoc env base = Fin.snoc (S ∘ env) v :=
    snoc_env_update S env base v (fun i => (henv i).1)
  have hout : T out = S out := Function.update_of_ne (by omega) _ _
  obtain ⟨b, hb', heb⟩ := hf B T (Fin.snoc env base) out (base+1) (by omega) henv'
    (update_clean hc) (hout ▸ hb) (by rw [henvEq]; exact h.2) none
  obtain ⟨c, hc', hec⟩ := clear_exec base none (Function.update T out (f.eval (T ∘ Fin.snoc env base)))
  have hv := e.length_le (S ∘ env) B h.1
  have hlen : (Function.update T out (f.eval (T ∘ Fin.snoc env base)) base).length ≤ B := by
    rw [Function.update_of_ne (by omega)]
    simpa only [T, Function.update_self] using hv
  have hlast : Function.update (Function.update T out (f.eval (T ∘ Fin.snoc env base))) base [] =
      Function.update S out ((Expr.bind e f).eval (S ∘ env)) := by
    rw [Function.update_comm (by omega : out ≠ base), Function.update_idem, ← hb0, Function.update_eq_self]
    rw [henvEq]
    rfl
  refine ⟨c+b+a, ?_, ?_⟩
  · dsimp only [cost]; omega
  · simpa only [code, hlast, Nat.add_assoc] using Exec.seq hea (Exec.seq heb hec)

end WordExpressions.Expr

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.ExpressionCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions.Expr
open StackModel.Command

theorem correct_cases {n} {e p q r : Expr n} (he : Correct e) (hp : Correct p)
    (hq : Correct q) (hr : Correct r) : Correct (.cases e p q r) := by
  intro B S env out base ho henv hc hb h s
  have hb0 := hc base le_rfl
  obtain ⟨a, ha, hea⟩ := he B S env base (base+1) (by omega)
    (fun i => ⟨by have := (henv i).1; omega, by have := (henv i).1; omega⟩)
    (hc.mono (by omega)) (by simp only [hb0, List.length_nil]; omega) h.1 s
  let v := e.eval (S ∘ env)
  let T := Function.update S base v.dropLast
  have hread : Exec (StackModel.Command.read base) none (Function.update S base v)
      v.getLast? T 1 := by
    simpa only [StackModel.Command.read, Function.update_self, Function.update_idem, T] using
      Exec.pop base (fun _ b => b) none (Function.update S base v)
  have henv' : ∀ i, env i < base+1 ∧ env i ≠ out := by
    intro i; have := henv i; omega
  have henvEq : T ∘ env = S ∘ env := env_update S env base _ (fun i => (henv i).1)
  have hout : T out = S out := Function.update_of_ne (by omega) _ _
  have hex : ∃ b ≤ max (p.cost B) (max (q.cost B) (r.cost B))+2,
      Exec (.branch Option.isSome
        (.branch (fun x : Option Bool => x.getD false) (r.code env out (base+1)) (q.code env out (base+1)))
        (p.code env out (base+1))) v.getLast? T none
        (Function.update T out ((Expr.cases e p q r).eval (S ∘ env))) b := by
    cases hv : v.getLast? with
    | none =>
      obtain ⟨b, hb', heb⟩ := hp B T env out (base+1) (by omega) henv' (update_clean hc)
        (hout ▸ hb) (by rw [henvEq]; simpa only [show (e.eval (S ∘ env)).getLast? = none from hv] using h.2) none
      refine ⟨b+1, by have := le_max_left (p.cost B) (max (q.cost B) (r.cost B)); omega, ?_⟩
      simpa only [eval, show (e.eval (S ∘ env)).getLast? = none from hv, henvEq] using
        (Exec.branch_false (c := .branch (fun x : Option Bool => x.getD false)
          (r.code env out (base+1)) (q.code env out (base+1))) (test := Option.isSome) (by rfl) heb)
    | some b => cases b with
      | false =>
        obtain ⟨b, hb', heb⟩ := hq B T env out (base+1) (by omega) henv' (update_clean hc)
          (hout ▸ hb) (by rw [henvEq]; simpa only [show (e.eval (S ∘ env)).getLast? = some false from hv] using h.2) (some false)
        have hh := Exec.branch_true (test := Option.isSome) (d := p.code env out (base+1)) (by rfl)
          (Exec.branch_false (test := fun x : Option Bool => x.getD false) (c := r.code env out (base+1)) (by rfl) heb)
        refine ⟨b+2, ?_, ?_⟩
        · have := (le_max_left (q.cost B) (r.cost B)).trans (le_max_right (p.cost B) _); omega
        · simpa only [eval, show (e.eval (S ∘ env)).getLast? = some false from hv,
            henvEq, Nat.add_assoc, Nat.reduceAdd] using hh
      | true =>
        obtain ⟨b, hb', heb⟩ := hr B T env out (base+1) (by omega) henv' (update_clean hc)
          (hout ▸ hb) (by rw [henvEq]; simpa only [show (e.eval (S ∘ env)).getLast? = some true from hv] using h.2) (some true)
        have hh := Exec.branch_true (test := Option.isSome) (d := p.code env out (base+1)) (by rfl)
          (Exec.branch_true (test := fun x : Option Bool => x.getD false) (d := q.code env out (base+1)) (by rfl) heb)
        refine ⟨b+2, ?_, ?_⟩
        · have := (le_max_right (q.cost B) (r.cost B)).trans (le_max_right (p.cost B) _); omega
        · simpa only [eval, show (e.eval (S ∘ env)).getLast? = some true from hv,
            henvEq, Nat.add_assoc, Nat.reduceAdd] using hh
  obtain ⟨b, hb', heb⟩ := hex
  obtain ⟨c, hc', hec⟩ := clear_exec base none (Function.update T out ((Expr.cases e p q r).eval (S ∘ env)))
  have hv := e.length_le (S ∘ env) B h.1
  have hlen : (Function.update T out ((Expr.cases e p q r).eval (S ∘ env)) base).length ≤ B := by
    rw [Function.update_of_ne (by omega)]
    simp only [T, Function.update_self]
    exact (List.dropLast_sublist v).length_le.trans hv
  have hlast : Function.update (Function.update T out ((Expr.cases e p q r).eval (S ∘ env))) base [] =
      Function.update S out ((Expr.cases e p q r).eval (S ∘ env)) := by
    rw [Function.update_comm (by omega : out ≠ base), Function.update_idem, ← hb0, Function.update_eq_self]
  refine ⟨c+b+1+a, ?_, ?_⟩
  · dsimp only [cost]; omega
  · simpa only [code, hlast, Nat.add_assoc] using Exec.seq hea (Exec.seq hread (Exec.seq heb hec))

end WordExpressions.Expr
namespace WordExpressions.Expr
open StackModel.Command

theorem correct_loop {n} {c a : Expr n} {f : Expr (n+2)} (hcorr : Correct c)
    (haCorr : Correct a) (hf : Correct f) : Correct (.loop c a f) := by
  intro B S env out base ho henv hc hb h s
  let ec := c.eval (S ∘ env)
  let stage := stages f.eval (S ∘ env) (a.eval (S ∘ env))
  have hb0 := hc base le_rfl
  have henvlo : ∀ i, env i < base := fun i => (henv i).1
  have hcB : ec.length ≤ B := c.length_le _ _ h.1
  have hstage : ∀ i ≤ ec.length, (stage i).length ≤ B := by
    intro i hi
    cases i with
    | zero => exact a.length_le _ _ h.2.1
    | succ i => exact f.length_le _ _ (h.2.2 i (by change i < ec.length; omega))
  obtain ⟨u, hu, heu⟩ := hcorr B S env base (base+1) (by omega)
    (fun i => ⟨by have := henvlo i; omega, by have := henvlo i; omega⟩)
    (hc.mono (by omega)) (by simp only [hb0, List.length_nil]; omega) h.1 s
  let S₁ := Function.update S base ec
  have hS₁env : S₁ ∘ env = S ∘ env := env_update S env base ec henvlo
  have hS₁out : S₁ out = S out := Function.update_of_ne (by omega) _ _
  obtain ⟨v, hv, hev⟩ := haCorr B S₁ env out (base+1) (by omega)
    (fun i => ⟨by have := henvlo i; omega, (henv i).2⟩)
    (update_clean hc) (hS₁out ▸ hb) (by rw [hS₁env]; exact h.2.1) none
  let X (i : ℕ) := Function.update (Function.update S out (stage i)) (base+1) (List.replicate i false)
  have hX : ∀ i, X i base = [] := by
    intro i
    simpa only [X, Function.update_of_ne (by omega : base ≠ base+1),
      Function.update_of_ne (by omega : base ≠ out)] using hb0
  let body := StackModel.Command.seq (copy out (base+2) (base+3))
    (.seq (f.code (Fin.snoc (Fin.snoc env (base+1)) (base+2)) out (base+3))
      (.seq (clear (base+2)) (.push (base+1) (fun _ => false))))
  have hbody : ∀ i, 0 ≤ i → i < 0+ec.length → ∀ w s,
      ∃ t ≤ f.cost B+12*B+11, Exec body s (Function.update (X i) base w) none
        (Function.update (X (i+1)) base w) t := by
    intro i _ hi w s
    simp only [zero_add] at hi
    let T := Function.update (X i) base w
    have hTclean : Clean T (base+2) :=
      (((hc.mono (by omega)).update (by omega : out < base+2)).update (by omega : base+1 < base+2)).update (by omega)
    have hTstash := hTclean (base+2) le_rfl
    have hTtmp := hTclean (base+3) (by omega)
    have hTidx : T (base+1) = List.replicate i false := by simp [T, X]
    have hTout : T out = stage i := by
      simp only [T, X, Function.update_of_ne (by omega : out ≠ base),
        Function.update_of_ne (by omega : out ≠ base+1), Function.update_self]
    obtain ⟨u, hu, heu⟩ := copy_exec out (base+2) (base+3) (by omega) (by omega) (by omega) s T
    let W := Function.update T (base+2) (stage i)
    have hcopy : Function.update (Function.update T (base+2) (T out)) (base+3) [] = W := by
      rw [hTout]
      apply Function.update_eq_self_iff.mpr
      simp only [Function.update_of_ne (by omega : base+3 ≠ base+2), hTtmp]
    rw [hcopy] at heu
    have henv' : ∀ j : Fin (n+2),
        (Fin.snoc (Fin.snoc env (base+1)) (base+2) : Fin (n+2) → ℕ) j < base+3 ∧
        (Fin.snoc (Fin.snoc env (base+1)) (base+2) : Fin (n+2) → ℕ) j ≠ out := by
      intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.snoc_last]; omega
      · simp only [Fin.snoc_castSucc]
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simp only [Fin.snoc_last]; omega
        · simp only [Fin.snoc_castSucc]; have := henv k; omega
    have hWenv : W ∘ Fin.snoc (Fin.snoc env (base+1)) (base+2) =
        Fin.snoc (Fin.snoc (S ∘ env) (List.replicate i false)) (stage i) := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [W]
      · simp only [Function.comp_apply, Fin.snoc_castSucc]
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simpa only [Fin.snoc_last, W, Function.update_of_ne (by omega : base+1 ≠ base+2)] using hTidx
        · simp only [Fin.snoc_castSucc, Function.comp_apply, W, T, X,
            Function.update_of_ne (by have := henvlo k; omega : env k ≠ base+2),
            Function.update_of_ne (by have := henvlo k; omega : env k ≠ base),
            Function.update_of_ne (by have := henvlo k; omega : env k ≠ base+1),
            Function.update_of_ne (henv k).2]
    have hWout : W out = stage i := by
      simpa only [W, Function.update_of_ne (by omega : out ≠ base+2)] using hTout
    have hWclean : Clean W (base+3) := (hTclean.mono (by omega)).update (by omega)
    obtain ⟨v, hv, hev⟩ := hf B W (Fin.snoc (Fin.snoc env (base+1)) (base+2)) out (base+3)
      (by omega) henv' hWclean (hWout ▸ hstage i (by omega)) (by rw [hWenv]; exact h.2.2 i hi) none
    have hnext : f.eval (W ∘ Fin.snoc (Fin.snoc env (base+1)) (base+2)) = stage (i+1) := by
      rw [hWenv]; rfl
    rw [hnext] at hev
    obtain ⟨z, hz, hez⟩ := clear_exec (base+2) none (Function.update W out (stage (i+1)))
    have hZlen : (Function.update W out (stage (i+1)) (base+2)).length ≤ B := by
      rw [Function.update_of_ne (by omega)]
      simpa only [W, Function.update_self] using hstage i (by omega)
    let Z := Function.update (Function.update W out (stage (i+1))) (base+2) []
    have hZ : Z = Function.update T out (stage (i+1)) := by
      dsimp only [Z, W]
      rw [Function.update_comm (by omega : out ≠ base+2), Function.update_idem,
        ← hTstash, Function.update_eq_self]
    have hpush := Exec.push (base+1) (fun _ : Option Bool => false) none Z
    have hfinal : Function.update Z (base+1) (Z (base+1) ++ [false]) = Function.update (X (i+1)) base w := by
      rw [hZ]
      funext j
      by_cases hj : j = base
      · subst j; simp only [T, X, Function.update_self, Function.update_of_ne (by omega : base ≠ base+1),
          Function.update_of_ne (by omega : base ≠ out)]
      by_cases hj' : j = base+1
      · subst j
        simp only [Function.update_self, Function.update_of_ne (by omega : base+1 ≠ base),
          Function.update_of_ne (by omega : base+1 ≠ out), hTidx, X]
        exact List.replicate_succ'.symm
      by_cases hj'' : j = out
      · subst j
        simp only [T, X, Function.update_self, Function.update_of_ne hj, Function.update_of_ne hj']
      · simp only [T, X, Function.update_of_ne hj, Function.update_of_ne hj', Function.update_of_ne hj'']
    rw [hfinal] at hpush
    refine ⟨1+z+v+u, ?_, ?_⟩
    · simp only [hTstash, hTtmp, hTout, List.length_nil, mul_zero, zero_add] at hu
      have hs := hstage i (by omega)
      omega
    · simpa only [body, Nat.add_assoc] using Exec.seq heu (Exec.seq hev (Exec.seq hez hpush))
  obtain ⟨w, hw, hew⟩ := drain_indexed body base X hX (f.cost B+12*B+11) 0 ec hbody none
  have hstart : Function.update (X 0) base ec = Function.update S₁ out (a.eval (S₁ ∘ env)) := by
    rw [hS₁env]
    dsimp only [X, stage, stages, List.replicate_zero, S₁]
    rw [Function.update_comm (by omega : out ≠ base+1)]
    have hh := hc (base+1) (by omega)
    rw [← hh, Function.update_eq_self, Function.update_comm (by omega : out ≠ base)]
  rw [hstart] at hew
  simp only [zero_add] at hew
  obtain ⟨z, hz, hez⟩ := clear_exec (base+1) none (X ec.length)
  have hlast : Function.update (X ec.length) (base+1) [] =
      Function.update S out ((Expr.loop c a f).eval (S ∘ env)) := by
    dsimp only [X]
    rw [Function.update_idem, Function.update_comm (by omega : out ≠ base+1)]
    have hh := hc (base+1) (by omega)
    rw [← hh, Function.update_eq_self]
    rfl
  have hlen : (X ec.length (base+1)).length = ec.length := by simp only [X, Function.update_self, List.length_replicate]
  rw [hlen] at hz
  rw [hlast] at hez
  refine ⟨z+w+v+u, ?_, ?_⟩
  · have hm := Nat.mul_le_mul_left (f.cost B+12*B+11+2) hcB
    dsimp only [cost]
    nlinarith
  · simpa only [code, body, Nat.add_assoc] using Exec.seq heu (Exec.seq hev (Exec.seq hew hez))

/-- The finite word language executes on literal stacks, with polynomial cost
in the lengths of all values in its evaluation. -/
theorem correct {n} (e : Expr n) : e.Correct := by
  induction e with
  | var i => exact correct_var i
  | nil => exact correct_nil
  | snoc e b ih => exact correct_snoc ih b
  | drop e ih => exact correct_drop ih
  | cases e p q r he hp hq hr => exact correct_cases he hp hq hr
  | bind e f he hf => exact correct_bind he hf
  | loop c a f hc ha hf => exact correct_loop hc ha hf

end WordExpressions.Expr
namespace StackModel.Command
variable {R : Type}

theorem restrict_update {N k} (h : 0 < N) (hk : k < N) (S : ℕ → Word) (v : Word) :
    Function.update S k v ∘ Fin.val = Function.update (S ∘ Fin.val) (finiteIndex N h k) v := by
  funext j
  by_cases hj : j.val = k
  · have he : j = finiteIndex N h k := Fin.ext (hj.trans (finiteIndex_val h hk).symm)
    simp only [Function.comp_apply, hj, Function.update_self]
    rw [he, Function.update_self]
  · have he : j ≠ finiteIndex N h k := by intro he; exact hj (congrArg Fin.val he |>.trans (finiteIndex_val h hk))
    simp only [Function.comp_apply, Function.update_of_ne hj, Function.update_of_ne he]

/-- A syntactically finite register program has the same counted execution on
its finite set of tracks, even though its correctness was proved with convenient
natural register names. -/
theorem Exec.restrict {c : Command ℕ R} {s S t T n} (hex : Exec c s S t T n)
    (N : ℕ) (hN : 0 < N) (hc : c.small N) :
    Exec (c.rename (finiteIndex N hN)) s (S ∘ Fin.val) t (T ∘ Fin.val) n := by
  induction hex with
  | skip s S => exact .skip _ _
  | modify f s S => exact .modify _ _ _
  | push k f s S =>
    have hk := hc k (by simp [registers])
    simpa only [Command.rename, restrict_update hN hk, Function.comp_apply, finiteIndex_val hN hk] using
      Exec.push (finiteIndex N hN k) f s (S ∘ Fin.val)
  | pop k f s S =>
    have hk := hc k (by simp [registers])
    simpa only [Command.rename, restrict_update hN hk, Function.comp_apply, finiteIndex_val hN hk] using
      Exec.pop (finiteIndex N hN k) f s (S ∘ Fin.val)
  | seq _ _ ihc ihd =>
    exact .seq (ihc (fun k hk => hc k (Finset.mem_union_left _ hk)))
      (ihd (fun k hk => hc k (Finset.mem_union_right _ hk)))
  | branch_true ht _ ih => exact .branch_true ht (ih (fun k hk => hc k (Finset.mem_union_left _ hk)))
  | branch_false ht _ ih => exact .branch_false ht (ih (fun k hk => hc k (Finset.mem_union_right _ hk)))
  | while_false test c s S ht => exact .while_false _ _ _ _ ht
  | while_true ht _ _ ihc ihw => exact .while_true ht (ihc hc) (ihw hc)

theorem small_exists (c : Command ℕ R) : ∃ N, 1 < N ∧ c.small N := by
  refine ⟨c.registers.sup id+2, by omega, ?_⟩
  intro k hk
  have h := Finset.le_sup (f := id) hk
  dsimp only [id_eq] at h
  omega

theorem testProgram_embeds {K : Type} (c : Command K (Option Bool)) (s : Option Bool) (out : K) :
    Embeds (c.testProgram s out) c (Sum.inl ∘ some) (.inl none) := by
  intro x
  simp only [testProgram, Function.comp_apply]
  congr 1
  funext a
  cases a <;> rfl

theorem Exec.testRun {K : Type} [DecidableEq K] {c : Command K (Option Bool)} {s S t T n}
    (h : Exec c s S t T n) (input out : K) (w : Word)
    (hS : S = Function.update (fun _ => []) input w) :
    (StackModel.run (c.testProgram s out) input w (3+n)).control =
      .inl ((T out).getLast?.getD false) := by
  have he := h.execution (c.testProgram s out) (Sum.inl ∘ some) (.inl none)
    (c.testProgram_embeds s out)
  subst S
  unfold StackModel.run
  rw [Function.iterate_add_apply]
  change ((StackModel.step (c.testProgram s out))^[3]
    ((StackModel.step (c.testProgram s out))^[n]
      ⟨.inr ((Sum.inl ∘ some) c.entry), s, Function.update (fun _ => []) input w⟩)).control = _
  rw [he]
  change (StackModel.step (c.testProgram s out) (StackModel.step (c.testProgram s out)
    (StackModel.step (c.testProgram s out) ⟨.inr (.inl none), t, T⟩))).control = _
  cases hb : (T out).getLast?.getD false <;> simp [StackModel.step, testProgram, hb]

end StackModel.Command
namespace ComputationBounds

theorem maximum {f g} (hf : Polynomial f) (hg : Polynomial g) : Polynomial (fun n => max (f n) (g n)) := by
  obtain ⟨C,d,h⟩ := add hf hg
  exact ⟨C,d,fun n => (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)).trans (h n)⟩

end ComputationBounds

namespace WordExpressions.Expr
open ComputationBounds

theorem cost_polynomial {n} (e : Expr n) : Polynomial e.cost := by
  induction e with
  | var _ => exact add (mul (constant 12) identity) (constant 8)
  | nil => exact add (mul (constant 3) identity) (constant 2)
  | snoc _ _ ih | drop _ ih => exact add ih (constant 1)
  | cases _ _ _ _ he hp hq hr =>
    exact add (add (add he (maximum hp (maximum hq hr))) (mul (constant 3) identity)) (constant 5)
  | bind _ _ he hf => exact add (add (add he hf) (mul (constant 3) identity)) (constant 2)
  | loop _ _ _ hc ha hf =>
    exact add (add (add (add hc ha) (mul (add (add hf (mul (constant 12) identity)) (constant 13)) identity))
      (mul (constant 3) identity)) (constant 4)

theorem outputBound_polynomial {n} (e : Expr n) : Polynomial e.outputBound := by
  have h := add (add e.cost_polynomial (mul (constant 15) identity)) (constant 13)
  exact add (constant 2) (mul h (add (mul (constant 2) (add identity h)) (constant 3)))

end WordExpressions.Expr

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.ExpressionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions.Expr
open StackModel.Command

theorem outputCode_exec (e : Expr 1) (w : Word) (B : ℕ) (hw : w.length ≤ B)
    (h : e.Bounded (fun _ => w) B) :
    ∃ t ≤ e.cost B+15*B+12, Exec e.outputCode none (Function.update (fun _ => []) 0 w) none
      (Function.update (fun _ => []) 0 (e.eval (fun _ => w))) t := by
  let S : ℕ → Word := Function.update (fun _ => []) 0 w
  have henv : S ∘ (fun _ : Fin 1 => 0) = fun _ => w := by funext i; simp [S]
  have hclean : Clean S 2 := by intro k hk; simp [S, show k ≠ 0 by omega]
  obtain ⟨a, ha, hea⟩ := e.correct B S (fun _ => 0) 1 2 (by omega) (by intro i; omega)
    hclean (by simp [S]) (by rw [henv]; exact h) none
  rw [henv] at hea
  let v := e.eval (fun _ => w)
  have hv : v.length ≤ B := e.length_le _ _ h
  let T := Function.update S 1 v
  obtain ⟨b, hb, heb⟩ := clear_exec 0 none T
  let U := Function.update T 0 []
  obtain ⟨c, hc, hec⟩ := copy_exec 1 0 2 (by omega) (by omega) (by omega) none U
  let V := Function.update (Function.update U 0 (U 1)) 2 []
  obtain ⟨d, hd, hed⟩ := clear_exec 1 none V
  have ht0 : T 0 = w := by simp [T, S]
  have hu0 : U 0 = [] := by simp [U]
  have hu1 : U 1 = v := by simp [U, T]
  have hu2 : U 2 = [] := by simp [U, T, S]
  have hv1 : V 1 = v := by simp [V, U, T]
  have hfinal : Function.update V 1 [] = Function.update (fun _ => []) 0 v := by
    funext k
    by_cases hk0 : k = 0
    · subst k; simp [V, U, T]
    by_cases hk1 : k = 1
    · subst k; simp
    by_cases hk2 : k = 2
    · subst k; simp [V]
    · simp [V, U, T, S, hk0, hk1, hk2]
  rw [hfinal] at hed
  refine ⟨d+c+b+a, ?_, ?_⟩
  · simp only [ht0] at hb
    simp only [hu0, hu1, hu2, List.length_nil, mul_zero, zero_add] at hc
    simp only [hv1] at hd
    omega
  · simpa only [outputCode, Nat.add_assoc] using Exec.seq hea (Exec.seq heb (Exec.seq hec hed))

/-- A complete local, finite-alphabet output producer from a proved bounded
word expression. Uniformity is in the expression, not in its inputs. -/
theorem computes (e : Expr 1) (B : ℕ → ℕ)
    (hw : ∀ n, n ≤ B n) (h : ∀ w, e.Bounded (fun _ => w) (B w.length)) :
    ∃ M : Machine, ComputesWithin M (fun w => e.eval (fun _ => w))
      (fun n => e.outputBound (B n)) := by
  obtain ⟨N,hN,hsmall⟩ := e.outputCode.small_exists
  let c := e.outputCode.rename (finiteIndex N (by omega))
  let input : Fin N := finiteIndex N (by omega) 0
  let P := c.program none
  refine ⟨StackModel.compile P input, ?_⟩
  intro w
  obtain ⟨t,ht,he⟩ := e.outputCode_exec w (B w.length) (hw _) (h w)
  have he' := he.restrict N (by omega) hsmall
  simp only [restrict_update (show 0 < N by omega) (show 0 < N by omega)] at he'
  have hs : (fun _ : ℕ => ([] : Word)) ∘ Fin.val = fun _ : Fin N => [] := rfl
  rw [hs] at he'
  have hr := he'.run input w rfl
  obtain ⟨T,hT,hTe⟩ := StackModel.run_execution P input w (t+1)
  change ∃ T ≤ _, _
  refine ⟨T, ?_, ?_, ?_⟩
  · apply hT.trans
    dsimp only [outputBound]
    have htp : t+1 ≤ e.cost (B w.length)+15*(B w.length)+13 := by omega
    have hn := hw w.length
    gcongr
  · rw [hTe, hr]
    rfl
  · rw [hTe, hr]
    exact StackModel.output_correct P input _ _ rfl

end WordExpressions.Expr

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.WordArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions.Poly

theorem computes {f : (Fin 1 → Word) → Word} (hf : Poly f) :
    ∃ (M : Machine) (C d : ℕ),
      ComputesWithin M (fun w => f (fun _ => w)) (fun n => C*(n+1)^d) := by
  obtain ⟨e,B,hB,he,hbound⟩ := hf
  let D := fun n => n+B n
  have hd : ∀ n, n ≤ D n := fun n => Nat.le_add_right _ _
  have hb : ∀ w, e.Bounded (fun _ => w) (D w.length) := by
    intro w
    exact e.bounded_mono (hbound _ _ (by intro i; rfl)) (Nat.le_add_left _ _)
  obtain ⟨M,hM⟩ := e.computes D hd hb
  obtain ⟨C,d,hCd⟩ := ComputationBounds.compose e.outputBound_polynomial
    (ComputationBounds.add ComputationBounds.identity hB)
  refine ⟨M,C,d,?_⟩
  intro w
  obtain ⟨t,ht,hhalt,hout⟩ := hM w
  exact ⟨t,ht.trans (hCd w.length),hhalt,by simpa only [he] using hout⟩

end WordExpressions.Poly

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.PolynomialArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions
namespace Poly
variable {n : ℕ}

theorem replicate {c : (Fin n → Word) → ℕ} (hc : NatPoly c) (b : Bool) :
    Poly (fun S => List.replicate (c S) b) := by
  apply (tabulate hc (BoolPoly.const b)).congr
  intro S
  simp

theorem append {u v : (Fin n → Word) → Word} (hu : Poly u) (hv : Poly v) :
    Poly (fun S => u S ++ v S) := by
  let p : (Fin (n+1) → Word) → Bool := fun T =>
    if (T (Fin.last n)).length < (u (T ∘ Fin.castSucc)).length then
      (u (T ∘ Fin.castSucc))[(T (Fin.last n)).length]?.getD false
    else (v (T ∘ Fin.castSucc))[(T (Fin.last n)).length-(u (T ∘ Fin.castSucc)).length]?.getD false
  have hp : BoolPoly p := by
    apply (branches
      (NatPoly.lt (NatPoly.var (Fin.last n)) (NatPoly.length (rename hu Fin.castSucc)))
      (nth (rename hu Fin.castSucc) (NatPoly.var (Fin.last n)))
      (nth (rename hv Fin.castSucc) (NatPoly.sub (NatPoly.var (Fin.last n))
        (NatPoly.length (rename hu Fin.castSucc))))).congr
    intro T
    dsimp only [p]
    by_cases hh : (T (Fin.last n)).length < (u (T ∘ Fin.castSucc)).length <;> simp [hh]
  have h := tabulate (NatPoly.add (NatPoly.length hu) (NatPoly.length hv)) hp
  apply h.congr
  intro S
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map, List.getElem_range, p, Fin.snoc_last, unary,
    List.length_replicate, snoc_prefix, List.getElem_append]
  split
  · rename_i hh
    rw [List.getElem?_eq_getElem hh]
    rfl
  · rename_i hh
    have hv' : i-(u S).length < (v S).length := by simp only [List.length_append] at hj; omega
    rw [List.getElem?_eq_getElem hv']
    rfl

theorem dropPrefix {w : (Fin n → Word) → Word} {c : (Fin n → Word) → ℕ}
    (hw : Poly w) (hc : NatPoly c) : Poly (fun S => (w S).drop (c S)) := by
  have hp := nth (rename hw Fin.castSucc)
    (NatPoly.add (NatPoly.rename hc Fin.castSucc) (NatPoly.var (Fin.last n)))
  apply (tabulate (NatPoly.sub (NatPoly.length hw) hc) hp).congr
  intro S
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map, List.getElem_range, Fin.snoc_last, unary, List.length_replicate,
    snoc_prefix, List.getElem_drop]
  rw [List.getElem?_eq_getElem (by simpa only [List.length_drop] using (show c S+i < (w S).length from by
    simp only [List.length_drop] at hj; omega))]
  rfl

end Poly
end WordExpressions

namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem bitsSize {f : (Fin n → Word) → ℕ} (hf : NatPoly f) : NatPoly (fun S => (f S).size) := by
  have hp : BoolPoly (fun T : Fin (n+1) → Word =>
      decide (Min.min (2^(T (Fin.last n)).length) (f (T ∘ Fin.castSucc)+1) ≤ f (T ∘ Fin.castSucc))) :=
    le (cappedPow (const 2) (var _) (succ (rename hf _))) (rename hf _)
  have hmax := findGreatest hf hp
  apply (ite (eqtest hf (const 0)) (const 0) (succ hmax)).congr
  intro S
  simp only [Fin.snoc_last, unary, List.length_replicate, snoc_prefix, decide_eq_true_eq]
  by_cases hz : f S = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    have hpos : 0 < (f S).size := by
      by_contra hh
      have := Nat.size_le.mp (show (f S).size ≤ 0 from by omega)
      simp only [pow_zero] at this
      omega
    have hsize : (f S).size ≤ f S := Nat.size_le.mpr Nat.lt_two_pow_self
    have hmaxeq : Nat.findGreatest (fun i => Min.min (2^i) (f S+1) ≤ f S) (f S) = (f S).size-1 := by
      apply Nat.findGreatest_eq_iff.mpr
      refine ⟨by omega, ?_, ?_⟩
      · intro _
        apply (min_le_left _ _).trans
        have hn : ¬ f S < 2^((f S).size-1) := by
          intro hn
          have := Nat.size_le.mpr hn
          omega
        omega
      · intro i hi _ hle
        have hpow : f S < 2^i := Nat.size_le.mp (by omega)
        omega
    rw [hmaxeq]
    congr 1
    omega

theorem testBit {f i : (Fin n → Word) → ℕ} (hf : NatPoly f) (hi : NatPoly i) :
    BoolPoly (fun S => (f S).testBit (i S)) := by
  apply (eqtest (mod (div hf (cappedPow (const 2) hi (succ hf))) (const 2)) (const 1)).congr
  intro S
  simp only [div_cap, Nat.testBit_eq_decide_div_mod_eq]

end WordExpressions.NatPoly
namespace WordExpressions.Poly
variable {n : ℕ}

theorem bits {f : (Fin n → Word) → ℕ} (hf : NatPoly f) : Poly (fun S => (f S).bits) := by
  apply (tabulate (NatPoly.bitsSize hf)
    (NatPoly.testBit (NatPoly.rename hf Fin.castSucc) (NatPoly.var (Fin.last n)))).congr
  intro S
  apply List.ext_getElem (by simp [Nat.size_eq_bits_len])
  intro i hi hj
  simp only [List.getElem_map, List.getElem_range, Fin.snoc_last, unary,
    List.length_replicate, snoc_prefix, Nat.testBit_eq_inth, List.getI_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem hj]
  rfl

theorem binary {f : (Fin n → Word) → ℕ} (hf : NatPoly f) : Poly (fun S => (f S).bits.reverse) :=
  reverse (bits hf)

end WordExpressions.Poly

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.FiniteEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem filterSelect {b j : (Fin n → Word) → ℕ} {p : (Fin (n+1) → Word) → Bool}
    (hb : NatPoly b) (hj : NatPoly j) (hp : BoolPoly p) :
    NatPoly (fun S => NumericFinite.select (b S) (fun i => p (Fin.snoc S (unary i))) (j S)) := by
  have hp' : BoolPoly (fun T : Fin (n+2) → Word =>
      p (Fin.snoc (T ∘ Fin.castSucc ∘ Fin.castSucc) (T (Fin.last (n+1))))) :=
    Poly.applyWord hp (Fin.castSucc ∘ Fin.castSucc) (Poly.var _)
  have hc := filterCount (var (Fin.last n)) hp'
  have htest := BoolPoly.and (lt (var (Fin.last n)) (rename hb Fin.castSucc))
    (BoolPoly.and hp (eqtest hc (rename hj Fin.castSucc)))
  apply (findGreatest hb htest).congr
  intro S
  dsimp only [NumericFinite.select]
  congr 2
  funext i
  simp only [Fin.snoc_last, unary, List.length_replicate, snoc_prefix,
    Bool.and_eq_true, decide_eq_true_eq]
  simp only [Function.comp_def, Fin.snoc_castSucc]

end WordExpressions.NatPoly

namespace WordExpressions.Expr
open StackModel.Command ComputationBounds

theorem decisionBound_polynomial {n} (e : Expr n) : Polynomial e.decisionBound := by
  have h := add (add e.cost_polynomial (mul (constant 15) identity)) (constant 15)
  exact add (constant 2) (mul h (add (mul (constant 2) (add identity h)) (constant 3)))

/-- The output bit is tested by three actual finite-control instructions.
Rejection is a literal rejecting state, including on malformed words. -/
theorem decides (e : Expr 1) (B : ℕ → ℕ)
    (hw : ∀ n, n ≤ B n) (h : ∀ w, e.Bounded (fun _ => w) (B w.length)) :
    ∃ M : Machine, DecidesWithin M {w | (e.eval (fun _ => w)).getLast?.getD false = true}
      (fun n => e.decisionBound (B n)) := by
  obtain ⟨N,hN,hsmall⟩ := e.outputCode.small_exists
  let c := e.outputCode.rename (finiteIndex N (by omega))
  let input : Fin N := finiteIndex N (by omega) 0
  let P := c.testProgram none input
  refine ⟨StackModel.compile P input, ?_⟩
  intro w
  obtain ⟨t,ht,he⟩ := e.outputCode_exec w (B w.length) (hw _) (h w)
  have he' := he.restrict N (by omega) hsmall
  simp only [restrict_update (show 0 < N by omega) (show 0 < N by omega)] at he'
  have hs : (fun _ : ℕ => ([] : Word)) ∘ Fin.val = fun _ : Fin N => [] := rfl
  rw [hs] at he'
  have hr := he'.testRun input input w rfl
  simp only [input, Function.update_self] at hr
  change (StackModel.run P input w (3+t)).control =
    .inl ((e.eval (fun _ => w)).getLast?.getD false) at hr
  obtain ⟨T,hT,hTe⟩ := StackModel.run_execution P input w (3+t)
  refine ⟨T, ?_, ?_, ?_⟩
  · apply hT.trans
    dsimp only [decisionBound]
    have htp : 3+t ≤ e.cost (B w.length)+15*(B w.length)+15 := by omega
    have hn := hw w.length
    gcongr
  · rw [hTe]
    simp only [Halted, StackModel.encodeConfig, hr]
    cases hb : (e.eval (fun _ => w)).getLast?.getD false <;> simp
  · rw [hTe]
    simp only [StackModel.encodeConfig, hr, Set.mem_ofPred_eq]
    cases hb : (e.eval (fun _ => w)).getLast?.getD false <;> simp
    change ¬(2 : Fin ((StackModel.compile P input).extraStates+3)) = 1
    intro heq
    have hv := congrArg Fin.val heq
    change 2 % ((StackModel.compile P input).extraStates+3) =
      1 % ((StackModel.compile P input).extraStates+3) at hv
    have h1 : 1 < (StackModel.compile P input).extraStates+3 := by omega
    have h2 : 2 < (StackModel.compile P input).extraStates+3 := by omega
    rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h1] at hv
    omega

end WordExpressions.Expr
namespace ComputationBounds

theorem exp_dominates {f g : ℕ → ℕ} (hf : Exponential f) (h : ∀ n, g n ≤ f n) : Exponential g := by
  obtain ⟨C,d,hf⟩ := hf
  exact ⟨C,d,fun n => (h n).trans (hf n)⟩

theorem two_pow {f : ℕ → ℕ} (hf : Polynomial f) : Exponential (fun n => 2^(f n)) := by
  obtain ⟨C,d,hf⟩ := hf
  exact ⟨C,d,fun n => Nat.pow_le_pow_right (by decide) (hf n)⟩

theorem polynomial_exponential {f : ℕ → ℕ} (hf : Polynomial f) : Exponential f :=
  exp_dominates (two_pow hf) (fun _ => (Nat.lt_two_pow_self).le)

theorem exp_constant (c : ℕ) : Exponential (fun _ => c) := polynomial_exponential (constant c)

theorem exp_identity : Exponential id := polynomial_exponential identity

theorem exp_add {f g : ℕ → ℕ} (hf : Exponential f) (hg : Exponential g) :
    Exponential (fun n => f n+g n) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  let p := fun n => C*(n+1)^d
  let q := fun n => D*(n+1)^e
  have hp : Polynomial p := ⟨C,d,fun _ => le_rfl⟩
  have hq : Polynomial q := ⟨D,e,fun _ => le_rfl⟩
  apply exp_dominates (two_pow (add (add hp hq) (constant 1)))
  intro n
  have ha : f n ≤ 2^(p n+q n) := (hf n).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right (p n) (q n)))
  have hb : g n ≤ 2^(p n+q n) := (hg n).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left (q n) (p n)))
  change f n+g n ≤ 2^(p n+q n+1)
  rw [pow_succ]
  omega

theorem exp_mul {f g : ℕ → ℕ} (hf : Exponential f) (hg : Exponential g) :
    Exponential (fun n => f n*g n) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  have hp : Polynomial (fun n => C*(n+1)^d) := ⟨C,d,fun _ => le_rfl⟩
  have hq : Polynomial (fun n => D*(n+1)^e) := ⟨D,e,fun _ => le_rfl⟩
  apply exp_dominates (two_pow (add hp hq))
  intro n
  simpa only [pow_add] using Nat.mul_le_mul (hf n) (hg n)

theorem exp_power {f : ℕ → ℕ} (hf : Exponential f) (d : ℕ) : Exponential (fun n => (f n)^d) := by
  induction d with
  | zero => simpa using exp_constant 1
  | succ d ih => simpa only [pow_succ] using exp_mul ih hf

theorem polynomial_exp_comp {f g : ℕ → ℕ} (hf : Polynomial f) (hg : Exponential g) :
    Exponential (fun n => f (g n)) := by
  obtain ⟨C,d,hf⟩ := hf
  exact exp_dominates (exp_mul (exp_constant C) (exp_power (exp_add hg (exp_constant 1)) d))
    (fun n => hf (g n))

end ComputationBounds

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.ExponentialComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions
open ComputationBounds

namespace Exp
variable {n : ℕ}

theorem congr {f g : (Fin n → Word) → Word} (h : Exp f) (he : ∀ S, f S = g S) : Exp g := by
  obtain ⟨e,B,hB,heval,hb⟩ := h
  exact ⟨e,B,hB,fun S => (heval S).trans (he S),hb⟩

/-- Feeding one-exponential data to a fixed polynomial word program stays
single-exponential; arbitrary composition of two exponential programs is not asserted. -/
theorem bindPoly {f : (Fin n → Word) → Word} {g : (Fin (n+1) → Word) → Word}
    (hf : Exp f) (hg : Poly g) : Exp (fun S => g (Fin.snoc S (f S))) := by
  obtain ⟨e,B,hB,he,hb⟩ := hf
  obtain ⟨a,A,hA,ha,hab⟩ := hg
  refine ⟨.bind e a, fun N => B N+A (N+B N),
    exp_add hB (polynomial_exp_comp hA (exp_add exp_identity hB)), ?_, ?_⟩
  · intro S
    simp only [Expr.eval, ha, he]
  · intro S N hS
    try dsimp only
    have hs := hb S N hS
    refine ⟨e.bounded_mono hs (by omega), ?_⟩
    apply a.bounded_mono (hab _ (N+B N) ?_) (by omega)
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using (e.length_le _ _ hs).trans (by omega : B N ≤ N+B N)
    · simpa only [Fin.snoc_castSucc] using (hS j).trans (by omega : N ≤ N+B N)

theorem loopPoly {c a : (Fin n → Word) → Word} {f : (Fin (n+2) → Word) → Word}
    (hc : Poly c) (ha : Poly a) (hf : Poly f) (H : ℕ → ℕ) (hH : Exponential H)
    (hstage : ∀ S N, (∀ j, (S j).length ≤ N) → ∀ i ≤ (c S).length,
      (Expr.stages f S (a S) i).length ≤ H N) :
    Exp (fun S => Expr.stages f S (a S) (c S).length) := by
  obtain ⟨ce,C,hC,hce,hcb⟩ := hc
  obtain ⟨ae,A,hA,hae,hab⟩ := ha
  obtain ⟨fe,F,hF,hfe,hfb⟩ := hf
  let D := fun N => C N+A N+F (N+C N+H N)
  have hp : Exponential D := exp_add (polynomial_exponential (add hC hA))
    (polynomial_exp_comp hF (exp_add (polynomial_exponential (add identity hC)) hH))
  refine ⟨.loop ce ae fe, D,hp,?_,?_⟩
  · intro S
    simp only [Expr.eval, hce, hae]
    exact Poly.stages_congr hfe _ _ _
  · intro S N hS
    try dsimp only
    have hcS := hcb S N hS
    have haS := hab S N hS
    refine ⟨ce.bounded_mono hcS (by dsimp [D]; omega),
      ae.bounded_mono haS (by dsimp [D]; omega), ?_⟩
    intro i hi
    apply fe.bounded_mono (hfb _ (N+C N+H N) ?_) (by dsimp [D]; omega)
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.snoc_last, hae, Poly.stages_congr hfe]
      have hi' : i ≤ (c S).length := by rw [← hce]; omega
      exact (hstage S N hS i hi').trans (by omega)
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp only [Fin.snoc_castSucc, Fin.snoc_last, List.length_replicate]
        have := ce.length_le _ _ hcS
        omega
      · simpa only [Fin.snoc_castSucc] using (hS k).trans (by omega : N ≤ N+C N+H N)

theorem powerBudget (C d : ℕ) :
    Exp (fun S : Fin 1 → Word => unary (2^(C*((S 0).length+1)^d))) := by
  have hp : NatPoly (fun S : Fin 1 → Word => C*((S 0).length+1)^d) :=
    NatPoly.mul (NatPoly.const C) (NatPoly.pow_const (NatPoly.succ (NatPoly.var 0)) d)
  let f : (Fin 3 → Word) → Word := fun T => T (accum 1) ++ T (accum 1)
  have hf : Poly f := Poly.append (Poly.var _) (Poly.var _)
  have hs (S : Fin 1 → Word) (i : ℕ) : Expr.stages f S (unary 1) i = unary (2^i) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      simp only [Expr.stages, f, extend_accum, ih, unary]
      rw [← List.replicate_add, pow_succ]
      congr 1
      omega
  have h := loopPoly hp (Poly.const (unary 1)) hf (fun N => 2^(C*(N+1)^d))
    ⟨C,d,fun _ => le_rfl⟩ (by
      intro S N hS i hi
      rw [hs]
      simp only [unary, List.length_replicate] at hi ⊢
      apply Nat.pow_le_pow_right (by decide)
      exact hi.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by have := hS 0; omega) d)))
  apply h.congr
  intro S
  simpa only [unary, List.length_replicate] using hs S (C*((S 0).length+1)^d)

/-- A genuine EXPTIME decider from a proved single-exponential Boolean program. -/
theorem inEXPTIME {p : (Fin 1 → Word) → Bool} (hp : Exp (fun S => boolWord (p S))) :
    InEXPTIME {w | p (fun _ => w) = true} := by
  obtain ⟨e,B,hB,he,hbound⟩ := hp
  let D := fun n => n+B n
  have hd : ∀ n, n ≤ D n := fun n => Nat.le_add_right _ _
  have hb : ∀ w, e.Bounded (fun _ => w) (D w.length) := by
    intro w
    exact e.bounded_mono (hbound _ _ (by intro i; rfl)) (Nat.le_add_left _ _)
  obtain ⟨M,hM⟩ := e.decides D hd hb
  obtain ⟨C,d,hCd⟩ := polynomial_exp_comp e.decisionBound_polynomial (exp_add exp_identity hB)
  refine ⟨M,C,d,?_⟩
  intro w
  obtain ⟨t,ht,hhalt,hacc⟩ := hM w
  refine ⟨t,ht.trans (hCd w.length),hhalt,?_⟩
  simpa only [Set.mem_ofPred_eq, he, boolWord, List.getLast?_singleton, Option.getD_some] using hacc

end Exp

/-- A polynomial budget-relative test is executed on a physically generated
unary exponential budget, rather than receiving an oracle-size bound. -/
theorem inEXPTIME_of_budget {L : BinaryLanguage} (C d : ℕ)
    {p : (Fin 2 → Word) → Bool} (hp : BoolPoly p)
    (h : ∀ w, p ![w, unary (2^(C*(w.length+1)^d))] = true ↔ w ∈ L) : InEXPTIME L := by
  have he := Exp.bindPoly (Exp.powerBudget C d) hp
  have hE := Exp.inEXPTIME he
  have hset : {w | p (Fin.snoc (fun _ : Fin 1 => w) (unary (2^(C*(w.length+1)^d)))) = true} = L := by
    ext w
    have henv : Fin.snoc (fun _ : Fin 1 => w) (unary (2^(C*(w.length+1)^d))) =
        ![w, unary (2^(C*(w.length+1)^d))] := by
      funext i
      fin_cases i <;> rfl
    simpa only [Set.mem_ofPred_eq, henv] using h w
  simpa only [hset] using hE

end WordExpressions

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.NumericKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace NumericKernel
open WordExpressions

/-- All loops below range over explicit unary word lengths. -/
theorem vectorMatch_poly : BoolPoly (fun S : Fin 7 → Word =>
    vectorMatch (S 0).length (S 1).length (S 2) (S 3) (S 4).length (S 5).length (S 6).length) := by
  unfold vectorMatch lookup
  apply BoolPoly.allRange (NatPoly.var 1)
  apply BoolPoly.anyRange (NatPoly.var 0)
  apply BoolPoly.and
  · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · apply Poly.nth (Poly.var 3)
    apply NatPoly.pair (NatPoly.var (Fin.last 8))
    apply NatPoly.digit <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

end NumericKernel
namespace NumericKernel
open WordExpressions

theorem vectorMatch_poly_of {n} {N w a z v : (Fin n → Word) → ℕ}
    {tr R : (Fin n → Word) → Word} (hN : NatPoly N) (hw : NatPoly w)
    (ht : Poly tr) (hR : Poly R) (ha : NatPoly a) (hz : NatPoly z) (hv : NatPoly v) :
    BoolPoly (fun S => vectorMatch (N S) (w S) (tr S) (R S) (a S) (z S) (v S)) := by
  have h := vectorMatch_poly.subst (g := ![fun S => unary (N S),fun S => unary (w S),tr,R,
    fun S => unary (a S),fun S => unary (z S),fun S => unary (v S)])
    (by intro i; fin_cases i; exacts [hN,hw,ht,hR,ha,hz,hv])
  simpa [unary] using h

theorem countMatch_poly : NatPoly (fun S : Fin 8 → Word =>
    countMatch (S 0).length (S 1).length (S 2).length (S 3) (S 4) (S 5)
      (S 6).length (S 7).length) := by
  unfold countMatch
  apply NatPoly.sumRange (NatPoly.var 2)
  apply NatPoly.ite
  · apply BoolPoly.and
    · unfold lookup; (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
    · apply vectorMatch_poly_of <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · exact NatPoly.const 1
  · exact NatPoly.const 0

theorem countMatch_poly_of {n} {N w b a v : (Fin n → Word) → ℕ}
    {ac tr R : (Fin n → Word) → Word} (hN : NatPoly N) (hw : NatPoly w) (hb : NatPoly b)
    (hac : Poly ac) (ht : Poly tr) (hR : Poly R) (ha : NatPoly a) (hv : NatPoly v) :
    NatPoly (fun S => countMatch (N S) (w S) (b S) (ac S) (tr S) (R S) (a S) (v S)) := by
  have h := countMatch_poly.subst (g := ![fun S => unary (N S),fun S => unary (w S),
    fun S => unary (b S),ac,tr,R,fun S => unary (a S),fun S => unary (v S)])
    (by intro i; fin_cases i; exacts [hN,hw,hb,hac,ht,hR,ha,hv])
  simpa [unary] using h

theorem entry_poly : BoolPoly (fun S : Fin 9 → Word =>
    entry (S 0).length (S 1).length (S 2).length (S 3).length (S 4) (S 5) (S 6)
      (S 7).length (S 8).length) := by
  unfold entry
  apply BoolPoly.and
  · unfold lookup; (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · apply BoolPoly.allRange
    · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
    · apply NatPoly.eqtest <;> apply countMatch_poly_of <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

theorem entry_poly_of {n} {N w br c a b : (Fin n → Word) → ℕ}
    {ac tr R : (Fin n → Word) → Word} (hN : NatPoly N) (hw : NatPoly w)
    (hbr : NatPoly br) (hc : NatPoly c) (hac : Poly ac) (ht : Poly tr) (hR : Poly R)
    (ha : NatPoly a) (hb : NatPoly b) :
    BoolPoly (fun S => entry (N S) (w S) (br S) (c S) (ac S) (tr S) (R S) (a S) (b S)) := by
  have h := entry_poly.subst (g := ![fun S => unary (N S),fun S => unary (w S),
    fun S => unary (br S),fun S => unary (c S),ac,tr,R,fun S => unary (a S),fun S => unary (b S)])
    (by intro i; fin_cases i; exacts [hN,hw,hbr,hc,hac,ht,hR,ha,hb])
  simpa [unary] using h

theorem step_poly : Poly (fun S : Fin 7 → Word =>
    step (S 0).length (S 1).length (S 2).length (S 3).length (S 4) (S 5) (S 6)) := by
  unfold step
  apply Poly.tabulateRange
  · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · apply entry_poly_of <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

theorem step_poly_of {n} {N w br c : (Fin n → Word) → ℕ}
    {ac tr R : (Fin n → Word) → Word} (hN : NatPoly N) (hw : NatPoly w)
    (hbr : NatPoly br) (hc : NatPoly c) (hac : Poly ac) (ht : Poly tr) (hR : Poly R) :
    Poly (fun S => step (N S) (w S) (br S) (c S) (ac S) (tr S) (R S)) := by
  have h := step_poly.subst (g := ![fun S => unary (N S),fun S => unary (w S),
    fun S => unary (br S),fun S => unary (c S),ac,tr,R])
    (by intro i; fin_cases i; exacts [hN,hw,hbr,hc,hac,ht,hR])
  simpa [unary] using h

end NumericKernel
namespace WordExpressions.Poly
variable {n : ℕ}

/-- Iteration with a proved output-length invariant.  Its loop count is a
physical unary word, not an unbounded recursion primitive. -/
theorem iterate {c b : (Fin n → Word) → ℕ} {a : (Fin n → Word) → Word}
    {f : (Fin n → Word) → Word → Word} (hc : NatPoly c) (hb : NatPoly b) (ha : Poly a)
    (hf : Poly (fun T => f (T ∘ Fin.castSucc) (T (Fin.last n))))
    (hlen : ∀ S W, (f S W).length ≤ b S) :
    Poly (fun S => (f S)^[c S] (a S)) := by
  let g : (Fin (n+2) → Word) → Word := fun T =>
    f (T ∘ Fin.castSucc ∘ Fin.castSucc) (T (Fin.last (n+1)))
  have hg : Poly g := by
    apply (hf.rename (Fin.lastCases (Fin.last (n+1)) (fun i => i.castSucc.castSucc))).congr
    intro T
    simp only [Function.comp_def, Fin.lastCases_castSucc, Fin.lastCases_last, g]
  have hs (S : Fin n → Word) (i : ℕ) : Expr.stages g S (a S) i = (f S)^[i] (a S) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      simp only [Expr.stages, Function.iterate_succ_apply']
      rw [ih]
      simp only [g, Function.comp_def, Fin.snoc_castSucc, Fin.snoc_last]
  obtain ⟨A,hA,hAb⟩ := ha.length_bound
  obtain ⟨B,hB,hBb⟩ := hb.bound
  have h := loop hc ha hg (fun N => A N+B N) (ComputationBounds.add hA hB) (by
    intro S N hS i _
    rw [hs]
    cases i with
    | zero => exact (hAb S N hS).trans (Nat.le_add_right _ _)
    | succ i =>
      rw [Function.iterate_succ_apply']
      exact ((hlen S _).trans (hBb S N hS)).trans (Nat.le_add_left _ _))
  apply h.congr
  intro S
  simpa only [unary, List.length_replicate] using hs S (c S)

end WordExpressions.Poly
namespace NumericKernel
open WordExpressions

theorem table_poly : Poly (fun S : Fin 8 → Word =>
    table (S 0).length (S 1).length (S 2).length (S 3).length (S 4) (S 5) (S 6) (S 7).length) := by
  apply Poly.iterate (NatPoly.var 7)
    (b := fun S => Nat.pair (S 0).length (S 0).length+1)
  · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · exact Poly.var 6
  · apply step_poly_of <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · intro S W
    simp only [step, List.length_map, List.length_range, le_refl]

end NumericKernel

namespace NumericKernel

variable {N width branch : ℕ} (D : Data N width branch)

theorem vectorMatch_correct {active trans W : Word} (he : Encoded D active trans)
    {R : Fin N → Fin N → Bool} (hR : Represents W R) (a : Fin N) (z : Fin branch)
    (v : Fin (N^width)) :
    vectorMatch N width trans W a z v =
      FiniteRefinement.vectorMatch R (D.next a z) (finFunctionFinEquiv.symm v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [vectorMatch, List.all_eq_true, List.mem_range, List.any_eq_true,
    Bool.and_eq_true, FiniteRefinement.vectorMatch, decide_eq_true_eq]
  constructor
  · intro h i
    obtain ⟨y,hy,ht,hm⟩ := h i i.isLt
    have ht' := he.2 a z i ⟨y,hy⟩
    have hnext : D.next a z i = ⟨y,hy⟩ := by
      simpa only [ht, decide_eq_true_eq, true_iff] using ht'.symm
    rw [hnext]
    exact (hR ⟨y,hy⟩ (finFunctionFinEquiv.symm v i)).symm.trans hm
  · intro h i hi
    let ii : Fin width := ⟨i,hi⟩
    refine ⟨D.next a z ii, (D.next a z ii).isLt, ?_, ?_⟩
    · simpa using he.2 a z ii (D.next a z ii)
    · exact (hR (D.next a z ii) (finFunctionFinEquiv.symm v ii)).trans (h ii)

end NumericKernel
namespace NumericKernel

theorem sum_range_fin (b : ℕ) (f : ℕ → ℕ) :
    ((List.range b).map f).sum = ∑ i : Fin b, f i := by
  induction b with
  | zero => simp
  | succ b ih => simp only [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, ih, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

theorem multiset_countP_sum {A : Type} (L : Multiset A) (p : A → Prop) [DecidablePred p] :
    L.countP p = (L.map (fun x => if p x then 1 else 0)).sum := by
  induction L using Multiset.induction_on with
  | empty => simp
  | @cons a L ih => simp only [Multiset.countP_cons, Multiset.map_cons, Multiset.sum_cons, ih, Nat.add_comm]

variable {N width branch : ℕ} (D : Data N width branch)

theorem countMatch_correct {active trans W : Word} (he : Encoded D active trans)
    {R : Fin N → Fin N → Bool} (hR : Represents W R) (a : Fin N) (v : Fin (N^width)) :
    countMatch N width branch active trans W a v =
      (D.vectors a).countP (fun w => FiniteRefinement.vectorMatch R w (finFunctionFinEquiv.symm v) = true) := by
  rw [countMatch, sum_range_fin]
  simp only [Data.vectors, Multiset.countP_map, Finset.filter_val, Multiset.filter_filter]
  rw [← Multiset.countP_eq_card_filter, multiset_countP_sum]
  change (∑ z : Fin branch, _) = ∑ z : Fin branch, _
  apply Finset.sum_congr rfl
  intro z _
  rw [he.1 a z, vectorMatch_correct D he hR a z v]
  simp only [Bool.and_eq_true]
  congr 1
  exact propext and_comm

theorem entry_correct {active trans W : Word} (he : Encoded D active trans)
    {R : Fin N → Fin N → Bool} (hR : Represents W R) (cap : ℕ) (hcap : N^width ≤ cap)
    (a b : Fin N) :
    entry N width branch cap active trans W a b = FiniteRefinement.tableStep D.vectors R a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [entry, hR a b, FiniteRefinement.tableStep, Bool.and_eq_true,
    List.all_eq_true, List.mem_range, decide_eq_true_eq, min_eq_left hcap]
  apply and_congr Iff.rfl
  constructor
  · intro h v
    have hh := h (finFunctionFinEquiv v) (finFunctionFinEquiv v).isLt
    simpa only [countMatch_correct D he hR, Equiv.symm_apply_apply] using hh
  · intro h v hv
    rw [countMatch_correct D he hR a ⟨v,hv⟩, countMatch_correct D he hR b ⟨v,hv⟩]
    exact h (finFunctionFinEquiv.symm ⟨v,hv⟩)

theorem lookup_step {active trans W : Word} (cap : ℕ) (a b : Fin N) :
    lookup (step N width branch cap active trans W) a b =
      entry N width branch cap active trans W a b := by
  have hb : Nat.pair a.val b.val < Nat.pair N N+1 := by
    have h1 := Nat.pair_lt_pair_left b.val a.isLt
    have h2 := Nat.pair_lt_pair_right N b.isLt
    omega
  simp only [lookup, step, List.getElem?_map, List.getElem?_range hb, Option.map_some,
    Option.getD_some, Nat.unpair_pair]

theorem step_correct {active trans W : Word} (he : Encoded D active trans)
    {R : Fin N → Fin N → Bool} (hR : Represents W R) (cap : ℕ) (hcap : N^width ≤ cap) :
    Represents (step N width branch cap active trans W) (FiniteRefinement.tableStep D.vectors R) := by
  intro a b
  rw [lookup_step]
  exact entry_correct D he hR cap hcap a b

theorem table_correct {active trans W : Word} (he : Encoded D active trans)
    {R : Fin N → Fin N → Bool} (hR : Represents W R) (cap : ℕ) (hcap : N^width ≤ cap) (s : ℕ) :
    Represents (table N width branch cap active trans W s) (FiniteRefinement.table D.vectors R s) := by
  induction s with
  | zero => exact hR
  | succ s ih =>
    simp only [table, FiniteRefinement.table, Function.iterate_succ_apply'] at *
    exact step_correct D he ih cap hcap

end NumericKernel

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.GraphEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions.BoolPoly
variable {n : ℕ}

theorem eqtest {p q : (Fin n → Word) → Bool} (hp : BoolPoly p) (hq : BoolPoly q) :
    BoolPoly (fun S => decide (p S=q S)) := by
  apply (or (and hp hq) (and (not hp) (not hq))).congr
  intro S
  dsimp only
  cases p S <;> cases q S <;> rfl

theorem propEq {p q : (Fin n → Word) → Prop} [∀ S, Decidable (p S)] [∀ S, Decidable (q S)]
    (hp : BoolPoly (fun S => decide (p S))) (hq : BoolPoly (fun S => decide (q S))) :
    BoolPoly (fun S => decide (p S = q S)) := by
  apply (eqtest hp hq).congr
  intro S
  by_cases h : p S <;> by_cases h' : q S <;> simp [h,h']

end WordExpressions.BoolPoly
namespace NumericGraph
open WordExpressions

theorem edge_poly {m} {n i j : (Fin m → Word) → ℕ} {W : (Fin m → Word) → Word}
    (hn : NatPoly n) (hW : Poly W) (hi : NatPoly i) (hj : NatPoly j) :
    BoolPoly (fun S => edge (n S) (W S) (i S) (j S)) :=
  Poly.nth hW (NatPoly.add (NatPoly.mul hi hn) hj)

theorem simple_poly : BoolPoly (fun S : Fin 2 → Word => simple (S 0).length (S 1)) := by
  unfold simple
  apply BoolPoly.allRange (NatPoly.var 0)
  apply BoolPoly.and
  · apply BoolPoly.not
    apply edge_poly <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · apply BoolPoly.allRange (NatPoly.var 0)
    apply BoolPoly.eqtest <;> apply edge_poly <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

theorem iso_poly : BoolPoly (fun S : Fin 4 → Word => iso (S 0).length (S 1).length (S 2) (S 3)) := by
  unfold iso
  apply BoolPoly.anyRange
  · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · apply BoolPoly.allRange (NatPoly.var 0)
    apply BoolPoly.allRange (NatPoly.var 0)
    apply BoolPoly.and
    · apply BoolPoly.propEq
      · apply NatPoly.eqtest <;> apply NatPoly.digit <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
    · apply BoolPoly.eqtest
      · apply edge_poly <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · apply edge_poly
        · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
        · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
        · apply NatPoly.digit <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
        · apply NatPoly.digit <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

theorem mateEdge_poly {m} {n x i j : (Fin m → Word) → ℕ}
    (hn : NatPoly n) (hx : NatPoly x) (hi : NatPoly i) (hj : NatPoly j) :
    BoolPoly (fun S => mateEdge (n S) (x S) (i S) (j S)) := by
  apply (BoolPoly.and (BoolPoly.not (NatPoly.eqtest hi hj))
    (NatPoly.testBit hx (NatPoly.add (NatPoly.mul (NatPoly.min hi hj) hn) (NatPoly.max hi hj)))).congr
  intro S
  simp only [mateEdge, decide_not]

theorem mate_poly : Poly (fun S : Fin 2 → Word => mate (S 0).length (S 1).length) := by
  unfold mate
  apply Poly.tabulateRange
  · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · apply mateEdge_poly <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

end NumericGraph

namespace NumericGraph

theorem number_lt (W : Word) : number W < 2^W.length := by
  induction W with
  | nil => decide
  | cons b W ih =>
    simp only [number, List.length_cons, pow_succ, Nat.bit_val]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

theorem mateGraph_covers (G : Graph) :
    ∀ i j : Fin G.order, (mateGraph G.order (number (matrixWord G))).edge i j = G.edge i j := by
  intro i j
  change mateEdge G.order (number (matrixWord G)) i j = _
  by_cases he : i=j
  · subst j
    simpa [mateEdge] using (G.loopless i).symm
  · have hv : i.val ≠ j.val := fun h => he (Fin.ext h)
    simp only [mateEdge, hv, ne_eq, not_false_eq_true, decide_true, Bool.true_and, testBit_number]
    by_cases h : i.val ≤ j.val
    · rw [min_eq_left h, max_eq_right h]
      exact edge_matrixWord G i j
    · rw [min_eq_right (by omega), max_eq_left (by omega)]
      exact (edge_matrixWord G j i).trans (G.symmetric j i)

theorem iso_correct (n cap : ℕ) (W V : Word) (hsW : simple n W = true) (hsV : simple n V = true)
    (hcap : n^n ≤ cap) :
    iso n cap W V = true ↔ Isomorphic (ofWord n W hsW) (ofWord n V hsV) := by
  simp only [iso, min_eq_left hcap, List.any_eq_true, List.mem_range, List.all_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨f,hf,h⟩
    let d : Fin n → Fin n := finFunctionFinEquiv.symm ⟨f,hf⟩
    have hd : Function.Injective d := by
      intro i j hij
      have hh := (h i i.isLt j j.isLt).1
      have he : NumericKernel.digit n f i = NumericKernel.digit n f j := congrArg Fin.val hij
      exact Fin.ext (Eq.mp hh he)
    have hb : Function.Bijective d := (Finite.injective_iff_bijective).mp hd
    refine ⟨Equiv.ofBijective d hb, ?_⟩
    intro i j
    exact (h i i.isLt j j.isLt).2
  · rintro ⟨e,he⟩
    let c := finFunctionFinEquiv e
    refine ⟨c,c.isLt,?_⟩
    intro i hi j hj
    have hd (a : Fin n) : NumericKernel.digit n c a = (e a).val :=
      congrArg (fun f => (f a).val) (finFunctionFinEquiv.symm_apply_apply e)
    rw [hd ⟨i,hi⟩, hd ⟨j,hj⟩]
    refine ⟨propext ?_, ?_⟩
    · exact ⟨fun h => congrArg Fin.val (e.injective (Fin.ext h)),
        fun h => congrArg (fun x : Fin n => (e x).val) (Fin.ext h)⟩
    · exact he ⟨i,hi⟩ ⟨j,hj⟩

end NumericGraph

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.NumericRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace NumericWL
open WordExpressions

theorem left_poly {m} {t a : (Fin m → Word) → ℕ} (ht : NatPoly t) (ha : NatPoly a) :
    BoolPoly (fun S => left (t S) (a S)) := NatPoly.lt ha ht

theorem code_poly {m} {t a : (Fin m → Word) → ℕ} (ht : NatPoly t) (ha : NatPoly a) :
    NatPoly (fun S => code (t S) (a S)) := NatPoly.iteProp (NatPoly.lt ha ht) ha (NatPoly.sub ha ht)

theorem selectedEdge_poly {m} {n t a i j : (Fin m → Word) → ℕ}
    {W V : (Fin m → Word) → Word} (hn : NatPoly n) (ht : NatPoly t) (hW : Poly W) (hV : Poly V)
    (ha : NatPoly a) (hi : NatPoly i) (hj : NatPoly j) :
    BoolPoly (fun S => selectedEdge (n S) (t S) (W S) (V S) (a S) (i S) (j S)) :=
  BoolPoly.ite (left_poly ht ha) (NumericGraph.edge_poly hn hW hi hj) (NumericGraph.edge_poly hn hV hi hj)

theorem equalCounts_poly : BoolPoly (fun S : Fin 2 → Word => equalCounts (S 0).length (S 1)) := by
  unfold equalCounts
  apply BoolPoly.allRange
  · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · apply NatPoly.eqtest <;> apply NatPoly.sumRange
    · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
    · apply NatPoly.ite
      · unfold NumericKernel.lookup
        (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
    · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
    · apply NatPoly.ite
      · unfold NumericKernel.lookup
        (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

theorem neighborActive_poly : BoolPoly (fun S : Fin 5 → Word =>
    neighborActive (S 0).length (S 1) (S 2) (S 3).length (S 4).length) := by
  unfold neighborActive
  apply selectedEdge_poly <;> first | apply code_poly <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange) | (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

theorem neighborTrans_poly : BoolPoly (fun S : Fin 5 → Word =>
    neighborTrans (S 0).length (S 1).length (S 2).length (S 3).length (S 4).length) := by
  unfold neighborTrans
  apply BoolPoly.and
  · apply BoolPoly.eqtest <;> apply left_poly <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · apply NatPoly.eqtest
    · apply code_poly <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
    · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

theorem tupleInitial_poly : BoolPoly (fun S : Fin 7 → Word => tupleInitial
    (S 0).length (S 1).length (S 2).length (S 3) (S 4) (S 5).length (S 6).length) := by
  unfold tupleInitial
  apply BoolPoly.allRange (NatPoly.var 1)
  apply BoolPoly.allRange (NatPoly.var 1)
  apply BoolPoly.and
  · apply BoolPoly.propEq <;> apply NatPoly.eqtest <;> apply NatPoly.digit
    all_goals first | apply code_poly <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange) | (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · apply BoolPoly.eqtest <;> apply selectedEdge_poly
    all_goals repeat' first | apply NatPoly.digit | apply code_poly | solve | (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

theorem tupleTrans_poly : BoolPoly (fun S : Fin 7 → Word => tupleTrans
    (S 0).length (S 1).length (S 2).length (S 3).length (S 4).length (S 5).length (S 6).length) := by
  unfold tupleTrans
  apply BoolPoly.and
  · apply BoolPoly.eqtest <;> apply left_poly <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · apply BoolPoly.allRange (NatPoly.var 1)
    apply NatPoly.eqtest
    · apply NatPoly.digit
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · apply code_poly <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
    · apply NatPoly.iteProp
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · apply NatPoly.digit
        · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
        · apply code_poly <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
        · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

end NumericWL

namespace NumericKernel
open WordExpressions

theorem table_poly_of {m} {N : (Fin m → Word) → ℕ} {w : (Fin m → Word) → ℕ} {b : (Fin m → Word) → ℕ} {c : (Fin m → Word) → ℕ} {ac : (Fin m → Word) → Word} {tr : (Fin m → Word) → Word} {ini : (Fin m → Word) → Word} {r : (Fin m → Word) → ℕ}
    (h_N : NatPoly N)    (h_w : NatPoly w)    (h_b : NatPoly b)    (h_c : NatPoly c)    (h_ac : Poly ac)    (h_tr : Poly tr)    (h_ini : Poly ini)    (h_r : NatPoly r) :
    Poly (fun S => table (N S) (w S) (b S) (c S) (ac S) (tr S) (ini S) (r S)) := by
  have h := table_poly.subst (g := ![fun S => unary (N S),fun S => unary (w S),fun S => unary (b S),fun S => unary (c S),ac,tr,ini,fun S => unary (r S)])
    (by intro i; fin_cases i; exacts [h_N,h_w,h_b,h_c,h_ac,h_tr,h_ini,h_r])
  simpa [unary] using h

end NumericKernel
namespace NumericWL
open WordExpressions

theorem equalCounts_poly_of {m} {t : (Fin m → Word) → ℕ} {W : (Fin m → Word) → Word}
    (h_t : NatPoly t)    (h_W : Poly W) :
    BoolPoly (fun S => equalCounts (t S) (W S)) := by
  have h := equalCounts_poly.subst (g := ![fun S => unary (t S),W])
    (by intro i; fin_cases i; exacts [h_t,h_W])
  simpa [unary] using h

end NumericWL
namespace NumericWL
open WordExpressions

theorem neighborActive_poly_of {m} {n : (Fin m → Word) → ℕ} {W : (Fin m → Word) → Word} {V : (Fin m → Word) → Word} {a : (Fin m → Word) → ℕ} {z : (Fin m → Word) → ℕ}
    (h_n : NatPoly n)    (h_W : Poly W)    (h_V : Poly V)    (h_a : NatPoly a)    (h_z : NatPoly z) :
    BoolPoly (fun S => neighborActive (n S) (W S) (V S) (a S) (z S)) := by
  have h := neighborActive_poly.subst (g := ![fun S => unary (n S),W,V,fun S => unary (a S),fun S => unary (z S)])
    (by intro i; fin_cases i; exacts [h_n,h_W,h_V,h_a,h_z])
  simpa [unary] using h

end NumericWL
namespace NumericWL
open WordExpressions

theorem neighborTrans_poly_of {m} {n : (Fin m → Word) → ℕ} {a : (Fin m → Word) → ℕ} {z : (Fin m → Word) → ℕ} {i : (Fin m → Word) → ℕ} {y : (Fin m → Word) → ℕ}
    (h_n : NatPoly n)    (h_a : NatPoly a)    (h_z : NatPoly z)    (h_i : NatPoly i)    (h_y : NatPoly y) :
    BoolPoly (fun S => neighborTrans (n S) (a S) (z S) (i S) (y S)) := by
  have h := neighborTrans_poly.subst (g := ![fun S => unary (n S),fun S => unary (a S),fun S => unary (z S),fun S => unary (i S),fun S => unary (y S)])
    (by intro i; fin_cases i; exacts [h_n,h_a,h_z,h_i,h_y])
  simpa [unary] using h

end NumericWL
namespace NumericWL
open WordExpressions

theorem tupleInitial_poly_of {m} {n : (Fin m → Word) → ℕ} {k : (Fin m → Word) → ℕ} {t : (Fin m → Word) → ℕ} {W : (Fin m → Word) → Word} {V : (Fin m → Word) → Word} {a : (Fin m → Word) → ℕ} {b : (Fin m → Word) → ℕ}
    (h_n : NatPoly n)    (h_k : NatPoly k)    (h_t : NatPoly t)    (h_W : Poly W)    (h_V : Poly V)    (h_a : NatPoly a)    (h_b : NatPoly b) :
    BoolPoly (fun S => tupleInitial (n S) (k S) (t S) (W S) (V S) (a S) (b S)) := by
  have h := tupleInitial_poly.subst (g := ![fun S => unary (n S),fun S => unary (k S),fun S => unary (t S),W,V,fun S => unary (a S),fun S => unary (b S)])
    (by intro i; fin_cases i; exacts [h_n,h_k,h_t,h_W,h_V,h_a,h_b])
  simpa [unary] using h

end NumericWL
namespace NumericWL
open WordExpressions

theorem tupleTrans_poly_of {m} {n : (Fin m → Word) → ℕ} {k : (Fin m → Word) → ℕ} {t : (Fin m → Word) → ℕ} {a : (Fin m → Word) → ℕ} {z : (Fin m → Word) → ℕ} {i : (Fin m → Word) → ℕ} {y : (Fin m → Word) → ℕ}
    (h_n : NatPoly n)    (h_k : NatPoly k)    (h_t : NatPoly t)    (h_a : NatPoly a)    (h_z : NatPoly z)    (h_i : NatPoly i)    (h_y : NatPoly y) :
    BoolPoly (fun S => tupleTrans (n S) (k S) (t S) (a S) (z S) (i S) (y S)) := by
  have h := tupleTrans_poly.subst (g := ![fun S => unary (n S),fun S => unary (k S),fun S => unary (t S),fun S => unary (a S),fun S => unary (z S),fun S => unary (i S),fun S => unary (y S)])
    (by intro i; fin_cases i; exacts [h_n,h_k,h_t,h_a,h_z,h_i,h_y])
  simpa [unary] using h

end NumericWL

namespace NumericGraph
open WordExpressions

theorem simple_poly_of {m} {n : (Fin m → Word) → ℕ} {W : (Fin m → Word) → Word}
    (h_n : NatPoly n)    (h_W : Poly W) :
    BoolPoly (fun S => simple (n S) (W S)) := by
  have h := simple_poly.subst (g := ![fun S => unary (n S),W])
    (by intro i; fin_cases i; exacts [h_n,h_W])
  simpa [unary] using h

end NumericGraph
namespace NumericGraph
open WordExpressions

theorem iso_poly_of {m} {n : (Fin m → Word) → ℕ} {c : (Fin m → Word) → ℕ} {W : (Fin m → Word) → Word} {V : (Fin m → Word) → Word}
    (h_n : NatPoly n)    (h_c : NatPoly c)    (h_W : Poly W)    (h_V : Poly V) :
    BoolPoly (fun S => iso (n S) (c S) (W S) (V S)) := by
  have h := iso_poly.subst (g := ![fun S => unary (n S),fun S => unary (c S),W,V])
    (by intro i; fin_cases i; exacts [h_n,h_c,h_W,h_V])
  simpa [unary] using h

end NumericGraph
namespace NumericGraph
open WordExpressions

theorem mate_poly_of {m} {n : (Fin m → Word) → ℕ} {mask : (Fin m → Word) → ℕ}
    (h_n : NatPoly n)    (h_mask : NatPoly mask) :
    Poly (fun S => mate (n S) (mask S)) := by
  have h := mate_poly.subst (g := ![fun S => unary (n S),fun S => unary (mask S)])
    (by intro i; fin_cases i; exacts [h_n,h_mask])
  simpa [unary] using h

end NumericGraph

namespace NumericWL
open WordExpressions

theorem neighborActiveTable_poly : Poly (fun S : Fin 3 → Word =>
    pairTable ((S 0).length+(S 0).length) (neighborActive (S 0).length (S 1) (S 2))) := by
  unfold pairTable
  apply Poly.tabulateRange
  · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · apply neighborActive_poly_of <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

theorem neighborTransTable_poly : Poly (fun S : Fin 1 → Word =>
    transTable ((S 0).length+(S 0).length) 1 (S 0).length (neighborTrans (S 0).length)) := by
  unfold transTable
  apply Poly.tabulateRange
  · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · exact neighborTrans_poly_of (NatPoly.var 0) ((NatPoly.var 1).unpair_fst)
      ((NatPoly.var 1).unpair_snd.unpair_fst) ((NatPoly.var 1).unpair_snd.unpair_snd.unpair_fst)
      ((NatPoly.var 1).unpair_snd.unpair_snd.unpair_snd)

theorem trueTable_poly {m} {N : (Fin m → Word) → ℕ} (hN : NatPoly N) :
    Poly (fun S => pairTable (N S) (fun _ _ => true)) := by
  unfold pairTable
  exact Poly.tabulateRange (NatPoly.succ (NatPoly.pair hN hN)) (BoolPoly.const true)

theorem tupleInitialTable_poly : Poly (fun S : Fin 5 → Word =>
    pairTable ((S 2).length+(S 2).length)
      (tupleInitial (S 0).length (S 1).length (S 2).length (S 3) (S 4))) := by
  unfold pairTable
  apply Poly.tabulateRange
  · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · apply tupleInitial_poly_of <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

theorem tupleTransTable_poly : Poly (fun S : Fin 3 → Word =>
    transTable ((S 2).length+(S 2).length) (S 1).length (S 0).length
      (tupleTrans (S 0).length (S 1).length (S 2).length)) := by
  unfold transTable
  apply Poly.tabulateRange
  · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · exact tupleTrans_poly_of (NatPoly.var 0) (NatPoly.var 1) (NatPoly.var 2)
      ((NatPoly.var 3).unpair_fst) ((NatPoly.var 3).unpair_snd.unpair_fst)
      ((NatPoly.var 3).unpair_snd.unpair_snd.unpair_fst) ((NatPoly.var 3).unpair_snd.unpair_snd.unpair_snd)

end NumericWL

namespace NumericWL
open WordExpressions

theorem neighborActiveTable_poly_of {m} {n : (Fin m → Word) → ℕ} {W V : (Fin m → Word) → Word}
    (hn : NatPoly n) (hW : Poly W) (hV : Poly V) :
    Poly (fun S => pairTable (n S+n S) (neighborActive (n S) (W S) (V S))) := by
  have h := neighborActiveTable_poly.subst (g := ![fun S => unary (n S),W,V])
    (by intro i; fin_cases i; exacts [hn,hW,hV])
  simpa [unary] using h

theorem neighborTransTable_poly_of {m} {n : (Fin m → Word) → ℕ} (hn : NatPoly n) :
    Poly (fun S => transTable (n S+n S) 1 (n S) (neighborTrans (n S))) := by
  have h := neighborTransTable_poly.subst (g := ![fun S => unary (n S)])
    (by intro i; fin_cases i; exact hn)
  simpa [unary] using h

theorem tupleInitialTable_poly_of {m} {n k t : (Fin m → Word) → ℕ} {W V : (Fin m → Word) → Word}
    (hn : NatPoly n) (hk : NatPoly k) (ht : NatPoly t) (hW : Poly W) (hV : Poly V) :
    Poly (fun S => pairTable (t S+t S) (tupleInitial (n S) (k S) (t S) (W S) (V S))) := by
  have h := tupleInitialTable_poly.subst (g := ![fun S => unary (n S),fun S => unary (k S),
    fun S => unary (t S),W,V]) (by intro i; fin_cases i; exacts [hn,hk,ht,hW,hV])
  simpa [unary] using h

theorem tupleTransTable_poly_of {m} {n k t : (Fin m → Word) → ℕ}
    (hn : NatPoly n) (hk : NatPoly k) (ht : NatPoly t) :
    Poly (fun S => transTable (t S+t S) (k S) (n S) (tupleTrans (n S) (k S) (t S))) := by
  have h := tupleTransTable_poly.subst (g := ![fun S => unary (n S),fun S => unary (k S),
    fun S => unary (t S)]) (by intro i; fin_cases i; exacts [hn,hk,ht])
  simpa [unary] using h

theorem neighbor_poly_of {m} {n c : (Fin m → Word) → ℕ} {W V : (Fin m → Word) → Word}
    (hn : NatPoly n) (hc : NatPoly c) (hW : Poly W) (hV : Poly V) :
    BoolPoly (fun S => neighbor (n S) (c S) (W S) (V S)) := by
  exact equalCounts_poly_of hn (NumericKernel.table_poly_of (hn.add hn) (NatPoly.const 1) hn hc
    (neighborActiveTable_poly_of hn hW hV) (neighborTransTable_poly_of hn)
    (trueTable_poly (hn.add hn)) ((hn.add hn).mul (hn.add hn)))

theorem tuple_poly_of {m} {n k c : (Fin m → Word) → ℕ} {W V : (Fin m → Word) → Word}
    (hn : NatPoly n) (hk : NatPoly k) (hc : NatPoly c) (hW : Poly W) (hV : Poly V) :
    BoolPoly (fun S => tuple (n S) (k S) (c S) (W S) (V S)) := by
  have ht := NatPoly.cappedPow hn hk hc
  exact equalCounts_poly_of ht (NumericKernel.table_poly_of (ht.add ht) hk hn hc
    (trueTable_poly (ht.add ht)) (tupleTransTable_poly_of hn hk ht)
    (tupleInitialTable_poly_of hn hk ht hW hV) ((ht.add ht).mul (ht.add ht)))

theorem equivalent_poly_of {m} {n k c : (Fin m → Word) → ℕ} {W V : (Fin m → Word) → Word}
    (hn : NatPoly n) (hk : NatPoly k) (hc : NatPoly c) (hW : Poly W) (hV : Poly V) :
    BoolPoly (fun S => equivalent (n S) (k S) (c S) (W S) (V S)) :=
  BoolPoly.iteProp (NatPoly.eqtest hk (NatPoly.const 1))
    (neighbor_poly_of hn hc hW hV) (tuple_poly_of hn hk hc hW hV)

end NumericWL

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.RefinementCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace NumericWL
open NumericKernel

theorem pair_bound {N a b : ℕ} (ha : a<N) (hb : b<N) : Nat.pair a b < Nat.pair N N+1 := by
  have h1 := Nat.pair_lt_pair_left b ha
  have h2 := Nat.pair_lt_pair_right N hb
  omega

theorem pairTable_lookup (N : ℕ) (p : ℕ → ℕ → Bool) (a b : Fin N) :
    lookup (pairTable N p) a b = p a b := by
  simp only [lookup, pairTable, List.getElem?_map,
    List.getElem?_range (pair_bound a.isLt b.isLt), Option.map_some, Option.getD_some, Nat.unpair_pair]

theorem transTable_lookup (N width branch : ℕ) (p : ℕ → ℕ → ℕ → ℕ → Bool)
    (a : Fin N) (z : Fin branch) (i : Fin width) (y : Fin N) :
    (transTable N width branch p)[Nat.pair a (Nat.pair z (Nat.pair i y))]?.getD false = p a z i y := by
  have h (a b c d : ℕ) (ha : a<c) (hb : b<d) : Nat.pair a b < Nat.pair c d :=
    (Nat.pair_lt_pair_left b ha).trans (Nat.pair_lt_pair_right c hb)
  have hh := h _ _ _ _ a.isLt (h _ _ _ _ z.isLt (h _ _ _ _ i.isLt y.isLt))
  simp only [transTable, List.getElem?_map, List.getElem?_range (Nat.lt_succ_of_lt hh),
    Option.map_some, Option.getD_some, Nat.unpair_pair]

theorem equalCounts_correct {t : ℕ} (W : Word) {C : Type} [DecidableEq C]
    (c : Fin (t+t) → C) (hW : ∀ a b : Fin (t+t), lookup W a b = true ↔ c a = c b) :
    equalCounts t W = true ↔
    (Finset.univ.val.map (fun x => c (sides t (.inl x)))) =
    (Finset.univ.val.map (fun x => c (sides t (.inr x)))) := by
  let L : Multiset (Fin (t+t)) := Finset.univ.val.map (fun x => sides t (.inl x))
  let R : Multiset (Fin (t+t)) := Finset.univ.val.map (fun x => sides t (.inr x))
  suffices h : equalCounts t W = true ↔ L.map c = R.map c by
    simpa only [L, R, Multiset.map_map, Function.comp_def] using h
  rw [FiniteRefinement.map_eq_iff_counts]
  simp only [equalCounts, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  have hc (a : Fin (t+t)) (f : Fin t → Fin (t+t)) :
      ((Finset.univ : Finset (Fin t)).val.map f).countP (fun b => c b = c a) =
      ∑ b : Fin t, if lookup W (f b) a then 1 else 0 := by
    rw [Multiset.countP_map, ← Multiset.countP_eq_card_filter, multiset_countP_sum]
    apply Finset.sum_congr rfl
    intro b _
    simp only [hW]
  constructor
  · intro h a
    rw [hc, hc]
    have he := h a a.isLt
    simp only [sum_range_fin, sides_inl, sides_inr] at he ⊢
    convert he using 1 <;> rfl
  · intro h a ha
    have he := h ⟨a,ha⟩
    rw [hc, hc] at he
    simp only [sum_range_fin, sides_inl, sides_inr] at he ⊢
    convert he using 1 <;> rfl

theorem neighborEncoded (n : ℕ) (W V : Word) :
    Encoded (neighborData n W V)
      (pairTable (n+n) (neighborActive n W V)) (transTable (n+n) 1 n (neighborTrans n)) := by
  constructor
  · intro a z
    exact pairTable_lookup _ _ a ⟨z.val,by omega⟩
  · intro a z i y
    rw [transTable_lookup]
    obtain ⟨a,rfl⟩ := (sides n).surjective a
    obtain ⟨y,rfl⟩ := (sides n).surjective y
    cases a <;> cases y <;>
      simp only [neighborTrans, neighborData, Equiv.symm_apply_apply, left_inl, left_inr,
        code_inl, code_inr, Equiv.apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq,
        Sum.inl_ne_inr, Sum.inr_ne_inl, decide_true, decide_false,
        Bool.true_and, Fin.ext_iff]
    all_goals simp [eq_comm]

theorem neighbor_vectors (n : ℕ) (W V : Word) (hW : NumericGraph.simple n W = true) (hV : NumericGraph.simple n V = true)
    (s : ℕ) (a : Fin n ⊕ Fin n) :
    ((neighborData n W V).vectors (sides n a)).map (fun v i => nc n W V hW hV s (v i)) =
    ((FiniteWL.neighbors (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) a).map
      (FiniteWL.neighbor (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) s)).map
      (fun c (_ : Fin 1) => c) := by
  cases a <;>
    simp only [Data.vectors, neighborData, neighborActive, selectedEdge, nc, FiniteWL.neighbors,
      NumericGraph.ofWord, Multiset.map_map, Function.comp_def, Equiv.symm_apply_apply,
      left_inl, left_inr, code_inl, code_inr, Bool.false_eq_true,
      ↓reduceIte, Finset.filter_val]

theorem neighbor_correct (n cap : ℕ) (W V : Word)
    (hW : NumericGraph.simple n W = true) (hV : NumericGraph.simple n V = true) (hcap : n+n ≤ cap) :
    neighbor n cap W V = true ↔
    Equivalent 1 (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) := by
  classical
  let c := nc n W V hW hV
  have hnext (s : ℕ) (a b : Fin (n+n)) : c (s+1) a = c (s+1) b ↔ c s a = c s b ∧
      ((neighborData n W V).vectors a).map (fun v i => c s (v i)) =
      ((neighborData n W V).vectors b).map (fun v i => c s (v i)) := by
    obtain ⟨a,rfl⟩ := (sides n).surjective a
    obtain ⟨b,rfl⟩ := (sides n).surjective b
    rw [neighbor_vectors, neighbor_vectors]
    have hinj : Function.Injective (fun x : NeighborColor s => fun _ : Fin 1 => x) :=
      fun x y h => congrFun h 0
    rw [(Multiset.map_injective hinj).eq_iff]
    simp only [c, nc, Equiv.symm_apply_apply]
    exact FiniteWL.neighbor_update (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) s a b
  have hi (a b : Fin (n+n)) : true = true ↔ c 0 a = c 0 b := by
    exact iff_of_true rfl (@Subsingleton.elim Unit inferInstance _ _)
  have hr : Represents (pairTable (n+n) (fun _ _ => true)) (fun _ _ : Fin (n+n) => true) :=
    pairTable_lookup _ _
  have htab := table_correct (neighborData n W V) (neighborEncoded n W V) hr cap
    (by simpa using hcap) ((n+n)^2)
  have hc (a b : Fin (n+n)) := FiniteRefinement.table_correct c (neighborData n W V).vectors hnext
      (fun _ _ => true) hi ((n+n)^2) a b
  rw [neighbor, ← pow_two, equalCounts_correct _ (c ((n+n)^2)) (fun a b => by rw [htab a b]; exact hc a b)]
  rw [FiniteWL.equivalent_cutoff]
  simp only [↓reduceIte, c, nc, Equiv.symm_apply_apply, FiniteWL.neighbor, Sum.elim_inl,
    Sum.elim_inr, neighborHistogram, NumericGraph.ofWord]

end NumericWL

namespace NumericWL
open NumericKernel

theorem digit_function {n k : ℕ} (v : Fin k → Fin n) (i : Fin k) :
    digit n (finFunctionFinEquiv v) i = (v i).val :=
  congrArg (fun f => (f i).val) (finFunctionFinEquiv.symm_apply_apply v)

theorem digits_update {n k : ℕ} (v w : Fin k → Fin n) (i : Fin k) (z : Fin n) :
    (∀ j<k, digit n (finFunctionFinEquiv w) j =
      if j=i.val then z.val else digit n (finFunctionFinEquiv v) j) ↔ Function.update v i z = w := by
  constructor
  · intro h
    funext j
    apply Fin.ext
    have hh := h j j.isLt
    rw [digit_function w j, digit_function v j] at hh
    by_cases he : j=i
    · subst j
      simpa only [Function.update_self, ↓reduceIte] using hh.symm
    · have hn : j.val ≠ i.val := fun h => he (Fin.ext h)
      simpa only [Function.update_of_ne he, hn, ↓reduceIte] using hh.symm
  · rintro rfl j hj
    let jj : Fin k := ⟨j,hj⟩
    rw [digit_function (Function.update v i z) jj, digit_function v jj]
    by_cases he : jj=i
    · have hv : j=i.val := congrArg Fin.val he
      simp only [he, Function.update_self, hv, ↓reduceIte]
    · have hn : j ≠ i.val := fun h => he (Fin.ext h)
      simp only [Function.update_of_ne he, hn, ↓reduceIte]

theorem tupleEncoded (n k : ℕ) (hk : 0<k) : Encoded (tupleData n k)
    (pairTable (n^k+n^k) (fun _ _ => true))
    (transTable (n^k+n^k) k n (tupleTrans n k (n^k))) := by
  constructor
  · intro a z
    unfold lookup pairTable
    -- Active is true; this table stores slots at least as far as every branch.
    have hz : z.val < n^k+n^k := by
      have hn : 0<n := Nat.zero_lt_of_lt z.isLt
      have hn' : n ≤ n^k := by simpa using Nat.pow_le_pow_right hn hk
      omega
    simp only [List.getElem?_map, List.getElem?_range (pair_bound a.isLt hz),
      Option.map_some, Option.getD_some, tupleData]
  · intro a z i y
    rw [transTable_lookup]
    obtain ⟨a,rfl⟩ := (te n k).surjective a
    obtain ⟨y,rfl⟩ := (te n k).surjective y
    simp only [tupleData, Equiv.symm_apply_apply]
    cases a <;> cases y <;>
      simp only [Equiv.apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
    all_goals apply Bool.eq_iff_iff.mpr
    all_goals simp only [tupleTrans, te_inl, te_inr, left_inl, left_inr, code_inl, code_inr,
      Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    all_goals first | simpa only [true_and] using digits_update _ _ _ _ | simp

end NumericWL

namespace NumericWL
open NumericKernel

theorem tuple_vectors (n k : ℕ) (W V : Word) (hW : NumericGraph.simple n W = true) (hV : NumericGraph.simple n V = true)
    (s : ℕ) (a : tuples n k) :
    ((tupleData n k).vectors (te n k a)).map (fun v i => tc n k W V hW hV s (v i)) =
    (FiniteWL.vectors (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) k a).map
      (fun v i => FiniteWL.tuple (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) k s (v i)) := by
  cases a <;>
    simp only [Data.vectors, tupleData, tc, FiniteWL.vectors, Equiv.symm_apply_apply,
      Finset.filter_true, Multiset.map_map, Function.comp_def]

theorem forall_bound2 {k : ℕ} {p : ℕ → ℕ → Prop} :
    (∀ i<k, ∀ j<k, p i j) ↔ ∀ i j : Fin k, p i j := by
  exact ⟨fun h i j => h i i.isLt j j.isLt, fun h i hi j hj => h ⟨i,hi⟩ ⟨j,hj⟩⟩

theorem tupleInitial_correct (n k : ℕ) (W V : Word)
    (hW : NumericGraph.simple n W = true) (hV : NumericGraph.simple n V = true)
    (a b : Fin (n^k+n^k)) : tupleInitial n k (n^k) W V a b = true ↔ tc n k W V hW hV 0 a = tc n k W V hW hV 0 b := by
  obtain ⟨a,rfl⟩ := (te n k).surjective a
  obtain ⟨b,rfl⟩ := (te n k).surjective b
  simp only [tc, Equiv.symm_apply_apply]
  cases a <;> cases b <;>
    dsimp only [FiniteWL.tuple, Sum.elim, tupleColor, TupleColor]
  all_goals
    simp only [
      Prod.mk.injEq, funext_iff, tupleInitial, List.all_eq_true, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq, forall_bound2, te_inl, te_inr, code_inl, code_inr,
      digit_function, selectedEdge, left_inl, left_inr, Bool.false_eq_true, ↓reduceIte,
      Fin.ext_iff, decide_eq_decide, forall_and, eq_iff_iff]

theorem tuple_correct (n k cap : ℕ) (W V : Word)
    (hW : NumericGraph.simple n W = true) (hV : NumericGraph.simple n V = true)
    (hk : 0<k) (hk1 : k≠1) (ht : n^k ≤ cap) (hcap : (n^k+n^k)^k ≤ cap) :
    tuple n k cap W V = true ↔
    Equivalent k (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) := by
  classical
  let c := tc n k W V hW hV
  have hnext (s : ℕ) (a b : Fin (n^k+n^k)) : c (s+1) a = c (s+1) b ↔ c s a = c s b ∧
      ((tupleData n k).vectors a).map (fun v i => c s (v i)) =
      ((tupleData n k).vectors b).map (fun v i => c s (v i)) := by
    obtain ⟨a,rfl⟩ := (te n k).surjective a
    obtain ⟨b,rfl⟩ := (te n k).surjective b
    rw [tuple_vectors, tuple_vectors]
    simp only [c, tc, Equiv.symm_apply_apply]
    exact FiniteWL.tuple_update (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) k s a b
  have hi := tupleInitial_correct n k W V hW hV
  have hr : Represents (pairTable (n^k+n^k) (tupleInitial n k (n^k) W V))
      (fun a b : Fin (n^k+n^k) => tupleInitial n k (n^k) W V a b) := pairTable_lookup _ _
  have htab := table_correct (tupleData n k) (tupleEncoded n k hk) hr cap hcap ((n^k+n^k)^2)
  have hc (a b : Fin (n^k+n^k)) := FiniteRefinement.table_correct c (tupleData n k).vectors hnext
      (fun a b => tupleInitial n k (n^k) W V a b) hi ((n^k+n^k)^2) a b
  rw [tuple, min_eq_left ht, ← pow_two,
    equalCounts_correct _ (c ((n^k+n^k)^2)) (fun a b => by rw [htab a b]; exact hc a b)]
  rw [FiniteWL.equivalent_cutoff, ite_eq_right hk1]
  have he (X : Graph) (s : ℕ) :
      (Finset.univ : Finset (Fin (X.order^k))).val.map (fun x =>
        tupleColor X k s (finFunctionFinEquiv.symm x)) = tupleHistogram X k s := by
    unfold tupleHistogram
    rw [← Multiset.map_univ_val_equiv (finFunctionFinEquiv.symm : Fin (X.order^k) ≃ (Fin k → Fin X.order)),
      Multiset.map_map]
    rfl
  -- The concrete equality below is proved by multiset reindexing, without
  -- identifying tuple colors pointwise between distinct dimension types.
  simp only [c, tc, te_symm_inl, te_symm_inr, FiniteWL.tuple, Sum.elim_inl, Sum.elim_inr]
  rw [he (NumericGraph.ofWord n W hW) ((n^k+n^k)^2), he (NumericGraph.ofWord n V hV) ((n^k+n^k)^2)]

end NumericWL

namespace WordExpressions.Poly
variable {n : ℕ}

theorem eqtest {u v : (Fin n → Word) → Word} (hu : Poly u) (hv : Poly v) :
    BoolPoly (fun S => decide (u S=v S)) := by
  have h := BoolPoly.and (NatPoly.eqtest (NatPoly.length hu) (NatPoly.length hv))
    (BoolPoly.allRange (p := fun S i => decide ((u S)[i]?.getD false = (v S)[i]?.getD false)) (NatPoly.length hu) (BoolPoly.eqtest
      (Poly.nth (hu.rename Fin.castSucc) (NatPoly.var (Fin.last n)))
      (Poly.nth (hv.rename Fin.castSucc) (NatPoly.var (Fin.last n)))))
  apply h.congr
  intro S
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hl,h⟩
    apply List.ext_getElem hl
    intro i hi hi'
    have hh := h i hi
    simpa only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi', Option.getD_some] using hh
  · intro he
    rw [he]
    exact ⟨rfl, fun _ _ => rfl⟩

end WordExpressions.Poly

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.DimensionDecider
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace NumericGraph

@[simp] theorem matrixWord_ofWord (n : ℕ) (W : Word) (h : simple n W = true) (hl : W.length=n*n) :
    matrixWord (ofWord n W h) = W := by
  apply List.ext_getElem (by simp [hl])
  intro t ht ht'
  have hn : 0<n := by have := Nat.zero_lt_of_lt ht'; rw [hl] at this; nlinarith
  let i : Fin n := ⟨t/n, (Nat.div_lt_iff_lt_mul hn).mpr (by simpa [hl] using ht')⟩
  let j : Fin n := ⟨t%n, Nat.mod_lt _ hn⟩
  have hij : i.val*n+j.val=t := by simpa only [i, j, Nat.mul_comm] using Nat.div_add_mod t n
  have hh := edge_matrixWord (ofWord n W h) i j
  change (matrixWord (ofWord n W h))[i.val*n+j.val]?.getD false = W[i.val*n+j.val]?.getD false at hh
  rw [hij, List.getElem?_eq_getElem ht, List.getElem?_eq_getElem ht'] at hh
  exact hh

end NumericGraph

/-- Positive-dimensional equivalence always fixes the order, even for the
ordinary-neighbor dimension-one convention. -/
theorem equivalent_order {G H : Graph} {k : ℕ} (hk : 0<k) (h : Equivalent k G H) : G.order=H.order := by
  by_cases hk1 : k=1
  · subst k
    have hh := congrArg Multiset.card ((show ∀ s, neighborHistogram G s=neighborHistogram H s from h) 0)
    simpa [neighborHistogram] using hh
  · obtain ⟨e,_⟩ := equivalent_degreeBijection (by omega) h
    simpa using Fintype.card_congr e

/-- Exhaustive masks suffice for all mates because order equality is proved,
not inserted as an extra hypothesis in identification. -/
theorem identifies_iff_masks (G : Graph) (k : ℕ) (hk : 0<k) : Identifies k G ↔
    ∀ x<2^(G.order*G.order), Equivalent k G (NumericGraph.mateGraph G.order x) →
      Isomorphic G (NumericGraph.mateGraph G.order x) := by
  constructor
  · intro h x _; exact h _
  · intro h H hH
    have hn := equivalent_order hk hH
    let x := NumericGraph.number (matrixWord H)
    have hx : x<2^(G.order*G.order) := by
      simpa [x, matrixWord_length, hn] using NumericGraph.number_lt (matrixWord H)
    have he : NumericGraph.mateGraph G.order x=H := by
      cases H with
      | mk m ed hs hl =>
        dsimp only at hn
        subst m
        apply Graph.ext (NumericGraph.mateGraph G.order x) ⟨G.order,ed,hs,hl⟩ rfl
        intro i j
        exact NumericGraph.mateGraph_covers ⟨G.order,ed,hs,hl⟩ i j
    simpa only [he] using h x hx (by simpa only [he] using hH)

namespace DimensionDecider

theorem valid_iff (n : ℕ) (w : Word) : valid n w = true ↔
    0<n ∧ w.take (n+1) = List.replicate n true ++ [false] ∧
      (matrix n w).length=n*n ∧ ∃ t, bits n w = true::t := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq]
  have hb : (bits n w)[0]?.getD false = true ↔ ∃ t, bits n w=true::t := by
    cases bits n w with
    | nil => simp
    | cons b w => cases b <;> simp
  rw [hb]
  tauto

theorem binaryValue_leading_pos {w : Word} (h : ∃ t, w=true::t) : 0<binaryValue w := by
  obtain ⟨t,rfl⟩ := h
  have ha (t : Word) (c : ℕ) (hc : 0<c) : 0<t.foldl (fun z b => 2*z+if b then 1 else 0) c := by
    induction t generalizing c with
    | nil => exact hc
    | cons b t ih =>
      apply ih
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  exact ha t 1 (by decide)

theorem input_valid (G : Graph) (w : Word) (hn : 0<G.order) (hb : ∃ t, w=true::t) :
    valid G.order (inputWord G w) = true := by
  apply (valid_iff _ _).mpr
  have hdrop : (inputWord G w).drop (G.order+1)=matrixWord G++w := by
    simp [inputWord, List.drop_append, List.drop_replicate]
  refine ⟨hn, ?_, ?_, ?_⟩
  · have : G.order+1 = (List.replicate G.order true ++ [false]).length := by simp
    rw [this]
    unfold inputWord
    rw [List.append_assoc (List.replicate G.order true ++ [false])]
    exact List.take_left
  · simp [matrix, hdrop]
  · simpa only [bits, ← List.drop_drop, hdrop, ← matrixWord_length G, List.drop_left] using hb

theorem input_extract (G : Graph) (w : Word) :
    matrix G.order (inputWord G w)=matrixWord G ∧ bits G.order (inputWord G w)=w := by
  have hdrop : (inputWord G w).drop (G.order+1)=matrixWord G++w := by
    simp [inputWord, List.drop_append, List.drop_replicate]
  constructor
  · simpa only [matrix, hdrop, ← matrixWord_length G] using (List.take_left (l₁ := matrixWord G) (l₂ := w))
  · simpa only [bits, ← List.drop_drop, hdrop, ← matrixWord_length G] using (List.drop_left (l₁ := matrixWord G) (l₂ := w))

theorem reconstruct {n : ℕ} {w : Word} (hv : valid n w=true)
    (hs : NumericGraph.simple n (matrix n w)=true) :
    w=inputWord (NumericGraph.ofWord n (matrix n w) hs) (bits n w) := by
  obtain ⟨_,hh,hl,_⟩ := (valid_iff n w).mp hv
  rw [inputWord, NumericGraph.matrixWord_ofWord _ _ _ hl]
  change w = (List.replicate n true ++ [false]) ++ matrix n w ++ bits n w
  rw [← hh, List.append_assoc]
  have hd : matrix n w ++ bits n w = w.drop (n+1) := by
    simp only [matrix, bits, ← List.drop_drop]
    exact List.take_append_drop _ _
  rw [hd, List.take_append_drop]

end DimensionDecider

namespace DimensionDecider

theorem budget_bounds {n k m : ℕ} (hn : n ≤ m) (hk : k ≤ max 2 n) :
    n+n  ≤  budget m ∧ n^k  ≤  budget m ∧ (n^k+n^k)^k  ≤  budget m ∧ n^n ≤ budget m ∧ 2^(n*n) ≤ budget m := by
  let s := m+1
  change n+n ≤ 2^(64*s^6) ∧ n^k ≤ 2^(64*s^6) ∧ (n^k+n^k)^k ≤ 2^(64*s^6) ∧ n^n ≤ 2^(64*s^6) ∧ 2^(n*n) ≤ 2^(64*s^6)
  have hs : 1 ≤ s := by omega
  have ns : n ≤ s := by omega
  have ks : k ≤ 2*s := by
    have : max 2 n ≤ 2*s := max_le (by omega) (by omega)
    exact hk.trans this
  have hs2 : s ≤ s^2 := Nat.le_pow (by decide)
  have hs6 : s^2 ≤ s^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hs3 : s^3 ≤ s^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have base : n ≤ 2^s := ns.trans (Nat.le_of_lt (Nat.lt_two_pow_self))
  have expbound : 2*s^2 ≤ 64*s^6 := by omega
  have nnpow : n^n ≤ 2^(s^2) := by
    calc n^n  ≤  (2^s)^n := Nat.pow_le_pow_left base _
      _ = 2^(s*n) := (pow_mul _ _ _).symm
      _  ≤  2^(s^2) := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have nkt : n^k ≤ 2^(2*s^2) := by
    calc n^k  ≤  (2^s)^k := Nat.pow_le_pow_left base _
      _ = 2^(s*k) := (pow_mul _ _ _).symm
      _  ≤  2^(2*s^2) := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have nt : n^k+n^k ≤ 2^(1+2*s^2) := by
    rw [pow_add, pow_one]
    omega
  have main : (n^k+n^k)^k ≤ 2^(64*s^6) := by
    calc (n^k+n^k)^k  ≤  (2^(1+2*s^2))^k := Nat.pow_le_pow_left nt _
      _ = 2^((1+2*s^2)*k) := (pow_mul _ _ _).symm
      _  ≤  2^(64*s^6) := Nat.pow_le_pow_right (by decide) (by
        have ht := Nat.mul_le_mul_left (1+2*s^2) ks
        have h3 : (1+2*s^2)*(2*s)=2*s+4*s^3 := by ring
        rw [h3] at ht
        omega)
  have nm : n*n ≤ 64*s^6 := by nlinarith
  refine ⟨?_, nkt.trans (Nat.pow_le_pow_right (by decide) expbound), main,
    nnpow.trans (Nat.pow_le_pow_right (by decide) (by omega)), Nat.pow_le_pow_right (by decide) nm⟩
  calc n+n  ≤  2*2^s := by omega
    _ = 2^(s+1) := (Nat.mul_comm 2 (2^s)).trans (pow_succ 2 s).symm
    _  ≤  2^(64*s^6) := Nat.pow_le_pow_right (by decide) (by omega)

end DimensionDecider

namespace NumericWL

theorem equivalent_correct (n k cap : ℕ) (W V : Word)
    (hW : NumericGraph.simple n W = true) (hV : NumericGraph.simple n V = true)
    (hk : 0 < k) (hn : n+n ≤ cap) (ht : n^k ≤ cap) (hp : (n^k+n^k)^k ≤ cap) :
    equivalent n k cap W V=true ↔ Equivalent k (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) := by
  by_cases h : k=1
  · subst k; rw [equivalent, ite_eq_left rfl]; exact neighbor_correct n cap W V hW hV hn
  · rw [equivalent, ite_eq_right h]; exact tuple_correct n k cap W V hW hV hk h ht hp

end NumericWL
namespace DimensionDecider

theorem identifies_correct (n k cap : ℕ) (W : Word) (hW : NumericGraph.simple n W=true)
    (hk : 0 < k) (hn : n+n ≤ cap) (ht : n^k ≤ cap) (hp : (n^k+n^k)^k ≤ cap)
    (he : n^n ≤ cap) (hm : 2^(n*n) ≤ cap) :
    identifies n k cap W=true ↔ Identifies k (NumericGraph.ofWord n W hW) := by
  rw [identifies_iff_masks _ _ hk]
  simp only [identifies, min_eq_left hm, List.all_eq_true, List.mem_range]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro _
  have hbool (a b : Bool) : (!a || b)=true ↔ (a=true → b=true) := by cases a <;> cases b <;> decide
  rw [hbool, NumericWL.equivalent_correct n k cap W (NumericGraph.mate n x) hW (NumericGraph.mate_simple n x)
    hk hn ht hp, NumericGraph.iso_correct n cap W (NumericGraph.mate n x) hW (NumericGraph.mate_simple n x) he,
    NumericGraph.ofWord_mate]

theorem capped_identifies (G : Graph) (k : ℕ) (hk : 0 < k) :
    Identifies (min k (max 2 G.order)) G ↔ WLdim G ≤ k := by
  have hm : 0 < max 2 G.order := by have := le_max_left 2 G.order; omega
  have hd : WLdim G ≤ max 2 G.order := (WLdim_le_iff hm).mpr (identifies_order G)
  rw [← WLdim_le_iff (lt_min hk hm)]
  omega

theorem decideWord_correct (w : Word) : decideWord (budget w.length) w=true ↔ w∈dimensionLanguage := by
  simp only [decideWord, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨n,hn,ha⟩
    have hn' : n ≤ w.length := by omega
    simp only [atOrder, Bool.and_eq_true] at ha
    obtain ⟨⟨hv,hs⟩,hi⟩ := ha
    obtain ⟨hpos,_,_,hb⟩ := (valid_iff n w).mp hv
    have hk := binaryValue_leading_pos hb
    have hc : 0 < min (binaryValue (bits n w)) (max 2 n) := lt_min hk (by have := le_max_left 2 n; omega)
    obtain ⟨b1,b2,b3,b4,b5⟩ := budget_bounds hn' (min_le_right (binaryValue (bits n w)) (max 2 n))
    have hI := (identifies_correct _ _ _ _ hs hc b1 b2 b3 b4 b5).mp hi
    have hd := (capped_identifies (NumericGraph.ofWord n (matrix n w) hs) _ hk).mp hI
    exact ⟨NumericGraph.ofWord n (matrix n w) hs, bits n w, hpos, hb, hk, reconstruct hv hs, hd⟩
  · rintro ⟨G,B,hG,hB,hk,rfl,hd⟩
    let w := inputWord G B
    have hn : G.order ≤ w.length := by simp [w, inputWord]
    refine ⟨G.order, by dsimp only [w] at hn; omega, ?_⟩
    have hv := input_valid G B hG hB
    obtain ⟨hmat,hbits⟩ := input_extract G B
    change atOrder G.order (budget w.length) w=true
    simp only [atOrder, w, hmat, hbits, hv, NumericGraph.simple_matrixWord, Bool.true_and]
    have hc : 0 < min (binaryValue B) (max 2 G.order) := lt_min hk (by have := le_max_left 2 G.order; omega)
    obtain ⟨b1,b2,b3,b4,b5⟩ := budget_bounds hn (min_le_right (binaryValue B) (max 2 G.order))
    rw [identifies_correct _ _ _ _ (NumericGraph.simple_matrixWord G) hc b1 b2 b3 b4 b5,
      NumericGraph.ofWord_matrixWord, capped_identifies G _ hk]
    exact hd

end DimensionDecider

namespace DimensionDecider
open WordExpressions

theorem matrix_poly {m} {n : (Fin m → Word) → ℕ} {w : (Fin m → Word) → Word}
    (hn : NatPoly n) (hw : Poly w) : Poly (fun S => matrix (n S) (w S)) :=
  Poly.take (Poly.dropPrefix hw (NatPoly.succ hn)) (hn.mul hn)

theorem bits_poly {m} {n : (Fin m → Word) → ℕ} {w : (Fin m → Word) → Word}
    (hn : NatPoly n) (hw : Poly w) : Poly (fun S => bits (n S) (w S)) :=
  Poly.dropPrefix hw ((NatPoly.succ hn).add (hn.mul hn))

theorem valid_poly {m} {n : (Fin m → Word) → ℕ} {w : (Fin m → Word) → Word}
    (hn : NatPoly n) (hw : Poly w) : BoolPoly (fun S => valid (n S) (w S)) :=
  BoolPoly.and (BoolPoly.and (BoolPoly.and (NatPoly.lt (NatPoly.const 0) hn)
    (Poly.eqtest (Poly.take hw (NatPoly.succ hn))
      (Poly.append (Poly.replicate hn true) (WordExpressions.Poly.const [false]))))
    (NatPoly.eqtest (NatPoly.length (matrix_poly hn hw)) (hn.mul hn)))
    (Poly.nth (bits_poly hn hw) (NatPoly.const 0))

theorem identifies_poly : BoolPoly (fun S : Fin 4 → Word =>
    identifies (S 0).length (S 1).length (S 2).length (S 3)) := by
  unfold identifies
  apply BoolPoly.allRange
  · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
  · apply BoolPoly.or
    · apply BoolPoly.not
      apply NumericWL.equivalent_poly_of
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · apply NumericGraph.mate_poly_of <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
    · apply NumericGraph.iso_poly_of
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)
      · apply NumericGraph.mate_poly_of <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

theorem identifies_poly_of {m} {n k c : (Fin m → Word) → ℕ} {W : (Fin m → Word) → Word}
    (hn : NatPoly n) (hk : NatPoly k) (hc : NatPoly c) (hW : Poly W) :
    BoolPoly (fun S => identifies (n S) (k S) (c S) (W S)) := by
  have h := identifies_poly.subst (g := ![fun S => unary (n S), fun S => unary (k S),
    fun S => unary (c S), W]) (by intro i; fin_cases i; exacts [hn,hk,hc,hW])
  simpa [unary] using h

theorem atOrder_poly {m} {n c : (Fin m → Word) → ℕ} {w : (Fin m → Word) → Word}
    (hn : NatPoly n) (hc : NatPoly c) (hw : Poly w) : BoolPoly (fun S => atOrder (n S) (c S) (w S)) :=
  BoolPoly.and (BoolPoly.and (valid_poly hn hw) (NumericGraph.simple_poly_of hn (matrix_poly hn hw)))
    (identifies_poly_of hn (NatPoly.decode (bits_poly hn hw) (NatPoly.max (NatPoly.const 2) hn))
      hc (matrix_poly hn hw))

theorem decideWord_poly : BoolPoly (fun S : Fin 2 → Word => decideWord (S 1).length (S 0)) := by
  unfold decideWord
  apply BoolPoly.anyRange (NatPoly.succ (NatPoly.var 0))
  apply atOrder_poly <;> (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

end DimensionDecider

/-- Membership for the literal parser, all-mates identification, and finite-alphabet tape model. -/
theorem dimensionLanguage_inEXPTIME : InEXPTIME dimensionLanguage := by
  apply WordExpressions.inEXPTIME_of_budget 64 6 DimensionDecider.decideWord_poly
  intro w
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, WordExpressions.unary, List.length_replicate]
  exact DimensionDecider.decideWord_correct w

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.FinitePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
/- Polynomially presented finite types. Membership refers to actual natural
codes and all iteration bounds have literal unary word realizers. -/

namespace FinitePresentation.Presented
open WordExpressions NumericFinite
variable {A : Word → Type}

theorem card_poly_of (P : Presented A) {n} {w : (Fin n → Word) → Word} (hw : Poly w) :
    NatPoly (fun S => P.card (w S)) :=
  P.card_poly.subst (g := fun _ => w) (fun _ => hw)

theorem select_poly (P : Presented A) : NatPoly (fun S : Fin 2 → Word => P.select (S 0) (S 1).length) := by
  apply (NatPoly.filterSelect (P.bound_poly.rename (fun _ => 0)) (NatPoly.var 1)
    (P.good_poly.rename ![0,2])).congr
  intro S
  simp [Fin.snoc, unary, select]

theorem select_poly_of (P : Presented A) {n} {w : (Fin n → Word) → Word} {i : (Fin n → Word) → ℕ}
    (hw : Poly w) (hi : NatPoly i) : NatPoly (fun S => P.select (w S) (i S)) := by
  have h := P.select_poly.subst (g := ![w, fun S => unary (i S)]) (by intro i; fin_cases i; exacts [hw,hi])
  simpa [unary] using h

end FinitePresentation.Presented

namespace FinitePresentation
open WordExpressions
variable {A : Word → Type}

namespace PresentedGraph
variable {P : Presented A} {G : ∀ w, SimpleGraph (A w)} (Q : PresentedGraph P G)

theorem graph_isomorphic (w : Word) [Fintype (A w)] : Isomorphic (Q.graph w) (graphOfSimple (G w)) := by
  classical
  refine ⟨(P.rankEquiv w).symm.trans (Fintype.equivFin (A w)), ?_⟩
  intro i j
  change Q.adjacent w (P.select w i) (P.select w j) = _
  rw [← P.code_decode w i, ← P.code_decode w j]
  change _ = (graphOfSimple (G w)).edge (Fintype.equivFin _ (P.decode w i)) (Fintype.equivFin _ (P.decode w j))
  rw [graphOfSimple_edge]
  apply Bool.eq_iff_iff.mpr
  simp only [Q.adjacent_iff, decide_eq_true_eq]

end PresentedGraph
end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.LeafPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions

theorem rows_get (n m : ℕ) (f : Fin n → Fin m → Bool) (i : Fin n) (j : Fin m) :
    (((List.ofFn fun a => List.ofFn (f a)).flatten)[i.val*m+j.val]?).getD false = f i j := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    simp only [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ (fun a => ?_) i
    · rw [List.getElem?_append_left (by simp)]
      simp
    · rw [List.getElem?_append_right (by simp only [List.length_ofFn, Fin.val_succ]; nlinarith)]
      simp only [List.length_ofFn, Fin.val_succ]
      rw [show (a.val+1)*m+j.val-m=a.val*m+j.val by simp only [Nat.add_mul, one_mul]; omega]
      exact ih (fun x => f x.succ) a

namespace PresentedGraph
variable {A : Word → Type} {P : Presented A} {G : ∀ w, SimpleGraph (A w)} (Q : PresentedGraph P G)

theorem matrix_eq (w : Word) : Q.matrix w=matrixWord (Q.graph w) := by
  apply List.ext_getElem (by simp [matrix, matrixWord_length, graph])
  intro i hi hj
  have hi' : i<P.card w*P.card w := by simpa [matrix] using hi
  have hn : 0<P.card w := by nlinarith
  have hdiv := Nat.div_lt_of_lt_mul hi'
  have hmod := Nat.mod_lt i hn
  have hentry := rows_get (P.card w) (P.card w) (Q.graph w).edge ⟨i/P.card w,hdiv⟩ ⟨i%P.card w,hmod⟩
  rw [show i/P.card w*P.card w+i%P.card w=i by simpa only [Nat.mul_comm] using Nat.div_add_mod i (P.card w)] at hentry
  change (matrixWord (Q.graph w))[i]?.getD false = _ at hentry
  rw [List.getElem?_eq_getElem hj, Option.getD_some] at hentry
  simpa only [matrix, List.getElem_map, List.getElem_range, graph] using hentry.symm

theorem matrix_poly : Poly (fun S : Fin 1 → Word => Q.matrix (S 0)) := by
  apply Poly.tabulateRange (NatPoly.mul P.card_poly P.card_poly)
  apply Q.adjacent_poly_of (Poly.var 0)
  · apply P.select_poly_of (Poly.var 0)
    exact NatPoly.div (NatPoly.var 1) (P.card_poly_of (Poly.var 0))
  · apply P.select_poly_of (Poly.var 0)
    exact NatPoly.mod (NatPoly.var 1) (P.card_poly_of (Poly.var 0))

theorem output_eq (k : Word → ℕ) (w : Word) : Q.output k w=inputWord (Q.graph w) (binaryWord (k w)) := by
  simp only [output, Q.matrix_eq, inputWord, graph]

theorem output_poly {k : Word → ℕ} (hk : NatPoly (fun S : Fin 1 → Word => k (S 0))) :
    Poly (fun S : Fin 1 → Word => Q.output k (S 0)) :=
  Poly.append (Poly.append (Poly.append (Poly.replicate P.card_poly true) (WordExpressions.Poly.const [false])) Q.matrix_poly)
    (Poly.binary hk)

end PresentedGraph
end FinitePresentation

theorem identifies_isomorphic {G H : Graph} (e : Isomorphic G H) (k : ℕ) : Identifies k G ↔ Identifies k H := by
  constructor
  · intro h I hI
    exact isomorphic_trans (isomorphic_symm e) (h I (equivalent_trans (isomorphic_equivalent e k) hI))
  · intro h I hI
    exact isomorphic_trans e (h I (equivalent_trans (isomorphic_equivalent (isomorphic_symm e) k) hI))

theorem WLdim_isomorphic {G H : Graph} (e : Isomorphic G H) : WLdim G=WLdim H := by
  apply Nat.le_antisymm
  · rw [WLdim_le_iff ((WLdim_spec H).1), identifies_isomorphic e]
    exact (WLdim_le_iff ((WLdim_spec H).1)).mp (le_refl _)
  · rw [WLdim_le_iff ((WLdim_spec G).1), identifies_isomorphic (isomorphic_symm e)]
    exact (WLdim_le_iff ((WLdim_spec G).1)).mp (le_refl _)

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.AffinePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions

variable {C B : Word → Type} [∀ w, Fintype (C w)] [∀ w, DecidableEq (C w)]
    (CP : Presented C) (BP : Presented B) (D : ∀ w, AffineBlocks (C w) (B w))

attribute [local instance] Classical.propDecidable

namespace AffineRealizer
variable {CP BP D} (F : AffineRealizer CP BP D)

variable [∀ w, Fintype (B w)]

theorem uncolored_isomorphic (w : Word) : Isomorphic (F.uncolored.graph w) ((D w).graph 0) :=
  F.uncolored.graph_isomorphic w

end AffineRealizer
end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.Hardness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation.MachineRealizer
open WordExpressions Machine
attribute [local instance] Classical.propDecidable Classical.decEq

 theorem graph_isomorphic (M : Machine) (C e : ℕ) (w : Word) :
    Isomorphic ((uncolored M C e).graph w) (M.reductionGraph C e w) :=
  (affine M C e).uncolored_isomorphic w

 theorem graph_nonempty (M : Machine) (C e : ℕ) (w : Word) :
    0<((uncolored M C e).graph w).order := by
  obtain ⟨f,_⟩ := graph_isomorphic M C e w
  have he : ((uncolored M C e).graph w).order=(M.reductionGraph C e w).order := by
    simpa only [Fintype.card_fin] using Fintype.card_congr f
  rw [he]
  exact M.reductionGraph_nonempty C e w

 theorem output_poly (M : Machine) (C e : ℕ) : Poly (fun X : Fin 1 → Word => output M C e (X 0)) :=
  (uncolored M C e).output_poly (dimension_poly C e)

 theorem output_correct {L : BinaryLanguage} {M : Machine} {C e : ℕ}
    (h : DecidesWithin M L (fun m => 2^(C*(m+1)^e))) (w : Word) :
    w∈L ↔ output M C e w∈dimensionLanguage := by
  rw [output,PresentedGraph.output_eq,inputWord_mem_iff _ (graph_nonempty M C e w) _
    (by have := reductionDimension_ge C e w.length; omega),
    WLdim_isomorphic (graph_isomorphic M C e w),M.reductionGraph_correct h w]
end FinitePresentation.MachineRealizer

/-- The reduction is an actual polynomial-time tape transducer. Relabeling is
by effective rank/select on polynomial finite coding families, not by an
arbitrary Fintype enumeration. Its semantic conclusion retains all graph mates. -/
theorem dimensionLanguage_hard : ∀ L : BinaryLanguage, InEXPTIME L → PolytimeManyOne L dimensionLanguage := by
  intro L ⟨M,C,e,h⟩
  obtain ⟨N,c,d,hN⟩ := (FinitePresentation.MachineRealizer.output_poly M C e).computes
  exact ⟨FinitePresentation.MachineRealizer.output M C e,N,c,d,hN,
    FinitePresentation.MachineRealizer.output_correct h⟩

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

theorem main_oai : EXPTIMEComplete dimensionLanguage :=
  ⟨dimensionLanguage_inEXPTIME, dimensionLanguage_hard⟩

end WLIdentification

end OAI
end

theorem solution : type_of% @OAI.WLIdentification.main_oai := @OAI.WLIdentification.main_oai
