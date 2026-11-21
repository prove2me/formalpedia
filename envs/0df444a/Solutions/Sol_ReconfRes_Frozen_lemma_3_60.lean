-- Prove2me | solution 1 for ReconfRes.Frozen.lemma_3_60
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T13:07:44.068948+00:00
-- url     : https://prove2.me/submissions/02bcadc4-d408-4c2a-b011-68572e46176c

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph
import Definitions.Def_ReconfRes_Frozen_PrivateTags
import Theorems.Thm_ReconfRes_Frozen_frozenConnected_of_lift_frozenConnected

section
open MultiplierAssoc206.Resolution
namespace ReconfRes.Frozen
set_option linter.unusedSectionVars false
namespace Dev.T60
variable {V : Type} [DecidableEq V] {α : ℕ}

theorem mem_parents (R : ProofDag V) (i j : Fin R.n) : j ∈ R.parents i ↔ (j, i) ∈ R.edges := by
  simp [ProofDag.parents]

theorem mem_consumers (R : ProofDag V) (i j : Fin R.n) : j ∈ R.consumers i ↔ (i, j) ∈ R.edges := by
  simp [ProofDag.consumers]

theorem anc_refl (R : ProofDag V) (x : Fin R.n) : R.Anc x x := Relation.ReflTransGen.refl
theorem anc_tail (R : ProofDag V) {x y z : Fin R.n} (h : R.Anc x y) (e : (y, z) ∈ R.edges) :
    R.Anc x z := Relation.ReflTransGen.tail h e
theorem anc_trans (R : ProofDag V) {x y z : Fin R.n} (h : R.Anc x y) (h2 : R.Anc y z) :
    R.Anc x z := Relation.ReflTransGen.trans h h2

section lift
variable (C : Fin α → Clause V) (t : Fin α → V) (R : ProofDag V) (pos : Fin α → Fin R.n)

/-- old node -/
abbrev oN (x : Fin R.n) : Fin (R.n + (α + α)) := Fin.castAdd (α + α) x
/-- tag-D node -/
abbrev dN (i : Fin α) : Fin (R.n + (α + α)) := Fin.natAdd R.n (Fin.castAdd α i)
/-- tag-U node -/
abbrev uN (i : Fin α) : Fin (R.n + (α + α)) := Fin.natAdd R.n (Fin.natAdd α i)

theorem oN_inj {x y : Fin R.n} (h : oN (α := α) R x = oN R y) : x = y := by
  have := congrArg Fin.val h; simpa [Fin.ext_iff] using this
theorem oN_ne_dN (x : Fin R.n) (i : Fin α) : oN R x ≠ dN R i := by
  intro h; have := congrArg Fin.val h; simp at this; have := x.isLt; omega
theorem oN_ne_uN (x : Fin R.n) (i : Fin α) : oN R x ≠ uN R i := by
  intro h; have := congrArg Fin.val h; simp at this; have := x.isLt; omega
theorem dN_ne_uN (i j : Fin α) : dN R i ≠ uN R j := by
  intro h; have := congrArg Fin.val h; simp at this; have := i.isLt; omega

theorem fin3 (y : Fin (R.n + (α + α))) :
    (∃ x, y = oN R x) ∨ (∃ i, y = dN R i) ∨ ∃ i, y = uN R i := by
  refine Fin.addCases (fun x => Or.inl ⟨x, rfl⟩) (fun z => ?_) y
  refine Fin.addCases (fun i => Or.inr (Or.inl ⟨i, rfl⟩)) (fun i => Or.inr (Or.inr ⟨i, rfl⟩)) z

theorem mem_lift_edges (a b : Fin (R.n + (α + α))) :
    (a, b) ∈ (lift C t R pos).edges ↔
      (∃ x y, (x, y) ∈ R.edges ∧ oN R x = a ∧ oN R y = b) ∨
      (∃ i, dN R i = a ∧ oN R (pos i) = b) ∨ (∃ i, uN R i = a ∧ oN R (pos i) = b) := by
  change (a, b) ∈ (R.edges.image (fun e => (Fin.castAdd (α + α) e.1, Fin.castAdd (α + α) e.2)) ∪
    Finset.univ.image (fun i => (Fin.natAdd R.n (Fin.castAdd α i), Fin.castAdd (α + α) (pos i))) ∪
    Finset.univ.image (fun i => (Fin.natAdd R.n (Fin.natAdd α i), Fin.castAdd (α + α) (pos i)))
      : Finset (Fin (R.n + (α + α)) × Fin (R.n + (α + α)))) ↔ _
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq,
    Prod.exists]
  exact or_assoc

theorem lift_parents_new_d (i : Fin α) : (lift C t R pos).parents (dN R i) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro z hz
  have : (z, dN R i) ∈ (lift C t R pos).edges := (mem_parents _ _ _).1 hz
  rcases (mem_lift_edges C t R pos _ _).1 this with ⟨x, y, _, _, h⟩ | ⟨j, _, h⟩ | ⟨j, _, h⟩
  · exact oN_ne_dN R y i h
  · exact oN_ne_dN R _ i h
  · exact oN_ne_dN R _ i h

theorem lift_parents_new_u (i : Fin α) : (lift C t R pos).parents (uN R i) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro z hz
  have : (z, uN R i) ∈ (lift C t R pos).edges := (mem_parents _ _ _).1 hz
  rcases (mem_lift_edges C t R pos _ _).1 this with ⟨x, y, _, _, h⟩ | ⟨j, _, h⟩ | ⟨j, _, h⟩
  · exact oN_ne_uN R y i h
  · exact oN_ne_uN R _ i h
  · exact oN_ne_uN R _ i h

theorem mem_lift_parents_old (y z : Fin (R.n + (α + α))) (y0 : Fin R.n) (hy : y = oN R y0) :
    z ∈ (lift C t R pos).parents y ↔
      (∃ x, x ∈ R.parents y0 ∧ z = oN R x) ∨ (∃ i, pos i = y0 ∧ z = dN R i) ∨
        (∃ i, pos i = y0 ∧ z = uN R i) := by
  subst hy
  refine Iff.trans (mem_parents (lift C t R pos) _ _) (Iff.trans (mem_lift_edges C t R pos _ _) ?_)
  constructor
  · rintro (⟨x, y, h, rfl, h2⟩ | ⟨i, rfl, h2⟩ | ⟨i, rfl, h2⟩)
    · exact Or.inl ⟨x, (mem_parents R _ _).2 (by have := oN_inj R h2; subst this; exact h), rfl⟩
    · exact Or.inr (Or.inl ⟨i, oN_inj R h2, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, oN_inj R h2, rfl⟩)
  · rintro (⟨x, h, rfl⟩ | ⟨i, h, rfl⟩ | ⟨i, h, rfl⟩)
    · exact Or.inl ⟨x, y0, (mem_parents R _ _).1 h, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨i, rfl, by rw [h]⟩)
    · exact Or.inr (Or.inr ⟨i, rfl, by rw [h]⟩)

theorem mem_lift_consumers_old (x : Fin R.n) (z : Fin (R.n + (α + α))) :
    z ∈ (lift C t R pos).consumers (oN R x) ↔ ∃ y, y ∈ R.consumers x ∧ z = oN R y := by
  refine Iff.trans (mem_consumers (lift C t R pos) _ _) (Iff.trans (mem_lift_edges C t R pos _ _) ?_)
  constructor
  · rintro (⟨x', y, h, h1, rfl⟩ | ⟨i, h1, _⟩ | ⟨i, h1, _⟩)
    · exact ⟨y, (mem_consumers R _ _).2 (by rw [← oN_inj R h1]; exact h), rfl⟩
    · exact absurd h1.symm (oN_ne_dN R _ _)
    · exact absurd h1.symm (oN_ne_uN R _ _)
  · rintro ⟨y, h, rfl⟩
    exact Or.inl ⟨x, y, (mem_consumers R _ _).1 h, rfl, rfl⟩


theorem lift_label_old (x : Fin R.n) : (lift C t R pos).label (oN R x) = R.label x := by
  show Fin.addCases (motive := fun _ => Clause V) R.label (Fin.addCases (motive := fun _ => Clause V) (tagD C t) (tagU t)) (Fin.castAdd (α + α) x) = _
  simp [Fin.addCases_left]
theorem lift_label_d (i : Fin α) : (lift C t R pos).label (dN R i) = tagD C t i := by
  show Fin.addCases (motive := fun _ => Clause V) R.label (Fin.addCases (motive := fun _ => Clause V) (tagD C t) (tagU t)) (Fin.natAdd R.n (Fin.castAdd α i)) = _
  simp [Fin.addCases_right, Fin.addCases_left]
theorem lift_label_u (i : Fin α) : (lift C t R pos).label (uN R i) = tagU t i := by
  show Fin.addCases (motive := fun _ => Clause V) R.label (Fin.addCases (motive := fun _ => Clause V) (tagD C t) (tagU t)) (Fin.natAdd R.n (Fin.natAdd α i)) = _
  simp only [Fin.addCases_right]

theorem lift_anc_old {x : Fin R.n} {z : Fin (R.n + (α + α))}
    (h : (lift C t R pos).Anc (oN R x) z) : ∃ y, z = oN R y ∧ R.Anc x y := by
  unfold ProofDag.Anc at h
  induction h with
  | refl => exact ⟨x, rfl, anc_refl R x⟩
  | tail _ hs ih =>
    obtain ⟨y, rfl, hy⟩ := ih
    rcases (mem_lift_edges C t R pos _ _).1 hs with ⟨x', y', h1, h2, h3⟩ | ⟨i, h1, _⟩ | ⟨i, h1, _⟩
    · have := oN_inj R h2; subst this
      exact ⟨y', h3.symm, anc_tail R hy h1⟩
    · exact absurd h1.symm (oN_ne_dN R _ _)
    · exact absurd h1.symm (oN_ne_uN R _ _)

theorem lift_anc_map {x y : Fin R.n} (h : R.Anc x y) :
    (lift C t R pos).Anc (oN R x) (oN R y) := by
  unfold ProofDag.Anc at h ⊢
  induction h with
  | refl => exact anc_refl _ _
  | tail _ hs ih =>
    exact anc_tail _ ih ((mem_lift_edges C t R pos _ _).2 (Or.inl ⟨_, _, hs, rfl, rfl⟩))

/-- old node as a node of the lift -/
def oL (x : Fin R.n) : Fin (lift C t R pos).n := Fin.castAdd (α + α) x
/-- D node as a node of the lift -/
def dL (i : Fin α) : Fin (lift C t R pos).n := Fin.natAdd R.n (Fin.castAdd α i)
/-- U node as a node of the lift -/
def uL (i : Fin α) : Fin (lift C t R pos).n := Fin.natAdd R.n (Fin.natAdd α i)

theorem lift_parents_nonaxiom (hIdx : IsIndexedBy C Finset.univ R pos) (x : Fin R.n)
    (hx : R.parents x ≠ ∅) :
    (lift C t R pos).parents (oN R x) =
      (R.parents x).image (oL C t R pos) := by
  ext z
  refine Iff.trans (mem_lift_parents_old C t R pos _ z x rfl) ?_
  simp only [Finset.mem_image, oL]
  constructor
  · rintro (⟨x', h, rfl⟩ | ⟨i, h, _⟩ | ⟨i, h, _⟩)
    · exact ⟨x', h, rfl⟩
    · exfalso; apply hx
      have : R.IsAxiomNode x := (hIdx.2.1 x).2 ⟨i, Finset.mem_univ _, h⟩
      exact this
    · exfalso; apply hx
      have : R.IsAxiomNode x := (hIdx.2.1 x).2 ⟨i, Finset.mem_univ _, h⟩
      exact this
  · rintro ⟨x', h, rfl⟩; exact Or.inl ⟨x', h, rfl⟩

theorem lift_parents_axiom (hIdx : IsIndexedBy C Finset.univ R pos) (i : Fin α) :
    (lift C t R pos).parents (oN R (pos i)) =
      ({dL C t R pos i, uL C t R pos i} : Finset (Fin (lift C t R pos).n)) := by
  have hax : R.parents (pos i) = ∅ := (hIdx.2.1 (pos i)).2 ⟨i, Finset.mem_univ _, rfl⟩
  ext z
  refine Iff.trans (mem_lift_parents_old C t R pos _ z (pos i) rfl) ?_
  constructor
  · rintro (⟨j, h, _⟩ | ⟨j, h, rfl⟩ | ⟨j, h, rfl⟩)
    · rw [hax] at h; simp at h
    · have := hIdx.1 (Finset.mem_univ _) (Finset.mem_univ _) h; subst this
      exact Finset.mem_insert.2 (Or.inl rfl)
    · have := hIdx.1 (Finset.mem_univ _) (Finset.mem_univ _) h; subst this
      exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 rfl))
  · intro h
    rcases Finset.mem_insert.1 h with rfl | h
    · exact Or.inr (Or.inl ⟨i, rfl, rfl⟩)
    · rw [Finset.mem_singleton] at h; subst h
      exact Or.inr (Or.inr ⟨i, rfl, rfl⟩)


theorem vars_mono (l : Literal V) (h : l.1 ∈ vars (inventoryFormula C)) :
    l.1 ∈ vars (tagFormula C t) := by
  unfold vars at h ⊢
  simp only [Finset.mem_biUnion, Finset.mem_image] at h ⊢
  obtain ⟨c, hc, l', hl', hl'1⟩ := h
  unfold inventoryFormula at hc
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hc
  obtain ⟨j, rfl⟩ := hc
  refine ⟨tagD C t j, ?_, l', ?_, hl'1⟩
  · unfold tagFormula; simp
  · simp [tagD, hl']

theorem lift_isVertex (hfresh : ∀ i j, ∀ l ∈ C j, l.1 ≠ t i)
    (w : ℕ) (hw : 1 + Finset.univ.sup (fun i => (C i).card) ≤ w)
    (hV : IsVertex (inventoryFormula C) w (2 * α - 1) R) (hIdx : IsIndexedBy C Finset.univ R pos) :
    IsVertex (tagFormula C t) w (4 * α - 1) (lift C t R pos) := by
  obtain ⟨⟨hacyc, hvars, hnode, hsinkc, hsinkl⟩, hlean, hwid, hsize⟩ := hV
  have hR : ∀ i, (R.parents i = ∅ ∧ R.label i ∈ inventoryFormula C) ∨ _ := hnode
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- acyclic
    intro i j hij hanc
    rcases (mem_lift_edges C t R pos _ _).1 hij with ⟨x, y, hxy, rfl, rfl⟩ | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
    · obtain ⟨y', hy', hanc'⟩ := lift_anc_old C t R pos hanc
      have := oN_inj R hy'; subst this
      exact hacyc x y hxy hanc'
    · obtain ⟨y', hy', _⟩ := lift_anc_old C t R pos hanc
      exact oN_ne_dN R _ _ hy'.symm
    · obtain ⟨y', hy', _⟩ := lift_anc_old C t R pos hanc
      exact oN_ne_uN R _ _ hy'.symm
  · -- vars
    intro i l hl
    rcases fin3 R i with ⟨x, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [lift_label_old] at hl; exact vars_mono C t l (hvars x l hl)
    · rw [lift_label_d] at hl
      unfold vars; simp only [Finset.mem_biUnion, Finset.mem_image]
      exact ⟨tagD C t k, by unfold tagFormula; simp, l, hl, rfl⟩
    · rw [lift_label_u] at hl
      unfold vars; simp only [Finset.mem_biUnion, Finset.mem_image]
      exact ⟨tagU t k, by unfold tagFormula; simp, l, hl, rfl⟩
  · -- nodes
    intro i
    rcases fin3 R i with ⟨x, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · by_cases hx : R.parents x = ∅
      · obtain ⟨k, _, hk⟩ := (hIdx.2.1 x).1 hx
        subst hk
        right; left
        refine ⟨uL C t R pos k, dL C t R pos k, (dN_ne_uN R k k).symm, ?_, t k, ?_⟩
        · rw [lift_parents_axiom C t R pos hIdx k]; exact Finset.pair_comm _ _
        · show ResolventOn (t k) ((lift C t R pos).label (uN R k)) ((lift C t R pos).label (dN R k))
            ((lift C t R pos).label (oN R (pos k)))
          rw [lift_label_u, lift_label_d, lift_label_old, hIdx.2.2 k (Finset.mem_univ _)]
          have hn : ((t k, false) : Literal V) ∉ C k := fun h => hfresh k k _ h rfl
          refine ⟨by simp [tagU], by simp [tagD], ?_⟩
          simp [tagU, tagD, Finset.erase_insert hn]
      · rcases hnode x with ⟨h, _⟩ | ⟨p₁, p₂, hne, hpar, y, hres⟩ | ⟨p, hpar, hsub⟩
        · exact absurd h hx
        · right; left
          refine ⟨oL C t R pos p₁, oL C t R pos p₂, ?_, ?_, y, ?_⟩
          · intro h; exact hne (oN_inj R h)
          · rw [lift_parents_nonaxiom C t R pos hIdx x hx, hpar, Finset.image_insert, Finset.image_singleton]
          · have e1 : (lift C t R pos).label (oL C t R pos p₁) = R.label p₁ := lift_label_old C t R pos p₁
            have e2 : (lift C t R pos).label (oL C t R pos p₂) = R.label p₂ := lift_label_old C t R pos p₂
            have e3 : (lift C t R pos).label (oN R x) = R.label x := lift_label_old C t R pos x
            rw [e1, e2, e3]; exact hres
        · right; right
          refine ⟨oL C t R pos p, ?_, ?_⟩
          · rw [lift_parents_nonaxiom C t R pos hIdx x hx, hpar, Finset.image_singleton]
          · have e1 : (lift C t R pos).label (oL C t R pos p) = R.label p := lift_label_old C t R pos p
            have e3 : (lift C t R pos).label (oN R x) = R.label x := lift_label_old C t R pos x
            rw [e1, e3]; exact hsub
    · left; exact ⟨lift_parents_new_d C t R pos k, by rw [lift_label_d]; unfold tagFormula; simp⟩
    · left; exact ⟨lift_parents_new_u C t R pos k, by rw [lift_label_u]; unfold tagFormula; simp⟩
  · -- sink consumers
    show (lift C t R pos).consumers (oN R R.sink) = ∅
    rw [Finset.eq_empty_iff_forall_notMem]
    intro z hz
    obtain ⟨y, hy, _⟩ := (mem_lift_consumers_old C t R pos R.sink z).1 hz
    rw [hsinkc] at hy; simp at hy
  · show (lift C t R pos).label (oN R R.sink) = ∅
    rw [lift_label_old]; exact hsinkl
  · -- lean
    intro i
    show (lift C t R pos).Anc i (oN R R.sink)
    rcases fin3 R i with ⟨x, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact lift_anc_map C t R pos (hlean x)
    · exact anc_trans (lift C t R pos)
        (anc_tail (lift C t R pos) (anc_refl (lift C t R pos) _)
          ((mem_lift_edges C t R pos _ _).2 (Or.inr (Or.inl ⟨k, rfl, rfl⟩))))
        (lift_anc_map C t R pos (hlean (pos k)))
    · exact anc_trans (lift C t R pos)
        (anc_tail (lift C t R pos) (anc_refl (lift C t R pos) _)
          ((mem_lift_edges C t R pos _ _).2 (Or.inr (Or.inr ⟨k, rfl, rfl⟩))))
        (lift_anc_map C t R pos (hlean (pos k)))
  · -- width
    unfold ProofDag.width
    refine Finset.sup_le (fun i _ => ?_)
    have hsup : ∀ k, (C k).card ≤ Finset.univ.sup (fun i => (C i).card) :=
      fun k => Finset.le_sup (f := fun i => (C i).card) (Finset.mem_univ k)
    rcases fin3 R i with ⟨x, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [lift_label_old]
      exact (Finset.le_sup (f := fun i => (R.label i).card) (Finset.mem_univ x)).trans hwid
    · rw [lift_label_d]
      exact (Finset.card_insert_le _ _).trans (by have := hsup k; omega)
    · rw [lift_label_u]
      have : (tagU t k).card = 1 := by simp [tagU]
      omega
  · -- size
    show R.n + (α + α) ≤ 4 * α - 1
    have h1 : R.size ≤ 2 * α - 1 := hsize
    have h2 : 0 < R.n := Fin.pos R.sink
    have h3 : R.size = R.n := rfl
    omega

end lift


section sub
variable {n n' : ℕ} {Q : Finset (Fin n)} {Q' : Finset (Fin n')} (m : ℕ)

theorem castAdd_not_mem {Q : Finset (Fin n)} {a : Fin n} (h : Fin.castAdd m a ∉ Q.image (Fin.castAdd m)) :
    a ∉ Q := fun hq => h (Finset.mem_image.2 ⟨a, hq, rfl⟩)

theorem castAdd_not_mem' {Q : Finset (Fin n)} {a : Fin n} (h : a ∉ Q) :
    Fin.castAdd m a ∉ Q.image (Fin.castAdd m) := by
  intro hq
  obtain ⟨b, hb, he⟩ := Finset.mem_image.1 hq
  have := Fin.castAdd_injective _ _ he
  subst this; exact h hb

theorem natAdd_not_mem (b : Fin m) : Fin.natAdd n b ∉ Q.image (Fin.castAdd m) := by
  intro hq
  obtain ⟨a, _, he⟩ := Finset.mem_image.1 hq
  have := congrArg Fin.val he
  simp at this; have := a.isLt; omega

/-- Extend a map of kept nodes to the lift (adding `m` new nodes, fixed). -/
def lf (g : {i // i ∉ Q} → {j // j ∉ Q'}) :
    {x : Fin (n + m) // x ∉ Q.image (Fin.castAdd m)} →
      {y : Fin (n' + m) // y ∉ Q'.image (Fin.castAdd m)} := fun x =>
  Fin.addCases (motive := fun z => z ∉ Q.image (Fin.castAdd m) →
      {y : Fin (n' + m) // y ∉ Q'.image (Fin.castAdd m)})
    (fun a h => ⟨Fin.castAdd m (g ⟨a, castAdd_not_mem m h⟩).1,
      castAdd_not_mem' m (g ⟨a, castAdd_not_mem m h⟩).2⟩)
    (fun b _ => ⟨Fin.natAdd n' b, natAdd_not_mem m b⟩) x.1 x.2

theorem lf_old (g : {i // i ∉ Q} → {j // j ∉ Q'}) (a : Fin n) (ha : a ∉ Q)
    (h : Fin.castAdd m a ∉ Q.image (Fin.castAdd m)) :
    (lf m g ⟨Fin.castAdd m a, h⟩).1 = Fin.castAdd m (g ⟨a, ha⟩).1 := by
  simp [lf, Fin.addCases_left]

theorem lf_new (g : {i // i ∉ Q} → {j // j ∉ Q'}) (b : Fin m)
    (h : Fin.natAdd n b ∉ Q.image (Fin.castAdd m)) :
    (lf m g ⟨Fin.natAdd n b, h⟩).1 = Fin.natAdd n' b := by
  simp [lf, Fin.addCases_right]

/-- The lifted identification of kept nodes. -/
def liftSub (φ : {i // i ∉ Q} ≃ {j // j ∉ Q'}) :
    {x : Fin (n + m) // x ∉ Q.image (Fin.castAdd m)} ≃
      {y : Fin (n' + m) // y ∉ Q'.image (Fin.castAdd m)} where
  toFun := lf m φ
  invFun := lf m φ.symm
  left_inv := by
    rintro ⟨x, hx⟩
    induction x using Fin.addCases with
    | left a =>
      have ha := castAdd_not_mem m hx
      apply Subtype.ext
      have h1 := lf_old m φ a ha hx
      have h2 := lf_old m φ.symm (φ ⟨a, ha⟩).1 (φ ⟨a, ha⟩).2
        (castAdd_not_mem' m (φ ⟨a, ha⟩).2)
      simp only [] at h1 ⊢
      rw [show lf m φ ⟨Fin.castAdd m a, hx⟩ = ⟨Fin.castAdd m (φ ⟨a, ha⟩).1, castAdd_not_mem' m (φ ⟨a, ha⟩).2⟩ from Subtype.ext h1]
      rw [h2]; simp
    | right b =>
      apply Subtype.ext
      have h1 := lf_new m φ b hx
      rw [show lf m φ ⟨Fin.natAdd n b, hx⟩ = ⟨Fin.natAdd n' b, natAdd_not_mem m b⟩ from Subtype.ext h1]
      exact lf_new m φ.symm b (natAdd_not_mem m b)
  right_inv := by
    rintro ⟨x, hx⟩
    induction x using Fin.addCases with
    | left a =>
      have ha := castAdd_not_mem m hx
      apply Subtype.ext
      have h1 := lf_old m φ.symm a ha hx
      have h2 := lf_old m φ (φ.symm ⟨a, ha⟩).1 (φ.symm ⟨a, ha⟩).2
        (castAdd_not_mem' m (φ.symm ⟨a, ha⟩).2)
      rw [show lf m φ.symm ⟨Fin.castAdd m a, hx⟩ = ⟨Fin.castAdd m (φ.symm ⟨a, ha⟩).1, castAdd_not_mem' m (φ.symm ⟨a, ha⟩).2⟩ from Subtype.ext h1]
      rw [h2]; simp
    | right b =>
      apply Subtype.ext
      have h1 := lf_new m φ.symm b hx
      rw [show lf m φ.symm ⟨Fin.natAdd n' b, hx⟩ = ⟨Fin.natAdd n b, natAdd_not_mem m b⟩ from Subtype.ext h1]
      exact lf_new m φ b (natAdd_not_mem m b)

end sub


theorem part3 (C : Fin α → Clause V) (t : Fin α → V) (ht : Function.Injective t)
    (hfresh : ∀ i j, ∀ l ∈ C j, l.1 ≠ t i) :
    (tagFormula C t).card = 2 * α ∧ ((∀ i, IsHornClause (C i)) → IsHorn (tagFormula C t)) := by
  have hD : Function.Injective (tagD C t) := by
    intro i j h
    have : (t i, false) ∈ tagD C t j := by rw [← h]; simp [tagD]
    simp only [tagD, Finset.mem_insert] at this
    rcases this with h1 | h1
    · exact ht (Prod.mk.inj h1).1
    · exact absurd rfl (hfresh i j _ h1)
  have hU : Function.Injective (tagU t) := by
    intro i j h
    have := Finset.singleton_inj.mp h
    exact ht (Prod.mk.inj this).1
  have hdisj : Disjoint (Finset.univ.image (tagD C t)) (Finset.univ.image (tagU t)) := by
    rw [Finset.disjoint_left]
    intro c h1 h2
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨i, rfl⟩ := h1
    obtain ⟨j, hj⟩ := h2
    have : (t i, false) ∈ tagU t j := by rw [hj]; simp [tagD]
    simp [tagU] at this
  refine ⟨?_, ?_⟩
  · unfold tagFormula
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hD,
      Finset.card_image_of_injective _ hU]
    simp; ring
  · intro hH c hc
    unfold tagFormula at hc
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hc
    rcases hc with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · have := hH i
      unfold IsHornClause at this ⊢
      simpa [tagD, Finset.filter_insert] using this
    · unfold IsHornClause tagU; exact (Finset.card_filter_le _ _).trans (by simp)

section moves
variable (C : Fin α → Clause V) (t : Fin α → V)

theorem E1 (R : ProofDag V) (pos : Fin α → Fin R.n) (x y : Fin R.n) :
    (oN R x, oN R y) ∈ (lift C t R pos).edges ↔ (x, y) ∈ R.edges := by
  refine (mem_lift_edges C t R pos _ _).trans ?_
  constructor
  · rintro (⟨x', y', h, h1, h2⟩ | ⟨i, h1, _⟩ | ⟨i, h1, _⟩)
    · rw [oN_inj R h1, oN_inj R h2] at h; exact h
    · exact absurd h1.symm (oN_ne_dN R _ _)
    · exact absurd h1.symm (oN_ne_uN R _ _)
  · intro h; exact Or.inl ⟨x, y, h, rfl, rfl⟩

theorem E2 (R : ProofDag V) (pos : Fin α → Fin R.n) (a : Fin (R.n + (α + α))) (j : Fin (α + α)) :
    (a, Fin.natAdd R.n j) ∉ (lift C t R pos).edges := by
  intro h
  rcases (mem_lift_edges C t R pos _ _).1 h with ⟨x, y, _, _, h2⟩ | ⟨i, _, h2⟩ | ⟨i, _, h2⟩
  · have := congrArg Fin.val h2; simp at this; have := y.isLt; omega
  · have := congrArg Fin.val h2; simp at this; have := (pos i).isLt; omega
  · have := congrArg Fin.val h2; simp at this; have := (pos i).isLt; omega

theorem E3 (R : ProofDag V) (pos : Fin α → Fin R.n) (j : Fin (α + α)) (y : Fin R.n) :
    (Fin.natAdd R.n j, oN R y) ∈ (lift C t R pos).edges ↔
      ∃ i : Fin α, (j = Fin.castAdd α i ∨ j = Fin.natAdd α i) ∧ pos i = y := by
  refine (mem_lift_edges C t R pos _ _).trans ?_
  constructor
  · rintro (⟨x', y', _, h1, _⟩ | ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩)
    · have := congrArg Fin.val h1; simp at this; have := x'.isLt; omega
    · have hj : j = Fin.castAdd α i := by
        have := congrArg Fin.val h1; apply Fin.ext; simpa using this.symm
      exact ⟨i, Or.inl hj, oN_inj R h2⟩
    · have hj : j = Fin.natAdd α i := by
        have := congrArg Fin.val h1; apply Fin.ext; simpa using this.symm
      exact ⟨i, Or.inr hj, oN_inj R h2⟩
  · rintro ⟨i, hj | hj, rfl⟩
    · exact Or.inr (Or.inl ⟨i, by rw [hj], rfl⟩)
    · exact Or.inr (Or.inr ⟨i, by rw [hj], rfl⟩)

theorem lift_label_new (R R' : ProofDag V) (pos : Fin α → Fin R.n) (pos' : Fin α → Fin R'.n)
    (b : Fin (α + α)) :
    (lift C t R' pos').label (Fin.natAdd R'.n b) = (lift C t R pos).label (Fin.natAdd R.n b) := by
  show Fin.addCases (motive := fun _ => Clause V) R'.label
      (Fin.addCases (motive := fun _ => Clause V) (tagD C t) (tagU t)) (Fin.natAdd R'.n b) =
    Fin.addCases (motive := fun _ => Clause V) R.label
      (Fin.addCases (motive := fun _ => Clause V) (tagD C t) (tagU t)) (Fin.natAdd R.n b)
  simp only [Fin.addCases_right]

end moves

section moves2
variable (C : Fin α → Clause V) (t : Fin α → V)

theorem ancIn_refl (R : ProofDag V) (Q : Finset (Fin R.n)) (x : Fin R.n) : R.AncIn Q x x :=
  Relation.ReflTransGen.refl
theorem ancIn_tail (R : ProofDag V) (Q : Finset (Fin R.n)) {x y z : Fin R.n} (h : R.AncIn Q x y)
    (e : y ∈ Q ∧ z ∈ Q ∧ (y, z) ∈ R.edges) : R.AncIn Q x z := by
  have : R.AncIn Q x y := h
  exact Relation.ReflTransGen.tail this ⟨e.1, e.2.1, e.2.2⟩

theorem lift_ancIn (R : ProofDag V) (pos : Fin α → Fin R.n) (Q : Finset (Fin R.n))
    {a b : Fin R.n} (h : R.AncIn Q a b) :
    (lift C t R pos).AncIn (Q.image (Fin.castAdd (α + α))) (oN R a) (oN R b) := by
  unfold ProofDag.AncIn at h ⊢
  induction h with
  | refl => exact ancIn_refl (lift C t R pos) _ _
  | tail _ hs ih =>
    refine ancIn_tail (lift C t R pos) _ ih ⟨?_, ?_, (E1 C t R pos _ _).2 hs.2.2⟩
    · exact Finset.mem_image.2 ⟨_, hs.1, rfl⟩
    · exact Finset.mem_image.2 ⟨_, hs.2.1, rfl⟩

theorem lift_block {k : ℕ} (R : ProofDag V) (pos : Fin α → Fin R.n)
    (hIdx : IsIndexedBy C Finset.univ R pos) (Q : Finset (Fin R.n)) (q : Fin R.n)
    (hQ : ∀ i ∈ Q, ¬ R.IsAxiomNode i) (hb : R.IsBlock k Q q) :
    (lift C t R pos).IsBlock k (Q.image (Fin.castAdd (α + α))) (oN R q) := by
  obtain ⟨hcard, ⟨hqQ, hout⟩, hbq⟩ := hb
  refine ⟨?_, ⟨Finset.mem_image.2 ⟨q, hqQ, rfl⟩, ?_⟩, ?_⟩
  · have h1 : Q.filter (fun i => (R.parents i).Nonempty) = Q :=
      Finset.filter_true_of_mem (fun x hx => Finset.nonempty_iff_ne_empty.2 (hQ x hx))
    rw [h1] at hcard
    have h2 : (Q.image (Fin.castAdd (α + α))).filter (fun i => ((lift C t R pos).parents i).Nonempty) =
        Q.image (Fin.castAdd (α + α)) := by
      refine Finset.filter_true_of_mem (fun z hz => ?_)
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
      rw [lift_parents_nonaxiom C t R pos hIdx x (hQ x hx)]
      exact Finset.Nonempty.image (Finset.nonempty_iff_ne_empty.2 (hQ x hx)) _
    exact (le_of_eq (congrArg Finset.card h2)).trans
      ((Finset.card_image_of_injective _ (Fin.castAdd_injective _ _)).le.trans hcard)
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    exact lift_ancIn C t R pos Q (hout x hx)
  · intro z hz hzq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    intro c hc
    obtain ⟨y, hy, rfl⟩ := (mem_lift_consumers_old C t R pos x c).1 hc
    have hxq : x ≠ q := fun h => hzq (by rw [h])
    exact Finset.mem_image.2 ⟨y, hbq x hx hxq hy, rfl⟩

theorem mem_inputs' (R : ProofDag V) (Q : Finset (Fin R.n)) (i : Fin R.n) :
    i ∈ R.inputs Q ↔ i ∉ Q ∧ ∃ j ∈ Q, (i, j) ∈ R.edges := by
  simp [ProofDag.inputs]

theorem lift_move {k : ℕ} (R R' : ProofDag V) (pos : Fin α → Fin R.n) (pos' : Fin α → Fin R'.n)
    (hIdx : IsIndexedBy C Finset.univ R pos) (hIdx' : IsIndexedBy C Finset.univ R' pos')
    {Q : Finset (Fin R.n)} {Q' : Finset (Fin R'.n)} {φ : {i // i ∉ Q} ≃ {j // j ∉ Q'}}
    (hmv : FrozenMoveVia k R R' Q Q' φ)
    (hpos : ∀ s : Fin α, ∀ h : pos s ∉ Q, (φ ⟨pos s, h⟩).1 = pos' s) :
    FrozenMoveVia k (lift C t R pos) (lift C t R' pos')
      (Q.image (Fin.castAdd (α + α))) (Q'.image (Fin.castAdd (α + α))) (liftSub (α + α) φ) := by
  obtain ⟨hm, hQ, hQ'⟩ := hmv
  have hm0 := hm
  obtain ⟨q, q', hb, hb', hlab, hl, hed, hin, hcons, hs1, hs2⟩ := hm0
  have hposQ : ∀ s, pos s ∉ Q := fun s hq =>
    hQ _ hq ((hIdx.2.1 _).2 ⟨s, Finset.mem_univ _, rfl⟩)
  refine ⟨⟨oN R q, oN R' q', lift_block C t R pos hIdx Q q hQ hb,
    lift_block C t R' pos' hIdx' Q' q' hQ' hb', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · show (lift C t R' pos').label (oN R' q') = (lift C t R pos).label (oN R q)
    rw [lift_label_old, lift_label_old]; exact hlab
  · rintro ⟨x, hx⟩
    induction x using Fin.addCases with
    | left a =>
      have ha := castAdd_not_mem (α + α) hx
      show (lift C t R' pos').label (lf (α + α) φ ⟨Fin.castAdd (α + α) a, hx⟩).1 =
        (lift C t R pos).label (Fin.castAdd (α + α) a)
      rw [lf_old (α + α) φ a ha hx]
      exact ((lift_label_old C t R' pos' _).trans (hl ⟨a, ha⟩)).trans (lift_label_old C t R pos a).symm
    | right b =>
      show (lift C t R' pos').label (lf (α + α) φ ⟨Fin.natAdd R.n b, hx⟩).1 =
        (lift C t R pos).label (Fin.natAdd R.n b)
      rw [lf_new (α + α) φ b hx]
      exact lift_label_new C t R R' pos pos' b
  · -- edges among kept nodes
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    induction x using Fin.addCases with
    | left a =>
      have ha := castAdd_not_mem (α + α) hx
      induction y using Fin.addCases with
      | left b =>
        have hb := castAdd_not_mem (α + α) hy
        show ((lf (α + α) φ ⟨Fin.castAdd (α + α) a, hx⟩).1, (lf (α + α) φ ⟨Fin.castAdd (α + α) b, hy⟩).1) ∈
          (lift C t R' pos').edges ↔ (Fin.castAdd (α + α) a, Fin.castAdd (α + α) b) ∈ (lift C t R pos).edges
        rw [lf_old (α + α) φ a ha hx, lf_old (α + α) φ b hb hy]
        exact (E1 C t R' pos' _ _).trans ((hed ⟨a, ha⟩ ⟨b, hb⟩).trans (E1 C t R pos _ _).symm)
      | right b =>
        show ((lf (α + α) φ ⟨Fin.castAdd (α + α) a, hx⟩).1, (lf (α + α) φ ⟨Fin.natAdd R.n b, hy⟩).1) ∈
          (lift C t R' pos').edges ↔ (Fin.castAdd (α + α) a, Fin.natAdd R.n b) ∈ (lift C t R pos).edges
        rw [lf_old (α + α) φ a ha hx, lf_new (α + α) φ b hy]
        exact iff_of_false (E2 C t R' pos' _ _) (E2 C t R pos _ _)
    | right a =>
      induction y using Fin.addCases with
      | left b =>
        have hb := castAdd_not_mem (α + α) hy
        show ((lf (α + α) φ ⟨Fin.natAdd R.n a, hx⟩).1, (lf (α + α) φ ⟨Fin.castAdd (α + α) b, hy⟩).1) ∈
          (lift C t R' pos').edges ↔ (Fin.natAdd R.n a, Fin.castAdd (α + α) b) ∈ (lift C t R pos).edges
        rw [lf_new (α + α) φ a hx, lf_old (α + α) φ b hb hy]
        refine (E3 C t R' pos' a _).trans (Iff.trans ?_ (E3 C t R pos a b).symm)
        constructor
        · rintro ⟨i, hj, h⟩
          refine ⟨i, hj, ?_⟩
          have h1 := hpos i (hposQ i)
          have : (φ ⟨pos i, hposQ i⟩) = φ ⟨b, hb⟩ := Subtype.ext (h1.trans h)
          have := congrArg Subtype.val (φ.injective this)
          exact this
        · rintro ⟨i, hj, h⟩
          refine ⟨i, hj, ?_⟩
          have h1 := hpos i (hposQ i)
          have e : (⟨pos i, hposQ i⟩ : {i // i ∉ Q}) = ⟨b, hb⟩ := Subtype.ext h
          rw [← h1, e]
      | right b =>
        show ((lf (α + α) φ ⟨Fin.natAdd R.n a, hx⟩).1, (lf (α + α) φ ⟨Fin.natAdd R.n b, hy⟩).1) ∈
          (lift C t R' pos').edges ↔ (Fin.natAdd R.n a, Fin.natAdd R.n b) ∈ (lift C t R pos).edges
        rw [lf_new (α + α) φ a hx, lf_new (α + α) φ b hy]
        exact iff_of_false (E2 C t R' pos' _ _) (E2 C t R pos _ _)
  · -- inputs
    rintro ⟨x, hx⟩ j hj he
    obtain ⟨j0, hj0, rfl⟩ := Finset.mem_image.1 hj
    induction x using Fin.addCases with
    | left a =>
      have ha := castAdd_not_mem (α + α) hx
      have he' : ((lf (α + α) φ ⟨Fin.castAdd (α + α) a, hx⟩).1, Fin.castAdd (α + α) j0) ∈
          (lift C t R' pos').edges := he
      rw [lf_old (α + α) φ a ha hx] at he'
      have h1 := hin ⟨a, ha⟩ j0 hj0 ((E1 C t R' pos' _ _).1 he')
      obtain ⟨_, j1, hj1, hj1e⟩ := (mem_inputs' R Q a).1 h1
      refine (mem_inputs' _ _ _).2 ⟨hx, Fin.castAdd (α + α) j1, Finset.mem_image.2 ⟨j1, hj1, rfl⟩, ?_⟩
      exact (E1 C t R pos _ _).2 hj1e
    | right b =>
      have he' : ((lf (α + α) φ ⟨Fin.natAdd R.n b, hx⟩).1, Fin.castAdd (α + α) j0) ∈
          (lift C t R' pos').edges := he
      rw [lf_new (α + α) φ b hx] at he'
      obtain ⟨i, _, hi⟩ := (E3 C t R' pos' b j0).1 he'
      exact absurd ((hIdx'.2.1 j0).2 ⟨i, Finset.mem_univ _, hi⟩) (hQ' j0 hj0)
  · -- consumers of the output
    rintro ⟨x, hx⟩
    induction x using Fin.addCases with
    | left a =>
      have ha := castAdd_not_mem (α + α) hx
      show (Fin.castAdd (α + α) q', (lf (α + α) φ ⟨Fin.castAdd (α + α) a, hx⟩).1) ∈ (lift C t R' pos').edges ↔
        (Fin.castAdd (α + α) q, Fin.castAdd (α + α) a) ∈ (lift C t R pos).edges
      rw [lf_old (α + α) φ a ha hx]
      exact (E1 C t R' pos' _ _).trans ((hcons ⟨a, ha⟩).trans (E1 C t R pos _ _).symm)
    | right b =>
      show (Fin.castAdd (α + α) q', (lf (α + α) φ ⟨Fin.natAdd R.n b, hx⟩).1) ∈ (lift C t R' pos').edges ↔
        (Fin.castAdd (α + α) q, Fin.natAdd R.n b) ∈ (lift C t R pos).edges
      rw [lf_new (α + α) φ b hx]
      exact iff_of_false (E2 C t R' pos' _ _) (E2 C t R pos _ _)
  · -- sink kept
    intro h
    have hs : R.sink ∉ Q := castAdd_not_mem (α + α) h
    show (lf (α + α) φ ⟨Fin.castAdd (α + α) R.sink, h⟩).1 = Fin.castAdd (α + α) R'.sink
    rw [lf_old (α + α) φ R.sink hs h, hs1 hs]
  · -- sink in Q
    intro h
    obtain ⟨x, hx, he⟩ := Finset.mem_image.1 h
    have hx' : x = R.sink := Fin.castAdd_injective _ _ he
    subst hx'
    obtain ⟨e1, e2⟩ := hs2 hx
    exact ⟨congrArg (Fin.castAdd (α + α)) e1, congrArg (Fin.castAdd (α + α)) e2⟩
  · intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hi
    intro h
    have : (lift C t R pos).parents (oN R x) = ∅ := h
    rw [lift_parents_nonaxiom C t R pos hIdx x (hQ x hx)] at this
    exact hQ x hx (Finset.image_eq_empty.1 this)
  · intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hi
    intro h
    have : (lift C t R' pos').parents (oN R' x) = ∅ := h
    rw [lift_parents_nonaxiom C t R' pos' hIdx' x (hQ' x hx)] at this
    exact hQ' x hx (Finset.image_eq_empty.1 this)

/-- The equivalence of the lifts induced by an equivalence of the old nodes. -/
def liftEq {n n' : ℕ} (e : Fin n ≃ Fin n') (m : ℕ) : Fin (n + m) ≃ Fin (n' + m) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin m))).trans finSumFinEquiv)

theorem liftEq_old {n n' : ℕ} (e : Fin n ≃ Fin n') (m : ℕ) (x : Fin n) :
    liftEq e m (Fin.castAdd m x) = Fin.castAdd m (e x) := by
  simp [liftEq, finSumFinEquiv_symm_apply_castAdd]

theorem liftEq_new {n n' : ℕ} (e : Fin n ≃ Fin n') (m : ℕ) (b : Fin m) :
    liftEq e m (Fin.natAdd n b) = Fin.natAdd n' b := by
  simp [liftEq, finSumFinEquiv_symm_apply_natAdd]

theorem lift_iso (R R' : ProofDag V) (pos : Fin α → Fin R.n) (pos' : Fin α → Fin R'.n)
    (e : Fin R.n ≃ Fin R'.n) (hl : ∀ i, R'.label (e i) = R.label i)
    (he : ∀ i j, (e i, e j) ∈ R'.edges ↔ (i, j) ∈ R.edges) (hsk : e R.sink = R'.sink)
    (hp : ∀ s, e (pos s) = pos' s) :
    (lift C t R pos).Iso (lift C t R' pos') := by
  refine ⟨liftEq e (α + α), ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left x =>
      show (lift C t R' pos').label (liftEq e (α + α) (Fin.castAdd (α + α) x)) = (lift C t R pos).label (Fin.castAdd (α + α) x)
      rw [liftEq_old]
      exact ((lift_label_old C t R' pos' _).trans (hl x)).trans (lift_label_old C t R pos x).symm
    | right b =>
      show (lift C t R' pos').label (liftEq e (α + α) (Fin.natAdd R.n b)) = (lift C t R pos).label (Fin.natAdd R.n b)
      rw [liftEq_new]
      exact lift_label_new C t R R' pos pos' b
  · intro i j
    induction i using Fin.addCases with
    | left x =>
      induction j using Fin.addCases with
      | left y =>
        show (liftEq e (α + α) (Fin.castAdd (α + α) x), liftEq e (α + α) (Fin.castAdd (α + α) y)) ∈
          (lift C t R' pos').edges ↔ (Fin.castAdd (α + α) x, Fin.castAdd (α + α) y) ∈ (lift C t R pos).edges
        rw [liftEq_old, liftEq_old]
        exact (E1 C t R' pos' _ _).trans ((he x y).trans (E1 C t R pos _ _).symm)
      | right b =>
        show (liftEq e (α + α) (Fin.castAdd (α + α) x), liftEq e (α + α) (Fin.natAdd R.n b)) ∈
          (lift C t R' pos').edges ↔ (Fin.castAdd (α + α) x, Fin.natAdd R.n b) ∈ (lift C t R pos).edges
        rw [liftEq_old, liftEq_new]
        exact iff_of_false (E2 C t R' pos' _ _) (E2 C t R pos _ _)
    | right a =>
      induction j using Fin.addCases with
      | left y =>
        show (liftEq e (α + α) (Fin.natAdd R.n a), liftEq e (α + α) (Fin.castAdd (α + α) y)) ∈
          (lift C t R' pos').edges ↔ (Fin.natAdd R.n a, Fin.castAdd (α + α) y) ∈ (lift C t R pos).edges
        rw [liftEq_new, liftEq_old]
        refine (E3 C t R' pos' a _).trans (Iff.trans ?_ (E3 C t R pos a y).symm)
        constructor
        · rintro ⟨i, hj, h⟩
          exact ⟨i, hj, e.injective ((hp i).trans h)⟩
        · rintro ⟨i, hj, h⟩
          exact ⟨i, hj, by rw [← hp i, h]⟩
      | right b =>
        show (liftEq e (α + α) (Fin.natAdd R.n a), liftEq e (α + α) (Fin.natAdd R.n b)) ∈
          (lift C t R' pos').edges ↔ (Fin.natAdd R.n a, Fin.natAdd R.n b) ∈ (lift C t R pos).edges
        rw [liftEq_new, liftEq_new]
        exact iff_of_false (E2 C t R' pos' _ _) (E2 C t R pos _ _)
  · show liftEq e (α + α) (Fin.castAdd (α + α) R.sink) = Fin.castAdd (α + α) R'.sink
    rw [liftEq_old, hsk]

theorem lift_step (hfresh : ∀ i j, ∀ l ∈ C j, l.1 ≠ t i) (w : ℕ)
    (hw : 1 + Finset.univ.sup (fun i => (C i).card) ≤ w) {k : ℕ}
    (P P' : Σ R : ProofDag V, Fin α → Fin R.n)
    (hstep : IndexedFrozenStep k (inventoryFormula C) w (2 * α - 1) C Finset.univ P P') :
    FrozenStep k (tagFormula C t) w (4 * α - 1) (lift C t P.1 P.2) (lift C t P'.1 P'.2) := by
  obtain ⟨hv, hv', hi, hi', hcase⟩ := hstep
  refine ⟨lift_isVertex C t P.1 P.2 hfresh w hw hv hi, lift_isVertex C t P'.1 P'.2 hfresh w hw hv' hi', ?_⟩
  rcases hcase with ⟨e, hl, he, hsk, hp⟩ | ⟨Q, Q', φ, hmv, hp⟩ | ⟨Q, Q', φ, hmv, hp⟩
  · exact Or.inl (lift_iso C t P.1 P'.1 P.2 P'.2 e hl he hsk (fun s => hp s (Finset.mem_univ s)))
  · exact Or.inr (Or.inl ⟨_, _, _, lift_move C t P.1 P'.1 P.2 P'.2 hi hi' hmv
      (fun s h => hp s (Finset.mem_univ s) h)⟩)
  · exact Or.inr (Or.inr ⟨_, _, _, lift_move C t P'.1 P.1 P'.2 P.2 hi' hi hmv
      (fun s h => hp s (Finset.mem_univ s) h)⟩)

theorem part2 (hfresh : ∀ i j, ∀ l ∈ C j, l.1 ≠ t i) (w : ℕ)
    (hw : 1 + Finset.univ.sup (fun i => (C i).card) ≤ w) {k : ℕ}
    (P P' : Σ R : ProofDag V, Fin α → Fin R.n)
    (hc : IndexedFrozenConnected k (inventoryFormula C) w (2 * α - 1) C Finset.univ P P') :
    FrozenConnected k (tagFormula C t) w (4 * α - 1) (lift C t P.1 P.2) (lift C t P'.1 P'.2) := by
  induction hc with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.tail ih (lift_step C t hfresh w hw _ _ hs)

end moves2
end Dev.T60

theorem chk_lemma_3_60 {V : Type} [DecidableEq V] (α : ℕ) (C : Fin α → Clause V)
    (hC : ∀ i, (C i).Nonempty) (w : ℕ) (hw : 1 + Finset.univ.sup (fun i => (C i).card) ≤ w)
    (t : Fin α → V) (ht : Function.Injective t) (hfresh : ∀ i j, ∀ l ∈ C j, l.1 ≠ t i)
    (k : ℕ) (hk : 1 ≤ k) :
    (∀ (R₁ R₂ : ProofDag V) (pos₁ : Fin α → Fin R₁.n) (pos₂ : Fin α → Fin R₂.n),
      IsTightIndexed C R₁ pos₁ → IsTightIndexed C R₂ pos₂ →
      FrozenConnected k (tagFormula C t) w (4 * α - 1) (lift C t R₁ pos₁) (lift C t R₂ pos₂) →
      FrozenConnected k (inventoryFormula C) w (2 * α - 1) R₁ R₂) ∧
    (∀ (R₁ R₂ : ProofDag V) (pos₁ : Fin α → Fin R₁.n) (pos₂ : Fin α → Fin R₂.n),
      IndexedFrozenConnected k (inventoryFormula C) w (2 * α - 1) C Finset.univ ⟨R₁, pos₁⟩ ⟨R₂, pos₂⟩ →
      FrozenConnected k (tagFormula C t) w (4 * α - 1) (lift C t R₁ pos₁) (lift C t R₂ pos₂)) ∧
    (tagFormula C t).card = 2 * α ∧
    ((∀ i, IsHornClause (C i)) → IsHorn (tagFormula C t)) := by
  refine ⟨?_, ?_, (Dev.T60.part3 C t ht hfresh).1, (Dev.T60.part3 C t ht hfresh).2⟩
  · intro R₁ R₂ pos₁ pos₂ h₁ h₂ hc
    exact frozenConnected_of_lift_frozenConnected α C hC w hw t ht hfresh k hk R₁ R₂ pos₁ pos₂ h₁ h₂ hc
  · intro R₁ R₂ pos₁ pos₂ hc
    exact Dev.T60.part2 C t hfresh w hw ⟨R₁, pos₁⟩ ⟨R₂, pos₂⟩ hc
end ReconfRes.Frozen
end

theorem solution : type_of% @ReconfRes.Frozen.chk_lemma_3_60 := @ReconfRes.Frozen.chk_lemma_3_60
