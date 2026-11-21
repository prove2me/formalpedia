-- Prove2me | solution 1 for ReconfRes.Frozen.decoding_capacity_two
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T22:09:22.902806+00:00
-- url     : https://prove2.me/submissions/eae2caba-730e-4618-b8f4-7cd0381b9feb

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph
import Definitions.Def_ReconfRes_Frozen_VertexCover
import Definitions.Def_ReconfRes_Frozen_Construction
import Theorems.Thm_ReconfRes_Frozen_lemma_3_47

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c
open ConstrData
/-!
Blueprint for `ReconfRes.Frozen.decoding_capacity_two` (the tree analysis of Lemmas 3.56/3.61).

Every tight refutation `R` is a read-once tree (Lemma 3.47 (1)).  The goal path is the chain of
descendants of the unique axiom node labelled `G`.  Every head `h` (and `A`) has a unique pivot
node `nu R (hd h)`, which lies on the goal path; dependencies order these events.  The proof of
the three claims reads literals off goal-path clauses.
-/
open Classical in
/-- The axiom node labelled `G` (junk: the sink). -/
def goalNode (D : ConstrData) (R : ProofDag (CVar D.TV)) : Fin R.n :=
  if h : ∃ i, R.parents i = ∅ ∧ R.label i = D.Gc then Classical.choose h else R.sink

open Classical in
/-- The (unique) node resolving on `x` (junk: the sink). -/
def nu {D : ConstrData} (R : ProofDag (CVar D.TV)) (x : CVar D.TV) : Fin R.n :=
  if h : ∃ i, R.HasPivot i x then Classical.choose h else R.sink

end ReconfRes.Frozen.Dev.Q427c
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS1
variable {V : Type} [DecidableEq V] {R : ProofDag V} {F : CNF V}
/-! ## Generic facts on read-once refutations -/
theorem mem_parents (i j : Fin R.n) : j ∈ R.parents i ↔ (j, i) ∈ R.edges := by
  simp [ProofDag.parents]

theorem mem_consumers (i j : Fin R.n) : j ∈ R.consumers i ↔ (i, j) ∈ R.edges := by
  simp [ProofDag.consumers]

theorem antisymm (hR : R.IsRefutationOf F) {i j : Fin R.n} (h1 : R.Anc i j) (h2 : R.Anc j i) :
    i = j := by
  unfold ProofDag.Anc at h1 h2
  rcases Relation.ReflTransGen.cases_head h1 with h | ⟨c, hc, hcj⟩
  · exact h
  · exact (hR.1 i c hc (hcj.trans h2)).elim

theorem uniq_consumer (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {a c c' : Fin R.n}
    (h : (a, c) ∈ R.edges) (h' : (a, c') ∈ R.edges) : c = c' := by
  have hs : a ≠ R.sink := by
    rintro rfl
    have : c ∈ R.consumers R.sink := (mem_consumers _ _).2 h
    rw [hR.2.2.2.1] at this; simp at this
  exact Finset.card_le_one.1 (hro.2.2 a hs).le c ((mem_consumers _ _).2 h) c'
    ((mem_consumers _ _).2 h')

theorem chain (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {a i j : Fin R.n}
    (hi : R.Anc a i) (hj : R.Anc a j) : R.Anc i j ∨ R.Anc j i := by
  unfold ProofDag.Anc at hi hj ⊢
  induction hi using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl hj
  | head hac hci ih =>
    rename_i a c
    rcases Relation.ReflTransGen.cases_head hj with rfl | ⟨c', hac', hc'j⟩
    · exact Or.inr (Relation.ReflTransGen.head hac hci)
    · rw [uniq_consumer hR hro hac hac'] at ih
      exact ih hc'j

theorem sibling_aux (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {p o k : Fin R.n}
    (hp : (p, k) ∈ R.edges) (ho : (o, k) ∈ R.edges) (hne : p ≠ o) (h : R.Anc p o) : False := by
  unfold ProofDag.Anc at h
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, hco⟩
  · exact hne h
  · rw [uniq_consumer hR hro hc hp] at hco
    exact hR.1 o k ho hco

/-- Two distinct parents of one node have no common ancestor. -/
theorem sibling (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {p o k a : Fin R.n}
    (hp : (p, k) ∈ R.edges) (ho : (o, k) ∈ R.edges) (hne : p ≠ o) (hap : R.Anc a p)
    (hao : R.Anc a o) : False := by
  rcases chain hR hro hap hao with h | h
  · exact sibling_aux hR hro hp ho hne h
  · exact sibling_aux hR hro ho hp (Ne.symm hne) h

theorem node_cases (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) (i : Fin R.n) :
    (R.parents i = ∅ ∧ R.label i ∈ F) ∨
    (∃ p₁ p₂, p₁ ≠ p₂ ∧ R.parents i = {p₁, p₂} ∧
      ∃ x, ResolventOn x (R.label p₁) (R.label p₂) (R.label i)) := by
  rcases hR.2.2.1 i with h | h | ⟨p, hp, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact (hro.2.1 i (by unfold ProofDag.IsWeakeningNode; rw [hp]; simp)).elim

theorem resolvent_sub {x : V} {A B C : Clause V} (h : ResolventOn x A B C) {l : Literal V}
    (hl : l ∈ C) : l ∈ A ∨ l ∈ B := by
  rw [h.2.2] at hl
  rcases Finset.mem_union.1 hl with h | h
  · exact Or.inl (Finset.mem_of_mem_erase h)
  · exact Or.inr (Finset.mem_of_mem_erase h)

/-- A node with a parent is a resolution node. -/
theorem edge_res (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {k' k : Fin R.n}
    (h : (k', k) ∈ R.edges) :
    ∃ q₁ q₂ x, q₁ ≠ q₂ ∧ R.parents k = {q₁, q₂} ∧
      ResolventOn x (R.label q₁) (R.label q₂) (R.label k) ∧ (k' = q₁ ∨ k' = q₂) := by
  rcases node_cases hR hro k with ⟨h0, -⟩ | ⟨q₁, q₂, hne, hpar, x, hx⟩
  · have : k' ∈ R.parents k := (mem_parents _ _).2 h
    rw [h0] at this; simp at this
  · have : k' ∈ R.parents k := (mem_parents _ _).2 h
    rw [hpar] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    exact ⟨q₁, q₂, x, hne, hpar, hx, this⟩

theorem edge_of_parents {k q₁ q₂ : Fin R.n} (h : R.parents k = {q₁, q₂}) :
    (q₁, k) ∈ R.edges ∧ (q₂, k) ∈ R.edges := by
  constructor
  · rw [← mem_parents, h]; simp
  · rw [← mem_parents, h]; simp

/-- A literal lost along an edge is the pivot literal on its side. -/
theorem drop (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {k' k : Fin R.n}
    (h : (k', k) ∈ R.edges) {l : Literal V} (hl : l ∈ R.label k') (hl' : l ∉ R.label k) :
    ∃ q₁ q₂ x, q₁ ≠ q₂ ∧ R.parents k = {q₁, q₂} ∧
      ResolventOn x (R.label q₁) (R.label q₂) (R.label k) ∧
      ((k' = q₁ ∧ l = (x, true)) ∨ (k' = q₂ ∧ l = (x, false))) := by
  obtain ⟨q₁, q₂, x, hne, hpar, hx, hk⟩ := edge_res hR hro h
  refine ⟨q₁, q₂, x, hne, hpar, hx, ?_⟩
  rcases hk with rfl | rfl
  · left; refine ⟨rfl, ?_⟩
    by_contra hc
    exact hl' (by rw [hx.2.2]; exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hc, hl⟩))
  · right; refine ⟨rfl, ?_⟩
    by_contra hc
    exact hl' (by rw [hx.2.2]; exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hc, hl⟩))

theorem exists_drop {a b : Fin R.n} (hab : R.Anc a b) {l : Literal V} (hl : l ∈ R.label a)
    (hl' : l ∉ R.label b) :
    ∃ k' k, R.Anc a k' ∧ (k', k) ∈ R.edges ∧ R.Anc k b ∧ l ∈ R.label k' ∧ l ∉ R.label k := by
  unfold ProofDag.Anc at hab
  induction hab with
  | refl => exact (hl' hl).elim
  | tail hab' hb ih =>
    rename_i b' b
    by_cases h : l ∈ R.label b'
    · exact ⟨b', b, hab', hb, Relation.ReflTransGen.refl, h, hl'⟩
    · obtain ⟨k', k, h1, h2, h3, h4, h5⟩ := ih h
      exact ⟨k', k, h1, h2, Relation.ReflTransGen.tail h3 hb, h4, h5⟩

/-! ### Induction along ancestry -/
open Classical in
/-- The number of ancestors. -/
def rank (R : ProofDag V) (j : Fin R.n) : ℕ := (Finset.univ.filter fun a => R.Anc a j).card

theorem rank_lt (hR : R.IsRefutationOf F) {p j : Fin R.n} (h : (p, j) ∈ R.edges) :
    rank R p < rank R j := by
  classical
  unfold rank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨j, by simp; exact Relation.ReflTransGen.refl, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun hjp => hR.1 p j h hjp
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact Relation.ReflTransGen.tail ha h

theorem anc_ind (hR : R.IsRefutationOf F) (P : Fin R.n → Prop)
    (h : ∀ j, (∀ p, (p, j) ∈ R.edges → P p) → P j) : ∀ j, P j := by
  suffices ∀ N, ∀ j, rank R j ≤ N → P j from fun j => this _ j le_rfl
  intro N
  induction N with
  | zero =>
    intro j hj
    exact h j fun p hp => absurd (rank_lt hR hp) (by omega)
  | succ N ih =>
    intro j hj
    exact h j fun p hp => ih p (by have := rank_lt hR hp; omega)

/-- Every literal comes from an axiom ancestor. -/
theorem origin (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {l : Literal V} :
    ∀ j, l ∈ R.label j → ∃ a, R.parents a = ∅ ∧ R.Anc a j ∧ l ∈ R.label a := by
  refine anc_ind hR _ fun j ih hl => ?_
  rcases node_cases hR hro j with ⟨h0, -⟩ | ⟨q₁, q₂, hne, hpar, x, hx⟩
  · exact ⟨j, h0, Relation.ReflTransGen.refl, hl⟩
  · have he := edge_of_parents hpar
    rcases resolvent_sub hx hl with h | h
    · obtain ⟨a, h1, h2, h3⟩ := ih q₁ he.1 h
      exact ⟨a, h1, Relation.ReflTransGen.tail h2 he.1, h3⟩
    · obtain ⟨a, h1, h2, h3⟩ := ih q₂ he.2 h
      exact ⟨a, h1, Relation.ReflTransGen.tail h2 he.2, h3⟩

/-! ### Horn -/
theorem horn_iff {C : Clause V} :
    IsHornClause C ↔ ∀ x y, (x, true) ∈ C → (y, true) ∈ C → x = y := by
  unfold IsHornClause
  rw [Finset.card_le_one]
  constructor
  · intro h x y hx hy
    have := h (x, true) (by simp [hx]) (y, true) (by simp [hy])
    simpa using this
  · intro h a ha b hb
    simp only [Finset.mem_filter] at ha hb
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    simp only at ha hb
    obtain ⟨ha, rfl⟩ := ha
    obtain ⟨hb, rfl⟩ := hb
    rw [h a1 b1 ha hb]

theorem horn_all (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    (hax : ∀ a, R.parents a = ∅ → IsHornClause (R.label a)) : ∀ j, IsHornClause (R.label j) := by
  refine anc_ind hR _ fun j ih => ?_
  rcases node_cases hR hro j with ⟨h0, -⟩ | ⟨q₁, q₂, hne, hpar, x, hx⟩
  · exact hax j h0
  · have he := edge_of_parents hpar
    have h1 := horn_iff.1 (ih q₁ he.1)
    have h2 := horn_iff.1 (ih q₂ he.2)
    have key : ∀ y, (y, true) ∈ R.label j → (y, true) ∈ R.label q₂ := by
      intro y hy
      rw [hx.2.2] at hy
      rcases Finset.mem_union.1 hy with h | h
      · obtain ⟨hne', hm⟩ := Finset.mem_erase.1 h
        exact (hne' (by rw [h1 y x hm hx.1])).elim
      · exact Finset.mem_of_mem_erase h
    exact horn_iff.2 fun a b ha hb => h2 a b (key a ha) (key b hb)

/-! ### Unit-only variables -/
/-- Every axiom containing `y` is the unit `{y}`. -/
def UnitOnly (R : ProofDag V) (y : V) : Prop :=
  ∀ a, R.parents a = ∅ → (y, true) ∈ R.label a → R.label a = {(y, true)}

/-- At most one axiom node contains `y`. -/
def UniqSrc (R : ProofDag V) (y : V) : Prop :=
  ∀ a a', R.parents a = ∅ → R.parents a' = ∅ → (y, true) ∈ R.label a → (y, true) ∈ R.label a' →
    a = a'

theorem unitOnly_all (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {y : V} (hy : UnitOnly R y) :
    ∀ j, (y, true) ∈ R.label j → R.label j = {(y, true)} := by
  refine anc_ind hR _ fun j ih hj => ?_
  rcases node_cases hR hro j with ⟨h0, -⟩ | ⟨q₁, q₂, hne, hpar, x, hx⟩
  · exact hy j h0 hj
  · exfalso
    have he := edge_of_parents hpar
    have hj' := hj
    rw [hx.2.2] at hj'
    rcases Finset.mem_union.1 hj' with h | h
    · obtain ⟨hne', hm⟩ := Finset.mem_erase.1 h
      have := ih q₁ he.1 hm
      have h2 := hx.1
      rw [this, Finset.mem_singleton] at h2
      exact hne' h2.symm
    · have := ih q₂ he.2 (Finset.mem_of_mem_erase h)
      have h2 := hx.2.1
      rw [this, Finset.mem_singleton] at h2
      simp at h2

end ReconfRes.Frozen.Dev.Q427c.PartS1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS1
variable {V : Type} [DecidableEq V] {R : ProofDag V} {F : CNF V}
variable (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {y : V} (hy : UniqSrc R y)
include hR hro hy
/-! ### Single-source variables -/
theorem common_src {j j' : Fin R.n} (h : (y, true) ∈ R.label j) (h' : (y, true) ∈ R.label j') :
    ∃ c, R.Anc c j ∧ R.Anc c j' := by
  obtain ⟨a, ha0, haj, ha⟩ := origin hR hro j h
  obtain ⟨a', ha0', haj', ha'⟩ := origin hR hro j' h'
  rw [hy a a' ha0 ha0' ha ha'] at haj
  exact ⟨a', haj, haj'⟩

theorem absent_at {i : Fin R.n} (hi : R.HasPivot i y) : (y, true) ∉ R.label i := by
  obtain ⟨p₁, p₂, hne, hpar, hx⟩ := hi
  have he := edge_of_parents hpar
  intro h
  rw [hx.2.2] at h
  rcases Finset.mem_union.1 h with h | h
  · exact (Finset.mem_erase.1 h).1 rfl
  · obtain ⟨c, h1, h2⟩ := common_src hR hro hy hx.1 (Finset.mem_of_mem_erase h)
    exact sibling hR hro he.1 he.2 hne h1 h2

theorem pivot_src {i : Fin R.n} (hi : R.HasPivot i y) :
    ∃ p, (p, i) ∈ R.edges ∧ (y, true) ∈ R.label p := by
  obtain ⟨p₁, p₂, hne, hpar, hx⟩ := hi
  exact ⟨p₁, (edge_of_parents hpar).1, hx.1⟩

theorem absent_after {i k : Fin R.n} (hi : R.HasPivot i y) (hik : R.Anc i k) :
    (y, true) ∉ R.label k := by
  unfold ProofDag.Anc at hik
  induction hik with
  | refl => exact absent_at hR hro hy hi
  | tail hik' hk ih =>
    rename_i k' k
    intro h
    obtain ⟨q₁, q₂, x, hne, hpar, hx, hk'⟩ := edge_res hR hro hk
    have he := edge_of_parents hpar
    obtain ⟨p, hp, hpy⟩ := pivot_src hR hro hy hi
    rcases resolvent_sub hx h with h1 | h1
    · rcases hk' with rfl | rfl
      · exact ih h1
      · obtain ⟨c, hc1, hc2⟩ := common_src hR hro hy h1 hpy
        exact sibling hR hro he.1 he.2 hne hc1
          ((Relation.ReflTransGen.tail hc2 hp).trans hik')
    · rcases hk' with rfl | rfl
      · obtain ⟨c, hc1, hc2⟩ := common_src hR hro hy h1 hpy
        exact sibling hR hro he.2 he.1 (Ne.symm hne) hc1
          ((Relation.ReflTransGen.tail hc2 hp).trans hik')
      · exact ih h1

theorem pivot_unique {i i' : Fin R.n} (hi : R.HasPivot i y) (hi' : R.HasPivot i' y) : i = i' := by
  suffices H : ∀ {i i' : Fin R.n}, R.HasPivot i y → R.HasPivot i' y → R.Anc i i' → i = i' by
    obtain ⟨p, hp, hpy⟩ := pivot_src hR hro hy hi
    obtain ⟨p', hp', hpy'⟩ := pivot_src hR hro hy hi'
    obtain ⟨c, hc1, hc2⟩ := common_src hR hro hy hpy hpy'
    rcases chain hR hro (Relation.ReflTransGen.tail hc1 hp) (Relation.ReflTransGen.tail hc2 hp')
      with h | h
    · exact H hi hi' h
    · exact (H hi' hi h).symm
  intro i i' hi hi' h
  unfold ProofDag.Anc at h
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨k', hik', hk'⟩
  · exact h.symm
  · exfalso
    obtain ⟨q₁, q₂, hne, hpar, hx⟩ := hi'
    have he := edge_of_parents hpar
    have hk'' : k' ∈ R.parents i' := (mem_parents _ _).2 hk'
    rw [hpar] at hk''
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk''
    rcases hk'' with rfl | rfl
    · exact absent_after hR hro hy hi hik' hx.1
    · obtain ⟨p, hp, hpy⟩ := pivot_src hR hro hy hi
      obtain ⟨c, hc1, hc2⟩ := common_src hR hro hy hx.1 hpy
      exact sibling hR hro he.1 he.2 hne hc1 ((Relation.ReflTransGen.tail hc2 hp).trans hik')

theorem no_taut_single {j : Fin R.n} (h1 : (y, true) ∈ R.label j) (h2 : (y, false) ∈ R.label j) :
    False := by
  have hsink : R.label R.sink = ∅ := hR.2.2.2.2
  obtain ⟨k', k, hjk', hk, hks, hy', hyk⟩ :=
    exists_drop (hro.1 j) h1 (by rw [hsink]; simp)
  obtain ⟨q₁, q₂, x, hne, hpar, hx, hc⟩ := drop hR hro hk hy' hyk
  rcases hc with ⟨rfl, hxy⟩ | ⟨rfl, hxy⟩
  · simp only [Prod.mk.injEq, and_true] at hxy
    subst hxy
    have hpk : R.HasPivot k y := ⟨k', q₂, hne, hpar, hx⟩
    -- `¬y` survives from `j` to `k'`
    have hn : (y, false) ∈ R.label k' := by
      by_contra hn
      obtain ⟨m', m, -, hm, hmk', hm1, hm2⟩ := exists_drop hjk' h2 hn
      obtain ⟨r₁, r₂, x', hne', hpar', hx', hc'⟩ := drop hR hro hm hm1 hm2
      rcases hc' with ⟨-, hc'⟩ | ⟨rfl, hc'⟩
      · simp at hc'
      · simp only [Prod.mk.injEq, and_true] at hc'
        subst hc'
        have := pivot_unique hR hro hy ⟨r₁, m', hne', hpar', hx'⟩ hpk
        subst this
        exact hR.1 k' m hk hmk'
    have hnk : (y, false) ∈ R.label k := by
      rw [hx.2.2]
      exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨by simp, hn⟩)
    obtain ⟨m', m, hkm', hm, -, hm1, hm2⟩ :=
      exists_drop (hro.1 k) hnk (by rw [hsink]; simp)
    obtain ⟨r₁, r₂, x', hne', hpar', hx', hc'⟩ := drop hR hro hm hm1 hm2
    rcases hc' with ⟨-, hc'⟩ | ⟨rfl, hc'⟩
    · simp at hc'
    · simp only [Prod.mk.injEq, and_true] at hc'
      subst hc'
      have := pivot_unique hR hro hy ⟨r₁, m', hne', hpar', hx'⟩ hpk
      subst this
      exact hR.1 m' m hm hkm'
  · simp at hxy

end ReconfRes.Frozen.Dev.Q427c.PartS1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS1
variable {V : Type} [DecidableEq V] {R : ProofDag V} {F : CNF V}
/-- With Horn axioms and every variable unit-only or single-source, pivots are unique. -/
theorem unique_pivot_gen (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    (hax : ∀ a, R.parents a = ∅ → IsHornClause (R.label a))
    (hvar : ∀ y, UniqSrc R y ∨ UnitOnly R y) :
    ∀ (i : Fin R.n) (x y : V), R.HasPivot i x → R.HasPivot i y → x = y := by
  have notaut : ∀ j y, (y, true) ∈ R.label j → (y, false) ∈ R.label j → False := by
    intro j y h1 h2
    rcases hvar y with hy | hy
    · exact no_taut_single hR hro hy h1 h2
    · rw [unitOnly_all hR hro hy j h1] at h2; simp at h2
  intro i x y ⟨p₁, p₂, hne, hpar, hx⟩ ⟨q₁, q₂, hne', hpar', hy⟩
  rw [hpar] at hpar'
  have hq1 : q₁ ∈ ({p₁, p₂} : Finset (Fin R.n)) := by rw [hpar']; simp
  have hq2 : q₂ ∈ ({p₁, p₂} : Finset (Fin R.n)) := by rw [hpar']; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq1 hq2
  rcases hq1 with h1 | h1
  · rw [h1] at hy
    exact horn_iff.1 (horn_all hR hro hax p₁) x y hx.1 hy.1
  · have h2 : q₂ = p₁ := by
      rcases hq2 with h2 | h2
      · exact h2
      · exact (hne' (h1.trans h2.symm)).elim
    rw [h1, h2] at hy
    exfalso
    apply notaut i y
    · rw [hx.2.2]
      exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨by simp, hy.1⟩)
    · rw [hx.2.2]
      exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨by simp, hy.2.1⟩)

end ReconfRes.Frozen.Dev.Q427c.PartS1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS1
open ConstrData
/-! ## The construction -/
theorem internal_len {τ : Type} (t : FBTree τ) :
    t.internalPaths.length + 1 = t.leaves.length := by
  induction t with
  | leaf v => simp [FBTree.internalPaths, FBTree.leaves]
  | node l r ihl ihr =>
    simp only [FBTree.internalPaths, FBTree.leaves, List.length_cons, List.length_append,
      List.length_map]
    omega

theorem internal_nodup {τ : Type} (t : FBTree τ) : t.internalPaths.Nodup := by
  induction t with
  | leaf v => simp [FBTree.internalPaths]
  | node l r ihl ihr =>
    simp only [FBTree.internalPaths]
    refine List.nodup_cons.2 ⟨by simp, ?_⟩
    refine List.Nodup.append (ihl.map (fun _ _ h => List.cons_injective h))
      (ihr.map (fun _ _ h => List.cons_injective h)) ?_
    intro x hx hy
    simp only [List.mem_map] at hx hy
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨b, -, hb⟩ := hy
    simp at hb

theorem filt_card {τ : Type} (t : FBTree τ) (h : 2 ≤ t.leaves.length) :
    ((t.internalPaths.filter fun p => p ≠ []).toFinset).card + 2 = t.leaves.length := by
  rw [List.toFinset_card_of_nodup ((internal_nodup t).filter _)]
  cases t with
  | leaf v => simp [FBTree.leaves] at h
  | node l r =>
    have hl := internal_len l
    have hr := internal_len r
    have : ((FBTree.node l r).internalPaths.filter fun p => p ≠ []) =
        l.internalPaths.map (false :: ·) ++ r.internalPaths.map (true :: ·) := by
      simp only [FBTree.internalPaths]
      rw [List.filter_cons_of_neg (by simp), List.filter_eq_self.2]
      intro a ha
      simp only [List.mem_append, List.mem_map] at ha
      rcases ha with ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩ <;> simp
    rw [this]
    simp only [FBTree.leaves, List.length_append, List.length_map]
    omega

theorem leaves_len {τ : Type} [Fintype τ] [DecidableEq τ] (t : FBTree τ)
    (h : t.LeavesExactly) : t.leaves.length = Fintype.card τ := by
  rw [← List.toFinset_card_of_nodup h.1]
  have : t.leaves.toFinset = Finset.univ := by ext x; simp [h.2 x]
  rw [this, Finset.card_univ]

theorem card_TV (D : ConstrData) : Fintype.card D.TV = D.m := by
  simp [ConstrData.m, ConstrData.TV, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]

theorem m_ge (D : ConstrData) (hD : D.Valid) : 2 ≤ D.m := by
  have := hD.1
  unfold ConstrData.m
  have : 1 ≤ D.b := by simp only [ConstrData.b]; omega
  nlinarith

theorem inner1_card (D : ConstrData) (hD : D.Valid) : D.inner1.card + 2 = D.m := by
  unfold ConstrData.inner1
  rw [Finset.card_image_of_injective _ (fun _ _ h => Head.i1.inj h)]
  have hl := leaves_len D.t1 hD.2.2.2.2.1
  rw [card_TV] at hl
  have := filt_card D.t1 (by rw [hl]; exact m_ge D hD)
  omega

theorem inner2_card (D : ConstrData) (hD : D.Valid) : D.inner2.card + 2 = D.m := by
  unfold ConstrData.inner2
  rw [Finset.card_image_of_injective _ (fun _ _ h => Head.i2.inj h)]
  have hl := leaves_len D.t2 hD.2.2.2.2.2
  rw [card_TV] at hl
  have := filt_card D.t2 (by rw [hl]; exact m_ge D hD)
  omega

theorem heads_card' (D : ConstrData) (hD : D.Valid) : D.heads.card + 2 = 4 * D.m := by
  have h1 := inner1_card D hD
  have h2 := inner2_card D hD
  have ha : (Finset.univ.image (Head.a (τ := D.TV))).card = D.m := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Head.a.inj h), Finset.card_univ, card_TV]
  have hb : (Finset.univ.image (Head.b (τ := D.TV))).card = D.m := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Head.b.inj h), Finset.card_univ, card_TV]
  have hTU : ({Head.T, Head.U} : Finset (Head D.TV)).card = 2 := by simp
  unfold ConstrData.heads
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Finset.card_union_of_disjoint]
  · omega
  all_goals
    refine Finset.disjoint_left.2 fun x hx hy => ?_
    simp only [ConstrData.inner1, ConstrData.inner2, Finset.mem_image, Finset.mem_univ,
      true_and] at hy
    obtain ⟨p, -, rfl⟩ := hy
    simp [ConstrData.inner1] at hx

/-- The number of source occurrences is `α`. -/
theorem srcs_card (D : ConstrData) (hD : D.Valid) : D.srcs.card = D.α := by
  have hh := heads_card' D hD
  have hm := m_ge D hD
  have hC : (D.heads.image (Src.C (τ := D.TV))).card = D.heads.card :=
    Finset.card_image_of_injective _ (fun _ _ h => Src.C.inj h)
  have hz : (D.heads.image (Src.z (τ := D.TV))).card = D.heads.card :=
    Finset.card_image_of_injective _ (fun _ _ h => Src.z.inj h)
  have hp : (D.ballast.image (Src.p (τ := D.TV))).card = D.r := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Src.p.inj h)]
    simp [ConstrData.ballast]
  have hP : (Finset.univ.image (Src.P (τ := D.TV))).card = D.m := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Src.P.inj h), Finset.card_univ, card_TV]
  have hQ : (Finset.univ.image (Src.Q (τ := D.TV))).card = D.m := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Src.Q.inj h), Finset.card_univ, card_TV]
  have h2 : ({Src.CA, Src.G} : Finset (Src D.TV)).card = 2 := by simp
  unfold ConstrData.srcs ConstrData.α
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
  · omega
  all_goals
    refine Finset.disjoint_left.2 fun x hx hy => ?_
    first
    | (simp only [Finset.mem_insert, Finset.mem_singleton] at hy
       rcases hy with rfl | rfl <;> simp at hx)
    | (simp only [Finset.mem_image] at hy
       obtain ⟨p, -, rfl⟩ := hy
       simp at hx)

theorem pos_inv (D : ConstrData) (s : Src D.TV) (y : CVar D.TV) (h : (y, true) ∈ D.inv s) :
    (∃ h', s = Src.C h' ∧ y = CVar.hd h') ∨ (s = Src.CA ∧ y = CVar.A) ∨
      (D.inv s = {(y, true)} ∧ (∀ h', y ≠ CVar.hd h') ∧ y ≠ CVar.A) := by
  cases s <;> simp [ConstrData.inv, ConstrData.Ch, ConstrData.CA, ConstrData.Gc] at h ⊢
  all_goals first
    | exact h
    | (subst h; simp)

theorem inv_eq_Ch (D : ConstrData) {s : Src D.TV} {h : Head D.TV} (hs : D.inv s = D.Ch h) :
    s = Src.C h := by
  have hm : (CVar.hd h, true) ∈ D.inv s := by rw [hs]; simp [ConstrData.Ch]
  rcases pos_inv D s _ hm with ⟨h', rfl, he⟩ | ⟨-, he⟩ | ⟨-, he, -⟩
  · cases he; rfl
  · cases he
  · exact (he h rfl).elim

theorem inv_eq_CA (D : ConstrData) {s : Src D.TV} (hs : D.inv s = D.CA) : s = Src.CA := by
  have hm : (CVar.A, true) ∈ D.inv s := by rw [hs]; simp [ConstrData.CA]
  rcases pos_inv D s _ hm with ⟨h', rfl, he⟩ | ⟨h1, -⟩ | ⟨-, -, he⟩
  · cases he
  · exact h1
  · exact (he rfl).elim

end ReconfRes.Frozen.Dev.Q427c.PartS1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS1
open ConstrData
variable {D : ConstrData} {R : ProofDag (CVar D.TV)}
theorem axiom_label (hR : D.IsTight R) (hro : R.IsReadOnce) {a : Fin R.n} (ha : R.parents a = ∅) :
    ∃ s ∈ D.srcs, D.inv s = R.label a := by
  rcases node_cases hR.1 hro a with ⟨-, h⟩ | ⟨p₁, p₂, hne, hpar, -⟩
  · simpa [ConstrData.formula] using h
  · rw [ha] at hpar
    have : p₁ ∈ (∅ : Finset (Fin R.n)) := by rw [hpar]; simp
    simp at this

theorem count_axiom (hR : D.IsTight R) (C : Clause (CVar D.TV)) :
    Multiset.count C R.axiomMultiset =
      ((Finset.univ.filter fun i => R.parents i = ∅).filter fun i => C = R.label i).card := by
  unfold ProofDag.axiomMultiset
  rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val]

theorem axiom_label_unique (hR : D.IsTight R) (C : Clause (CVar D.TV)) (s0 : Src D.TV)
    (hC : ∀ s, D.inv s = C → s = s0) {a a' : Fin R.n} (ha : R.parents a = ∅)
    (ha' : R.parents a' = ∅) (hl : R.label a = C) (hl' : R.label a' = C) : a = a' := by
  by_contra hne
  have h1 : 1 < Multiset.count C R.axiomMultiset := by
    rw [count_axiom hR]
    exact Finset.one_lt_card.2 ⟨a, by simp [ha, hl], a', by simp [ha', hl'], hne⟩
  have h2 : Multiset.count C D.inventory ≤ 1 := by
    unfold ConstrData.inventory
    rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val]
    refine (Finset.card_le_card (t := {s0}) fun s hs => ?_).trans (by simp)
    simp only [Finset.mem_filter] at hs
    simp [hC s hs.2.symm]
  rw [hR.2.2.1] at h1
  omega

theorem uniqSrc_hd (hR : D.IsTight R) (hro : R.IsReadOnce) (h : Head D.TV) :
    UniqSrc R (CVar.hd h) := by
  intro a a' ha ha' hy hy'
  have key : ∀ b, R.parents b = ∅ → (CVar.hd h, true) ∈ R.label b → R.label b = D.Ch h := by
    intro b hb hyb
    obtain ⟨s, -, hs⟩ := axiom_label hR hro hb
    rw [← hs] at hyb ⊢
    rcases pos_inv D s _ hyb with ⟨h', rfl, he⟩ | ⟨-, he⟩ | ⟨-, he, -⟩
    · cases he; rfl
    · cases he
    · exact (he h rfl).elim
  exact axiom_label_unique hR _ _ (fun s hs => inv_eq_Ch D hs) ha ha' (key a ha hy) (key a' ha' hy')

theorem uniqSrc_A (hR : D.IsTight R) (hro : R.IsReadOnce) : UniqSrc R CVar.A := by
  intro a a' ha ha' hy hy'
  have key : ∀ b, R.parents b = ∅ → (CVar.A, true) ∈ R.label b → R.label b = D.CA := by
    intro b hb hyb
    obtain ⟨s, -, hs⟩ := axiom_label hR hro hb
    rw [← hs] at hyb ⊢
    rcases pos_inv D s _ hyb with ⟨h', rfl, he⟩ | ⟨rfl, -⟩ | ⟨-, -, he⟩
    · cases he
    · rfl
    · exact (he rfl).elim
  exact axiom_label_unique hR _ _ (fun s hs => inv_eq_CA D hs) ha ha' (key a ha hy) (key a' ha' hy')

theorem unitOnly_of (hR : D.IsTight R) (hro : R.IsReadOnce) {y : CVar D.TV}
    (hy1 : ∀ h, y ≠ CVar.hd h) (hy2 : y ≠ CVar.A) : UnitOnly R y := by
  intro a ha hya
  obtain ⟨s, -, hs⟩ := axiom_label hR hro ha
  rw [← hs] at hya ⊢
  rcases pos_inv D s _ hya with ⟨h', -, he⟩ | ⟨-, he⟩ | ⟨he, -⟩
  · exact (hy1 h' he).elim
  · exact (hy2 he).elim
  · exact he

theorem hvar (hR : D.IsTight R) (hro : R.IsReadOnce) (y : CVar D.TV) :
    UniqSrc R y ∨ UnitOnly R y := by
  cases y with
  | hd h => exact Or.inl (uniqSrc_hd hR hro h)
  | A => exact Or.inl (uniqSrc_A hR hro)
  | z h => exact Or.inr (unitOnly_of hR hro (by simp) (by simp))
  | f v => exact Or.inr (unitOnly_of hR hro (by simp) (by simp))
  | p j => exact Or.inr (unitOnly_of hR hro (by simp) (by simp))

theorem hax (hR : D.IsTight R) (hro : R.IsReadOnce) :
    ∀ a, R.parents a = ∅ → IsHornClause (R.label a) := by
  intro a ha
  obtain ⟨s, -, hs⟩ := axiom_label hR hro ha
  rw [← hs]
  refine horn_iff.2 fun x y hx hy => ?_
  rcases pos_inv D s _ hx with ⟨h, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨he, -⟩
  · rcases pos_inv D _ _ hy with ⟨h', he, rfl⟩ | ⟨he, -⟩ | ⟨he, -⟩
    · cases he; rfl
    · cases he
    · rw [he] at hx; simp at hx; exact hx
  · rcases pos_inv D _ _ hy with ⟨h', he, rfl⟩ | ⟨-, rfl⟩ | ⟨he, -⟩
    · cases he
    · rfl
    · rw [he] at hx; simp at hx; exact hx
  · rw [he] at hy; simp at hy; exact hy.symm

end ReconfRes.Frozen.Dev.Q427c.PartS1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS1
open ConstrData
variable (D : ConstrData)
/-! ## The targets -/
theorem tight_readOnce (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) :
    R.IsReadOnce := by
  have hc : Multiset.card D.inventory = D.α := by
    unfold ConstrData.inventory
    rw [Multiset.card_map, Finset.card_val, srcs_card D hD]
  have hm := m_ge D hD
  have hα : 1 ≤ D.α := by unfold ConstrData.α; omega
  exact (lemma_3_47 D.formula D.inventory (hc ▸ hα)).1 R hR.1 hR.2.1 hR.2.2.1 (hc ▸ hR.2.2.2)

end ReconfRes.Frozen.Dev.Q427c.PartS1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c
open ConstrData
variable (D : ConstrData)
/-! ## Part S: structure of tight refutations -/
alias tight_readOnce := ReconfRes.Frozen.Dev.Q427c.PartS1.tight_readOnce

end ReconfRes.Frozen.Dev.Q427c
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS1
open ConstrData
variable (D : ConstrData)
/-- Claim 3: unique pivots (Horn clauses, and no tautological clause: every variable has either
a single positive axiom occurrence or only unit positive axiom occurrences). -/
theorem unique_pivot (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) :
    ∀ (i : Fin R.n) (x y : CVar D.TV), R.HasPivot i x → R.HasPivot i y → x = y := by
  have hro := tight_readOnce D hD hR
  exact unique_pivot_gen hR.1 hro (hax hR hro) (hvar hR hro)

end ReconfRes.Frozen.Dev.Q427c.PartS1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c
open ConstrData
variable (D : ConstrData)
alias unique_pivot := ReconfRes.Frozen.Dev.Q427c.PartS1.unique_pivot

end ReconfRes.Frozen.Dev.Q427c
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS1
open ConstrData
variable (D : ConstrData)
theorem goal_axiom (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) :
    R.parents (goalNode D R) = ∅ ∧ R.label (goalNode D R) = D.Gc := by
  have hex : ∃ i, R.parents i = ∅ ∧ R.label i = D.Gc := by
    have hG : D.Gc ∈ R.axiomMultiset := by
      rw [hR.2.2.1]
      unfold ConstrData.inventory
      exact Multiset.mem_map.2 ⟨Src.G, by simp [ConstrData.srcs], rfl⟩
    unfold ProofDag.axiomMultiset at hG
    obtain ⟨i, hi, hl⟩ := Multiset.mem_map.1 hG
    simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨i, hi, hl⟩
  unfold goalNode
  rw [dif_pos hex]
  exact Classical.choose_spec hex

end ReconfRes.Frozen.Dev.Q427c.PartS1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c
open ConstrData
variable (D : ConstrData)
alias goal_axiom := ReconfRes.Frozen.Dev.Q427c.PartS1.goal_axiom

end ReconfRes.Frozen.Dev.Q427c
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS1
open ConstrData
variable (D : ConstrData)
/-- Descendants of the goal node are totally ordered by ancestry. -/
theorem goal_total (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R)
    {i j : Fin R.n} (hi : R.Anc (goalNode D R) i) (hj : R.Anc (goalNode D R) j) :
    R.Anc i j ∨ R.Anc j i :=
  chain hR.1 (tight_readOnce D hD hR) hi hj

end ReconfRes.Frozen.Dev.Q427c.PartS1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c
open ConstrData
variable (D : ConstrData)
alias goal_total := ReconfRes.Frozen.Dev.Q427c.PartS1.goal_total

end ReconfRes.Frozen.Dev.Q427c
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS1
open ConstrData
variable (D : ConstrData)
theorem anc_antisymm (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R)
    {i j : Fin R.n} (h1 : R.Anc i j) (h2 : R.Anc j i) : i = j :=
  antisymm hR.1 h1 h2

end ReconfRes.Frozen.Dev.Q427c.PartS1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c
open ConstrData
variable (D : ConstrData)
alias anc_antisymm := ReconfRes.Frozen.Dev.Q427c.PartS1.anc_antisymm

end ReconfRes.Frozen.Dev.Q427c
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS1
open ConstrData
variable (D : ConstrData)
/-- Every head and `A` is pivoted, on the goal path. -/
theorem nu_spec (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) (x : CVar D.TV)
    (hx : x = CVar.A ∨ ∃ h ∈ D.heads, x = CVar.hd h) :
    R.HasPivot (nu R x) x ∧ R.Anc (goalNode D R) (nu R x) := by
  have hro := tight_readOnce D hD hR
  have hu : UniqSrc R x := by
    rcases hx with rfl | ⟨h, -, rfl⟩
    · exact uniqSrc_A hR hro
    · exact uniqSrc_hd hR hro h
  have hg : (x, false) ∈ R.label (goalNode D R) := by
    rw [(goal_axiom D hD hR).2]
    rcases hx with rfl | ⟨h, hh, rfl⟩
    · simp [ConstrData.Gc]
    · simp [ConstrData.Gc]; exact hh
  obtain ⟨k', k, hgk', hk, -, h1, h2⟩ :=
    exists_drop (hro.1 _) hg (by rw [hR.1.2.2.2.2]; simp)
  obtain ⟨q₁, q₂, x', hne, hpar, hx', hc⟩ := drop hR.1 hro hk h1 h2
  rcases hc with ⟨-, hc⟩ | ⟨rfl, hc⟩
  · simp at hc
  · simp only [Prod.mk.injEq, and_true] at hc
    subst hc
    have hpk : R.HasPivot k x := ⟨q₁, k', hne, hpar, hx'⟩
    have hex : ∃ i, R.HasPivot i x := ⟨k, hpk⟩
    have hnu : R.HasPivot (nu R x) x := by
      unfold nu; rw [dif_pos hex]; exact Classical.choose_spec hex
    refine ⟨hnu, ?_⟩
    rw [pivot_unique hR.1 hro hu hnu hpk]
    exact Relation.ReflTransGen.tail hgk' hk

end ReconfRes.Frozen.Dev.Q427c.PartS1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c
open ConstrData
variable (D : ConstrData)
alias nu_spec := ReconfRes.Frozen.Dev.Q427c.PartS1.nu_spec

end ReconfRes.Frozen.Dev.Q427c
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS2
open ReconfRes.Frozen
variable {V : Type} [DecidableEq V]
theorem mem_parents (R : ProofDag V) (i j : Fin R.n) : j ∈ R.parents i ↔ (j, i) ∈ R.edges := by
  simp [ProofDag.parents]

theorem mem_consumers (R : ProofDag V) (i j : Fin R.n) :
    j ∈ R.consumers i ↔ (i, j) ∈ R.edges := by
  simp [ProofDag.consumers]

theorem anc_trans {R : ProofDag V} {a b c : Fin R.n} (h1 : R.Anc a b) (h2 : R.Anc b c) :
    R.Anc a c := Relation.ReflTransGen.trans h1 h2

theorem anc_of_edge {R : ProofDag V} {a b : Fin R.n} (h : (a, b) ∈ R.edges) : R.Anc a b :=
  Relation.ReflTransGen.single h

theorem anc_refl (R : ProofDag V) (a : Fin R.n) : R.Anc a a := Relation.ReflTransGen.refl

theorem anc_last {R : ProofDag V} {a b : Fin R.n} (h : R.Anc a b) (hne : a ≠ b) :
    ∃ q, (q, b) ∈ R.edges ∧ R.Anc a q := by
  rcases Relation.ReflTransGen.cases_tail h with h' | ⟨q, hq, he⟩
  · exact absurd h'.symm hne
  · exact ⟨q, he, hq⟩

theorem anc_first {R : ProofDag V} {a b : Fin R.n} (h : R.Anc a b) (hne : a ≠ b) :
    ∃ w, (a, w) ∈ R.edges ∧ R.Anc w b := by
  rcases Relation.ReflTransGen.cases_head h with h' | ⟨w, hw, he⟩
  · exact absurd h' hne
  · exact ⟨w, hw, he⟩

end ReconfRes.Frozen.Dev.Q427c.PartS2
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS2
open ReconfRes.Frozen
variable {V : Type} [DecidableEq V]
variable {F : CNF V}
theorem anc_antisymm' {R : ProofDag V} (hR : R.IsRefutationOf F) {a b : Fin R.n}
    (h1 : R.Anc a b) (h2 : R.Anc b a) : a = b := by
  by_contra hne
  obtain ⟨w, hw, hwb⟩ := anc_first h1 hne
  exact hR.1 a w hw (anc_trans hwb h2)

theorem consumer_unique {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {a w1 w2 : Fin R.n} (h1 : (a, w1) ∈ R.edges) (h2 : (a, w2) ∈ R.edges) : w1 = w2 := by
  have hs : a ≠ R.sink := by
    rintro rfl
    have := hR.2.2.2.1
    have : w1 ∈ R.consumers R.sink := (mem_consumers R _ _).2 h1
    simp_all
  obtain ⟨c, hc⟩ := Finset.card_eq_one.1 (hro.2.2 a hs)
  have e1 : w1 ∈ R.consumers a := (mem_consumers R _ _).2 h1
  have e2 : w2 ∈ R.consumers a := (mem_consumers R _ _).2 h2
  rw [hc, Finset.mem_singleton] at e1 e2
  rw [e1, e2]

theorem desc_total {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {c i j : Fin R.n} (hi : R.Anc c i) (hj : R.Anc c j) : R.Anc i j ∨ R.Anc j i := by
  induction hi using Relation.ReflTransGen.head_induction_on generalizing j with
  | refl => exact Or.inl hj
  | head hcw hwi ih =>
    rename_i c w
    by_cases hcj : c = j
    · subst hcj
      exact Or.inr (Relation.ReflTransGen.head hcw hwi)
    · obtain ⟨w', hw', hw'j⟩ := anc_first hj hcj
      have := consumer_unique hR hro hcw hw'
      subst this
      exact ih hw'j

theorem parents_incomp {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {p q k : Fin R.n} (hp : (p, k) ∈ R.edges) (hq : (q, k) ∈ R.edges) (h : R.Anc p q) :
    p = q := by
  by_contra hne
  obtain ⟨w, hw, hwq⟩ := anc_first h hne
  have := consumer_unique hR hro hw hp
  subst this
  exact hR.1 q w hq hwq

theorem parents_eq {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {c p q k : Fin R.n} (hcp : R.Anc c p) (hcq : R.Anc c q)
    (hp : (p, k) ∈ R.edges) (hq : (q, k) ∈ R.edges) : p = q := by
  rcases desc_total hR hro hcp hcq with h | h
  · exact parents_incomp hR hro hp hq h
  · exact (parents_incomp hR hro hq hp h).symm

open Classical in
/-- Number of ancestors, a well-founded measure. -/
def mu (R : ProofDag V) (i : Fin R.n) : ℕ := (Finset.univ.filter fun j => R.Anc j i).card

open Classical in
theorem mu_lt {R : ProofDag V} (hR : R.IsRefutationOf F) {p i : Fin R.n}
    (h : (p, i) ∈ R.edges) : mu R p < mu R i := by
  unfold mu
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i, by simp [anc_refl], ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hip
    exact hR.1 p i h hip
  · intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hj
    exact Relation.ReflTransGen.tail hj h

theorem node_cases {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    (i : Fin R.n) :
    (R.parents i = ∅ ∧ R.label i ∈ F) ∨
    ∃ p₁ p₂ x, p₁ ≠ p₂ ∧ R.parents i = {p₁, p₂} ∧
      ResolventOn x (R.label p₁) (R.label p₂) (R.label i) := by
  rcases hR.2.2.1 i with h | ⟨p₁, p₂, hne, hp, x, hx⟩ | ⟨p, hp, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨p₁, p₂, x, hne, hp, hx⟩
  · exact absurd (by simp [ProofDag.IsWeakeningNode, hp]) (hro.2.1 i)

theorem edge1 {R : ProofDag V} {i p₁ p₂ : Fin R.n} (h : R.parents i = {p₁, p₂}) :
    (p₁, i) ∈ R.edges := (mem_parents R _ _).1 (by rw [h]; simp)

theorem edge2 {R : ProofDag V} {i p₁ p₂ : Fin R.n} (h : R.parents i = {p₁, p₂}) :
    (p₂, i) ∈ R.edges := (mem_parents R _ _).1 (by rw [h]; simp)

theorem pivot_nonaxiom {R : ProofDag V} {i : Fin R.n} {y : V} (h : R.HasPivot i y) :
    R.parents i ≠ ∅ := by
  obtain ⟨p₁, p₂, -, hp, -⟩ := h
  rw [hp]; simp

/-- Single source: `c` is the only axiom node containing the positive literal `y`. -/
def SS (R : ProofDag V) (y : V) (c : Fin R.n) : Prop :=
  ∀ a, R.parents a = ∅ → (y, true) ∈ R.label a → a = c

theorem ss_main {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {y : V} {c : Fin R.n} (hc : SS R y c) :
    ∀ N, ∀ j, mu R j = N → (y, true) ∈ R.label j →
      R.Anc c j ∧ ∀ i, R.Anc c i → R.Anc i j → ¬ R.HasPivot i y := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro j hN hy
  subst hN
  have IH : ∀ p, (p, j) ∈ R.edges → (y, true) ∈ R.label p →
      R.Anc c p ∧ ∀ i, R.Anc c i → R.Anc i p → ¬ R.HasPivot i y :=
    fun p hp hyp => ih _ (mu_lt hR hp) p rfl hyp
  rcases node_cases hR hro j with ⟨hax, -⟩ | ⟨p₁, p₂, x, hne, hp, hres⟩
  · have := hc j hax hy
    subst this
    refine ⟨anc_refl R _, fun i h1 h2 hpiv => ?_⟩
    have := anc_antisymm' hR h1 h2
    subst this
    exact pivot_nonaxiom hpiv hax
  · obtain ⟨-, -, hlab⟩ := hres
    have hy' : ∃ p, (p, j) ∈ R.edges ∧ (y, true) ∈ R.label p := by
      rw [hlab, Finset.mem_union] at hy
      rcases hy with h | h
      · exact ⟨p₁, edge1 hp, Finset.mem_of_mem_erase h⟩
      · exact ⟨p₂, edge2 hp, Finset.mem_of_mem_erase h⟩
    obtain ⟨p, hpj, hyp⟩ := hy'
    obtain ⟨hcp, hno⟩ := IH p hpj hyp
    refine ⟨Relation.ReflTransGen.tail hcp hpj, fun i hci hij => ?_⟩
    by_cases hieq : i = j
    · subst hieq
      rintro ⟨q₁, q₂, hqne, hq, hq1, hq2, hql⟩
      have hyq2 : (y, true) ∈ R.label q₂ := by
        rw [hql, Finset.mem_union] at hy
        rcases hy with h | h
        · simp at h
        · exact Finset.mem_of_mem_erase h
      have e1 := edge1 hq
      have e2 := edge2 hq
      exact hqne (parents_eq hR hro (IH q₁ e1 hq1).1 (IH q₂ e2 hyq2).1 e1 e2)
    · obtain ⟨q, hqj, hiq⟩ := anc_last hij hieq
      have : q = p := parents_eq hR hro (anc_trans hci hiq) hcp hqj hpj
      subst this
      exact hno i hci hiq

theorem ss_anc {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {y : V} {c : Fin R.n} (hc : SS R y c) {j : Fin R.n} (hy : (y, true) ∈ R.label j) :
    R.Anc c j := (ss_main hR hro hc _ j rfl hy).1

theorem ss_pivot_unique {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {y : V} {c : Fin R.n} (hc : SS R y c) {k₁ k₂ : Fin R.n}
    (h1 : R.HasPivot k₁ y) (h2 : R.HasPivot k₂ y) : k₁ = k₂ := by
  have key : ∀ a b, R.HasPivot a y → R.HasPivot b y → R.Anc a b → a = b := by
    intro a b ha hb hab
    by_contra hne
    obtain ⟨q, hqb, haq⟩ := anc_last hab hne
    obtain ⟨P₁, P₂, -, hP, hP1, -, -⟩ := hb
    obtain ⟨A₁, A₂, -, hA, hA1, -, -⟩ := id ha
    have hca : R.Anc c a := anc_trans (ss_anc hR hro hc hA1) (anc_of_edge (edge1 hA))
    have hcP := ss_anc hR hro hc hP1
    have : q = P₁ := parents_eq hR hro (anc_trans hca haq) hcP hqb (edge1 hP)
    subst this
    exact (ss_main hR hro hc _ q rfl hP1).2 a hca haq ha
  obtain ⟨A₁, A₂, -, hA, hA1, -, -⟩ := id h1
  obtain ⟨B₁, B₂, -, hB, hB1, -, -⟩ := id h2
  have ca := anc_trans (ss_anc hR hro hc hA1) (anc_of_edge (edge1 hA))
  have cb := anc_trans (ss_anc hR hro hc hB1) (anc_of_edge (edge1 hB))
  rcases desc_total hR hro ca cb with h | h
  · exact key _ _ h1 h2 h
  · exact (key _ _ h2 h1 h).symm

theorem removal {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {y : V} {a j : Fin R.n} (ha : (y, false) ∈ R.label a) (haj : R.Anc a j)
    (hj : (y, false) ∉ R.label j) :
    ∃ k q₁ q₂, q₁ ≠ q₂ ∧ R.parents k = {q₁, q₂} ∧
      ResolventOn y (R.label q₁) (R.label q₂) (R.label k) ∧ R.Anc a q₂ := by
  induction haj with
  | refl => exact absurd ha hj
  | tail hab hbc ih =>
    rename_i b c
    by_cases hb : (y, false) ∈ R.label b
    · rcases node_cases hR hro c with ⟨hax, -⟩ | ⟨p₁, p₂, x, hne, hp, hres⟩
      · have : b ∈ R.parents c := (mem_parents R _ _).2 hbc
        rw [hax] at this; simp at this
      · have hbm : b ∈ R.parents c := (mem_parents R _ _).2 hbc
        rw [hp, Finset.mem_insert, Finset.mem_singleton] at hbm
        obtain ⟨h1, h2, hlab⟩ := hres
        rcases hbm with rfl | rfl
        · exfalso; apply hj
          rw [hlab]
          exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨by simp, hb⟩)
        · by_cases hxy : x = y
          · subst hxy
            exact ⟨c, p₁, b, hne, hp, ⟨h1, h2, hlab⟩, hab⟩
          · exfalso; apply hj
            rw [hlab]
            exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨by simp [Ne.symm hxy], hb⟩)
    · exact ih hb

end ReconfRes.Frozen.Dev.Q427c.PartS2
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS2
open ReconfRes.Frozen
open ConstrData
variable (D : ConstrData)
theorem axiom_label {F : CNF (CVar D.TV)} {R : ProofDag (CVar D.TV)} (hR : R.IsRefutationOf F)
    {a : Fin R.n} (ha : R.parents a = ∅) : R.label a ∈ F := by
  rcases hR.2.2.1 a with h | ⟨p₁, p₂, -, hp, -⟩ | ⟨p, hp, -⟩
  · exact h.2
  · have : p₁ ∈ R.parents a := by rw [hp]; simp
    rw [ha] at this; simp at this
  · have : p ∈ R.parents a := by rw [hp]; simp
    rw [ha] at this; simp at this

theorem src_unique {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) {s0 : Src D.TV}
    (hs0 : s0 ∈ D.srcs) {l : Literal (CVar D.TV)} (hl : l ∈ D.inv s0)
    (huniq : ∀ s ∈ D.srcs, l ∈ D.inv s → s = s0) :
    ∃ c, R.parents c = ∅ ∧ R.label c = D.inv s0 ∧
      ∀ a, R.parents a = ∅ → l ∈ R.label a → a = c := by
  have hf : D.srcs.filter (fun s => D.inv s0 = D.inv s) = {s0} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hs, he⟩
      exact huniq s hs (he ▸ hl)
    · rintro rfl
      exact ⟨hs0, rfl⟩
  have h1 : Multiset.count (D.inv s0) D.inventory = 1 := by
    unfold ConstrData.inventory
    rw [Multiset.count_map, ← Finset.filter_val, hf]
    rfl
  have h2 : Multiset.count (D.inv s0) R.axiomMultiset = 1 := hR.2.2.1 ▸ h1
  unfold ProofDag.axiomMultiset at h2
  rw [Multiset.count_map, ← Finset.filter_val] at h2
  obtain ⟨c, hc⟩ := Finset.card_eq_one.1 h2
  have hcm : c ∈ ((Finset.univ.filter fun i => R.parents i = ∅).filter
      fun i => D.inv s0 = R.label i) := by rw [hc]; simp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcm
  refine ⟨c, hcm.1, hcm.2.symm, fun a ha hla => ?_⟩
  have hF := axiom_label D hR.1 ha
  unfold ConstrData.formula at hF
  obtain ⟨s, hs, hse⟩ := Finset.mem_image.1 hF
  have := huniq s hs (hse ▸ hla)
  subst this
  have ham : a ∈ ((Finset.univ.filter fun i => R.parents i = ∅).filter
      fun i => D.inv s = R.label i) := by simp [ha, hse]
  rw [hc] at ham
  simpa using ham

theorem hd_src {h : Head D.TV} : ∀ s ∈ D.srcs, (CVar.hd h, true) ∈ D.inv s → s = Src.C h := by
  intro s _ hs
  cases s <;> simp [ConstrData.inv, ConstrData.Ch, ConstrData.CA, ConstrData.Gc] at hs ⊢
  exact hs.symm

theorem A_src : ∀ s ∈ D.srcs, (CVar.A, true) ∈ D.inv s → s = Src.CA := by
  intro s _ hs
  cases s <;> simp [ConstrData.inv, ConstrData.Ch, ConstrData.CA, ConstrData.Gc] at hs ⊢

theorem hd_source {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) {h : Head D.TV}
    (hh : h ∈ D.heads) :
    ∃ c, R.parents c = ∅ ∧ R.label c = D.Ch h ∧ SS R (CVar.hd h) c := by
  obtain ⟨c, h1, h2, h3⟩ := src_unique D hR (s0 := Src.C h) (by simp [ConstrData.srcs, hh])
    (l := (CVar.hd h, true)) (by simp [ConstrData.inv, ConstrData.Ch]) (hd_src D)
  exact ⟨c, h1, h2, h3⟩

theorem ss_of {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) {y : CVar D.TV}
    (hy : y = CVar.A ∨ ∃ d ∈ D.heads, y = CVar.hd d) : ∃ c, SS R y c := by
  rcases hy with rfl | ⟨d, hd, rfl⟩
  · obtain ⟨c, -, -, h3⟩ := src_unique D hR (s0 := Src.CA) (by simp [ConstrData.srcs])
      (l := (CVar.A, true)) (by simp [ConstrData.inv, ConstrData.CA]) (A_src D)
    exact ⟨c, h3⟩
  · obtain ⟨c, -, -, h3⟩ := hd_source D hR hd
    exact ⟨c, h3⟩

theorem core (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) {h : Head D.TV}
    (hh : h ∈ D.heads) {y : CVar D.TV} (hy : y = CVar.A ∨ ∃ d ∈ D.heads, y = CVar.hd d)
    (hne : CVar.hd h ≠ y) (hyC : (y, false) ∈ D.Ch h) :
    R.Anc (nu R (CVar.hd h)) (nu R y) ∧ nu R (CVar.hd h) ≠ nu R y := by
  have hro := Q427c.tight_readOnce D hD hR
  have hRef := hR.1
  obtain ⟨c, hcax, hcl, hcs⟩ := hd_source D hR hh
  obtain ⟨cy, hcys⟩ := ss_of D hR hy
  obtain ⟨hN, hgN⟩ := Q427c.nu_spec D hD hR (CVar.hd h) (Or.inr ⟨h, hh, rfl⟩)
  obtain ⟨hM, hgM⟩ := Q427c.nu_spec D hD hR y hy
  set N := nu R (CVar.hd h)
  set M := nu R y
  set g := goalNode D R
  have hsink : ∀ z, (z, false) ∉ R.label R.sink := by
    intro z; rw [hRef.2.2.2.2]; simp
  -- `c ⇝ M`
  obtain ⟨k, q₁, q₂, hqne, hq, hres, hcq₂⟩ :=
    removal hRef hro (hcl ▸ hyC) (hR.2.1 c) (hsink y)
  have hkM : k = M := ss_pivot_unique hRef hro hcys ⟨q₁, q₂, hqne, hq, hres⟩ hM
  have hcM : R.Anc c M := hkM ▸ anc_trans hcq₂ (anc_of_edge (edge2 hq))
  -- `c ⇝ N`
  have hcN : R.Anc c N := by
    obtain ⟨p₁, p₂, -, hp, hp1, -, -⟩ := id hN
    exact anc_trans (ss_anc hRef hro hcs hp1) (anc_of_edge (edge1 hp))
  have hNM : N ≠ M := by
    intro e
    exact hne (Q427c.unique_pivot D hD hR N _ _ hN (e ▸ hM))
  refine ⟨?_, hNM⟩
  rcases desc_total hRef hro hcN hcM with h1 | h1
  · exact h1
  exfalso
  obtain ⟨r, hrN, hMr⟩ := anc_last h1 (Ne.symm hNM)
  have hgl := (Q427c.goal_axiom D hD hR).2
  have hgx : (CVar.hd h, false) ∈ R.label g := by
    rw [hgl]; simp [ConstrData.Gc, hh]
  obtain ⟨k', u₁, u₂, hune, hu, hres', hgu₂⟩ :=
    removal hRef hro hgx (hR.2.1 g) (hsink _)
  have hkN : k' = N := ss_pivot_unique hRef hro hcs ⟨u₁, u₂, hune, hu, hres'⟩ hN
  subst hkN
  have hcu₁ := ss_anc hRef hro hcs hres'.1
  have hru : r = u₁ := parents_eq hRef hro (anc_trans hcM hMr) hcu₁ hrN (edge1 hu)
  subst hru
  exact hune (parents_eq hRef hro (anc_trans hgM hMr) hgu₂ hrN (edge2 hu))

/-- `x`'s event strictly precedes `y`'s. -/
def Bef (R : ProofDag (CVar D.TV)) (x y : CVar D.TV) : Prop :=
  R.Anc (nu R x) (nu R y) ∧ nu R x ≠ nu R y

theorem bef_trans (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R)
    {x y z : CVar D.TV} (h1 : Bef D R x y) (h2 : Bef D R y z) : Bef D R x z := by
  refine ⟨anc_trans h1.1 h2.1, fun e => h1.2 ?_⟩
  have h3 := h2.1
  rw [← e] at h3
  exact Q427c.anc_antisymm D hD hR h1.1 h3

theorem step (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R)
    {h d : Head D.TV} (hh : h ∈ D.heads) (hd : d ∈ D.heads) (hne : h ≠ d)
    (hdep : d ∈ D.deps h) : Bef D R (CVar.hd h) (CVar.hd d) := by
  refine core D hD hR hh (Or.inr ⟨d, hd, rfl⟩) (by simpa using hne) ?_
  unfold ConstrData.Ch
  exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hdep))

end ReconfRes.Frozen.Dev.Q427c.PartS2
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS2
open ReconfRes.Frozen
variable {τ : Type}
theorem sub_append (t : FBTree τ) (p : List Bool) (b : Bool) (s : FBTree τ)
    (h : t.subtreeAt (p ++ [b]) = some s) : ∃ l r, t.subtreeAt p = some (FBTree.node l r) := by
  induction t generalizing p with
  | leaf v =>
    cases p <;> simp [FBTree.subtreeAt] at h
  | node l r ihl ihr =>
    cases p with
    | nil => exact ⟨l, r, rfl⟩
    | cons c p =>
      cases c
      · exact ihl p (by simpa [FBTree.subtreeAt] using h)
      · exact ihr p (by simpa [FBTree.subtreeAt] using h)

theorem sub_internal (t : FBTree τ) (p : List Bool) (l r : FBTree τ)
    (h : t.subtreeAt p = some (FBTree.node l r)) : p ∈ t.internalPaths := by
  induction t generalizing p with
  | leaf v =>
    cases p <;> simp [FBTree.subtreeAt] at h
  | node l' r' ihl ihr =>
    cases p with
    | nil => simp [FBTree.internalPaths]
    | cons c p =>
      cases c
      · simp only [FBTree.internalPaths, List.mem_cons, List.mem_append, List.mem_map]
        exact Or.inr (Or.inl ⟨p, ihl p (by simpa [FBTree.subtreeAt] using h), rfl⟩)
      · simp only [FBTree.internalPaths, List.mem_cons, List.mem_append, List.mem_map]
        exact Or.inr (Or.inr ⟨p, ihr p (by simpa [FBTree.subtreeAt] using h), rfl⟩)

theorem internal_sub (t : FBTree τ) (p : List Bool) (h : p ∈ t.internalPaths) :
    ∃ l r, t.subtreeAt p = some (FBTree.node l r) := by
  induction t generalizing p with
  | leaf v => simp [FBTree.internalPaths] at h
  | node l r ihl ihr =>
    simp only [FBTree.internalPaths, List.mem_cons, List.mem_append, List.mem_map] at h
    rcases h with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨l, r, rfl⟩
    · simpa [FBTree.subtreeAt] using ihl q hq
    · simpa [FBTree.subtreeAt] using ihr q hq

theorem leaf_path (t : FBTree τ) (v : τ) (h : v ∈ t.leaves) :
    ∃ p, t.subtreeAt p = some (FBTree.leaf v) := by
  induction t with
  | leaf w =>
    simp [FBTree.leaves] at h
    subst h
    exact ⟨[], rfl⟩
  | node l r ihl ihr =>
    simp only [FBTree.leaves, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨p, hp⟩ := ihl h
      exact ⟨false :: p, by simpa [FBTree.subtreeAt] using hp⟩
    · obtain ⟨p, hp⟩ := ihr h
      exact ⟨true :: p, by simpa [FBTree.subtreeAt] using hp⟩

end ReconfRes.Frozen.Dev.Q427c.PartS2
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS2
open ReconfRes.Frozen
open ConstrData
variable (D : ConstrData)
theorem head1_of {q : List Bool} (hq : q ≠ []) {s : FBTree D.TV} (hs : D.t1.subtreeAt q = some s) :
    (D.head1 q = Head.i1 q ∧ Head.i1 q ∈ D.heads) ∨ ∃ v, D.head1 q = Head.a v := by
  cases s with
  | leaf v => exact Or.inr ⟨v, by simp [ConstrData.head1, hs]⟩
  | node l r =>
    refine Or.inl ⟨by simp [ConstrData.head1, hs, hq], ?_⟩
    simp [ConstrData.heads, ConstrData.inner1, sub_internal _ _ _ _ hs, hq]

theorem head2_of {q : List Bool} (hq : q ≠ []) {s : FBTree D.TV} (hs : D.t2.subtreeAt q = some s) :
    (D.head2 q = Head.i2 q ∧ Head.i2 q ∈ D.heads) ∨ ∃ v, D.head2 q = Head.b v := by
  cases s with
  | leaf v => exact Or.inr ⟨v, by simp [ConstrData.head2, hs]⟩
  | node l r =>
    refine Or.inl ⟨by simp [ConstrData.head2, hs, hq], ?_⟩
    simp [ConstrData.heads, ConstrData.inner2, sub_internal _ _ _ _ hs, hq]

theorem a_mem (v : D.TV) : Head.a v ∈ D.heads := by simp [ConstrData.heads]

theorem b_mem (v : D.TV) : Head.b v ∈ D.heads := by simp [ConstrData.heads]

theorem T_mem : Head.T ∈ D.heads := by simp [ConstrData.heads]

theorem U_mem : Head.U ∈ D.heads := by simp [ConstrData.heads]

theorem ne_len {q : List Bool} {b : Bool} : q ≠ q ++ [b] := by
  intro h
  have := congrArg List.length h
  simp at this

theorem reach1 (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) :
    ∀ p : List Bool, p ≠ [] → ∀ s, D.t1.subtreeAt p = some s →
      Bef D R (CVar.hd Head.T) (CVar.hd (D.head1 p)) := by
  intro p
  induction p using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton q b ih =>
    intro _ s hs
    obtain ⟨l, r, hq'⟩ := sub_append _ q b s hs
    have hdm : D.head1 (q ++ [b]) ∈ D.heads ∧ D.head1 (q ++ [b]) ≠ Head.T ∧
        D.head1 (q ++ [b]) ≠ Head.i1 q := by
      rcases head1_of D (by simp) hs with ⟨e, hm⟩ | ⟨v, e⟩
      · rw [e]; exact ⟨hm, by simp, by simp [(ne_len (q := q) (b := b)).symm]⟩
      · rw [e]; exact ⟨a_mem D v, by simp, by simp⟩
    by_cases hq : q = []
    · subst hq
      refine step D hD hR (T_mem D) hdm.1 (Ne.symm hdm.2.1) ?_
      cases b <;> simp [ConstrData.deps]
    · have h1 := ih hq _ hq'
      rcases head1_of D hq hq' with ⟨e, hm⟩ | ⟨v, e⟩
      · rw [e] at h1
        refine bef_trans D hD hR h1 (step D hD hR hm hdm.1 (Ne.symm hdm.2.2) ?_)
        cases b <;> simp [ConstrData.deps]
      · simp [ConstrData.head1, hq', hq] at e

theorem reach2 (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) :
    ∀ p : List Bool, p ≠ [] → ∀ s, D.t2.subtreeAt p = some s →
      Bef D R (CVar.hd Head.U) (CVar.hd (D.head2 p)) := by
  intro p
  induction p using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton q b ih =>
    intro _ s hs
    obtain ⟨l, r, hq'⟩ := sub_append _ q b s hs
    have hdm : D.head2 (q ++ [b]) ∈ D.heads ∧ D.head2 (q ++ [b]) ≠ Head.U ∧
        D.head2 (q ++ [b]) ≠ Head.i2 q := by
      rcases head2_of D (by simp) hs with ⟨e, hm⟩ | ⟨v, e⟩
      · rw [e]; exact ⟨hm, by simp, by simp [(ne_len (q := q) (b := b)).symm]⟩
      · rw [e]; exact ⟨b_mem D v, by simp, by simp⟩
    by_cases hq : q = []
    · subst hq
      refine step D hD hR (U_mem D) hdm.1 (Ne.symm hdm.2.1) ?_
      cases b <;> simp [ConstrData.deps]
    · have h1 := ih hq _ hq'
      rcases head2_of D hq hq' with ⟨e, hm⟩ | ⟨v, e⟩
      · rw [e] at h1
        refine bef_trans D hD hR h1 (step D hD hR hm hdm.1 (Ne.symm hdm.2.2) ?_)
        cases b <;> simp [ConstrData.deps]
      · simp [ConstrData.head2, hq', hq] at e

theorem not_leaf (hD : D.Valid) (t : FBTree D.TV) (ht : ∀ v, v ∈ t.leaves) (v : D.TV) :
    t ≠ FBTree.leaf v := by
  intro hv
  have hn := hD.1
  have h1 := ht (⟨0, by omega⟩, ⟨0, by omega⟩)
  have h2 := ht (⟨1, by omega⟩, ⟨0, by omega⟩)
  rw [hv] at h1 h2
  simp only [FBTree.leaves, List.mem_singleton] at h1 h2
  rw [← h2] at h1
  simp [Prod.ext_iff] at h1

theorem TU (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) :
    Bef D R (CVar.hd Head.T) (CVar.hd Head.U) :=
  step D hD hR (T_mem D) (U_mem D) (by simp) (by simp [ConstrData.deps])

/-- `U` precedes every `b_v`. -/
theorem U_before_b (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) (v : D.TV) :
    R.Anc (nu R (CVar.hd Head.U)) (nu R (CVar.hd (Head.b v))) ∧
      nu R (CVar.hd Head.U) ≠ nu R (CVar.hd (Head.b v)) := by
  obtain ⟨p, hp⟩ := leaf_path _ v (hD.2.2.2.2.2.2 v)
  have hpne : p ≠ [] := by
    rintro rfl
    exact not_leaf D hD _ hD.2.2.2.2.2.2 v (by simpa [FBTree.subtreeAt] using hp)
  have h := reach2 D hD hR p hpne _ hp
  have e : D.head2 p = Head.b v := by simp [ConstrData.head2, hp]
  rw [e] at h
  exact h

/-- `T` is the first head event. -/
theorem T_before (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R)
    (h : Head D.TV) (hh : h ∈ D.heads) (hT : h ≠ Head.T) :
    R.Anc (nu R (CVar.hd Head.T)) (nu R (CVar.hd h)) ∧
      nu R (CVar.hd Head.T) ≠ nu R (CVar.hd h) := by
  cases h with
  | T => exact absurd rfl hT
  | U => exact TU D hD hR
  | a v =>
    obtain ⟨p, hp⟩ := leaf_path _ v (hD.2.2.2.2.1.2 v)
    have hpne : p ≠ [] := by
      rintro rfl
      exact not_leaf D hD _ hD.2.2.2.2.1.2 v (by simpa [FBTree.subtreeAt] using hp)
    have h := reach1 D hD hR p hpne _ hp
    have e : D.head1 p = Head.a v := by simp [ConstrData.head1, hp]
    rw [e] at h
    exact h
  | b v => exact bef_trans D hD hR (TU D hD hR) (U_before_b D hD hR v)
  | i1 p =>
    have hp : p ∈ D.t1.internalPaths ∧ p ≠ [] := by
      simpa [ConstrData.heads, ConstrData.inner1, ConstrData.inner2] using hh
    obtain ⟨l, r, hs⟩ := internal_sub _ p hp.1
    have h := reach1 D hD hR p hp.2 _ hs
    have e : D.head1 p = Head.i1 p := by simp [ConstrData.head1, hs, hp.2]
    rw [e] at h
    exact h
  | i2 p =>
    have hp : p ∈ D.t2.internalPaths ∧ p ≠ [] := by
      simpa [ConstrData.heads, ConstrData.inner1, ConstrData.inner2] using hh
    obtain ⟨l, r, hs⟩ := internal_sub _ p hp.1
    have h := reach2 D hD hR p hp.2 _ hs
    have e : D.head2 p = Head.i2 p := by simp [ConstrData.head2, hs, hp.2]
    rw [e] at h
    exact bef_trans D hD hR (TU D hD hR) h

end ReconfRes.Frozen.Dev.Q427c.PartS2
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c
open ConstrData
variable (D : ConstrData)
alias T_before := ReconfRes.Frozen.Dev.Q427c.PartS2.T_before

alias U_before_b := ReconfRes.Frozen.Dev.Q427c.PartS2.U_before_b

end ReconfRes.Frozen.Dev.Q427c
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS2
open ReconfRes.Frozen
open ConstrData
variable (D : ConstrData)
/-- `a_v` precedes `b_u` for every edge `uv` of `J`. -/
theorem a_before_b (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) (v u : D.TV)
    (hvu : D.J.Adj v u) :
    R.Anc (nu R (CVar.hd (Head.a v))) (nu R (CVar.hd (Head.b u))) ∧
      nu R (CVar.hd (Head.a v)) ≠ nu R (CVar.hd (Head.b u)) :=
  step D hD hR (a_mem D v) (b_mem D u) (by simp) (by simp [ConstrData.deps, hvu])

end ReconfRes.Frozen.Dev.Q427c.PartS2
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c
open ConstrData
variable (D : ConstrData)
alias a_before_b := ReconfRes.Frozen.Dev.Q427c.PartS2.a_before_b

end ReconfRes.Frozen.Dev.Q427c
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS2
open ReconfRes.Frozen
open ConstrData
variable (D : ConstrData)
/-- Every head precedes `A`. -/
theorem before_A (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R)
    (h : Head D.TV) (hh : h ∈ D.heads) :
    R.Anc (nu R (CVar.hd h)) (nu R CVar.A) ∧ nu R (CVar.hd h) ≠ nu R CVar.A :=
  core D hD hR hh (Or.inl rfl) (by simp) (by simp [ConstrData.Ch])

end ReconfRes.Frozen.Dev.Q427c.PartS2
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c
open ConstrData
variable (D : ConstrData)
alias before_A := ReconfRes.Frozen.Dev.Q427c.PartS2.before_A

end ReconfRes.Frozen.Dev.Q427c
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartS1
open ConstrData
variable (D : ConstrData)
/-- The number of heads. -/
theorem heads_card (hD : D.Valid) : D.heads.card = 4 * D.m - 2 := by
  have := heads_card' D hD
  omega

end ReconfRes.Frozen.Dev.Q427c.PartS1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c
open ConstrData
variable (D : ConstrData)
alias heads_card := ReconfRes.Frozen.Dev.Q427c.PartS1.heads_card

end ReconfRes.Frozen.Dev.Q427c
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartT
open ReconfRes.Frozen
variable {V : Type} [DecidableEq V]
/-! ## Generic facts on read-once refutations (copied from Part S2) -/
theorem mem_parents (R : ProofDag V) (i j : Fin R.n) : j ∈ R.parents i ↔ (j, i) ∈ R.edges := by
  simp [ProofDag.parents]

theorem mem_consumers (R : ProofDag V) (i j : Fin R.n) :
    j ∈ R.consumers i ↔ (i, j) ∈ R.edges := by
  simp [ProofDag.consumers]

theorem anc_trans {R : ProofDag V} {a b c : Fin R.n} (h1 : R.Anc a b) (h2 : R.Anc b c) :
    R.Anc a c := Relation.ReflTransGen.trans h1 h2

theorem anc_of_edge {R : ProofDag V} {a b : Fin R.n} (h : (a, b) ∈ R.edges) : R.Anc a b :=
  Relation.ReflTransGen.single h

theorem anc_refl (R : ProofDag V) (a : Fin R.n) : R.Anc a a := Relation.ReflTransGen.refl

theorem anc_last {R : ProofDag V} {a b : Fin R.n} (h : R.Anc a b) (hne : a ≠ b) :
    ∃ q, (q, b) ∈ R.edges ∧ R.Anc a q := by
  rcases Relation.ReflTransGen.cases_tail h with h' | ⟨q, hq, he⟩
  · exact absurd h'.symm hne
  · exact ⟨q, he, hq⟩

theorem anc_first {R : ProofDag V} {a b : Fin R.n} (h : R.Anc a b) (hne : a ≠ b) :
    ∃ w, (a, w) ∈ R.edges ∧ R.Anc w b := by
  rcases Relation.ReflTransGen.cases_head h with h' | ⟨w, hw, he⟩
  · exact absurd h' hne
  · exact ⟨w, hw, he⟩

end ReconfRes.Frozen.Dev.Q427c.PartT
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartT
open ReconfRes.Frozen
variable {V : Type} [DecidableEq V]
variable {F : CNF V}
theorem anc_antisymm' {R : ProofDag V} (hR : R.IsRefutationOf F) {a b : Fin R.n}
    (h1 : R.Anc a b) (h2 : R.Anc b a) : a = b := by
  by_contra hne
  obtain ⟨w, hw, hwb⟩ := anc_first h1 hne
  exact hR.1 a w hw (anc_trans hwb h2)

theorem consumer_unique {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {a w1 w2 : Fin R.n} (h1 : (a, w1) ∈ R.edges) (h2 : (a, w2) ∈ R.edges) : w1 = w2 := by
  have hs : a ≠ R.sink := by
    rintro rfl
    have := hR.2.2.2.1
    have : w1 ∈ R.consumers R.sink := (mem_consumers R _ _).2 h1
    simp_all
  obtain ⟨c, hc⟩ := Finset.card_eq_one.1 (hro.2.2 a hs)
  have e1 : w1 ∈ R.consumers a := (mem_consumers R _ _).2 h1
  have e2 : w2 ∈ R.consumers a := (mem_consumers R _ _).2 h2
  rw [hc, Finset.mem_singleton] at e1 e2
  rw [e1, e2]

theorem desc_total {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {c i j : Fin R.n} (hi : R.Anc c i) (hj : R.Anc c j) : R.Anc i j ∨ R.Anc j i := by
  induction hi using Relation.ReflTransGen.head_induction_on generalizing j with
  | refl => exact Or.inl hj
  | head hcw hwi ih =>
    rename_i c w
    by_cases hcj : c = j
    · subst hcj
      exact Or.inr (Relation.ReflTransGen.head hcw hwi)
    · obtain ⟨w', hw', hw'j⟩ := anc_first hj hcj
      have := consumer_unique hR hro hcw hw'
      subst this
      exact ih hw'j

theorem parents_incomp {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {p q k : Fin R.n} (hp : (p, k) ∈ R.edges) (hq : (q, k) ∈ R.edges) (h : R.Anc p q) :
    p = q := by
  by_contra hne
  obtain ⟨w, hw, hwq⟩ := anc_first h hne
  have := consumer_unique hR hro hw hp
  subst this
  exact hR.1 q w hq hwq

theorem parents_eq {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {c p q k : Fin R.n} (hcp : R.Anc c p) (hcq : R.Anc c q)
    (hp : (p, k) ∈ R.edges) (hq : (q, k) ∈ R.edges) : p = q := by
  rcases desc_total hR hro hcp hcq with h | h
  · exact parents_incomp hR hro hp hq h
  · exact (parents_incomp hR hro hq hp h).symm

open Classical in
/-- Number of ancestors, a well-founded measure. -/
def mu (R : ProofDag V) (i : Fin R.n) : ℕ := (Finset.univ.filter fun j => R.Anc j i).card

open Classical in
theorem mu_lt {R : ProofDag V} (hR : R.IsRefutationOf F) {p i : Fin R.n}
    (h : (p, i) ∈ R.edges) : mu R p < mu R i := by
  unfold mu
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i, by simp [anc_refl], ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hip
    exact hR.1 p i h hip
  · intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hj
    exact Relation.ReflTransGen.tail hj h

theorem anc_ind {R : ProofDag V} (hR : R.IsRefutationOf F) (P : Fin R.n → Prop)
    (h : ∀ j, (∀ p, (p, j) ∈ R.edges → P p) → P j) : ∀ j, P j := by
  suffices ∀ N, ∀ j, mu R j ≤ N → P j from fun j => this _ j le_rfl
  intro N
  induction N with
  | zero =>
    intro j hj
    exact h j fun p hp => absurd (mu_lt hR hp) (by omega)
  | succ N ih =>
    intro j hj
    exact h j fun p hp => ih p (by have := mu_lt hR hp; omega)

theorem node_cases {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    (i : Fin R.n) :
    (R.parents i = ∅ ∧ R.label i ∈ F) ∨
    ∃ p₁ p₂ x, p₁ ≠ p₂ ∧ R.parents i = {p₁, p₂} ∧
      ResolventOn x (R.label p₁) (R.label p₂) (R.label i) := by
  rcases hR.2.2.1 i with h | ⟨p₁, p₂, hne, hp, x, hx⟩ | ⟨p, hp, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨p₁, p₂, x, hne, hp, hx⟩
  · exact absurd (by simp [ProofDag.IsWeakeningNode, hp]) (hro.2.1 i)

theorem edge1 {R : ProofDag V} {i p₁ p₂ : Fin R.n} (h : R.parents i = {p₁, p₂}) :
    (p₁, i) ∈ R.edges := (mem_parents R _ _).1 (by rw [h]; simp)

theorem edge2 {R : ProofDag V} {i p₁ p₂ : Fin R.n} (h : R.parents i = {p₁, p₂}) :
    (p₂, i) ∈ R.edges := (mem_parents R _ _).1 (by rw [h]; simp)

theorem pivot_nonaxiom {R : ProofDag V} {i : Fin R.n} {y : V} (h : R.HasPivot i y) :
    R.parents i ≠ ∅ := by
  obtain ⟨p₁, p₂, -, hp, -⟩ := h
  rw [hp]; simp

/-- Single source: `c` is the only axiom node containing the positive literal `y`. -/
def SS (R : ProofDag V) (y : V) (c : Fin R.n) : Prop :=
  ∀ a, R.parents a = ∅ → (y, true) ∈ R.label a → a = c

theorem ss_main {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {y : V} {c : Fin R.n} (hc : SS R y c) :
    ∀ N, ∀ j, mu R j = N → (y, true) ∈ R.label j →
      R.Anc c j ∧ ∀ i, R.Anc c i → R.Anc i j → ¬ R.HasPivot i y := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro j hN hy
  subst hN
  have IH : ∀ p, (p, j) ∈ R.edges → (y, true) ∈ R.label p →
      R.Anc c p ∧ ∀ i, R.Anc c i → R.Anc i p → ¬ R.HasPivot i y :=
    fun p hp hyp => ih _ (mu_lt hR hp) p rfl hyp
  rcases node_cases hR hro j with ⟨hax, -⟩ | ⟨p₁, p₂, x, hne, hp, hres⟩
  · have := hc j hax hy
    subst this
    refine ⟨anc_refl R _, fun i h1 h2 hpiv => ?_⟩
    have := anc_antisymm' hR h1 h2
    subst this
    exact pivot_nonaxiom hpiv hax
  · obtain ⟨-, -, hlab⟩ := hres
    have hy' : ∃ p, (p, j) ∈ R.edges ∧ (y, true) ∈ R.label p := by
      rw [hlab, Finset.mem_union] at hy
      rcases hy with h | h
      · exact ⟨p₁, edge1 hp, Finset.mem_of_mem_erase h⟩
      · exact ⟨p₂, edge2 hp, Finset.mem_of_mem_erase h⟩
    obtain ⟨p, hpj, hyp⟩ := hy'
    obtain ⟨hcp, hno⟩ := IH p hpj hyp
    refine ⟨Relation.ReflTransGen.tail hcp hpj, fun i hci hij => ?_⟩
    by_cases hieq : i = j
    · subst hieq
      rintro ⟨q₁, q₂, hqne, hq, hq1, hq2, hql⟩
      have hyq2 : (y, true) ∈ R.label q₂ := by
        rw [hql, Finset.mem_union] at hy
        rcases hy with h | h
        · simp at h
        · exact Finset.mem_of_mem_erase h
      have e1 := edge1 hq
      have e2 := edge2 hq
      exact hqne (parents_eq hR hro (IH q₁ e1 hq1).1 (IH q₂ e2 hyq2).1 e1 e2)
    · obtain ⟨q, hqj, hiq⟩ := anc_last hij hieq
      have : q = p := parents_eq hR hro (anc_trans hci hiq) hcp hqj hpj
      subst this
      exact hno i hci hiq

theorem ss_anc {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {y : V} {c : Fin R.n} (hc : SS R y c) {j : Fin R.n} (hy : (y, true) ∈ R.label j) :
    R.Anc c j := (ss_main hR hro hc _ j rfl hy).1

theorem ss_pivot_unique {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {y : V} {c : Fin R.n} (hc : SS R y c) {k₁ k₂ : Fin R.n}
    (h1 : R.HasPivot k₁ y) (h2 : R.HasPivot k₂ y) : k₁ = k₂ := by
  have key : ∀ a b, R.HasPivot a y → R.HasPivot b y → R.Anc a b → a = b := by
    intro a b ha hb hab
    by_contra hne
    obtain ⟨q, hqb, haq⟩ := anc_last hab hne
    obtain ⟨P₁, P₂, -, hP, hP1, -, -⟩ := hb
    obtain ⟨A₁, A₂, -, hA, hA1, -, -⟩ := id ha
    have hca : R.Anc c a := anc_trans (ss_anc hR hro hc hA1) (anc_of_edge (edge1 hA))
    have hcP := ss_anc hR hro hc hP1
    have : q = P₁ := parents_eq hR hro (anc_trans hca haq) hcP hqb (edge1 hP)
    subst this
    exact (ss_main hR hro hc _ q rfl hP1).2 a hca haq ha
  obtain ⟨A₁, A₂, -, hA, hA1, -, -⟩ := id h1
  obtain ⟨B₁, B₂, -, hB, hB1, -, -⟩ := id h2
  have ca := anc_trans (ss_anc hR hro hc hA1) (anc_of_edge (edge1 hA))
  have cb := anc_trans (ss_anc hR hro hc hB1) (anc_of_edge (edge1 hB))
  rcases desc_total hR hro ca cb with h | h
  · exact key _ _ h1 h2 h
  · exact (key _ _ h2 h1 h).symm

/-- A negative literal lost between `a` and `j` is removed at a pivot node between them. -/
theorem removal' {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {y : V} {a j : Fin R.n} (ha : (y, false) ∈ R.label a) (haj : R.Anc a j)
    (hj : (y, false) ∉ R.label j) :
    ∃ k q₁ q₂, q₁ ≠ q₂ ∧ R.parents k = {q₁, q₂} ∧
      ResolventOn y (R.label q₁) (R.label q₂) (R.label k) ∧ R.Anc a q₂ ∧ R.Anc k j := by
  induction haj with
  | refl => exact absurd ha hj
  | tail hab hbc ih =>
    rename_i b c
    by_cases hb : (y, false) ∈ R.label b
    · rcases node_cases hR hro c with ⟨hax, -⟩ | ⟨p₁, p₂, x, hne, hp, hres⟩
      · have : b ∈ R.parents c := (mem_parents R _ _).2 hbc
        rw [hax] at this; simp at this
      · have hbm : b ∈ R.parents c := (mem_parents R _ _).2 hbc
        rw [hp, Finset.mem_insert, Finset.mem_singleton] at hbm
        obtain ⟨h1, h2, hlab⟩ := hres
        rcases hbm with rfl | rfl
        · exfalso; apply hj
          rw [hlab]
          exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨by simp, hb⟩)
        · by_cases hxy : x = y
          · subst hxy
            exact ⟨c, p₁, b, hne, hp, ⟨h1, h2, hlab⟩, hab, anc_refl R c⟩
          · exfalso; apply hj
            rw [hlab]
            exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨by simp [Ne.symm hxy], hb⟩)
    · obtain ⟨k, q₁, q₂, h1, h2, h3, h4, h5⟩ := ih hb
      exact ⟨k, q₁, q₂, h1, h2, h3, h4, Relation.ReflTransGen.tail h5 hbc⟩

/-- For a variable whose only positive axiom is the unit `c = {y}`, `c` is the only node
containing `y`. -/
theorem unit_node {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {y : V} {c : Fin R.n} (hcl : R.label c = {(y, true)}) (hc : SS R y c) :
    ∀ j, (y, true) ∈ R.label j → j = c := by
  refine anc_ind hR _ fun j ih hj => ?_
  rcases node_cases hR hro j with ⟨hax, -⟩ | ⟨p₁, p₂, x, hne, hp, h1, h2, hlab⟩
  · exact hc j hax hj
  · exfalso
    rw [hlab, Finset.mem_union] at hj
    rcases hj with h | h
    · obtain ⟨hne', hm⟩ := Finset.mem_erase.1 h
      have e := ih p₁ (edge1 hp) hm
      rw [e, hcl, Finset.mem_singleton] at h1
      exact hne' h1.symm
    · have e := ih p₂ (edge2 hp) (Finset.mem_of_mem_erase h)
      rw [e, hcl, Finset.mem_singleton] at h2
      simp at h2

theorem unit_pivot_unique {R : ProofDag V} (hR : R.IsRefutationOf F) (hro : R.IsReadOnce)
    {y : V} {c : Fin R.n} (hcl : R.label c = {(y, true)}) (hc : SS R y c) {k k' : Fin R.n}
    (h : R.HasPivot k y) (h' : R.HasPivot k' y) : k = k' := by
  obtain ⟨p₁, p₂, -, hp, hp1, -, -⟩ := h
  obtain ⟨q₁, q₂, -, hq, hq1, -, -⟩ := h'
  have e1 := unit_node hR hro hcl hc p₁ hp1
  have e2 := unit_node hR hro hcl hc q₁ hq1
  rw [e1] at hp
  rw [e2] at hq
  exact consumer_unique hR hro (edge1 hp) (edge1 hq)

end ReconfRes.Frozen.Dev.Q427c.PartT
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartT
open ReconfRes.Frozen
open ConstrData
variable (D : ConstrData)
/-! ## Sources of the construction (copied from Part S2) -/
theorem axiom_label {F : CNF (CVar D.TV)} {R : ProofDag (CVar D.TV)} (hR : R.IsRefutationOf F)
    {a : Fin R.n} (ha : R.parents a = ∅) : R.label a ∈ F := by
  rcases hR.2.2.1 a with h | ⟨p₁, p₂, -, hp, -⟩ | ⟨p, hp, -⟩
  · exact h.2
  · have : p₁ ∈ R.parents a := by rw [hp]; simp
    rw [ha] at this; simp at this
  · have : p ∈ R.parents a := by rw [hp]; simp
    rw [ha] at this; simp at this

theorem src_unique {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) {s0 : Src D.TV}
    (hs0 : s0 ∈ D.srcs) {l : Literal (CVar D.TV)} (hl : l ∈ D.inv s0)
    (huniq : ∀ s ∈ D.srcs, l ∈ D.inv s → s = s0) :
    ∃ c, R.parents c = ∅ ∧ R.label c = D.inv s0 ∧
      ∀ a, R.parents a = ∅ → l ∈ R.label a → a = c := by
  have hf : D.srcs.filter (fun s => D.inv s0 = D.inv s) = {s0} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hs, he⟩
      exact huniq s hs (he ▸ hl)
    · rintro rfl
      exact ⟨hs0, rfl⟩
  have h1 : Multiset.count (D.inv s0) D.inventory = 1 := by
    unfold ConstrData.inventory
    rw [Multiset.count_map, ← Finset.filter_val, hf]
    rfl
  have h2 : Multiset.count (D.inv s0) R.axiomMultiset = 1 := hR.2.2.1 ▸ h1
  unfold ProofDag.axiomMultiset at h2
  rw [Multiset.count_map, ← Finset.filter_val] at h2
  obtain ⟨c, hc⟩ := Finset.card_eq_one.1 h2
  have hcm : c ∈ ((Finset.univ.filter fun i => R.parents i = ∅).filter
      fun i => D.inv s0 = R.label i) := by rw [hc]; simp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcm
  refine ⟨c, hcm.1, hcm.2.symm, fun a ha hla => ?_⟩
  have hF := axiom_label D hR.1 ha
  unfold ConstrData.formula at hF
  obtain ⟨s, hs, hse⟩ := Finset.mem_image.1 hF
  have := huniq s hs (hse ▸ hla)
  subst this
  have ham : a ∈ ((Finset.univ.filter fun i => R.parents i = ∅).filter
      fun i => D.inv s = R.label i) := by simp [ha, hse]
  rw [hc] at ham
  simpa using ham

theorem hd_src {h : Head D.TV} : ∀ s ∈ D.srcs, (CVar.hd h, true) ∈ D.inv s → s = Src.C h := by
  intro s _ hs
  cases s <;> simp [ConstrData.inv, ConstrData.Ch, ConstrData.CA, ConstrData.Gc] at hs ⊢
  exact hs.symm

theorem A_src : ∀ s ∈ D.srcs, (CVar.A, true) ∈ D.inv s → s = Src.CA := by
  intro s _ hs
  cases s <;> simp [ConstrData.inv, ConstrData.Ch, ConstrData.CA, ConstrData.Gc] at hs ⊢

theorem z_src {h : Head D.TV} : ∀ s ∈ D.srcs, (CVar.z h, true) ∈ D.inv s → s = Src.z h := by
  intro s _ hs
  cases s <;> simp [ConstrData.inv, ConstrData.Ch, ConstrData.CA, ConstrData.Gc] at hs ⊢
  exact hs.symm

theorem hd_source {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) {h : Head D.TV}
    (hh : h ∈ D.heads) :
    ∃ c, R.parents c = ∅ ∧ R.label c = D.Ch h ∧ SS R (CVar.hd h) c := by
  obtain ⟨c, h1, h2, h3⟩ := src_unique D hR (s0 := Src.C h) (by simp [ConstrData.srcs, hh])
    (l := (CVar.hd h, true)) (by simp [ConstrData.inv, ConstrData.Ch]) (hd_src D)
  exact ⟨c, h1, h2, h3⟩

theorem A_source {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) :
    ∃ c, R.parents c = ∅ ∧ R.label c = D.CA ∧ SS R CVar.A c := by
  obtain ⟨c, h1, h2, h3⟩ := src_unique D hR (s0 := Src.CA) (by simp [ConstrData.srcs])
    (l := (CVar.A, true)) (by simp [ConstrData.inv, ConstrData.CA]) (A_src D)
  exact ⟨c, h1, h2, h3⟩

theorem z_source {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) {h : Head D.TV}
    (hh : h ∈ D.heads) :
    ∃ c, R.parents c = ∅ ∧ R.label c = {(CVar.z h, true)} ∧ SS R (CVar.z h) c := by
  obtain ⟨c, h1, h2, h3⟩ := src_unique D hR (s0 := Src.z h) (by simp [ConstrData.srcs, hh])
    (l := (CVar.z h, true)) (by simp [ConstrData.inv]) (z_src D)
  exact ⟨c, h1, h2, h3⟩

theorem card_TV : Fintype.card D.TV = D.m := by
  simp [ConstrData.m, ConstrData.TV, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]

theorem T_mem : Head.T ∈ D.heads := by simp [ConstrData.heads]

theorem a_mem (v : D.TV) : Head.a v ∈ D.heads := by simp [ConstrData.heads]

theorem b_mem (v : D.TV) : Head.b v ∈ D.heads := by simp [ConstrData.heads]

/-! ## The goal path around `nu T` -/
/-- A negative literal of a single-source variable `y` persists from `a` to `N` if the
`y`-pivot node `M` comes strictly after `N`. -/
theorem persist_ss (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R)
    {y : CVar D.TV} {c : Fin R.n} (hc : SS R y c) {a N M : Fin R.n}
    (ha : (y, false) ∈ R.label a) (haN : R.Anc a N) (hM : R.HasPivot M y)
    (hNM : R.Anc N M) (hne : N ≠ M) : (y, false) ∈ R.label N := by
  have hro := Q427c.tight_readOnce D hD hR
  by_contra hn
  obtain ⟨k, q₁, q₂, hqne, hq, hres, -, hkN⟩ := removal' hR.1 hro ha haN hn
  have e := ss_pivot_unique hR.1 hro hc ⟨q₁, q₂, hqne, hq, hres⟩ hM
  subst e
  exact hne (Q427c.anc_antisymm D hD hR hNM hkN)

/-- No node strictly before `nu A` on the goal path descends from the `C_A` axiom. -/
theorem no_cross (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R)
    {cA : Fin R.n} (hcA : SS R CVar.A cA) {N : Fin R.n} (h1 : R.Anc cA N)
    (h2 : R.Anc (goalNode D R) N) (h3 : R.Anc N (nu R CVar.A)) (h4 : N ≠ nu R CVar.A) :
    False := by
  have hro := Q427c.tight_readOnce D hD hR
  have hRef := hR.1
  obtain ⟨hM, -⟩ := Q427c.nu_spec D hD hR CVar.A (Or.inl rfl)
  have hgl := (Q427c.goal_axiom D hD hR).2
  have hgx : (CVar.A, false) ∈ R.label (goalNode D R) := by
    rw [hgl]; simp [ConstrData.Gc]
  have hsink : (CVar.A, false) ∉ R.label R.sink := by rw [hRef.2.2.2.2]; simp
  obtain ⟨k, u₁, u₂, hune, hu, hres, hgu₂, -⟩ := removal' hRef hro hgx (hR.2.1 _) hsink
  have hk := ss_pivot_unique hRef hro hcA ⟨u₁, u₂, hune, hu, hres⟩ hM
  subst hk
  obtain ⟨r, hr, hNr⟩ := anc_last h3 h4
  have e1 := parents_eq hRef hro (anc_trans h1 hNr) (ss_anc hRef hro hcA hres.1) hr (edge1 hu)
  have e2 := parents_eq hRef hro (anc_trans h2 hNr) hgu₂ hr (edge2 hu)
  exact hune (e1.symm.trans e2)

/-- The goal clause after the `T` event contains `¬A`, `¬h` for every other head, `¬z_T`, and
`¬f_v` for every unselected `v`. -/
theorem label_T_sub (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) :
    ({(CVar.A, false)} ∪ (D.heads.erase Head.T).image (fun h => (CVar.hd h, false)) ∪
      {(CVar.z Head.T, false)} ∪
      (Finset.univ.filter fun v => v ∉ D.selected R).image (fun v => (CVar.f v, false)) :
        Finset (Literal (CVar D.TV))) ⊆ R.label (nu R (CVar.hd Head.T)) := by
  have hro := Q427c.tight_readOnce D hD hR
  have hRef := hR.1
  have hT := T_mem D
  obtain ⟨hN, hgN⟩ := Q427c.nu_spec D hD hR (CVar.hd Head.T) (Or.inr ⟨_, hT, rfl⟩)
  have hgl := (Q427c.goal_axiom D hD hR).2
  obtain ⟨cT, -, hcTl, hcT⟩ := hd_source D hR hT
  have hcTN : R.Anc cT (nu R (CVar.hd Head.T)) := by
    obtain ⟨p₁, p₂, -, hp, hp1, -, -⟩ := id hN
    exact anc_trans (ss_anc hRef hro hcT hp1) (anc_of_edge (edge1 hp))
  obtain ⟨cA, -, hcAl, hcA⟩ := A_source D hR
  obtain ⟨hMA, -⟩ := Q427c.nu_spec D hD hR CVar.A (Or.inl rfl)
  obtain ⟨hTA1, hTA2⟩ := Q427c.before_A D hD hR Head.T hT
  refine Finset.union_subset (Finset.union_subset (Finset.union_subset ?_ ?_) ?_) ?_
  · rw [Finset.singleton_subset_iff]
    exact persist_ss D hD hR hcA (by rw [hgl]; simp [ConstrData.Gc]) hgN hMA hTA1 hTA2
  · intro l hl
    simp only [Finset.mem_image, Finset.mem_erase] at hl
    obtain ⟨h, ⟨hne, hh⟩, rfl⟩ := hl
    obtain ⟨ch, -, -, hch⟩ := hd_source D hR hh
    obtain ⟨hMh, -⟩ := Q427c.nu_spec D hD hR (CVar.hd h) (Or.inr ⟨h, hh, rfl⟩)
    obtain ⟨b1, b2⟩ := Q427c.T_before D hD hR h hh hne
    exact persist_ss D hD hR hch (by rw [hgl]; simp [ConstrData.Gc, hh]) hgN hMh b1 b2
  · rw [Finset.singleton_subset_iff]
    by_contra hn
    obtain ⟨k, q₁, q₂, hqne, hq, hres, -, hkN⟩ := removal' hRef hro (y := CVar.z Head.T)
      (a := cT) (by rw [hcTl]; simp [ConstrData.Ch]) hcTN hn
    obtain ⟨cz, -, hczl, hcz⟩ := z_source D hR hT
    have hAz : (CVar.z Head.T, false) ∈ R.label cA := by
      rw [hcAl]; simp [ConstrData.CA, hT]
    obtain ⟨k', u₁, u₂, hune, hu, hres', hAu, -⟩ :=
      removal' hRef hro hAz (hR.2.1 cA) (by rw [hRef.2.2.2.2]; simp)
    have e := unit_pivot_unique hRef hro hczl hcz ⟨q₁, q₂, hqne, hq, hres⟩
      ⟨u₁, u₂, hune, hu, hres'⟩
    subst e
    exact no_cross D hD hR hcA (anc_trans (anc_trans hAu (anc_of_edge (edge2 hu))) hkN) hgN
      hTA1 hTA2
  · intro l hl
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    obtain ⟨v, hv, rfl⟩ := hl
    by_contra hn
    obtain ⟨k, q₁, q₂, hqne, hq, hres, -, hkN⟩ := removal' hRef hro (y := CVar.f v)
      (a := cT) (by rw [hcTl]; simp [ConstrData.Ch, ConstrData.Xh]) hcTN hn
    apply hv
    have ha := Q427c.T_before D hD hR (Head.a v) (a_mem D v) (by simp)
    have hb := Q427c.T_before D hD hR (Head.b v) (b_mem D v) (by simp)
    obtain ⟨hpa, -⟩ := Q427c.nu_spec D hD hR (CVar.hd (Head.a v)) (Or.inr ⟨_, a_mem D v, rfl⟩)
    obtain ⟨hpb, -⟩ := Q427c.nu_spec D hD hR (CVar.hd (Head.b v)) (Or.inr ⟨_, b_mem D v, rfl⟩)
    simp only [ConstrData.selected, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨k, _, _, ⟨q₁, q₂, hqne, hq, hres⟩, hpa, hpb, anc_trans hkN ha.1, anc_trans hkN hb.1⟩

end ReconfRes.Frozen.Dev.Q427c.PartT
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c
open ConstrData
variable (D : ConstrData)
/-! ## Part T: the clause after `T`, and claim 1 -/

end ReconfRes.Frozen.Dev.Q427c
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartT
open ReconfRes.Frozen
open ConstrData
variable (D : ConstrData)
/-- Claim 1. -/
theorem claim1 (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R)
    (hW : R.width ≤ D.W) : D.b * D.K ≤ (D.selected R).card + 1 := by
  have hc := Finset.card_le_card (label_T_sub D hD hR)
  have hw : (R.label (nu R (CVar.hd Head.T))).card ≤ R.width := by
    unfold ProofDag.width
    exact Finset.le_sup (f := fun i => (R.label i).card) (Finset.mem_univ _)
  have hT := T_mem D
  have hhc := Q427c.heads_card D hD
  have herase : (D.heads.erase Head.T).card = D.heads.card - 1 := Finset.card_erase_of_mem hT
  have hi1 : ((D.heads.erase Head.T).image (fun h => ((CVar.hd h, false) : Literal (CVar D.TV)))).card
      = (D.heads.erase Head.T).card :=
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)
  have hi2 : ((Finset.univ.filter fun v => v ∉ D.selected R).image
      (fun v => ((CVar.f v, false) : Literal (CVar D.TV)))).card
      = (Finset.univ.filter fun v => v ∉ D.selected R).card :=
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)
  have hf := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset D.TV))
    (fun v => v ∈ D.selected R)
  have hsel : (Finset.univ.filter fun v => v ∈ D.selected R) = D.selected R := by ext; simp
  rw [hsel, Finset.card_univ, card_TV] at hf
  have hl : D.b * D.K ≤ D.m := by
    unfold ConstrData.m
    exact Nat.mul_le_mul_left _ (by have := hD.2.2.1; omega)
  have hm : 2 ≤ D.n := hD.1
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Finset.card_union_of_disjoint] at hc
  · rw [hi1, hi2, herase, Finset.card_singleton, Finset.card_singleton] at hc
    unfold ConstrData.W ConstrData.β ConstrData.q ConstrData.ℓ at hW
    generalize D.b * D.K = L at *
    omega
  all_goals
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Finset.mem_erase,
      Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    aesop

end ReconfRes.Frozen.Dev.Q427c.PartT
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c
open ConstrData
variable (D : ConstrData)
alias claim1 := ReconfRes.Frozen.Dev.Q427c.PartT.claim1

end ReconfRes.Frozen.Dev.Q427c
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartI1
variable {V : Type} [DecidableEq V] {R : ProofDag V} {F : CNF V}
/-! ## Generic facts on read-once refutations -/
theorem mem_parents (i j : Fin R.n) : j ∈ R.parents i ↔ (j, i) ∈ R.edges := by
  simp [ProofDag.parents]

theorem mem_consumers (i j : Fin R.n) : j ∈ R.consumers i ↔ (i, j) ∈ R.edges := by
  simp [ProofDag.consumers]

theorem antisymm (hR : R.IsRefutationOf F) {i j : Fin R.n} (h1 : R.Anc i j) (h2 : R.Anc j i) :
    i = j := by
  unfold ProofDag.Anc at h1 h2
  rcases Relation.ReflTransGen.cases_head h1 with h | ⟨c, hc, hcj⟩
  · exact h
  · exact (hR.1 i c hc (hcj.trans h2)).elim

theorem uniq_consumer (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {a c c' : Fin R.n}
    (h : (a, c) ∈ R.edges) (h' : (a, c') ∈ R.edges) : c = c' := by
  have hs : a ≠ R.sink := by
    rintro rfl
    have : c ∈ R.consumers R.sink := (mem_consumers _ _).2 h
    rw [hR.2.2.2.1] at this; simp at this
  exact Finset.card_le_one.1 (hro.2.2 a hs).le c ((mem_consumers _ _).2 h) c'
    ((mem_consumers _ _).2 h')

theorem chain (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {a i j : Fin R.n}
    (hi : R.Anc a i) (hj : R.Anc a j) : R.Anc i j ∨ R.Anc j i := by
  unfold ProofDag.Anc at hi hj ⊢
  induction hi using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl hj
  | head hac hci ih =>
    rename_i a c
    rcases Relation.ReflTransGen.cases_head hj with rfl | ⟨c', hac', hc'j⟩
    · exact Or.inr (Relation.ReflTransGen.head hac hci)
    · rw [uniq_consumer hR hro hac hac'] at ih
      exact ih hc'j

theorem sibling_aux (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {p o k : Fin R.n}
    (hp : (p, k) ∈ R.edges) (ho : (o, k) ∈ R.edges) (hne : p ≠ o) (h : R.Anc p o) : False := by
  unfold ProofDag.Anc at h
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, hco⟩
  · exact hne h
  · rw [uniq_consumer hR hro hc hp] at hco
    exact hR.1 o k ho hco

/-- Two distinct parents of one node have no common ancestor. -/
theorem sibling (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {p o k a : Fin R.n}
    (hp : (p, k) ∈ R.edges) (ho : (o, k) ∈ R.edges) (hne : p ≠ o) (hap : R.Anc a p)
    (hao : R.Anc a o) : False := by
  rcases chain hR hro hap hao with h | h
  · exact sibling_aux hR hro hp ho hne h
  · exact sibling_aux hR hro ho hp (Ne.symm hne) h

theorem node_cases (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) (i : Fin R.n) :
    (R.parents i = ∅ ∧ R.label i ∈ F) ∨
    (∃ p₁ p₂, p₁ ≠ p₂ ∧ R.parents i = {p₁, p₂} ∧
      ∃ x, ResolventOn x (R.label p₁) (R.label p₂) (R.label i)) := by
  rcases hR.2.2.1 i with h | h | ⟨p, hp, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact (hro.2.1 i (by unfold ProofDag.IsWeakeningNode; rw [hp]; simp)).elim

theorem resolvent_sub {x : V} {A B C : Clause V} (h : ResolventOn x A B C) {l : Literal V}
    (hl : l ∈ C) : l ∈ A ∨ l ∈ B := by
  rw [h.2.2] at hl
  rcases Finset.mem_union.1 hl with h | h
  · exact Or.inl (Finset.mem_of_mem_erase h)
  · exact Or.inr (Finset.mem_of_mem_erase h)

/-- A node with a parent is a resolution node. -/
theorem edge_res (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {k' k : Fin R.n}
    (h : (k', k) ∈ R.edges) :
    ∃ q₁ q₂ x, q₁ ≠ q₂ ∧ R.parents k = {q₁, q₂} ∧
      ResolventOn x (R.label q₁) (R.label q₂) (R.label k) ∧ (k' = q₁ ∨ k' = q₂) := by
  rcases node_cases hR hro k with ⟨h0, -⟩ | ⟨q₁, q₂, hne, hpar, x, hx⟩
  · have : k' ∈ R.parents k := (mem_parents _ _).2 h
    rw [h0] at this; simp at this
  · have : k' ∈ R.parents k := (mem_parents _ _).2 h
    rw [hpar] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    exact ⟨q₁, q₂, x, hne, hpar, hx, this⟩

theorem edge_of_parents {k q₁ q₂ : Fin R.n} (h : R.parents k = {q₁, q₂}) :
    (q₁, k) ∈ R.edges ∧ (q₂, k) ∈ R.edges := by
  constructor
  · rw [← mem_parents, h]; simp
  · rw [← mem_parents, h]; simp

/-- A literal lost along an edge is the pivot literal on its side. -/
theorem drop (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {k' k : Fin R.n}
    (h : (k', k) ∈ R.edges) {l : Literal V} (hl : l ∈ R.label k') (hl' : l ∉ R.label k) :
    ∃ q₁ q₂ x, q₁ ≠ q₂ ∧ R.parents k = {q₁, q₂} ∧
      ResolventOn x (R.label q₁) (R.label q₂) (R.label k) ∧
      ((k' = q₁ ∧ l = (x, true)) ∨ (k' = q₂ ∧ l = (x, false))) := by
  obtain ⟨q₁, q₂, x, hne, hpar, hx, hk⟩ := edge_res hR hro h
  refine ⟨q₁, q₂, x, hne, hpar, hx, ?_⟩
  rcases hk with rfl | rfl
  · left; refine ⟨rfl, ?_⟩
    by_contra hc
    exact hl' (by rw [hx.2.2]; exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hc, hl⟩))
  · right; refine ⟨rfl, ?_⟩
    by_contra hc
    exact hl' (by rw [hx.2.2]; exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hc, hl⟩))

theorem exists_drop {a b : Fin R.n} (hab : R.Anc a b) {l : Literal V} (hl : l ∈ R.label a)
    (hl' : l ∉ R.label b) :
    ∃ k' k, R.Anc a k' ∧ (k', k) ∈ R.edges ∧ R.Anc k b ∧ l ∈ R.label k' ∧ l ∉ R.label k := by
  unfold ProofDag.Anc at hab
  induction hab with
  | refl => exact (hl' hl).elim
  | tail hab' hb ih =>
    rename_i b' b
    by_cases h : l ∈ R.label b'
    · exact ⟨b', b, hab', hb, Relation.ReflTransGen.refl, h, hl'⟩
    · obtain ⟨k', k, h1, h2, h3, h4, h5⟩ := ih h
      exact ⟨k', k, h1, h2, Relation.ReflTransGen.tail h3 hb, h4, h5⟩

/-! ### Induction along ancestry -/
open Classical in
/-- The number of ancestors. -/
def rank (R : ProofDag V) (j : Fin R.n) : ℕ := (Finset.univ.filter fun a => R.Anc a j).card

theorem rank_lt (hR : R.IsRefutationOf F) {p j : Fin R.n} (h : (p, j) ∈ R.edges) :
    rank R p < rank R j := by
  classical
  unfold rank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨j, by simp; exact Relation.ReflTransGen.refl, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun hjp => hR.1 p j h hjp
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact Relation.ReflTransGen.tail ha h

theorem anc_ind (hR : R.IsRefutationOf F) (P : Fin R.n → Prop)
    (h : ∀ j, (∀ p, (p, j) ∈ R.edges → P p) → P j) : ∀ j, P j := by
  suffices ∀ N, ∀ j, rank R j ≤ N → P j from fun j => this _ j le_rfl
  intro N
  induction N with
  | zero =>
    intro j hj
    exact h j fun p hp => absurd (rank_lt hR hp) (by omega)
  | succ N ih =>
    intro j hj
    exact h j fun p hp => ih p (by have := rank_lt hR hp; omega)

/-- Every literal comes from an axiom ancestor. -/
theorem origin (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {l : Literal V} :
    ∀ j, l ∈ R.label j → ∃ a, R.parents a = ∅ ∧ R.Anc a j ∧ l ∈ R.label a := by
  refine anc_ind hR _ fun j ih hl => ?_
  rcases node_cases hR hro j with ⟨h0, -⟩ | ⟨q₁, q₂, hne, hpar, x, hx⟩
  · exact ⟨j, h0, Relation.ReflTransGen.refl, hl⟩
  · have he := edge_of_parents hpar
    rcases resolvent_sub hx hl with h | h
    · obtain ⟨a, h1, h2, h3⟩ := ih q₁ he.1 h
      exact ⟨a, h1, Relation.ReflTransGen.tail h2 he.1, h3⟩
    · obtain ⟨a, h1, h2, h3⟩ := ih q₂ he.2 h
      exact ⟨a, h1, Relation.ReflTransGen.tail h2 he.2, h3⟩

/-! ### Unit-only variables -/
/-- Every axiom containing `y` is the unit `{y}`. -/
def UnitOnly (R : ProofDag V) (y : V) : Prop :=
  ∀ a, R.parents a = ∅ → (y, true) ∈ R.label a → R.label a = {(y, true)}

/-- At most one axiom node contains `y`. -/
def UniqSrc (R : ProofDag V) (y : V) : Prop :=
  ∀ a a', R.parents a = ∅ → R.parents a' = ∅ → (y, true) ∈ R.label a → (y, true) ∈ R.label a' →
    a = a'

theorem unitOnly_all (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {y : V} (hy : UnitOnly R y) :
    ∀ j, (y, true) ∈ R.label j → R.label j = {(y, true)} := by
  refine anc_ind hR _ fun j ih hj => ?_
  rcases node_cases hR hro j with ⟨h0, -⟩ | ⟨q₁, q₂, hne, hpar, x, hx⟩
  · exact hy j h0 hj
  · exfalso
    have he := edge_of_parents hpar
    have hj' := hj
    rw [hx.2.2] at hj'
    rcases Finset.mem_union.1 hj' with h | h
    · obtain ⟨hne', hm⟩ := Finset.mem_erase.1 h
      have := ih q₁ he.1 hm
      have h2 := hx.1
      rw [this, Finset.mem_singleton] at h2
      exact hne' h2.symm
    · have := ih q₂ he.2 (Finset.mem_of_mem_erase h)
      have h2 := hx.2.1
      rw [this, Finset.mem_singleton] at h2
      simp at h2

end ReconfRes.Frozen.Dev.Q427c.PartI1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartI1
variable {V : Type} [DecidableEq V] {R : ProofDag V} {F : CNF V}
variable (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {y : V} (hy : UniqSrc R y)
include hR hro hy
/-! ### Single-source variables -/
theorem common_src {j j' : Fin R.n} (h : (y, true) ∈ R.label j) (h' : (y, true) ∈ R.label j') :
    ∃ c, R.Anc c j ∧ R.Anc c j' := by
  obtain ⟨a, ha0, haj, ha⟩ := origin hR hro j h
  obtain ⟨a', ha0', haj', ha'⟩ := origin hR hro j' h'
  rw [hy a a' ha0 ha0' ha ha'] at haj
  exact ⟨a', haj, haj'⟩

theorem absent_at {i : Fin R.n} (hi : R.HasPivot i y) : (y, true) ∉ R.label i := by
  obtain ⟨p₁, p₂, hne, hpar, hx⟩ := hi
  have he := edge_of_parents hpar
  intro h
  rw [hx.2.2] at h
  rcases Finset.mem_union.1 h with h | h
  · exact (Finset.mem_erase.1 h).1 rfl
  · obtain ⟨c, h1, h2⟩ := common_src hR hro hy hx.1 (Finset.mem_of_mem_erase h)
    exact sibling hR hro he.1 he.2 hne h1 h2

theorem pivot_src {i : Fin R.n} (hi : R.HasPivot i y) :
    ∃ p, (p, i) ∈ R.edges ∧ (y, true) ∈ R.label p := by
  obtain ⟨p₁, p₂, hne, hpar, hx⟩ := hi
  exact ⟨p₁, (edge_of_parents hpar).1, hx.1⟩

theorem absent_after {i k : Fin R.n} (hi : R.HasPivot i y) (hik : R.Anc i k) :
    (y, true) ∉ R.label k := by
  unfold ProofDag.Anc at hik
  induction hik with
  | refl => exact absent_at hR hro hy hi
  | tail hik' hk ih =>
    rename_i k' k
    intro h
    obtain ⟨q₁, q₂, x, hne, hpar, hx, hk'⟩ := edge_res hR hro hk
    have he := edge_of_parents hpar
    obtain ⟨p, hp, hpy⟩ := pivot_src hR hro hy hi
    rcases resolvent_sub hx h with h1 | h1
    · rcases hk' with rfl | rfl
      · exact ih h1
      · obtain ⟨c, hc1, hc2⟩ := common_src hR hro hy h1 hpy
        exact sibling hR hro he.1 he.2 hne hc1
          ((Relation.ReflTransGen.tail hc2 hp).trans hik')
    · rcases hk' with rfl | rfl
      · obtain ⟨c, hc1, hc2⟩ := common_src hR hro hy h1 hpy
        exact sibling hR hro he.2 he.1 (Ne.symm hne) hc1
          ((Relation.ReflTransGen.tail hc2 hp).trans hik')
      · exact ih h1

theorem pivot_unique {i i' : Fin R.n} (hi : R.HasPivot i y) (hi' : R.HasPivot i' y) : i = i' := by
  suffices H : ∀ {i i' : Fin R.n}, R.HasPivot i y → R.HasPivot i' y → R.Anc i i' → i = i' by
    obtain ⟨p, hp, hpy⟩ := pivot_src hR hro hy hi
    obtain ⟨p', hp', hpy'⟩ := pivot_src hR hro hy hi'
    obtain ⟨c, hc1, hc2⟩ := common_src hR hro hy hpy hpy'
    rcases chain hR hro (Relation.ReflTransGen.tail hc1 hp) (Relation.ReflTransGen.tail hc2 hp')
      with h | h
    · exact H hi hi' h
    · exact (H hi' hi h).symm
  intro i i' hi hi' h
  unfold ProofDag.Anc at h
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨k', hik', hk'⟩
  · exact h.symm
  · exfalso
    obtain ⟨q₁, q₂, hne, hpar, hx⟩ := hi'
    have he := edge_of_parents hpar
    have hk'' : k' ∈ R.parents i' := (mem_parents _ _).2 hk'
    rw [hpar] at hk''
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk''
    rcases hk'' with rfl | rfl
    · exact absent_after hR hro hy hi hik' hx.1
    · obtain ⟨p, hp, hpy⟩ := pivot_src hR hro hy hi
      obtain ⟨c, hc1, hc2⟩ := common_src hR hro hy hx.1 hpy
      exact sibling hR hro he.1 he.2 hne hc1 ((Relation.ReflTransGen.tail hc2 hp).trans hik')

theorem no_taut_single {j : Fin R.n} (h1 : (y, true) ∈ R.label j) (h2 : (y, false) ∈ R.label j) :
    False := by
  have hsink : R.label R.sink = ∅ := hR.2.2.2.2
  obtain ⟨k', k, hjk', hk, hks, hy', hyk⟩ :=
    exists_drop (hro.1 j) h1 (by rw [hsink]; simp)
  obtain ⟨q₁, q₂, x, hne, hpar, hx, hc⟩ := drop hR hro hk hy' hyk
  rcases hc with ⟨rfl, hxy⟩ | ⟨rfl, hxy⟩
  · simp only [Prod.mk.injEq, and_true] at hxy
    subst hxy
    have hpk : R.HasPivot k y := ⟨k', q₂, hne, hpar, hx⟩
    -- `¬y` survives from `j` to `k'`
    have hn : (y, false) ∈ R.label k' := by
      by_contra hn
      obtain ⟨m', m, -, hm, hmk', hm1, hm2⟩ := exists_drop hjk' h2 hn
      obtain ⟨r₁, r₂, x', hne', hpar', hx', hc'⟩ := drop hR hro hm hm1 hm2
      rcases hc' with ⟨-, hc'⟩ | ⟨rfl, hc'⟩
      · simp at hc'
      · simp only [Prod.mk.injEq, and_true] at hc'
        subst hc'
        have := pivot_unique hR hro hy ⟨r₁, m', hne', hpar', hx'⟩ hpk
        subst this
        exact hR.1 k' m hk hmk'
    have hnk : (y, false) ∈ R.label k := by
      rw [hx.2.2]
      exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨by simp, hn⟩)
    obtain ⟨m', m, hkm', hm, -, hm1, hm2⟩ :=
      exists_drop (hro.1 k) hnk (by rw [hsink]; simp)
    obtain ⟨r₁, r₂, x', hne', hpar', hx', hc'⟩ := drop hR hro hm hm1 hm2
    rcases hc' with ⟨-, hc'⟩ | ⟨rfl, hc'⟩
    · simp at hc'
    · simp only [Prod.mk.injEq, and_true] at hc'
      subst hc'
      have := pivot_unique hR hro hy ⟨r₁, m', hne', hpar', hx'⟩ hpk
      subst this
      exact hR.1 m' m hm hkm'
  · simp at hxy

end ReconfRes.Frozen.Dev.Q427c.PartI1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartI1
variable {V : Type} [DecidableEq V] {R : ProofDag V} {F : CNF V}
theorem anc_last {a b : Fin R.n} (h : R.Anc a b) (hne : a ≠ b) :
    ∃ q, (q, b) ∈ R.edges ∧ R.Anc a q := by
  rcases Relation.ReflTransGen.cases_tail h with h' | ⟨q, hq, he⟩
  · exact absurd h'.symm hne
  · exact ⟨q, he, hq⟩

/-- A negative literal lost between `a` and `j` is removed at a pivot node in between. -/
theorem neg_drop (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {y : V} {a j : Fin R.n}
    (ha : (y, false) ∈ R.label a) (haj : R.Anc a j) (hj : (y, false) ∉ R.label j) :
    ∃ k, R.HasPivot k y ∧ R.Anc a k ∧ R.Anc k j := by
  obtain ⟨k', k, h1, h2, h3, h4, h5⟩ := exists_drop haj ha hj
  obtain ⟨q₁, q₂, x, hne, hpar, hx, hc⟩ := drop hR hro h2 h4 h5
  rcases hc with ⟨-, hc⟩ | ⟨-, hc⟩
  · simp at hc
  · simp only [Prod.mk.injEq, and_true] at hc
    subst hc
    exact ⟨k, ⟨q₁, q₂, hne, hpar, hx⟩, Relation.ReflTransGen.tail h1 h2, h3⟩

theorem src_anc (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {y : V} (hy : UniqSrc R y)
    {c j : Fin R.n} (hc0 : R.parents c = ∅) (hcy : (y, true) ∈ R.label c)
    (hj : (y, true) ∈ R.label j) : R.Anc c j := by
  obtain ⟨a, ha0, haj, ha⟩ := origin hR hro j hj
  rwa [hy a c ha0 hc0 ha hcy] at haj

theorem src_anc_pivot (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {y : V} (hy : UniqSrc R y)
    {c N : Fin R.n} (hc0 : R.parents c = ∅) (hcy : (y, true) ∈ R.label c)
    (hN : R.HasPivot N y) : R.Anc c N := by
  obtain ⟨p₁, p₂, -, hpar, hx⟩ := hN
  exact Relation.ReflTransGen.tail (src_anc hR hro hy hc0 hcy hx.1) (edge_of_parents hpar).1

/-- The chain of the source `c` of `y` meets the chain of `g` (which carries `¬y`) only at or
after the `y`-pivot node. -/
theorem junction (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {y : V} (hy : UniqSrc R y)
    {c g N j : Fin R.n} (hc0 : R.parents c = ∅) (hcy : (y, true) ∈ R.label c)
    (hgy : (y, false) ∈ R.label g) (hN : R.HasPivot N y) (hcj : R.Anc c j) (hgj : R.Anc g j) :
    R.Anc N j := by
  have hcN := src_anc_pivot hR hro hy hc0 hcy hN
  rcases chain hR hro hcN hcj with h | h
  · exact h
  by_cases hjN : j = N
  · rw [hjN]; exact Relation.ReflTransGen.refl
  obtain ⟨r, hrN, hjr⟩ := anc_last h hjN
  have hN' := hN
  obtain ⟨p₁, p₂, hne, hpar, hx⟩ := hN'
  have he := edge_of_parents hpar
  have hr : r ∈ R.parents N := (mem_parents _ _).2 hrN
  rw [hpar] at hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  have hcp1 := src_anc hR hro hy hc0 hcy hx.1
  rcases hr with hr | hr
  · rw [hr] at hjr
    have hgp : R.Anc g p₁ := hgj.trans hjr
    have hneg : (y, false) ∈ R.label p₁ := by
      by_contra hn
      obtain ⟨k, hk, -, hkr⟩ := neg_drop hR hro hgy hgp hn
      rw [pivot_unique hR hro hy hk hN] at hkr
      exact hR.1 p₁ N he.1 hkr
    exact (no_taut_single hR hro hy hx.1 hneg).elim
  · rw [hr] at hjr
    exact (sibling hR hro he.1 he.2 hne hcp1 (hcj.trans hjr)).elim

theorem unit_axiom (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {y : V} (hy : UnitOnly R y)
    {j : Fin R.n} (hj : (y, true) ∈ R.label j) : R.parents j = ∅ := by
  rcases node_cases hR hro j with ⟨h0, -⟩ | ⟨q₁, q₂, hne, hpar, x, hx⟩
  · exact h0
  · exfalso
    have hj' := hj
    rw [hx.2.2] at hj'
    rcases Finset.mem_union.1 hj' with h | h
    · obtain ⟨hne', hm⟩ := Finset.mem_erase.1 h
      have := unitOnly_all hR hro hy q₁ hm
      have h2 := hx.1
      rw [this, Finset.mem_singleton] at h2
      exact hne' h2.symm
    · have := unitOnly_all hR hro hy q₂ (Finset.mem_of_mem_erase h)
      have h2 := hx.2.1
      rw [this, Finset.mem_singleton] at h2
      simp at h2

theorem pivot_unit (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {y : V} (hy : UnitOnly R y)
    {k : Fin R.n} (hk : R.HasPivot k y) :
    ∃ u, R.parents u = ∅ ∧ R.label u = {(y, true)} ∧ (u, k) ∈ R.edges := by
  obtain ⟨p₁, p₂, -, hpar, hx⟩ := hk
  exact ⟨p₁, unit_axiom hR hro hy hx.1, unitOnly_all hR hro hy p₁ hx.1, (edge_of_parents hpar).1⟩

/-- The pattern shared by the cases of `fact_interval`. -/
theorem bpat (hR : R.IsRefutationOf F) (hro : R.IsReadOnce) {g cM cL M L w : Fin R.n}
    (hMw : R.Anc cM w) (hLw : R.Anc cL w) (hwL : R.Anc w L) (hwL' : w ≠ L)
    (hML : R.Anc M L) (hML' : M ≠ L) (hcM : R.Anc cM M) (hgM : R.Anc g M)
    (jL : ∀ j, R.Anc cL j → R.Anc g j → R.Anc L j) : False := by
  rcases chain hR hro hcM hMw with h | h
  · exact hwL' (antisymm hR hwL (jL w hLw (hgM.trans h)))
  · exact hML' (antisymm hR hML (jL M (hLw.trans h) hgM))

end ReconfRes.Frozen.Dev.Q427c.PartI1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartI1
open ConstrData
/-! ## The construction -/
theorem pos_inv (D : ConstrData) (s : Src D.TV) (y : CVar D.TV) (h : (y, true) ∈ D.inv s) :
    (∃ h', s = Src.C h' ∧ y = CVar.hd h') ∨ (s = Src.CA ∧ y = CVar.A) ∨
      (D.inv s = {(y, true)} ∧ (∀ h', y ≠ CVar.hd h') ∧ y ≠ CVar.A) := by
  cases s <;> simp [ConstrData.inv, ConstrData.Ch, ConstrData.CA, ConstrData.Gc] at h ⊢
  all_goals first
    | exact h
    | (subst h; simp)

theorem inv_eq_Ch (D : ConstrData) {s : Src D.TV} {h : Head D.TV} (hs : D.inv s = D.Ch h) :
    s = Src.C h := by
  have hm : (CVar.hd h, true) ∈ D.inv s := by rw [hs]; simp [ConstrData.Ch]
  rcases pos_inv D s _ hm with ⟨h', rfl, he⟩ | ⟨-, he⟩ | ⟨-, he, -⟩
  · cases he; rfl
  · cases he
  · exact (he h rfl).elim

theorem inv_eq_CA (D : ConstrData) {s : Src D.TV} (hs : D.inv s = D.CA) : s = Src.CA := by
  have hm : (CVar.A, true) ∈ D.inv s := by rw [hs]; simp [ConstrData.CA]
  rcases pos_inv D s _ hm with ⟨h', rfl, he⟩ | ⟨h1, -⟩ | ⟨-, -, he⟩
  · cases he
  · exact h1
  · exact (he rfl).elim

end ReconfRes.Frozen.Dev.Q427c.PartI1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartI1
open ConstrData
variable {D : ConstrData} {R : ProofDag (CVar D.TV)}
theorem axiom_label (hR : D.IsTight R) (hro : R.IsReadOnce) {a : Fin R.n} (ha : R.parents a = ∅) :
    ∃ s ∈ D.srcs, D.inv s = R.label a := by
  rcases node_cases hR.1 hro a with ⟨-, h⟩ | ⟨p₁, p₂, hne, hpar, -⟩
  · simpa [ConstrData.formula] using h
  · rw [ha] at hpar
    have : p₁ ∈ (∅ : Finset (Fin R.n)) := by rw [hpar]; simp
    simp at this

theorem count_axiom (hR : D.IsTight R) (C : Clause (CVar D.TV)) :
    Multiset.count C R.axiomMultiset =
      ((Finset.univ.filter fun i => R.parents i = ∅).filter fun i => C = R.label i).card := by
  unfold ProofDag.axiomMultiset
  rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val]

theorem axiom_label_unique (hR : D.IsTight R) (C : Clause (CVar D.TV)) (s0 : Src D.TV)
    (hC : ∀ s, D.inv s = C → s = s0) {a a' : Fin R.n} (ha : R.parents a = ∅)
    (ha' : R.parents a' = ∅) (hl : R.label a = C) (hl' : R.label a' = C) : a = a' := by
  by_contra hne
  have h1 : 1 < Multiset.count C R.axiomMultiset := by
    rw [count_axiom hR]
    exact Finset.one_lt_card.2 ⟨a, by simp [ha, hl], a', by simp [ha', hl'], hne⟩
  have h2 : Multiset.count C D.inventory ≤ 1 := by
    unfold ConstrData.inventory
    rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val]
    refine (Finset.card_le_card (t := {s0}) fun s hs => ?_).trans (by simp)
    simp only [Finset.mem_filter] at hs
    simp [hC s hs.2.symm]
  rw [hR.2.2.1] at h1
  omega

theorem uniqSrc_hd (hR : D.IsTight R) (hro : R.IsReadOnce) (h : Head D.TV) :
    UniqSrc R (CVar.hd h) := by
  intro a a' ha ha' hy hy'
  have key : ∀ b, R.parents b = ∅ → (CVar.hd h, true) ∈ R.label b → R.label b = D.Ch h := by
    intro b hb hyb
    obtain ⟨s, -, hs⟩ := axiom_label hR hro hb
    rw [← hs] at hyb ⊢
    rcases pos_inv D s _ hyb with ⟨h', rfl, he⟩ | ⟨-, he⟩ | ⟨-, he, -⟩
    · cases he; rfl
    · cases he
    · exact (he h rfl).elim
  exact axiom_label_unique hR _ _ (fun s hs => inv_eq_Ch D hs) ha ha' (key a ha hy) (key a' ha' hy')

theorem uniqSrc_A (hR : D.IsTight R) (hro : R.IsReadOnce) : UniqSrc R CVar.A := by
  intro a a' ha ha' hy hy'
  have key : ∀ b, R.parents b = ∅ → (CVar.A, true) ∈ R.label b → R.label b = D.CA := by
    intro b hb hyb
    obtain ⟨s, -, hs⟩ := axiom_label hR hro hb
    rw [← hs] at hyb ⊢
    rcases pos_inv D s _ hyb with ⟨h', rfl, he⟩ | ⟨rfl, -⟩ | ⟨-, -, he⟩
    · cases he
    · rfl
    · exact (he rfl).elim
  exact axiom_label_unique hR _ _ (fun s hs => inv_eq_CA D hs) ha ha' (key a ha hy) (key a' ha' hy')

theorem unitOnly_of (hR : D.IsTight R) (hro : R.IsReadOnce) {y : CVar D.TV}
    (hy1 : ∀ h, y ≠ CVar.hd h) (hy2 : y ≠ CVar.A) : UnitOnly R y := by
  intro a ha hya
  obtain ⟨s, -, hs⟩ := axiom_label hR hro ha
  rw [← hs] at hya ⊢
  rcases pos_inv D s _ hya with ⟨h', -, he⟩ | ⟨-, he⟩ | ⟨he, -⟩
  · exact (hy1 h' he).elim
  · exact (hy2 he).elim
  · exact he

theorem exists_src_node (hR : D.IsTight R) {s : Src D.TV} (hs : s ∈ D.srcs) :
    ∃ c, R.parents c = ∅ ∧ R.label c = D.inv s := by
  have hG : D.inv s ∈ R.axiomMultiset := by
    rw [hR.2.2.1]
    unfold ConstrData.inventory
    exact Multiset.mem_map.2 ⟨s, hs, rfl⟩
  unfold ProofDag.axiomMultiset at hG
  obtain ⟨i, hi, hl⟩ := Multiset.mem_map.1 hG
  simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact ⟨i, hi, hl⟩

theorem uniqSrc_unit (hR : D.IsTight R) (hro : R.IsReadOnce) {y : CVar D.TV}
    (hy1 : ∀ h, y ≠ CVar.hd h) (hy2 : y ≠ CVar.A) (s0 : Src D.TV)
    (huniq : ∀ s, (y, true) ∈ D.inv s → s = s0) : UniqSrc R y := by
  intro a a' ha ha' hya hya'
  have hu := unitOnly_of hR hro hy1 hy2
  exact axiom_label_unique hR {(y, true)} s0 (fun s hs => huniq s (by rw [hs]; simp)) ha ha'
    (hu a ha hya) (hu a' ha' hya')

theorem uniqSrc_z (hR : D.IsTight R) (hro : R.IsReadOnce) (h : Head D.TV) :
    UniqSrc R (CVar.z h) := by
  refine uniqSrc_unit hR hro (by simp) (by simp) (Src.z h) fun s hm => ?_
  cases s <;> simp [ConstrData.inv, ConstrData.Ch, ConstrData.CA, ConstrData.Gc] at hm ⊢
  exact hm.symm

theorem uniqSrc_p (hR : D.IsTight R) (hro : R.IsReadOnce) (j : ℕ) :
    UniqSrc R (CVar.p j) := by
  refine uniqSrc_unit hR hro (by simp) (by simp) (Src.p j) fun s hm => ?_
  cases s <;> simp [ConstrData.inv, ConstrData.Ch, ConstrData.CA, ConstrData.Gc] at hm ⊢
  exact hm.symm

/-- At most two axiom nodes are the unit `{f_v}`. -/
theorem f_units (hR : D.IsTight R) (v : D.TV) {u₁ u₂ u₃ : Fin R.n}
    (h1 : R.parents u₁ = ∅) (h2 : R.parents u₂ = ∅) (h3 : R.parents u₃ = ∅)
    (l1 : R.label u₁ = {(CVar.f v, true)}) (l2 : R.label u₂ = {(CVar.f v, true)})
    (l3 : R.label u₃ = {(CVar.f v, true)}) : u₁ = u₂ ∨ u₁ = u₃ ∨ u₂ = u₃ := by
  by_contra hc
  push Not at hc
  obtain ⟨h12, h13, h23⟩ := hc
  have hA : 3 ≤ Multiset.count ({(CVar.f v, true)} : Clause (CVar D.TV)) R.axiomMultiset := by
    rw [count_axiom hR]
    have hsub : ({u₁, u₂, u₃} : Finset (Fin R.n)) ⊆
        ((Finset.univ.filter fun i => R.parents i = ∅).filter
          fun i => ({(CVar.f v, true)} : Clause (CVar D.TV)) = R.label i) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simp [*]
    calc 3 = ({u₁, u₂, u₃} : Finset (Fin R.n)).card :=
          (Finset.card_eq_three.2 ⟨u₁, u₂, u₃, h12, h13, h23, rfl⟩).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hB : Multiset.count ({(CVar.f v, true)} : Clause (CVar D.TV)) D.inventory ≤ 2 := by
    unfold ConstrData.inventory
    rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val]
    refine (Finset.card_le_card (t := {Src.P v, Src.Q v}) fun s hs => ?_).trans
      Finset.card_le_two
    simp only [Finset.mem_filter] at hs
    have hm : (CVar.f v, true) ∈ D.inv s := by rw [← hs.2]; simp
    cases s <;> simp [ConstrData.inv, ConstrData.Ch, ConstrData.CA, ConstrData.Gc] at hm ⊢
    · exact hm.symm
    · exact hm.symm
  rw [hR.2.2.1] at hA
  omega

theorem f_three (hR : D.IsTight R) (hro : R.IsReadOnce) (v : D.TV) {k₁ k₂ k₃ : Fin R.n}
    (p1 : R.HasPivot k₁ (CVar.f v)) (p2 : R.HasPivot k₂ (CVar.f v))
    (p3 : R.HasPivot k₃ (CVar.f v)) : k₁ = k₂ ∨ k₁ = k₃ ∨ k₂ = k₃ := by
  have hu := unitOnly_of hR hro (y := CVar.f v) (by simp) (by simp)
  obtain ⟨u₁, a1, l1, e1⟩ := pivot_unit hR.1 hro hu p1
  obtain ⟨u₂, a2, l2, e2⟩ := pivot_unit hR.1 hro hu p2
  obtain ⟨u₃, a3, l3, e3⟩ := pivot_unit hR.1 hro hu p3
  rcases f_units hR v a1 a2 a3 l1 l2 l3 with h | h | h
  · rw [h] at e1; exact Or.inl (uniq_consumer hR.1 hro e1 e2)
  · rw [h] at e1; exact Or.inr (Or.inl (uniq_consumer hR.1 hro e1 e3))
  · rw [h] at e2; exact Or.inr (Or.inr (uniq_consumer hR.1 hro e2 e3))

end ReconfRes.Frozen.Dev.Q427c.PartI1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartI1
open ConstrData
variable (D : ConstrData)
/-! ## The targets -/
theorem hd_node {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) {h : Head D.TV}
    (hh : h ∈ D.heads) : ∃ c, R.parents c = ∅ ∧ R.label c = D.Ch h :=
  exists_src_node hR (s := Src.C h) (by simp [ConstrData.srcs, hh])

theorem g_hd (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) {h : Head D.TV}
    (hh : h ∈ D.heads) : (CVar.hd h, false) ∈ R.label (goalNode D R) := by
  rw [(Q427c.goal_axiom D hD hR).2]; simp [ConstrData.Gc, hh]

/-- The chain of `C_h` meets the goal path at `nu h`. -/
theorem junc_hd (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) {h : Head D.TV}
    (hh : h ∈ D.heads) {c : Fin R.n} (hc0 : R.parents c = ∅) (hcl : R.label c = D.Ch h) :
    ∀ j, R.Anc c j → R.Anc (goalNode D R) j → R.Anc (nu R (CVar.hd h)) j := by
  have hro := Q427c.tight_readOnce D hD hR
  exact fun j hcj hgj => junction hR.1 hro (uniqSrc_hd hR hro h) hc0
    (by rw [hcl]; simp [ConstrData.Ch]) (g_hd D hD hR hh)
    (Q427c.nu_spec D hD hR _ (Or.inr ⟨h, hh, rfl⟩)).1 hcj hgj

theorem c_nu (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) {h : Head D.TV}
    (hh : h ∈ D.heads) {c : Fin R.n} (hc0 : R.parents c = ∅) (hcl : R.label c = D.Ch h) :
    R.Anc c (nu R (CVar.hd h)) := by
  have hro := Q427c.tight_readOnce D hD hR
  exact src_anc_pivot hR.1 hro (uniqSrc_hd hR hro h) hc0 (by rw [hcl]; simp [ConstrData.Ch])
    (Q427c.nu_spec D hD hR _ (Or.inr ⟨h, hh, rfl⟩)).1

theorem piv_ne (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) {a b : Fin R.n}
    {x y : CVar D.TV} (ha : R.HasPivot a x) (hb : R.HasPivot b y) (hxy : x ≠ y) : a ≠ b := by
  rintro rfl
  exact hxy (Q427c.unique_pivot D hD hR a x y ha hb)

theorem fi_core (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) (v : D.TV)
    {hF hL : Head D.TV} (hFm : hF ∈ D.heads) (hLm : hL ∈ D.heads) (hFT : hF ≠ Head.T)
    (hLT : hL ≠ Head.T) (hFL : hF ≠ hL) (fF : (CVar.f v, false) ∈ D.Ch hF)
    (fL : (CVar.f v, false) ∈ D.Ch hL) {x i : Fin R.n} (hx : R.HasPivot x (CVar.f v))
    (hxF : R.Anc x (nu R (CVar.hd hF))) (hFi : R.Anc (nu R (CVar.hd hF)) i)
    (hiL : R.Anc i (nu R (CVar.hd hL))) : (CVar.f v, false) ∈ R.label i := by
  have hro := Q427c.tight_readOnce D hD hR
  have hRf := hR.1
  have hTm : Head.T ∈ D.heads := by simp [ConstrData.heads]
  obtain ⟨cT, cT0, cTl⟩ := hd_node D hR hTm
  obtain ⟨cF, cF0, cFl⟩ := hd_node D hR hFm
  obtain ⟨cL, cL0, cLl⟩ := hd_node D hR hLm
  obtain ⟨pT, gT⟩ := Q427c.nu_spec D hD hR _ (Or.inr ⟨_, hTm, rfl⟩)
  obtain ⟨pF, gF⟩ := Q427c.nu_spec D hD hR _ (Or.inr ⟨_, hFm, rfl⟩)
  obtain ⟨pL, gL⟩ := Q427c.nu_spec D hD hR _ (Or.inr ⟨_, hLm, rfl⟩)
  have jF := junc_hd D hD hR hFm cF0 cFl
  have jL := junc_hd D hD hR hLm cL0 cLl
  have aT := c_nu D hD hR hTm cT0 cTl
  have aF := c_nu D hD hR hFm cF0 cFl
  obtain ⟨TF, TF'⟩ := Q427c.T_before D hD hR hF hFm hFT
  obtain ⟨TL, TL'⟩ := Q427c.T_before D hD hR hL hLm hLT
  have FL' : nu R (CVar.hd hF) ≠ nu R (CVar.hd hL) := piv_ne D hD hR pF pL (by simpa using hFL)
  have FL : R.Anc (nu R (CVar.hd hF)) (nu R (CVar.hd hL)) := hFi.trans hiL
  by_contra hn
  obtain ⟨wT, pwT, cwT, wTi⟩ :=
    neg_drop hRf hro (by rw [cTl]; simp [ConstrData.Ch, ConstrData.Xh]) (aT.trans (TF.trans hFi)) hn
  obtain ⟨wF, pwF, cwF, wFi⟩ := neg_drop hRf hro (by rw [cFl]; exact fF) (aF.trans hFi) hn
  obtain ⟨wL, pwL, cwL, -⟩ := neg_drop hRf hro (by rw [cLl]; exact fL) (hro.1 cL)
    (by rw [hRf.2.2.2.2]; simp)
  have hB : wL ≠ wT := by
    intro e
    rw [e] at cwL
    exact bpat hRf hro cwT cwL (wTi.trans hiL) (piv_ne D hD hR pwT pL (by simp)) TL TL' aT gT jL
  have hC : wL ≠ wF := by
    intro e
    rw [e] at cwL
    exact bpat hRf hro cwF cwL (wFi.trans hiL) (piv_ne D hD hR pwF pL (by simp)) FL FL' aF gF jL
  have hTF : wT = wF := by
    rcases f_three hR hro v pwT pwF pwL with h | h | h
    · exact h
    · exact (hB h.symm).elim
    · exact (hC h.symm).elim
  have hD1 : x ≠ wL := by
    intro e
    rw [← e] at cwL
    exact FL' (antisymm hRf FL (jL _ (cwL.trans hxF) gF))
  have hD2 : x ≠ wT := by
    intro e
    rw [← e] at cwT
    rw [← hTF, ← e] at cwF
    exact bpat hRf hro cwT cwF hxF (piv_ne D hD hR hx pF (by simp)) TF TF' aT gT jF
  rcases f_three hR hro v hx pwT pwL with h | h | h
  · exact hD2 h
  · exact hD1 h
  · exact hB h.symm

/-- A selected fact is present on the goal path from its first to its last variable event. -/
theorem fact_interval (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R)
    (v : D.TV) (hv : v ∈ D.selected R) (i : Fin R.n) (hg : R.Anc (goalNode D R) i)
    (h1 : R.Anc (nu R (CVar.hd (Head.a v))) i ∨ R.Anc (nu R (CVar.hd (Head.b v))) i)
    (h2 : R.Anc i (nu R (CVar.hd (Head.a v))) ∨ R.Anc i (nu R (CVar.hd (Head.b v)))) :
    (CVar.f v, false) ∈ R.label i := by
  have hro := Q427c.tight_readOnce D hD hR
  have ham : Head.a v ∈ D.heads := by simp [ConstrData.heads]
  have hbm : Head.b v ∈ D.heads := by simp [ConstrData.heads]
  obtain ⟨pa, ga⟩ := Q427c.nu_spec D hD hR _ (Or.inr ⟨_, ham, rfl⟩)
  obtain ⟨pb, gb⟩ := Q427c.nu_spec D hD hR _ (Or.inr ⟨_, hbm, rfl⟩)
  simp only [ConstrData.selected, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz⟩ := hv
  rw [pivot_unique hR.1 hro (uniqSrc_hd hR hro _) hy pa] at hxy
  rw [pivot_unique hR.1 hro (uniqSrc_hd hR hro _) hz pb] at hxz
  have fa : (CVar.f v, false) ∈ D.Ch (Head.a v) := by simp [ConstrData.Ch, ConstrData.Xh]
  have fb : (CVar.f v, false) ∈ D.Ch (Head.b v) := by simp [ConstrData.Ch, ConstrData.Xh]
  have c1 := fun {i : Fin R.n} => fi_core D hD hR v ham hbm (by simp) (by simp) (by simp) fa fb
    (i := i) hx hxy
  have c2 := fun {i : Fin R.n} => fi_core D hD hR v hbm ham (by simp) (by simp) (by simp) fb fa
    (i := i) hx hxz
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · rw [Q427c.anc_antisymm D hD hR h2 h1]
    rcases Q427c.goal_total D hD hR ga gb with t | t
    · exact c1 Relation.ReflTransGen.refl t
    · exact c2 t Relation.ReflTransGen.refl
  · exact c1 h1 h2
  · exact c2 h1 h2
  · rw [Q427c.anc_antisymm D hD hR h2 h1]
    rcases Q427c.goal_total D hD hR ga gb with t | t
    · exact c1 t Relation.ReflTransGen.refl
    · exact c2 Relation.ReflTransGen.refl t

end ReconfRes.Frozen.Dev.Q427c.PartI1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c
open ConstrData
variable (D : ConstrData)
/-! ## Part I: fact intervals, the clauses between `U` and `A`, and claim 2 -/
alias fact_interval := ReconfRes.Frozen.Dev.Q427c.PartI1.fact_interval

end ReconfRes.Frozen.Dev.Q427c
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartI1
open ConstrData
variable (D : ConstrData)
/-- Between `U` (inclusive) and `A` (exclusive) the goal clause carries `¬A`, one of `¬h`, `¬z_h`
for every head, and every ballast literal. -/
theorem mid_label (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) (i : Fin R.n)
    (h1 : R.Anc (nu R (CVar.hd Head.U)) i) (h2 : R.Anc i (nu R CVar.A)) (h3 : i ≠ nu R CVar.A) :
    (CVar.A, false) ∈ R.label i ∧
      (∀ h ∈ D.heads, (CVar.hd h, false) ∈ R.label i ∨ (CVar.z h, false) ∈ R.label i) ∧
      ∀ j ∈ D.ballast, (CVar.p j, false) ∈ R.label i := by
  have hro := Q427c.tight_readOnce D hD hR
  have hRf := hR.1
  have hUm : Head.U ∈ D.heads := by simp [ConstrData.heads]
  obtain ⟨pU, gU⟩ := Q427c.nu_spec D hD hR _ (Or.inr ⟨_, hUm, rfl⟩)
  obtain ⟨pA, gA⟩ := Q427c.nu_spec D hD hR CVar.A (Or.inl rfl)
  have hgi : R.Anc (goalNode D R) i := gU.trans h1
  have hgl := (Q427c.goal_axiom D hD hR).2
  obtain ⟨cA, cA0, cAl⟩ := exists_src_node hR (s := Src.CA) (by simp [ConstrData.srcs])
  have hnot : ¬ R.Anc cA i := by
    intro hc
    have := junction hRf hro (uniqSrc_A hR hro) cA0
      (by rw [cAl]; simp [ConstrData.inv, ConstrData.CA]) (by rw [hgl]; simp [ConstrData.Gc])
      pA hc hgi
    exact h3 (Q427c.anc_antisymm D hD hR h2 this)
  have late : ∀ y, UniqSrc R y → (y, false) ∈ R.label cA → ∀ a, (y, false) ∈ R.label a →
      R.Anc a i → (y, false) ∈ R.label i := by
    intro y hy hyA a ha hai
    by_contra hn
    obtain ⟨k, pk, -, hki⟩ := neg_drop hRf hro ha hai hn
    obtain ⟨k₂, pk₂, hAk₂, -⟩ := neg_drop hRf hro hyA (hro.1 cA)
      (by rw [hRf.2.2.2.2]; simp)
    rw [pivot_unique hRf hro hy pk pk₂] at hki
    exact hnot (hAk₂.trans hki)
  refine ⟨?_, ?_, ?_⟩
  · by_contra hn
    obtain ⟨k, pk, -, hki⟩ := neg_drop hRf hro (by rw [hgl]; simp [ConstrData.Gc]) hgi hn
    rw [pivot_unique hRf hro (uniqSrc_A hR hro) pk pA] at hki
    exact h3 (Q427c.anc_antisymm D hD hR h2 hki)
  · intro h hh
    by_cases hc : R.Anc (nu R (CVar.hd h)) i
    · right
      obtain ⟨c, c0, cl⟩ := hd_node D hR hh
      refine late _ (uniqSrc_z hR hro h) (by rw [cAl]; simp [ConstrData.inv, ConstrData.CA, hh])
        c (by rw [cl]; simp [ConstrData.Ch]) ((c_nu D hD hR hh c0 cl).trans hc)
    · left
      by_contra hn
      obtain ⟨k, pk, -, hki⟩ := neg_drop hRf hro (g_hd D hD hR hh) hgi hn
      rw [pivot_unique hRf hro (uniqSrc_hd hR hro h) pk
        (Q427c.nu_spec D hD hR _ (Or.inr ⟨h, hh, rfl⟩)).1] at hki
      exact hc hki
  · intro j hj
    obtain ⟨c, c0, cl⟩ := hd_node D hR hUm
    exact late _ (uniqSrc_p hR hro j) (by rw [cAl]; simp [ConstrData.inv, ConstrData.CA, hj])
      c (by rw [cl]; simp [ConstrData.Ch, ConstrData.Xh, hj]) ((c_nu D hD hR hUm c0 cl).trans h1)

end ReconfRes.Frozen.Dev.Q427c.PartI1
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c
open ConstrData
variable (D : ConstrData)
alias mid_label := ReconfRes.Frozen.Dev.Q427c.PartI1.mid_label

end ReconfRes.Frozen.Dev.Q427c
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c.PartI2
open ReconfRes.Frozen ConstrData
variable (D : ConstrData)
theorem anc_trans' {R : ProofDag (CVar D.TV)} {a b c : Fin R.n} (h1 : R.Anc a b)
    (h2 : R.Anc b c) : R.Anc a c := Relation.ReflTransGen.trans h1 h2

theorem anc_refl' (R : ProofDag (CVar D.TV)) (a : Fin R.n) : R.Anc a a :=
  Relation.ReflTransGen.refl

theorem a_mem_heads (v : D.TV) : Head.a v ∈ D.heads := by
  simp [ConstrData.heads]

theorem b_mem_heads (v : D.TV) : Head.b v ∈ D.heads := by
  simp [ConstrData.heads]

open Classical in
/-- The later of the two events of `v`. -/
def last (R : ProofDag (CVar D.TV)) (v : D.TV) : Fin R.n :=
  if R.Anc (nu R (CVar.hd (Head.a v))) (nu R (CVar.hd (Head.b v))) then
    nu R (CVar.hd (Head.b v)) else nu R (CVar.hd (Head.a v))

theorem last_props (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) (v : D.TV) :
    R.Anc (goalNode D R) (last D R v) ∧
      R.Anc (nu R (CVar.hd (Head.a v))) (last D R v) ∧
      R.Anc (nu R (CVar.hd (Head.b v))) (last D R v) ∧
      (last D R v = nu R (CVar.hd (Head.a v)) ∨ last D R v = nu R (CVar.hd (Head.b v))) := by
  have hA := (Q427c.nu_spec D hD hR (CVar.hd (Head.a v))
    (Or.inr ⟨Head.a v, a_mem_heads D v, rfl⟩)).2
  have hB := (Q427c.nu_spec D hD hR (CVar.hd (Head.b v))
    (Or.inr ⟨Head.b v, b_mem_heads D v, rfl⟩)).2
  unfold last
  split_ifs with h
  · exact ⟨hB, h, anc_refl' D R _, Or.inr rfl⟩
  · have h' : R.Anc (nu R (CVar.hd (Head.b v))) (nu R (CVar.hd (Head.a v))) :=
      (Q427c.goal_total D hD hR hA hB).resolve_left h
    exact ⟨hA, anc_refl' D R _, h', Or.inl rfl⟩

theorem fact_w (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) (v w : D.TV)
    (hw : w ∈ D.selected R) (ha : D.J.Adj w v) (hl : R.Anc (last D R v) (last D R w)) :
    (CVar.f w, false) ∈ R.label (last D R v) := by
  obtain ⟨hg, _, hBv, _⟩ := last_props D hD hR v
  obtain ⟨_, _, _, hw4⟩ := last_props D hD hR w
  refine Q427c.fact_interval D hD hR w hw _ hg
    (Or.inl (anc_trans' D (Q427c.a_before_b D hD hR w v ha).1 hBv)) ?_
  rcases hw4 with h | h
  · exact Or.inl (h ▸ hl)
  · exact Or.inr (h ▸ hl)

theorem fact_v (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) (v : D.TV)
    (hv : v ∈ D.selected R) : (CVar.f v, false) ∈ R.label (last D R v) := by
  obtain ⟨hg, hAv, _, h4⟩ := last_props D hD hR v
  refine Q427c.fact_interval D hD hR v hv _ hg (Or.inl hAv) ?_
  rcases h4 with h | h
  · exact Or.inl (h ▸ anc_refl' D R _)
  · exact Or.inr (h ▸ anc_refl' D R _)

theorem mid_v (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) (v : D.TV) :
    R.Anc (nu R (CVar.hd Head.U)) (last D R v) ∧ R.Anc (last D R v) (nu R CVar.A) ∧
      last D R v ≠ nu R CVar.A := by
  obtain ⟨_, _, hBv, h4⟩ := last_props D hD hR v
  refine ⟨anc_trans' D (Q427c.U_before_b D hD hR v).1 hBv, ?_⟩
  rcases h4 with h | h
  · rw [h]; exact Q427c.before_A D hD hR _ (a_mem_heads D v)
  · rw [h]; exact Q427c.before_A D hD hR _ (b_mem_heads D v)

theorem q_pos (hD : D.Valid) : 1 ≤ D.q ∧ 1 ≤ D.m := by
  obtain ⟨hn, hK1, hKn, _⟩ := hD
  have h := Nat.mul_le_mul_left D.b hKn
  rw [mul_add, mul_one] at h
  have hb : 2 ≤ D.b := by simp [ConstrData.b]
  simp only [ConstrData.q, ConstrData.m, ConstrData.ℓ]
  omega

open Classical in
theorem core (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R)
    (hW : R.width ≤ D.W) (v w1 w2 : D.TV) (hv : v ∈ D.selected R) (hw1 : w1 ∈ D.selected R)
    (hw2 : w2 ∈ D.selected R) (hne : w1 ≠ w2) (ha1 : D.J.Adj w1 v) (ha2 : D.J.Adj w2 v)
    (hl1 : R.Anc (last D R v) (last D R w1)) (hl2 : R.Anc (last D R v) (last D R w2)) :
    False := by
  set e := last D R v with he
  obtain ⟨m1, m2, m3⟩ := mid_v D hD hR v
  obtain ⟨hAe, hHe, hPe⟩ := Q427c.mid_label D hD hR e m1 m2 m3
  have f0 := fact_v D hD hR v hv
  have f1 := fact_w D hD hR v w1 hw1 ha1 hl1
  have f2 := fact_w D hD hR v w2 hw2 ha2 hl2
  have hv1 : v ≠ w1 := by
    rintro rfl; simp [ConstrData.J] at ha1
  have hv2 : v ≠ w2 := by
    rintro rfl; simp [ConstrData.J] at ha2
  let g : Head D.TV → Literal (CVar D.TV) := fun h =>
    if (CVar.hd h, false) ∈ R.label e then (CVar.hd h, false) else (CVar.z h, false)
  let S1 : Finset (Literal (CVar D.TV)) := {(CVar.A, false)}
  let S2 : Finset (Literal (CVar D.TV)) := D.heads.image g
  let S3 : Finset (Literal (CVar D.TV)) := D.ballast.image (fun j => (CVar.p j, false))
  let S4 : Finset (Literal (CVar D.TV)) := {(CVar.f v, false), (CVar.f w1, false), (CVar.f w2, false)}
  have hsub : S1 ∪ S2 ∪ S3 ∪ S4 ⊆ R.label e := by
    intro x hx
    simp only [S1, S2, S3, S4, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_insert] at hx
    rcases hx with ((rfl | ⟨h, hh, rfl⟩) | ⟨j, hj, rfl⟩) | (rfl | rfl | rfl)
    · exact hAe
    · simp only [g]
      split_ifs with hc
      · exact hc
      · exact (hHe h hh).resolve_left hc
    · exact hPe j hj
    · exact f0
    · exact f1
    · exact f2
  have hg_inj : Set.InjOn g D.heads := by
    intro h1 _ h2 _ hgg
    simp only [g] at hgg
    split_ifs at hgg <;> simp_all
  have c2 : S2.card = D.heads.card := Finset.card_image_of_injOn hg_inj
  have c3 : S3.card = D.r := by
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
    simp [ConstrData.ballast]
  have c4 : S4.card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · simpa using hne
    · simp [hv1, hv2]
  have d12 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [S1, S2, Finset.mem_singleton, Finset.mem_image] at hx hx2
    obtain ⟨h, _, hh⟩ := hx2
    subst hx
    simp only [g] at hh
    split_ifs at hh <;> simp at hh
  have d123 : Disjoint (S1 ∪ S2) S3 := by
    rw [Finset.disjoint_left]
    intro x hx hx3
    simp only [S1, S2, S3, Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hx hx3
    obtain ⟨j, _, rfl⟩ := hx3
    rcases hx with hx | ⟨h, _, hh⟩
    · simp at hx
    · simp only [g] at hh
      split_ifs at hh <;> simp at hh
  have d1234 : Disjoint (S1 ∪ S2 ∪ S3) S4 := by
    rw [Finset.disjoint_left]
    intro x hx hx4
    simp only [S1, S2, S3, S4, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_insert] at hx hx4
    rcases hx with (hx | ⟨h, _, hh⟩) | ⟨j, _, hj⟩
    · rcases hx4 with rfl | rfl | rfl <;> simp at hx
    · simp only [g] at hh
      split_ifs at hh <;> rcases hx4 with rfl | rfl | rfl <;> simp at hh
    · rcases hx4 with rfl | rfl | rfl <;> simp at hj
  have hcard : (S1 ∪ S2 ∪ S3 ∪ S4).card = 1 + D.heads.card + D.r + 3 := by
    rw [Finset.card_union_of_disjoint d1234, Finset.card_union_of_disjoint d123,
      Finset.card_union_of_disjoint d12, c2, c3, c4]
    simp [S1]
  have hle : (R.label e).card ≤ R.width :=
    Finset.le_sup (f := fun i => (R.label i).card) (Finset.mem_univ e)
  have := Finset.card_le_card hsub
  rw [hcard, Q427c.heads_card D hD] at this
  obtain ⟨hq, hm⟩ := q_pos D hD
  simp only [ConstrData.W, ConstrData.β, ConstrData.r] at hW this
  omega

theorem twins (R : ProofDag (CVar D.TV)) (u : Fin D.n) (hu : u ∈ D.decoded R) :
    ∃ c1 c2, c1 ≠ c2 ∧ (u, c1) ∈ D.selected R ∧ (u, c2) ∈ D.selected R := by
  simp only [ConstrData.decoded, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  obtain ⟨c1, h1, c2, h2, hne⟩ := Finset.one_lt_card.1 hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  exact ⟨c1, c2, hne, h1, h2⟩

/-- Pick the twin with the earliest `last`. -/
theorem pick_min (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R) (v1 v2 : D.TV) :
    ∃ x, (x = v1 ∨ x = v2) ∧ R.Anc (last D R x) (last D R v1) ∧
      R.Anc (last D R x) (last D R v2) := by
  rcases Q427c.goal_total D hD hR (last_props D hD hR v1).1 (last_props D hD hR v2).1 with h | h
  · exact ⟨v1, Or.inl rfl, anc_refl' D R _, h⟩
  · exact ⟨v2, Or.inr rfl, h, anc_refl' D R _⟩

/-- Claim 2. -/
theorem claim2 (hD : D.Valid) {R : ProofDag (CVar D.TV)} (hR : D.IsTight R)
    (hW : R.width ≤ D.W) : IsIndepSet D.J0 (D.decoded R) := by
  intro u hu u' hu' hadj
  obtain ⟨c1, c2, hc, s1, s2⟩ := twins D R u hu
  obtain ⟨c3, c4, hc', s3, s4⟩ := twins D R u' hu'
  have adj : ∀ c c', D.J.Adj (u, c) (u', c') := fun c c' => by simpa [ConstrData.J] using hadj
  have adj' : ∀ c c', D.J.Adj (u', c') (u, c) := fun c c' => (adj c c').symm
  obtain ⟨x, hx, hx1, hx2⟩ := pick_min D hD hR (u, c1) (u, c2)
  obtain ⟨y, hy, hy1, hy2⟩ := pick_min D hD hR (u', c3) (u', c4)
  have hxs : x ∈ D.selected R := by rcases hx with rfl | rfl <;> assumption
  have hys : y ∈ D.selected R := by rcases hy with rfl | rfl <;> assumption
  obtain ⟨xc, hxc⟩ : ∃ c, x = (u, c) := by rcases hx with rfl | rfl <;> exact ⟨_, rfl⟩
  obtain ⟨yc, hyc⟩ : ∃ c, y = (u', c) := by rcases hy with rfl | rfl <;> exact ⟨_, rfl⟩
  rcases Q427c.goal_total D hD hR (last_props D hD hR x).1 (last_props D hD hR y).1 with h | h
  · refine core D hD hR hW x (u', c3) (u', c4) hxs s3 s4 (by simpa using hc')
      (hxc ▸ adj' _ _) (hxc ▸ adj' _ _) (anc_trans' D h hy1) (anc_trans' D h hy2)
  · refine core D hD hR hW y (u, c1) (u, c2) hys s1 s2 (by simpa using hc)
      (hyc ▸ adj _ _) (hyc ▸ adj _ _) (anc_trans' D h hx1) (anc_trans' D h hx2)

end ReconfRes.Frozen.Dev.Q427c.PartI2
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen.Dev.Q427c
open ConstrData
variable (D : ConstrData)
alias claim2 := ReconfRes.Frozen.Dev.Q427c.PartI2.claim2

/-! ## Assembly -/
theorem chk_decoding_capacity_two (hD : D.Valid) (R : ProofDag (CVar D.TV))
    (hR : D.IsTight R) (hW : R.width ≤ D.W) :
    D.b * D.K ≤ (D.selected R).card + 1 ∧ IsIndepSet D.J0 (D.decoded R) ∧
    ∀ (i : Fin R.n) (x y : CVar D.TV), R.HasPivot i x → R.HasPivot i y → x = y :=
  ⟨claim1 D hD hR hW, claim2 D hD hR hW, unique_pivot D hD hR⟩

end ReconfRes.Frozen.Dev.Q427c
end
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace ReconfRes.Frozen
theorem chk_decoding_capacity_two (D : ConstrData) (hD : D.Valid) (R : ProofDag (CVar D.TV))
    (hR : D.IsTight R) (hW : R.width ≤ D.W) :
    D.b * D.K ≤ (D.selected R).card + 1 ∧ IsIndepSet D.J0 (D.decoded R) ∧
    ∀ (i : Fin R.n) (x y : CVar D.TV), R.HasPivot i x → R.HasPivot i y → x = y :=
  Dev.Q427c.chk_decoding_capacity_two D hD R hR hW

end ReconfRes.Frozen
end
end

open ReconfRes.Frozen in
theorem solution : type_of% @ReconfRes.Frozen.chk_decoding_capacity_two := @ReconfRes.Frozen.chk_decoding_capacity_two
