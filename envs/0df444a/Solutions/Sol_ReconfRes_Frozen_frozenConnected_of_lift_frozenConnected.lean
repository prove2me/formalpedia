-- Prove2me | solution 1 for ReconfRes.Frozen.frozenConnected_of_lift_frozenConnected
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T21:17:35.743311+00:00
-- url     : https://prove2.me/submissions/3c6f65eb-22ce-4a3d-946a-05ea22cf9a52

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph
import Definitions.Def_ReconfRes_Frozen_PrivateTags
import Theorems.Thm_ReconfRes_Frozen_proposition_3_3
import Theorems.Thm_ReconfRes_Frozen_lemma_3_47

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
/-!
Blueprint for `ReconfRes.Frozen.frozenConnected_of_lift_frozenConnected` (Lemma 3.60 (1)).

Route: contract one tag at a time.  For a CNF `Φ`, a variable `t` and a vertex `X` of
`G^fr_k(Φ,w,s)` that is *good* (the unit `{t}` is exactly one of its axiom clauses, no other axiom
clause contains the literal `t`, and `s + 1 ≤ 2·#axioms`, so `X` is a read-once tree by
Lemma 3.47), the unit node `u` has a single consumer `c`, which resolves on `t` with its other
parent `p`.  The contraction deletes `u` and `c`, sends the consumers of `c` to `p`, and erases
`¬t` from every clause.  Frozen steps of good vertices project to frozen steps (Part B).  Applying
this to the last tag of `liftFirst (j+1) R` gives (up to isomorphism) `liftFirst j R` (Part C).
-/
/-! ## The one-tag contraction -/
/-- The nodes kept by the contraction: all but the unit node `u` and its consumer `c`. -/
def keep (X : ProofDag V) (u c : Fin X.n) : Finset (Fin X.n) :=
  Finset.univ.filter fun x => x ≠ u ∧ x ≠ c

/-- The indexing of the kept nodes by `Fin`. -/
noncomputable def kE (X : ProofDag V) (u c : Fin X.n) :
    Fin (keep X u c).card ≃ {x // x ∈ keep X u c} :=
  (keep X u c).equivFin.symm

/-- The node that represents `x` after contracting `c` onto `p`. -/
def rep (X : ProofDag V) (c p : Fin X.n) (x : Fin X.n) : Fin X.n := if x = c then p else x

/-- The contraction of the tag gadget `u → c ← p` with tag variable `t`: delete `u` and `c`,
make every consumer of `c` a consumer of `p`, erase `¬t` from every clause. -/
noncomputable def contract (X : ProofDag V) (u c p : Fin X.n) (t : V)
    (h : rep X c p X.sink ∈ keep X u c) : ProofDag V where
  n := (keep X u c).card
  label i := (X.label (kE X u c i).1).erase (t, false)
  edges := Finset.univ.filter fun e =>
    ((kE X u c e.1).1, (kE X u c e.2).1) ∈ X.edges ∨
      ((kE X u c e.1).1 = p ∧ (c, (kE X u c e.2).1) ∈ X.edges)
  sink := (kE X u c).symm ⟨_, h⟩

/-- `P` is the contraction of `X` at the tag variable `t`. -/
def IsProj (t : V) (X P : ProofDag V) : Prop :=
  ∃ (u c p : Fin X.n) (h : rep X c p X.sink ∈ keep X u c),
    X.label u = {(t, true)} ∧ X.parents u = ∅ ∧ (u, c) ∈ X.edges ∧ (p, c) ∈ X.edges ∧ p ≠ u ∧
    P = contract X u c p t h

/-- The standing hypotheses of the one-tag contraction for a vertex `X` of `G^fr(Φ,w,s)`. -/
def Good (Φ : CNF V) (w s : ℕ) (t : V) (X : ProofDag V) : Prop :=
  IsVertex Φ w s X ∧ X.axiomMultiset.count {(t, true)} = 1 ∧
  (∀ E ∈ X.axiomMultiset, E ≠ {(t, true)} → (t, true) ∉ E) ∧
  s + 1 ≤ 2 * Multiset.card X.axiomMultiset

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartA
variable {V : Type} [DecidableEq V]
/-! ## Generic helpers -/
theorem mem_parents (R : ProofDag V) (i j : Fin R.n) : j ∈ R.parents i ↔ (j, i) ∈ R.edges := by
  simp [ProofDag.parents]

theorem mem_consumers (R : ProofDag V) (i j : Fin R.n) :
    j ∈ R.consumers i ↔ (i, j) ∈ R.edges := by
  simp [ProofDag.consumers]

theorem no_loop {Φ : CNF V} {X : ProofDag V} (hR : X.IsRefutationOf Φ) {a b : Fin X.n}
    (h : (a, b) ∈ X.edges) : a ≠ b := by
  rintro rfl; exact hR.1 a a h Relation.ReflTransGen.refl

theorem sink_ne_of_edge {Φ : CNF V} {X : ProofDag V} (hR : X.IsRefutationOf Φ) {a b : Fin X.n}
    (h : (a, b) ∈ X.edges) : a ≠ X.sink := by
  rintro rfl
  have := hR.2.2.2.1
  have hb : b ∈ X.consumers X.sink := (mem_consumers _ _ _).2 h
  rw [this] at hb; simp at hb

theorem consumers_eq {Φ : CNF V} {X : ProofDag V} (hR : X.IsRefutationOf Φ) (hro : X.IsReadOnce)
    {a b : Fin X.n} (h : (a, b) ∈ X.edges) : X.consumers a = {b} := by
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp (hro.2.2 a (sink_ne_of_edge hR h))
  have : b ∈ X.consumers a := (mem_consumers _ _ _).2 h
  rw [hd] at this ⊢
  simp at this; rw [this]

theorem wf_edges {Φ : CNF V} {X : ProofDag V} (hR : X.IsRefutationOf Φ) :
    WellFounded (Relation.TransGen fun a b => (a, b) ∈ X.edges) := by
  have : IsTrans (Fin X.n) (Relation.TransGen fun a b => (a, b) ∈ X.edges) :=
    ⟨fun _ _ _ => Relation.TransGen.trans⟩
  have : IsIrrefl (Fin X.n) (Relation.TransGen fun a b => (a, b) ∈ X.edges) := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨b, hab, hba⟩ := Relation.TransGen.head'_iff.mp ha
    exact hR.1 a b hab hba
  exact Finite.wellFounded_of_trans_of_irrefl _

theorem mem_axiomMultiset {X : ProofDag V} {i : Fin X.n} (h : X.parents i = ∅) :
    X.label i ∈ X.axiomMultiset := by
  unfold ProofDag.axiomMultiset
  exact Multiset.mem_map.2 ⟨i, by simp [h], rfl⟩

/-! ## Good vertices -/
/-- A good vertex is read-once. -/
theorem good_readOnce {Φ : CNF V} {w s : ℕ} {t : V} {X : ProofDag V} (hX : Good Φ w s t X) :
    X.IsReadOnce := by
  obtain ⟨⟨hR, hL, _, hs⟩, h1, _, h3⟩ := hX
  have hM : 1 ≤ Multiset.card X.axiomMultiset := by
    have := Multiset.count_le_card ({(t, true)} : Clause V) X.axiomMultiset
    omega
  exact (lemma_3_47 Φ X.axiomMultiset hM).1 X hR hL rfl (by omega)

end ReconfRes.Frozen.Dev.Q427.PartA
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
/-! ## Part A: structure of good vertices, the contraction is a vertex -/

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartA
variable {V : Type} [DecidableEq V]
theorem exists_unit_axiom {Φ : CNF V} {w s : ℕ} {t : V} {X : ProofDag V} (hX : Good Φ w s t X) :
    ∃ u, X.parents u = ∅ ∧ X.label u = {(t, true)} := by
  have h1 := hX.2.1
  have : ({(t, true)} : Clause V) ∈ X.axiomMultiset := by
    rw [← Multiset.count_pos]; omega
  unfold ProofDag.axiomMultiset at this
  obtain ⟨u, hu, hl⟩ := Multiset.mem_map.1 this
  exact ⟨u, by simpa using hu, hl⟩

theorem axiom_unique {Φ : CNF V} {w s : ℕ} {t : V} {X : ProofDag V} (hX : Good Φ w s t X)
    {a b : Fin X.n} (ha : X.parents a = ∅) (hb : X.parents b = ∅)
    (la : X.label a = {(t, true)}) (lb : X.label b = {(t, true)}) : a = b := by
  have h1 := hX.2.1
  unfold ProofDag.axiomMultiset at h1
  rw [Multiset.count_map, ← Finset.filter_val] at h1
  have h2 : ((Finset.univ.filter fun i => X.parents i = ∅).filter
      fun i => ({(t, true)} : Clause V) = X.label i).card ≤ 1 := by
    rw [Finset.card_def]; omega
  exact Finset.card_le_one.mp h2 a (by simp [ha, la]) b (by simp [hb, lb])

theorem unit_char {Φ : CNF V} {w s : ℕ} {t : V} {X : ProofDag V} (hX : Good Φ w s t X) :
    ∀ x, (t, true) ∈ X.label x → X.parents x = ∅ ∧ X.label x = {(t, true)} := by
  have hR := hX.1.1
  have hro := good_readOnce hX
  intro x
  induction x using (wf_edges hR).induction with
  | _ x ih =>
  intro hx
  rcases hR.2.2.1 x with ⟨hpx, hlx⟩ | ⟨p₁, p₂, hne, hpar, y, hy1, hy2, hyl⟩ | ⟨q, hq, hsub⟩
  · refine ⟨hpx, ?_⟩
    by_contra hne
    exact hX.2.2.1 _ (mem_axiomMultiset hpx) hne hx
  · exfalso
    have hp1 : (p₁, x) ∈ X.edges := by rw [← mem_parents, hpar]; simp
    have hp2 : (p₂, x) ∈ X.edges := by rw [← mem_parents, hpar]; simp
    rw [hyl] at hx
    rcases Finset.mem_union.mp hx with h | h
    · obtain ⟨_, l1⟩ := ih p₁ (Relation.TransGen.single hp1) (Finset.mem_of_mem_erase h)
      rw [l1] at hy1 h
      simp at hy1; subst hy1
      simp at h
    · obtain ⟨_, l2⟩ := ih p₂ (Relation.TransGen.single hp2) (Finset.mem_of_mem_erase h)
      rw [l2] at hy2; simp at hy2
  · exfalso
    exact hro.2.1 x (by unfold ProofDag.IsWeakeningNode; rw [hq]; simp)

/-- A good vertex has exactly one node whose clause contains the literal `t`: an axiom node
labelled `{t}`. -/
theorem good_unit {Φ : CNF V} {w s : ℕ} {t : V} {X : ProofDag V} (hX : Good Φ w s t X) :
    ∃ u, X.label u = {(t, true)} ∧ X.parents u = ∅ ∧ ∀ x, (t, true) ∈ X.label x → x = u := by
  obtain ⟨u, hpu, hlu⟩ := exists_unit_axiom hX
  refine ⟨u, hlu, hpu, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := unit_char hX x hx
  exact axiom_unique hX h1 hpu h2 hlu

end ReconfRes.Frozen.Dev.Q427.PartA
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
alias good_unit := ReconfRes.Frozen.Dev.Q427.PartA.good_unit

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartA
variable {V : Type} [DecidableEq V]
theorem unit_uniq {Φ : CNF V} {w s : ℕ} {t : V} {X : ProofDag V} (hX : Good Φ w s t X)
    {u : Fin X.n} (hu : X.label u = {(t, true)}) :
    X.parents u = ∅ ∧ ∀ x, (t, true) ∈ X.label x → x = u := by
  obtain ⟨u0, hl0, hp0, huniq⟩ := good_unit hX
  have hu0 : u = u0 := huniq u (by rw [hu]; simp)
  subst hu0
  exact ⟨hp0, huniq⟩

/-- The tag gadget of a good vertex. -/
theorem good_gadget {Φ : CNF V} {w s : ℕ} {t : V} {X : ProofDag V} (hX : Good Φ w s t X)
    {u : Fin X.n} (hu : X.label u = {(t, true)}) :
    ∃ c p, X.consumers u = {c} ∧ X.parents c = {u, p} ∧ p ≠ u ∧ p ≠ c ∧ X.consumers p = {c} ∧
      (t, false) ∈ X.label p ∧ X.label c = (X.label p).erase (t, false) ∧
      rep X c p X.sink ∈ keep X u c := by
  obtain ⟨hpu, huniq⟩ := unit_uniq hX hu
  have hro := good_readOnce hX
  have hR := hX.1.1
  have husink : u ≠ X.sink := by
    intro h; have := hR.2.2.2.2; rw [← h, hu] at this; simp at this
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hro.2.2 u husink)
  have huc : (u, c) ∈ X.edges := by rw [← mem_consumers, hc]; simp
  have hupc : u ∈ X.parents c := (mem_parents _ _ _).2 huc
  rcases hR.2.2.1 c with ⟨hpc, _⟩ | ⟨p₁, p₂, hne, hpar, y, hy1, hy2, hyl⟩ | ⟨q, hq, _⟩
  · rw [hpc] at hupc; simp at hupc
  · rw [hpar] at hupc
    simp at hupc
    rcases hupc with rfl | rfl
    · rw [hu] at hy1; simp at hy1; subst hy1
      have hpe : (p₂, c) ∈ X.edges := by rw [← mem_parents, hpar]; simp
      have hpc : p₂ ≠ c := no_loop hR hpe
      refine ⟨c, p₂, hc, hpar, hne.symm, hpc, consumers_eq hR hro hpe, hy2, ?_, ?_⟩
      · rw [hyl, hu]; simp
      · have hcu : c ≠ u := (no_loop hR huc).symm
        unfold rep keep
        split_ifs with hs
        · simp [hne.symm, hpc]
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, hs⟩
          intro h; exact husink h.symm
    · rw [hu] at hy2; simp at hy2
  · exfalso
    exact hro.2.1 c (by unfold ProofDag.IsWeakeningNode; rw [hq]; simp)

end ReconfRes.Frozen.Dev.Q427.PartA
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
alias good_gadget := ReconfRes.Frozen.Dev.Q427.PartA.good_gadget

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartA
variable {V : Type} [DecidableEq V]
/-- In a good vertex, only the consumer of the unit resolves on `t`. -/
theorem good_pivot {Φ : CNF V} {w s : ℕ} {t : V} {X : ProofDag V} (hX : Good Φ w s t X)
    {u c : Fin X.n} (hu : X.label u = {(t, true)}) (hc : (u, c) ∈ X.edges)
    {i p₁ p₂ : Fin X.n} {x : V} (hi : i ≠ c) (hpar : X.parents i = {p₁, p₂})
    (hres : ResolventOn x (X.label p₁) (X.label p₂) (X.label i)) : x ≠ t := by
  rintro rfl
  obtain ⟨hpu, huniq⟩ := unit_uniq hX hu
  have h1 : p₁ = u := huniq p₁ hres.1
  subst h1
  have hpe : (p₁, i) ∈ X.edges := by rw [← mem_parents, hpar]; simp
  have := consumers_eq hX.1.1 (good_readOnce hX) hc
  have hi' : i ∈ X.consumers p₁ := (mem_consumers _ _ _).2 hpe
  rw [this] at hi'; simp at hi'; exact hi hi'

end ReconfRes.Frozen.Dev.Q427.PartA
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartA
variable {V : Type} [DecidableEq V]
/-- A good vertex has a contraction. -/
theorem exists_proj {Φ : CNF V} {w s : ℕ} {t : V} {X : ProofDag V} (hX : Good Φ w s t X) :
    ∃ P, IsProj t X P := by
  obtain ⟨u, hlu, hpu, _⟩ := good_unit hX
  obtain ⟨c, p, hc, hpc, hpu', _, _, _, _, hk⟩ := good_gadget hX hlu
  refine ⟨_, u, c, p, hk, hlu, hpu, ?_, ?_, hpu', rfl⟩
  · rw [← mem_consumers, hc]; simp
  · rw [← mem_parents, hpc]; simp

end ReconfRes.Frozen.Dev.Q427.PartA
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
alias exists_proj := ReconfRes.Frozen.Dev.Q427.PartA.exists_proj

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartA
variable {V : Type} [DecidableEq V]
theorem proj_data {Φ : CNF V} {w s : ℕ} {t : V} {X : ProofDag V} (hX : Good Φ w s t X)
    {u c p : Fin X.n} (hlu : X.label u = {(t, true)}) (huc : (u, c) ∈ X.edges)
    (hpc : (p, c) ∈ X.edges) (hpu : p ≠ u) :
    X.consumers u = {c} ∧ X.parents c = {u, p} ∧ p ≠ c ∧ X.consumers p = {c} ∧
      (t, false) ∈ X.label p ∧ X.label c = (X.label p).erase (t, false) := by
  obtain ⟨c', p', hc', hpc', hpu', hpc'', hcp', ht', hl', _⟩ := good_gadget hX hlu
  have : c' = c := by
    have := (mem_consumers _ _ _).2 huc; rw [hc'] at this; simp at this; exact this.symm
  subst this
  have : p' = p := by
    have := (mem_parents _ _ _).2 hpc; rw [hpc'] at this; simp at this
    rcases this with h | h
    · exact absurd h hpu
    · exact h.symm
  subst this
  exact ⟨hc', hpc', hpc'', hcp', ht', hl'⟩

/-- The contraction is determined. -/
theorem proj_unique {Φ : CNF V} {w s : ℕ} {t : V} {X P P' : ProofDag V} (hX : Good Φ w s t X)
    (hP : IsProj t X P) (hP' : IsProj t X P') : P = P' := by
  obtain ⟨u, c, p, h, hlu, hpu, huc, hpc, hpnu, rfl⟩ := hP
  obtain ⟨u', c', p', h', hlu', hpu', huc', hpc', hpnu', rfl⟩ := hP'
  obtain ⟨_, huniq⟩ := unit_uniq hX hlu
  have : u' = u := huniq u' (by rw [hlu']; simp)
  subst this
  obtain ⟨hcu, hparc, _⟩ := proj_data hX hlu huc hpc hpnu
  have : c' = c := by
    have := (mem_consumers _ _ _).2 huc'; rw [hcu] at this; simpa using this
  subst this
  have : p' = p := by
    have := (mem_parents _ _ _).2 hpc'; rw [hparc] at this; simp at this
    rcases this with h | h
    · exact absurd h hpnu'
    · exact h
  subst this
  rfl

end ReconfRes.Frozen.Dev.Q427.PartA
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
alias proj_unique := ReconfRes.Frozen.Dev.Q427.PartA.proj_unique

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartA
variable {V : Type} [DecidableEq V]
/-! ## Frozen steps keep goodness -/
theorem iso_parents_empty {X Y : ProofDag V} (e : Fin X.n ≃ Fin Y.n)
    (he : ∀ i j, (e i, e j) ∈ Y.edges ↔ (i, j) ∈ X.edges) (i : Fin X.n) :
    Y.parents (e i) = ∅ ↔ X.parents i = ∅ := by
  simp only [Finset.eq_empty_iff_forall_notMem, mem_parents]
  constructor
  · intro h j hj; exact h (e j) ((he j i).2 hj)
  · intro h j hj
    obtain ⟨j', rfl⟩ := e.surjective j
    exact h j' ((he j' i).1 hj)

theorem iso_axiomMultiset {X Y : ProofDag V} (h : X.Iso Y) :
    X.axiomMultiset = Y.axiomMultiset := by
  obtain ⟨e, hl, he, hs⟩ := h
  unfold ProofDag.axiomMultiset
  have : (Finset.univ.filter fun j => Y.parents j = ∅) =
      (Finset.univ.filter fun i => X.parents i = ∅).map e.toEmbedding := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp [iso_parents_empty e he]
  rw [this, Finset.map_val, Multiset.map_map]
  congr 1
  funext i
  simp [hl]

theorem good_of_eq {Φ : CNF V} {w s : ℕ} {t : V} {X Y : ProofDag V} (hX : Good Φ w s t X)
    (hY : IsVertex Φ w s Y) (h : X.axiomMultiset = Y.axiomMultiset) : Good Φ w s t Y := by
  obtain ⟨_, h1, h2, h3⟩ := hX
  rw [h] at h1 h2 h3
  exact ⟨hY, h1, h2, h3⟩

/-- Goodness is preserved by a frozen step (moves and isomorphisms keep the axiom multiset). -/
theorem good_of_step {k : ℕ} (hk : 1 ≤ k) {Φ : CNF V} {w s : ℕ} {t : V} {X Y : ProofDag V}
    (hX : Good Φ w s t X) (h : FrozenStep k Φ w s X Y) : Good Φ w s t Y := by
  obtain ⟨hvX, hvY, hiso | hm | hm⟩ := h
  · exact good_of_eq hX hvY (iso_axiomMultiset hiso)
  · exact good_of_eq hX hvY ((proposition_3_3 k hk Φ w s).1 X Y ⟨hvX, hvY, Or.inl hm⟩)
  · exact good_of_eq hX hvY ((proposition_3_3 k hk Φ w s).1 X Y ⟨hvX, hvY, Or.inr hm⟩)

/-! ## The contraction API -/
theorem mem_keep {X : ProofDag V} {u c x : Fin X.n} : x ∈ keep X u c ↔ x ≠ u ∧ x ≠ c := by
  simp [keep]

theorem kE_mem (X : ProofDag V) (u c : Fin X.n) (a : Fin (keep X u c).card) :
    (kE X u c a).1 ≠ u ∧ (kE X u c a).1 ≠ c := mem_keep.1 (kE X u c a).2

theorem kE_inj {X : ProofDag V} {u c : Fin X.n} {a b : Fin (keep X u c).card}
    (h : (kE X u c a).1 = (kE X u c b).1) : a = b :=
  (kE X u c).injective (Subtype.ext h)

theorem rep_of_ne {X : ProofDag V} {c p x : Fin X.n} (h : x ≠ c) : rep X c p x = x := by
  simp [rep, h]

theorem rep_c {X : ProofDag V} {c p : Fin X.n} : rep X c p c = p := by simp [rep]

theorem rep_mem {X : ProofDag V} {u c p x : Fin X.n} (hpu : p ≠ u) (hpc : p ≠ c) (hx : x ≠ u) :
    rep X c p x ∈ keep X u c := by
  rw [mem_keep]
  by_cases h : x = c
  · subst h; rw [rep_c]; exact ⟨hpu, hpc⟩
  · rw [rep_of_ne h]; exact ⟨hx, h⟩

/-- The kept node representing `x`. -/
noncomputable def pr (X : ProofDag V) (u c p : Fin X.n) (t : V)
    (h : rep X c p X.sink ∈ keep X u c) (x : Fin X.n) : Fin (contract X u c p t h).n :=
  if hx : rep X c p x ∈ keep X u c then (kE X u c).symm ⟨_, hx⟩ else (kE X u c).symm ⟨_, h⟩

theorem kE_pr {X : ProofDag V} {u c p : Fin X.n} {t : V} (h : rep X c p X.sink ∈ keep X u c)
    {x : Fin X.n} (hx : rep X c p x ∈ keep X u c) : (kE X u c (pr X u c p t h x)).1 = rep X c p x := by
  simp [pr, hx]

theorem pr_kE {X : ProofDag V} {u c p : Fin X.n} {t : V} (h : rep X c p X.sink ∈ keep X u c)
    (a : Fin (contract X u c p t h).n) : pr X u c p t h (kE X u c a).1 = a := by
  have hm := kE_mem X u c a
  have hr : rep X c p (kE X u c a).1 = (kE X u c a).1 := rep_of_ne hm.2
  apply kE_inj
  rw [kE_pr h (by rw [hr]; exact (kE X u c a).2), hr]

theorem pr_c {X : ProofDag V} {u c p : Fin X.n} {t : V} (h : rep X c p X.sink ∈ keep X u c)
    (hpc : p ≠ c) : pr X u c p t h c = pr X u c p t h p := by
  unfold pr; rw [rep_c, rep_of_ne hpc]

theorem contract_label {X : ProofDag V} {u c p : Fin X.n} {t : V}
    {h : rep X c p X.sink ∈ keep X u c} (i : Fin (contract X u c p t h).n) :
    (contract X u c p t h).label i = (X.label (kE X u c i).1).erase (t, false) := rfl

theorem mem_contract_edges {X : ProofDag V} {u c p : Fin X.n} {t : V}
    {h : rep X c p X.sink ∈ keep X u c} (a b : Fin (contract X u c p t h).n) :
    (a, b) ∈ (contract X u c p t h).edges ↔ ((kE X u c a).1, (kE X u c b).1) ∈ X.edges ∨
      ((kE X u c a).1 = p ∧ (c, (kE X u c b).1) ∈ X.edges) := by
  exact ⟨fun h' => (Finset.mem_filter.1 h').2, fun h' => Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩⟩

theorem contract_sink {X : ProofDag V} {u c p : Fin X.n} {t : V}
    {h : rep X c p X.sink ∈ keep X u c} :
    (contract X u c p t h).sink = pr X u c p t h X.sink := by
  simp [contract, pr, h]

theorem res_erase {y t : V} {A B C : Clause V} (hy : y ≠ t) (h : ResolventOn y A B C) :
    ResolventOn y (A.erase (t, false)) (B.erase (t, false)) (C.erase (t, false)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Finset.mem_erase.2 ⟨by simp, h1⟩, Finset.mem_erase.2 ⟨by simp [hy], h2⟩, ?_⟩
  subst h3
  ext l
  simp only [Finset.mem_erase, Finset.mem_union]
  tauto

theorem card_keep {X : ProofDag V} {u c : Fin X.n} (huc : u ≠ c) :
    (keep X u c).card + 2 = X.n := by
  have : keep X u c = Finset.univ \ {u, c} := by ext x; simp [keep]
  rw [this, Finset.card_univ_diff, Fintype.card_fin, Finset.card_pair huc]
  have := Finset.card_le_univ ({u, c} : Finset (Fin X.n))
  rw [Fintype.card_fin, Finset.card_pair huc] at this
  omega

/-- The standing facts about the gadget. -/
structure Gad (Φ : CNF V) (X : ProofDag V) (u c p : Fin X.n) (t : V) : Prop where
  ref : X.IsRefutationOf Φ
  ro : X.IsReadOnce
  lu : X.label u = {(t, true)}
  pu : X.parents u = ∅
  uniq : ∀ x, (t, true) ∈ X.label x → x = u
  cu : X.consumers u = {c}
  pc : X.parents c = {u, p}
  pnu : p ≠ u
  pnc : p ≠ c
  cp : X.consumers p = {c}
  tp : (t, false) ∈ X.label p
  lc : X.label c = (X.label p).erase (t, false)
  piv : ∀ (i : Fin X.n) (p₁ : Fin X.n) (p₂ : Fin X.n) (x : V), i ≠ c →
    X.parents i = {p₁, p₂} → ResolventOn x (X.label p₁) (X.label p₂) (X.label i) → x ≠ t

end ReconfRes.Frozen.Dev.Q427.PartA
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartA
variable {V : Type} [DecidableEq V]
variable {Φ : CNF V} {X : ProofDag V} {u c p : Fin X.n} {t : V}
theorem Gad.ucne (G : Gad Φ X u c p t) : u ≠ c := by
  intro h
  have : u ∈ X.parents c := by rw [G.pc]; simp
  rw [← h, G.pu] at this; simp at this

theorem Gad.edge_u (G : Gad Φ X u c p t) {y : Fin X.n} (hy : (u, y) ∈ X.edges) : y = c := by
  have := (mem_consumers _ _ _).2 hy; rw [G.cu] at this; simpa using this

theorem Gad.edge_p (G : Gad Φ X u c p t) {y : Fin X.n} (hy : (p, y) ∈ X.edges) : y = c := by
  have := (mem_consumers _ _ _).2 hy; rw [G.cp] at this; simpa using this

theorem Gad.edge_to_u (G : Gad Φ X u c p t) {y : Fin X.n} (hy : (y, u) ∈ X.edges) : False := by
  have := (mem_parents _ _ _).2 hy; rw [G.pu] at this; simp at this

theorem Gad.edge_pc (G : Gad Φ X u c p t) : (p, c) ∈ X.edges := by
  rw [← mem_parents, G.pc]; simp

theorem Gad.edge_to_c (G : Gad Φ X u c p t) {y : Fin X.n} (hy : (y, c) ∈ X.edges) :
    y = u ∨ y = p := by
  have := (mem_parents _ _ _).2 hy; rw [G.pc] at this; simpa using this

end ReconfRes.Frozen.Dev.Q427.PartA
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartA
variable {V : Type} [DecidableEq V]
variable {Φ : CNF V} {X : ProofDag V} {u c p : Fin X.n} {t : V}
variable (h : rep X c p X.sink ∈ keep X u c)
theorem Gad.edge_iff (G : Gad Φ X u c p t) (a i : Fin (contract X u c p t h).n) :
    (a, i) ∈ (contract X u c p t h).edges ↔
      ∃ z, (z, (kE X u c i).1) ∈ X.edges ∧ z ≠ u ∧ pr X u c p t h z = a := by
  rw [mem_contract_edges]
  constructor
  · rintro (he | ⟨hp, he⟩)
    · exact ⟨_, he, (kE_mem X u c a).1, pr_kE h a⟩
    · refine ⟨c, he, G.ucne.symm, ?_⟩
      apply kE_inj
      rw [kE_pr h (rep_mem G.pnu G.pnc G.ucne.symm), rep_c, hp]
  · rintro ⟨z, hz, hzu, rfl⟩
    have hk := kE_pr (t := t) h (rep_mem G.pnu G.pnc hzu)
    by_cases hzc : z = c
    · subst hzc
      right; rw [hk, rep_c]; exact ⟨rfl, hz⟩
    · left; rw [hk, rep_of_ne hzc]; exact hz

theorem Gad.parents_contract (G : Gad Φ X u c p t) (i : Fin (contract X u c p t h).n) :
    (contract X u c p t h).parents i = (X.parents (kE X u c i).1).image (pr X u c p t h) := by
  ext a
  rw [mem_parents, G.edge_iff h, Finset.mem_image]
  simp only [mem_parents]
  constructor
  · rintro ⟨z, hz, _, rfl⟩; exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z, hz, ?_, rfl⟩
    intro hzu; rw [hzu] at hz
    exact (kE_mem X u c i).2 (G.edge_u hz)

theorem Gad.label_pr (G : Gad Φ X u c p t) {z : Fin X.n} (hz : z ≠ u) :
    (contract X u c p t h).label (pr X u c p t h z) = (X.label z).erase (t, false) := by
  rw [contract_label, kE_pr h (rep_mem G.pnu G.pnc hz)]
  by_cases hzc : z = c
  · subst hzc; rw [rep_c, G.lc, Finset.erase_idem]
  · rw [rep_of_ne hzc]

theorem Gad.edge_anc (G : Gad Φ X u c p t) {a b : Fin (contract X u c p t h).n}
    (hab : (a, b) ∈ (contract X u c p t h).edges) : X.Anc (kE X u c a).1 (kE X u c b).1 := by
  rcases (mem_contract_edges a b).1 hab with he | ⟨hp, he⟩
  · exact Relation.ReflTransGen.single he
  · rw [hp]; exact (Relation.ReflTransGen.single G.edge_pc).tail he

theorem Gad.anc_map (G : Gad Φ X u c p t) {a b : Fin (contract X u c p t h).n}
    (hab : (contract X u c p t h).Anc a b) : X.Anc (kE X u c a).1 (kE X u c b).1 := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ he ih => exact ih.trans (G.edge_anc h he)

theorem Gad.acyclic (G : Gad Φ X u c p t) :
    ∀ i j, (i, j) ∈ (contract X u c p t h).edges → (contract X u c p t h).Anc j i → False := by
  intro i j hij hji
  have hX := G.anc_map h hji
  rcases (mem_contract_edges i j).1 hij with he | ⟨hp, he⟩
  · exact G.ref.1 _ _ he hX
  · rw [hp] at hX; exact G.ref.1 _ _ G.edge_pc (Relation.ReflTransGen.head he hX)

theorem Gad.anc_sink (G : Gad Φ X u c p t) : ∀ x, X.Anc x X.sink → x ≠ u →
    (contract X u c p t h).Anc (pr X u c p t h x) (contract X u c p t h).sink := by
  intro x hx
  induction hx using Relation.ReflTransGen.head_induction_on with
  | refl => intro _; rw [contract_sink]; exact Relation.ReflTransGen.refl
  | head hxy hyz ih =>
    rename_i x y
    intro hxu
    have hyu : y ≠ u := by rintro rfl; exact G.edge_to_u hxy
    refine Relation.ReflTransGen.trans ?_ (ih hyu)
    by_cases hyc : y = c
    · subst hyc
      rcases G.edge_to_c hxy with h1 | h1
      · exact absurd h1 hxu
      · subst h1; rw [pr_c h G.pnc]
    · apply Relation.ReflTransGen.single
      show (pr X u c p t h x, pr X u c p t h y) ∈ (contract X u c p t h).edges
      rw [G.edge_iff h]
      refine ⟨x, ?_, hxu, rfl⟩
      rw [kE_pr h (rep_mem G.pnu G.pnc hyu), rep_of_ne hyc]; exact hxy

theorem Gad.node {Φ' : CNF V} (G : Gad Φ X u c p t)
    (hΦ' : ∀ E ∈ Φ, E ≠ {(t, true)} → E.erase (t, false) ∈ Φ')
    (a : Fin (contract X u c p t h).n) :
    ((contract X u c p t h).parents a = ∅ ∧ (contract X u c p t h).label a ∈ Φ') ∨
    (∃ p₁ p₂, p₁ ≠ p₂ ∧ (contract X u c p t h).parents a = {p₁, p₂} ∧
      ∃ x, ResolventOn x ((contract X u c p t h).label p₁) ((contract X u c p t h).label p₂)
        ((contract X u c p t h).label a)) ∨
    (∃ q, (contract X u c p t h).parents a = {q} ∧
      (contract X u c p t h).label q ⊆ (contract X u c p t h).label a) := by
  obtain ⟨hau, hac⟩ := kE_mem X u c a
  have hpar := G.parents_contract h a
  rcases G.ref.2.2.1 (kE X u c a).1 with ⟨hp0, hl0⟩ | ⟨p₁, p₂, hne, hp12, y, hres⟩ | ⟨q, hq, _⟩
  · left
    refine ⟨by rw [hpar, hp0]; simp, ?_⟩
    rw [contract_label]
    apply hΦ' _ hl0
    intro he; exact hau (G.uniq _ (by rw [he]; simp))
  · right; left
    have e1 : (p₁, (kE X u c a).1) ∈ X.edges := by rw [← mem_parents, hp12]; simp
    have e2 : (p₂, (kE X u c a).1) ∈ X.edges := by rw [← mem_parents, hp12]; simp
    have h1u : p₁ ≠ u := by rintro rfl; exact hac (G.edge_u e1)
    have h2u : p₂ ≠ u := by rintro rfl; exact hac (G.edge_u e2)
    have hyt := G.piv _ _ _ _ hac hp12 hres
    refine ⟨pr X u c p t h p₁, pr X u c p t h p₂, ?_, by rw [hpar, hp12]; simp, y, ?_⟩
    · intro heq
      have k1 := kE_pr (t := t) h (rep_mem G.pnu G.pnc h1u)
      have k2 := kE_pr (t := t) h (rep_mem G.pnu G.pnc h2u)
      rw [heq, k2] at k1
      by_cases c1 : p₁ = c
      · subst c1
        rw [rep_c, rep_of_ne (Ne.symm hne)] at k1
        subst k1
        exact hac (G.edge_p e2)
      · by_cases c2 : p₂ = c
        · subst c2
          rw [rep_c, rep_of_ne c1] at k1
          rw [← k1] at e1
          exact hac (G.edge_p e1)
        · rw [rep_of_ne c1, rep_of_ne c2] at k1
          exact hne k1.symm
    · rw [G.label_pr h h1u, G.label_pr h h2u, contract_label]; exact res_erase hyt hres
  · exfalso; exact G.ro.2.1 _ (by unfold ProofDag.IsWeakeningNode; rw [hq]; simp)

theorem Gad.sink_label (G : Gad Φ X u c p t) :
    (contract X u c p t h).label (contract X u c p t h).sink = ∅ := by
  rw [contract_label, contract_sink, kE_pr h h]
  by_cases hs : X.sink = c
  · rw [hs, rep_c, ← G.lc, ← hs]; exact G.ref.2.2.2.2
  · rw [rep_of_ne hs, G.ref.2.2.2.2]; simp

theorem Gad.sink_cons (G : Gad Φ X u c p t) :
    (contract X u c p t h).consumers (contract X u c p t h).sink = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro b hb
  rw [mem_consumers, mem_contract_edges, contract_sink, kE_pr h h] at hb
  obtain ⟨hbu, hbc⟩ := kE_mem X u c b
  by_cases hs : X.sink = c
  · rw [hs, rep_c] at hb
    rcases hb with he | ⟨_, he⟩
    · exact hbc (G.edge_p he)
    · exact sink_ne_of_edge G.ref he hs.symm
  · rw [rep_of_ne hs] at hb
    rcases hb with he | ⟨hp, he⟩
    · exact sink_ne_of_edge G.ref he rfl
    · exact sink_ne_of_edge G.ref G.edge_pc hp.symm

theorem Gad.vars {Φ' : CNF V} (G : Gad Φ X u c p t)
    (hΦ' : ∀ E ∈ Φ, E ≠ {(t, true)} → E.erase (t, false) ∈ Φ')
    (a : Fin (contract X u c p t h).n) :
    ∀ l ∈ (contract X u c p t h).label a, l.1 ∈ vars Φ' := by
  intro l hl
  rw [contract_label, Finset.mem_erase] at hl
  obtain ⟨hlf, hl⟩ := hl
  have hlt : l.1 ≠ t := by
    intro he
    obtain ⟨v, b⟩ := l
    simp only at he; subst he
    cases b
    · exact hlf rfl
    · exact (kE_mem X u c a).1 (G.uniq _ hl)
  have hv := G.ref.2.1 _ l hl
  simp only [ReconfRes.Frozen.vars, Finset.mem_biUnion, Finset.mem_image] at hv ⊢
  obtain ⟨E, hE, l', hl', hl'1⟩ := hv
  refine ⟨E.erase (t, false), hΦ' E hE ?_, l', ?_, hl'1⟩
  · intro he; rw [he] at hl'; simp at hl'; rw [hl'] at hl'1; exact hlt hl'1.symm
  · rw [Finset.mem_erase]; refine ⟨?_, hl'⟩
    intro he; rw [he] at hl'1; exact hlt hl'1.symm

theorem Gad.width_le (G : Gad Φ X u c p t) {w : ℕ} (hw : X.width ≤ w) :
    (contract X u c p t h).width ≤ w := by
  unfold ProofDag.width
  apply Finset.sup_le
  intro i _
  rw [contract_label]
  exact le_trans Finset.card_erase_le
    (le_trans (Finset.le_sup (f := fun j => (X.label j).card) (Finset.mem_univ (kE X u c i).1)) hw)

theorem Gad.isVertex {Φ' : CNF V} {w s : ℕ} (G : Gad Φ X u c p t)
    (hΦ' : ∀ E ∈ Φ, E ≠ {(t, true)} → E.erase (t, false) ∈ Φ')
    (hw : X.width ≤ w) (hs : X.size ≤ s) : IsVertex Φ' w (s - 2) (contract X u c p t h) := by
  refine ⟨⟨G.acyclic h, G.vars h hΦ', G.node h hΦ', G.sink_cons h, G.sink_label h⟩, ?_,
    G.width_le h hw, ?_⟩
  · intro a
    have := G.anc_sink h _ (G.ro.1 (kE X u c a).1) (kE_mem X u c a).1
    rwa [pr_kE] at this
  · have := card_keep (X := X) G.ucne
    change (keep X u c).card ≤ s - 2
    change X.n ≤ s at hs
    omega

end ReconfRes.Frozen.Dev.Q427.PartA
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartA
variable {V : Type} [DecidableEq V]
/-- The contraction of a good vertex is a vertex at budget `s - 2`, over any formula `Φ'` that
contains the erased clauses of `Φ`. -/
theorem proj_isVertex {Φ Φ' : CNF V} {w s : ℕ} {t : V} {X P : ProofDag V}
    (hΦ' : ∀ E ∈ Φ, E ≠ {(t, true)} → E.erase (t, false) ∈ Φ')
    (hX : Good Φ w s t X) (hP : IsProj t X P) : IsVertex Φ' w (s - 2) P := by
  obtain ⟨u, c, p, h, hlu, hpu, huc, hpc, hpnu, rfl⟩ := hP
  obtain ⟨hcu, hparc, hpnc, hcp, htp, hlc⟩ := proj_data hX hlu huc hpc hpnu
  obtain ⟨_, huniq⟩ := unit_uniq hX hlu
  have G : Gad Φ X u c p t := ⟨hX.1.1, good_readOnce hX, hlu, hpu, huniq, hcu, hparc, hpnu, hpnc,
    hcp, htp, hlc, fun i p₁ p₂ x hi hpar hres => good_pivot hX hlu huc hi hpar hres⟩
  exact G.isVertex h hΦ' hX.1.2.2.1 hX.1.2.2.2

end ReconfRes.Frozen.Dev.Q427.PartA
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
alias proj_isVertex := ReconfRes.Frozen.Dev.Q427.PartA.proj_isVertex

alias good_of_step := ReconfRes.Frozen.Dev.Q427.PartA.good_of_step

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartB
variable {V : Type} [DecidableEq V]
/-! ## The contraction API -/
/-- The edge relation of the contraction, on original nodes. -/
def cE (X : ProofDag V) (c p : Fin X.n) (a b : Fin X.n) : Prop :=
  (a, b) ∈ X.edges ∨ (a = p ∧ (c, b) ∈ X.edges)

/-- The original node of a contracted index. -/
noncomputable def org (X : ProofDag V) (u c : Fin X.n) (i : Fin (keep X u c).card) : Fin X.n := (kE X u c i).1

/-- The contracted index of a kept node. -/
noncomputable def idx (X : ProofDag V) (u c : Fin X.n) (x : Fin X.n) (hx : x ∈ keep X u c) :
    Fin (keep X u c).card := (kE X u c).symm ⟨x, hx⟩

end ReconfRes.Frozen.Dev.Q427.PartB
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartB
variable {V : Type} [DecidableEq V]
variable {X : ProofDag V} {u c p : Fin X.n} {t : V}
theorem org_idx (x : Fin X.n) (hx : x ∈ keep X u c) : org X u c (idx X u c x hx) = x := by
  simp [org, idx]

theorem org_mem (i : Fin (keep X u c).card) : org X u c i ∈ keep X u c := (kE X u c i).2

theorem org_inj {i j : Fin (keep X u c).card} (h : org X u c i = org X u c j) : i = j :=
  (kE X u c).injective (Subtype.ext h)

theorem mem_keep {x : Fin X.n} : x ∈ keep X u c ↔ x ≠ u ∧ x ≠ c := by simp [keep]

theorem c_edges {h : rep X c p X.sink ∈ keep X u c} (i j : Fin (contract X u c p t h).n) :
    (i, j) ∈ (contract X u c p t h).edges ↔ cE X c p (org X u c i) (org X u c j) := by
  unfold contract
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem c_label {h : rep X c p X.sink ∈ keep X u c} (i : Fin (contract X u c p t h).n) :
    (contract X u c p t h).label i = (X.label (org X u c i)).erase (t, false) := rfl

theorem c_sink {h : rep X c p X.sink ∈ keep X u c} :
    org X u c (contract X u c p t h).sink = rep X c p X.sink := by
  simp [contract, org]

end ReconfRes.Frozen.Dev.Q427.PartB
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartB
variable {V : Type} [DecidableEq V]
/-! ## The tag gadget -/
/-- The facts about the tag gadget `u → c ← p` of a good vertex. -/
structure Gad (X : ProofDag V) (t : V) (u c p : Fin X.n) : Prop where
  lu : X.label u = {(t, true)}
  pu : X.parents u = ∅
  uniq : ∀ x, (t, true) ∈ X.label x → x = u
  cu : X.consumers u = {c}
  pc : X.parents c = {u, p}
  pu_ne : p ≠ u
  pc_ne : p ≠ c
  cp : X.consumers p = {c}
  lp : (t, false) ∈ X.label p
  lc : X.label c = (X.label p).erase (t, false)
  acyc : ∀ i j, (i, j) ∈ X.edges → X.Anc j i → False
  lean : X.IsLean

end ReconfRes.Frozen.Dev.Q427.PartB
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartB
variable {V : Type} [DecidableEq V]
variable {X : ProofDag V} {t : V} {u c p : Fin X.n}
theorem Gad.edge_u (G : Gad X t u c p) (x : Fin X.n) : (u, x) ∈ X.edges ↔ x = c := by
  have h := G.cu
  rw [Finset.ext_iff] at h
  simpa [ProofDag.consumers] using h x

theorem Gad.edge_p (G : Gad X t u c p) (x : Fin X.n) : (p, x) ∈ X.edges ↔ x = c := by
  have h := G.cp
  rw [Finset.ext_iff] at h
  simpa [ProofDag.consumers] using h x

theorem Gad.edge_c (G : Gad X t u c p) (x : Fin X.n) : (x, c) ∈ X.edges ↔ x = u ∨ x = p := by
  have h := G.pc
  rw [Finset.ext_iff] at h
  simpa [ProofDag.parents] using h x

theorem Gad.p_keep (G : Gad X t u c p) : p ∈ keep X u c := mem_keep.2 ⟨G.pu_ne, G.pc_ne⟩

theorem Gad.no_loop (G : Gad X t u c p) (x : Fin X.n) : (x, x) ∉ X.edges :=
  fun hx => G.acyc x x hx Relation.ReflTransGen.refl

theorem Gad.nonax (G : Gad X t u c p) {x : Fin X.n} (hxc : x ≠ c) (hx : X.parents x ≠ ∅) :
    ∃ y ∈ keep X u c, cE X c p y x := by
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.2 hx
  simp only [ProofDag.parents, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  by_cases hzu : z = u
  · subst hzu; exact absurd ((G.edge_u x).1 hz) hxc
  by_cases hzc : z = c
  · subst hzc; exact ⟨p, G.p_keep, Or.inr ⟨rfl, hz⟩⟩
  · exact ⟨z, mem_keep.2 ⟨hzu, hzc⟩, Or.inl hz⟩

theorem gad_of_proj {Φ : CNF V} {w s : ℕ} {P : ProofDag V} (hX : Good Φ w s t X)
    (hP : IsProj t X P) :
    ∃ (u c p : Fin X.n) (h : rep X c p X.sink ∈ keep X u c),
      Gad X t u c p ∧ P = contract X u c p t h := by
  obtain ⟨u, c, p, h, hu, hpu, huc, hpc, hpu', rfl⟩ := hP
  obtain ⟨u0, hu0, hpu0, huniq⟩ := good_unit hX
  have e0 : u = u0 := huniq u (by rw [hu]; simp)
  subst e0
  obtain ⟨c0, p0, hcu, hpar, hp0u, hp0c, hcp, htp, hlc, hk⟩ := good_gadget hX hu
  have ec : c = c0 := by
    have : c ∈ X.consumers u := by simp [ProofDag.consumers, huc]
    rw [hcu] at this; simpa using this
  subst ec
  have ep : p = p0 := by
    have : p ∈ X.parents c := by simp [ProofDag.parents, hpc]
    rw [hpar] at this
    simp at this; tauto
  subst ep
  exact ⟨u, c, p, h, ⟨hu, hpu, huniq, hcu, hpar, hp0u, hp0c, hcp, htp, hlc,
    hX.1.1.1, hX.1.2.1⟩, rfl⟩

end ReconfRes.Frozen.Dev.Q427.PartB
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartB
variable {V : Type} [DecidableEq V]
/-! ## Isomorphisms of contractions -/
theorem contract_iso {X Y : ProofDag V} {u c p : Fin X.n} {u' c' p' : Fin Y.n} {t : V}
    {h : rep X c p X.sink ∈ keep X u c} {h' : rep Y c' p' Y.sink ∈ keep Y u' c'}
    (f : Fin X.n → Fin Y.n) (g : Fin Y.n → Fin X.n)
    (hf : ∀ x ∈ keep X u c, f x ∈ keep Y u' c' ∧ g (f x) = x)
    (hg : ∀ y ∈ keep Y u' c', g y ∈ keep X u c ∧ f (g y) = y)
    (hl : ∀ x ∈ keep X u c, (Y.label (f x)).erase (t, false) = (X.label x).erase (t, false))
    (he : ∀ x ∈ keep X u c, ∀ y ∈ keep X u c, (cE Y c' p' (f x) (f y) ↔ cE X c p x y))
    (hs : f (rep X c p X.sink) = rep Y c' p' Y.sink) :
    (contract X u c p t h).Iso (contract Y u' c' p' t h') := by
  let e : Fin (contract X u c p t h).n ≃ Fin (contract Y u' c' p' t h').n :=
    { toFun := fun i => idx Y u' c' (f (org X u c i)) (hf _ (org_mem i)).1
      invFun := fun j => idx X u c (g (org Y u' c' j)) (hg _ (org_mem j)).1
      left_inv := fun i => by
        apply org_inj; simp only [org_idx]; exact (hf _ (org_mem i)).2
      right_inv := fun j => by
        apply org_inj; simp only [org_idx]; exact (hg _ (org_mem j)).2 }
  have eapp : ∀ i, org Y u' c' (e i) = f (org X u c i) := fun i => org_idx _ _
  refine ⟨e, fun i => ?_, fun i j => ?_, ?_⟩
  · rw [c_label, c_label, eapp]
    exact hl _ (org_mem i)
  · rw [c_edges, c_edges, eapp, eapp]
    exact he _ (org_mem i) _ (org_mem j)
  · apply org_inj
    rw [eapp, c_sink, c_sink]
    exact hs

theorem proj_iso {Φ : CNF V} {w s : ℕ} {t : V} {X Y P Q : ProofDag V}
    (hX : Good Φ w s t X) (hY : Good Φ w s t Y) (h : X.Iso Y)
    (hP : IsProj t X P) (hQ : IsProj t Y Q) : P.Iso Q := by
  obtain ⟨u, c, p, hh, G, rfl⟩ := gad_of_proj hX hP
  obtain ⟨u', c', p', hh', G', rfl⟩ := gad_of_proj hY hQ
  obtain ⟨e, hel, hee, hes⟩ := h
  have eu : e u = u' := G'.uniq _ (by rw [hel, G.lu]; simp)
  have ec : e c = c' := by
    rw [← G'.edge_u, ← eu, hee, G.edge_u]
  have ep : e p = p' := by
    have h1 : (e p, c') ∈ Y.edges := by
      rw [← ec, hee, G.edge_c]; exact Or.inr rfl
    rcases (G'.edge_c _).1 h1 with h2 | h2
    · exact absurd (e.injective (h2.trans eu.symm)) G.pu_ne
    · exact h2
  refine contract_iso e e.symm (fun x hx => ?_) (fun y hy => ?_) (fun x _ => by rw [hel])
    (fun x _ y _ => ?_) ?_
  · rw [mem_keep] at hx ⊢
    refine ⟨⟨?_, ?_⟩, e.symm_apply_apply x⟩
    · rw [← eu]; exact fun h => hx.1 (e.injective h)
    · rw [← ec]; exact fun h => hx.2 (e.injective h)
  · rw [mem_keep] at hy ⊢
    refine ⟨⟨?_, ?_⟩, e.apply_symm_apply y⟩
    · intro h; apply hy.1; rw [← eu, ← h]; simp
    · intro h; apply hy.2; rw [← ec, ← h]; simp
  · simp only [cE, ← ep, ← ec, hee, e.injective.eq_iff]
  · rw [← hes]
    simp only [rep]
    by_cases hs : X.sink = c
    · rw [if_pos hs, if_pos (by rw [hs, ec]), ep]
    · rw [if_neg hs, if_neg (by rw [← ec]; exact fun h => hs (e.injective h))]

end ReconfRes.Frozen.Dev.Q427.PartB
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
/-! ## Part B: frozen steps project to frozen steps -/
alias proj_iso := ReconfRes.Frozen.Dev.Q427.PartB.proj_iso

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartB
variable {V : Type} [DecidableEq V]
/-! ## Frozen moves of contractions -/
theorem mem_inputs {R : ProofDag V} {Q : Finset (Fin R.n)} {x : Fin R.n} :
    x ∈ R.inputs Q ↔ x ∉ Q ∧ ∃ j ∈ Q, (x, j) ∈ R.edges := by
  simp [ProofDag.inputs]

theorem mem_consumers {R : ProofDag V} {i j : Fin R.n} : j ∈ R.consumers i ↔ (i, j) ∈ R.edges := by
  simp [ProofDag.consumers]

theorem mem_parents {R : ProofDag V} {i j : Fin R.n} : j ∈ R.parents i ↔ (j, i) ∈ R.edges := by
  simp [ProofDag.parents]

/-- Paths inside `S` in the contraction, on original nodes. -/
def KAnc (X : ProofDag V) (c p : Fin X.n) (S : Finset (Fin X.n)) (x y : Fin X.n) : Prop :=
  Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ cE X c p a b) x y

/-- A block of the contraction, described on original nodes. -/
structure KBlock (X : ProofDag V) (u c p : Fin X.n) (k : ℕ) (S : Finset (Fin X.n))
    (r : Fin X.n) : Prop where
  sub : S ⊆ keep X u c
  card : S.card ≤ k
  mem : r ∈ S
  anc : ∀ x ∈ S, KAnc X c p S x r
  clos : ∀ x ∈ S, x ≠ r → ∀ y ∈ keep X u c, cE X c p x y → y ∈ S
  nonax : ∀ x ∈ S, ∃ y ∈ keep X u c, cE X c p y x

/-- The contracted indices of a set of kept nodes. -/
noncomputable def bset (X : ProofDag V) (u c p : Fin X.n) (t : V)
    (h : rep X c p X.sink ∈ keep X u c) (S : Finset (Fin X.n)) :
    Finset (Fin (contract X u c p t h).n) := by
  classical
  exact Finset.univ.filter fun i : Fin (contract X u c p t h).n => org X u c i ∈ S

/-- The contracted index of a kept node, typed for the contraction. -/
noncomputable def idxC (X : ProofDag V) (u c p : Fin X.n) (t : V)
    (h : rep X c p X.sink ∈ keep X u c) (x : Fin X.n) (hx : x ∈ keep X u c) :
    Fin (contract X u c p t h).n := (kE X u c).symm ⟨x, hx⟩

end ReconfRes.Frozen.Dev.Q427.PartB
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartB
variable {V : Type} [DecidableEq V]
variable {X : ProofDag V} {u c p : Fin X.n} {t : V}
theorem mem_bset {h : rep X c p X.sink ∈ keep X u c} {S : Finset (Fin X.n)}
    {i : Fin (contract X u c p t h).n} :
    i ∈ bset X u c p t h S ↔ org X u c i ∈ S := by
  simp [bset]

theorem org_idxC {h : rep X c p X.sink ∈ keep X u c} (x : Fin X.n) (hx : x ∈ keep X u c) :
    org X u c (idxC X u c p t h x hx) = x := by
  simp [org, idxC]

theorem kanc_to {h : rep X c p X.sink ∈ keep X u c}
    {S : Finset (Fin X.n)} (hS : S ⊆ keep X u c) {x y : Fin X.n} (H : KAnc X c p S x y) :
    ∀ i j : Fin (contract X u c p t h).n, org X u c i = x → org X u c j = y →
      (contract X u c p t h).AncIn (bset X u c p t h S) i j := by
  induction H with
  | refl =>
    intro i j hi hj
    rw [org_inj (hi.trans hj.symm)]
    exact Relation.ReflTransGen.refl
  | @tail b y' _ hst ih =>
    intro i j hi hj
    obtain ⟨hb, hy, he⟩ := hst
    refine Relation.ReflTransGen.tail (ih i (idxC X u c p t h b (hS hb)) hi (org_idxC _ _))
      ⟨mem_bset.2 (by rw [org_idxC]; exact hb), mem_bset.2 (by rw [hj]; exact hy),
        (c_edges _ _).2 (by rw [org_idxC, hj]; exact he)⟩

theorem kblock_to {h : rep X c p X.sink ∈ keep X u c} {k : ℕ} {S : Finset (Fin X.n)}
    {r : Fin X.n} (B : KBlock X u c p k S r) :
    (contract X u c p t h).IsBlock k (bset X u c p t h S) (idxC X u c p t h r (B.sub B.mem)) ∧
    ∀ i ∈ bset X u c p t h S, ¬ (contract X u c p t h).IsAxiomNode i := by
  refine ⟨⟨?_, ⟨?_, fun i hi => ?_⟩, fun i hi hne => ?_⟩, fun i hi => ?_⟩
  · calc _ ≤ (bset X u c p t h S).card := Finset.card_filter_le _ _
      _ ≤ S.card := Finset.card_le_card_of_injOn (org X u c) (fun i hi => mem_bset.1 hi)
          (fun i _ j _ e => org_inj e)
      _ ≤ k := B.card
  · exact mem_bset.2 (by rw [org_idxC]; exact B.mem)
  · exact kanc_to B.sub (B.anc _ (mem_bset.1 hi)) i _ rfl (org_idxC _ _)
  · intro j hj
    rw [mem_consumers, c_edges] at hj
    refine mem_bset.2 (B.clos _ (mem_bset.1 hi) (fun e => hne (org_inj (by rw [e, org_idxC]))) _
      (org_mem j) hj)
  · intro hax
    obtain ⟨y, hy, he⟩ := B.nonax _ (mem_bset.1 hi)
    have : idxC X u c p t h y hy ∈ (contract X u c p t h).parents i := by
      exact mem_parents.2 ((c_edges _ _).2 (by rw [org_idxC]; exact he))
    unfold ProofDag.IsAxiomNode at hax
    rw [hax] at this
    simp at this

end ReconfRes.Frozen.Dev.Q427.PartB
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartB
variable {V : Type} [DecidableEq V]
set_option maxHeartbeats 400000 in
theorem contract_move {X Y : ProofDag V} {u c p : Fin X.n} {u' c' p' : Fin Y.n} {t : V}
    {h : rep X c p X.sink ∈ keep X u c} {h' : rep Y c' p' Y.sink ∈ keep Y u' c'} {k : ℕ}
    {S : Finset (Fin X.n)} {S' : Finset (Fin Y.n)} {r : Fin X.n} {r' : Fin Y.n}
    (f : Fin X.n → Fin Y.n) (g : Fin Y.n → Fin X.n)
    (B1 : KBlock X u c p k S r) (B2 : KBlock Y u' c' p' k S' r')
    (hf : ∀ x ∈ keep X u c, x ∉ S → f x ∈ keep Y u' c' ∧ f x ∉ S' ∧ g (f x) = x)
    (hg : ∀ y ∈ keep Y u' c', y ∉ S' → g y ∈ keep X u c ∧ g y ∉ S ∧ f (g y) = y)
    (hlq : (Y.label r').erase (t, false) = (X.label r).erase (t, false))
    (hl : ∀ x ∈ keep X u c, x ∉ S →
      (Y.label (f x)).erase (t, false) = (X.label x).erase (t, false))
    (he : ∀ x ∈ keep X u c, x ∉ S → ∀ y ∈ keep X u c, y ∉ S →
      (cE Y c' p' (f x) (f y) ↔ cE X c p x y))
    (hin : ∀ x ∈ keep X u c, x ∉ S → ∀ y ∈ S', cE Y c' p' (f x) y → ∃ z ∈ S, cE X c p x z)
    (hout : ∀ x ∈ keep X u c, x ∉ S → (cE Y c' p' r' (f x) ↔ cE X c p r x))
    (hsk : rep X c p X.sink ∉ S → f (rep X c p X.sink) = rep Y c' p' Y.sink)
    (hsk2 : rep X c p X.sink ∈ S → rep X c p X.sink = r ∧ rep Y c' p' Y.sink = r') :
    FrozenMove k (contract X u c p t h) (contract Y u' c' p' t h') := by
  obtain ⟨b1, f1⟩ := kblock_to (t := t) (h := h) B1
  obtain ⟨b2, f2⟩ := kblock_to (t := t) (h := h') B2
  have nS : ∀ i : {i : Fin (contract X u c p t h).n // i ∉ bset X u c p t h S}, org X u c i.1 ∉ S :=
    fun i hh => i.2 (mem_bset.2 hh)
  have nS' : ∀ j : {j : Fin (contract Y u' c' p' t h').n // j ∉ bset Y u' c' p' t h' S'},
      org Y u' c' j.1 ∉ S' :=
    fun j hh => j.2 (mem_bset.2 hh)
  let ψ : {i : Fin (contract X u c p t h).n // i ∉ bset X u c p t h S} ≃
      {j : Fin (contract Y u' c' p' t h').n // j ∉ bset Y u' c' p' t h' S'} :=
    { toFun := fun i => ⟨idxC Y u' c' p' t h' (f (org X u c i.1)) (hf _ (org_mem _) (nS i)).1, by
          intro hh; have := mem_bset.1 hh; rw [org_idxC] at this
          exact (hf _ (org_mem _) (nS i)).2.1 this⟩
      invFun := fun j => ⟨idxC X u c p t h (g (org Y u' c' j.1)) (hg _ (org_mem _) (nS' j)).1, by
          intro hh; have := mem_bset.1 hh; rw [org_idxC] at this
          exact (hg _ (org_mem _) (nS' j)).2.1 this⟩
      left_inv := fun i => by
        apply Subtype.ext; apply org_inj; simp only [org_idxC]
        exact (hf _ (org_mem _) (nS i)).2.2
      right_inv := fun j => by
        apply Subtype.ext; apply org_inj; simp only [org_idxC]
        exact (hg _ (org_mem _) (nS' j)).2.2 }
  have ψapp : ∀ i, org Y u' c' (ψ i).1 = f (org X u c i.1) := fun i =>
    org_idxC (p := p') (t := t) (h := h') _ _
  refine ⟨bset X u c p t h S, bset Y u' c' p' t h' S', ψ, ⟨idxC X u c p t h r (B1.sub B1.mem),
    idxC Y u' c' p' t h' r' (B2.sub B2.mem), b1, b2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, f1, f2⟩
  · rw [c_label, c_label, org_idxC, org_idxC]; exact hlq
  · intro i; rw [c_label, c_label, ψapp]; exact hl _ (org_mem _) (nS i)
  · intro i j; rw [c_edges, c_edges, ψapp, ψapp]
    exact he _ (org_mem _) (nS i) _ (org_mem _) (nS j)
  · intro i j hj hij
    rw [c_edges, ψapp] at hij
    obtain ⟨z, hz, hcz⟩ := hin _ (org_mem _) (nS i) _ (mem_bset.1 hj) hij
    rw [mem_inputs]
    exact ⟨i.2, idxC X u c p t h z (B1.sub hz), mem_bset.2 (by rw [org_idxC]; exact hz),
      (c_edges _ _).2 (by rw [org_idxC]; exact hcz)⟩
  · intro i; rw [c_edges, c_edges, ψapp, org_idxC, org_idxC]; exact hout _ (org_mem _) (nS i)
  · intro hs
    apply org_inj
    rw [ψapp, c_sink, c_sink]
    exact hsk (by rw [← c_sink (t := t) (h := h)]; exact fun hh => hs (mem_bset.2 hh))
  · intro hs
    have := hsk2 (by rw [← c_sink (t := t) (h := h)]; exact mem_bset.1 hs)
    constructor
    · apply org_inj; rw [c_sink, org_idxC]; exact this.1
    · apply org_inj; rw [c_sink, org_idxC]; exact this.2

/-! ## The situation of a frozen move between good vertices -/
/-- A frozen move `X → Y` with blocks `Q`, `Q'`, outputs `q`, `q'`, the identification `f`
(inverse `g`) outside the blocks, and the tag gadgets on both sides. -/
structure Sit (k : ℕ) (X Y : ProofDag V) (t : V) (u c p : Fin X.n) (u' c' p' : Fin Y.n)
    (Q : Finset (Fin X.n)) (Q' : Finset (Fin Y.n)) (f : Fin X.n → Fin Y.n)
    (g : Fin Y.n → Fin X.n) (q : Fin X.n) (q' : Fin Y.n) : Prop where
  gX : Gad X t u c p
  gY : Gad Y t u' c' p'
  bX : X.IsBlock k Q q
  bY : Y.IsBlock k Q' q'
  lq : Y.label q' = X.label q
  fQ : ∀ x, x ∉ Q → f x ∉ Q'
  gf : ∀ x, x ∉ Q → g (f x) = x
  gQ : ∀ y, y ∉ Q' → g y ∉ Q
  fg : ∀ y, y ∉ Q' → f (g y) = y
  lab : ∀ x, x ∉ Q → Y.label (f x) = X.label x
  edg : ∀ x y, x ∉ Q → y ∉ Q → ((f x, f y) ∈ Y.edges ↔ (x, y) ∈ X.edges)
  inp : ∀ x, x ∉ Q → ∀ y ∈ Q', (f x, y) ∈ Y.edges → x ∈ X.inputs Q
  inp' : ∀ y, y ∉ Q' → ∀ x ∈ Q, (g y, x) ∈ X.edges → y ∈ Y.inputs Q'
  out : ∀ x, x ∉ Q → ((q', f x) ∈ Y.edges ↔ (q, x) ∈ X.edges)
  snk : X.sink ∉ Q → f X.sink = Y.sink
  snk2 : X.sink ∈ Q → X.sink = q ∧ Y.sink = q'
  frX : ∀ i ∈ Q, ¬ X.IsAxiomNode i
  frY : ∀ j ∈ Q', ¬ Y.IsAxiomNode j
  card : Q'.card = Q.card

end ReconfRes.Frozen.Dev.Q427.PartB
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartB
variable {V : Type} [DecidableEq V]
variable {k : ℕ} {X Y : ProofDag V} {t : V} {u c p : Fin X.n} {u' c' p' : Fin Y.n}
  {Q : Finset (Fin X.n)} {Q' : Finset (Fin Y.n)} {f : Fin X.n → Fin Y.n}
  {g : Fin Y.n → Fin X.n} {q : Fin X.n} {q' : Fin Y.n}
theorem Sit.symm (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') :
    Sit k Y X t u' c' p' u c p Q' Q g f q' q where
  gX := S.gY
  gY := S.gX
  bX := S.bY
  bY := S.bX
  lq := S.lq.symm
  fQ := S.gQ
  gf := S.fg
  gQ := S.fQ
  fg := S.gf
  lab := fun y hy => by rw [← S.lab _ (S.gQ y hy), S.fg y hy]
  edg := fun x y hx hy => by rw [← S.edg _ _ (S.gQ x hx) (S.gQ y hy), S.fg x hx, S.fg y hy]
  inp := S.inp'
  inp' := S.inp
  out := fun y hy => by rw [← S.out _ (S.gQ y hy), S.fg y hy]
  snk := fun hs => by
    have h1 : X.sink ∉ Q := fun h => hs (by rw [(S.snk2 h).2]; exact S.bY.2.1.1)
    rw [← S.snk h1, S.gf _ h1]
  snk2 := fun hs => by
    have h1 : X.sink ∈ Q := by
      by_contra h1; exact S.fQ _ h1 (by rw [S.snk h1]; exact hs)
    exact ⟨(S.snk2 h1).2, (S.snk2 h1).1⟩
  frX := S.frY
  frY := S.frX
  card := S.card.symm

theorem Sit.u_nQ (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') : u ∉ Q :=
  fun h => S.frX u h S.gX.pu

theorem Sit.q_mem (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') : q ∈ Q := S.bX.2.1.1

theorem Sit.fu (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') : f u = u' :=
  S.gY.uniq _ (by rw [S.lab _ S.u_nQ, S.gX.lu]; simp)

theorem Sit.finj (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') {x y : Fin X.n} (hx : x ∉ Q)
    (hy : y ∉ Q) (e : f x = f y) : x = y := by
  rw [← S.gf x hx, ← S.gf y hy, e]

theorem Sit.fc (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∉ Q) : f c = c' := by
  rw [← S.gY.edge_u, ← S.fu, S.edg _ _ S.u_nQ hc, S.gX.edge_u]

theorem Sit.cQ (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∈ Q) : c' ∈ Q' := by
  by_contra h
  have h1 := S.gQ _ h
  have h2 : (f u, f (g c')) ∈ Y.edges := by rw [S.fu, S.fg _ h, S.gY.edge_u]
  rw [S.edg _ _ S.u_nQ h1, S.gX.edge_u] at h2
  exact h1 (h2 ▸ hc)

theorem Sit.keep_f (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') {x : Fin X.n}
    (hx : x ∈ keep X u c) (hxQ : x ∉ Q) : f x ∈ keep Y u' c' := by
  rw [mem_keep] at hx ⊢
  refine ⟨fun h => hx.1 (S.finj hxQ S.u_nQ (h.trans S.fu.symm)), fun h => ?_⟩
  by_cases hc : c ∈ Q
  · exact S.fQ x hxQ (h ▸ S.cQ hc)
  · exact hx.2 (S.finj hxQ hc (h.trans (S.fc hc).symm))

theorem blk_card {R : ProofDag V} {k : ℕ} {Q : Finset (Fin R.n)} {q : Fin R.n}
    (b : R.IsBlock k Q q) (fr : ∀ i ∈ Q, ¬ R.IsAxiomNode i) : Q.card ≤ k := by
  have : Q.filter (fun i => (R.parents i).Nonempty) = Q :=
    Finset.filter_true_of_mem (fun i hi => Finset.nonempty_iff_ne_empty.2 (fr i hi))
  rw [← this]; exact b.1

theorem kanc_of_ancIn {X : ProofDag V} {c p : Fin X.n} {Q : Finset (Fin X.n)} {x y : Fin X.n}
    (H : X.AncIn Q x y) : KAnc X c p Q x y := by
  induction H with
  | refl => exact .refl
  | tail _ hab ih => exact ih.tail ⟨hab.1, hab.2.1, Or.inl hab.2.2⟩

/-! ### Case (a): `c ∉ Q` -/
theorem Sit.a_fp (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∉ Q) (hp : p ∉ Q) :
    f p = p' := by
  have h1 : (f p, c') ∈ Y.edges := by
    rw [← S.fc hc, S.edg _ _ hp hc, S.gX.edge_c]; exact Or.inr rfl
  rcases (S.gY.edge_c _).1 h1 with h2 | h2
  · exact absurd (S.finj hp S.u_nQ (h2.trans S.fu.symm)) S.gX.pu_ne
  · exact h2

theorem Sit.a_pq (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∉ Q) (hp : p ∈ Q) :
    p = q := by
  by_contra hne
  exact hc (S.bX.2.2 p hp hne (mem_consumers.2 ((S.gX.edge_p c).2 rfl)))

theorem Sit.a_pq' (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∉ Q) (hp : p ∈ Q) :
    p' = q' := by
  have h1 : (q', f c) ∈ Y.edges := by rw [S.out _ hc, ← S.a_pq hc hp, S.gX.edge_p]
  rw [S.fc hc, S.gY.edge_c] at h1
  rcases h1 with h | h
  · exact absurd (h ▸ S.bY.2.1.1) S.symm.u_nQ
  · exact h.symm

theorem Sit.a_pQ (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∉ Q) :
    p ∈ Q ↔ p' ∈ Q' := by
  constructor
  · intro hp; rw [S.a_pq' hc hp]; exact S.bY.2.1.1
  · intro hp; by_contra h; exact S.fQ _ h (by rw [S.a_fp hc h]; exact hp)

theorem Sit.a_fp_iff (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∉ Q) {x : Fin X.n}
    (hx : x ∉ Q) : f x = p' ↔ x = p := by
  by_cases hp : p ∈ Q
  · constructor
    · intro h; exact absurd (by rw [h]; exact (S.a_pQ hc).1 hp) (S.fQ x hx)
    · intro h; exact absurd (by rw [h] at hx; exact hp) (by rw [h] at hx; exact hx)
  · rw [← S.a_fp hc hp]; exact ⟨S.finj hx hp, fun h => h ▸ rfl⟩

theorem Sit.a_qp (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∉ Q) :
    q' = p' ↔ q = p := by
  by_cases hp : p ∈ Q
  · exact ⟨fun _ => (S.a_pq hc hp).symm, fun _ => (S.a_pq' hc hp).symm⟩
  · constructor
    · intro h; exact absurd (h ▸ S.bY.2.1.1) (fun h' => hp ((S.a_pQ hc).2 h'))
    · intro h; exact absurd (h ▸ S.q_mem) hp

theorem Sit.a_block (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∉ Q) :
    KBlock X u c p k Q q where
  sub := fun x hx => mem_keep.2 ⟨fun e => S.u_nQ (e ▸ hx), fun e => hc (e ▸ hx)⟩
  card := blk_card S.bX S.frX
  mem := S.q_mem
  anc := fun x hx => kanc_of_ancIn (S.bX.2.1.2 x hx)
  clos := fun x hx hne y hy hxy => by
    rcases hxy with he | ⟨rfl, he⟩
    · exact S.bX.2.2 x hx hne (mem_consumers.2 he)
    · exact absurd (S.a_pq hc hx) hne
  nonax := fun x hx => S.gX.nonax (fun e => hc (e ▸ hx)) (S.frX x hx)

theorem case_a (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∉ Q)
    {h : rep X c p X.sink ∈ keep X u c} {h' : rep Y c' p' Y.sink ∈ keep Y u' c'} :
    FrozenMove k (contract X u c p t h) (contract Y u' c' p' t h') := by
  have hc' : c' ∉ Q' := fun h => hc (S.symm.cQ h)
  refine contract_move f g (S.a_block hc) (S.symm.a_block hc')
    (fun x hx hxQ => ⟨S.keep_f hx hxQ, S.fQ x hxQ, S.gf x hxQ⟩)
    (fun y hy hyQ => ⟨S.symm.keep_f hy hyQ, S.gQ y hyQ, S.fg y hyQ⟩)
    (by rw [S.lq]) (fun x _ hx => by rw [S.lab x hx]) ?_ ?_ ?_ ?_ ?_
  · intro x _ hx y _ hy
    unfold cE
    rw [S.edg _ _ hx hy, ← S.fc hc, S.edg _ _ hc hy, S.a_fp_iff hc hx]
  · intro x _ hx y hy hxy
    rcases hxy with h1 | ⟨h1, h2⟩
    · obtain ⟨-, z, hz, hz'⟩ := mem_inputs.1 (S.inp x hx y hy h1)
      exact ⟨z, hz, Or.inl hz'⟩
    · have hxp := (S.a_fp_iff hc hx).1 h1
      rw [← S.fc hc] at h2
      obtain ⟨-, z, hz, hz'⟩ := mem_inputs.1 (S.inp c hc y hy h2)
      exact ⟨z, hz, Or.inr ⟨hxp, hz'⟩⟩
  · intro x _ hx
    unfold cE
    rw [S.out x hx, ← S.fc hc, S.edg _ _ hc hx, S.a_qp hc]
  · intro hs
    simp only [rep] at hs ⊢
    by_cases hsc : X.sink = c
    · rw [if_pos hsc] at hs ⊢
      have e1 := S.snk (hsc ▸ hc)
      rw [hsc, S.fc hc] at e1
      rw [if_pos e1.symm, S.a_fp hc hs]
    · rw [if_neg hsc] at hs ⊢
      have e1 := S.snk hs
      have e2 : Y.sink ≠ c' := by
        intro e; rw [← e1, ← S.fc hc] at e; exact hsc (S.finj hs hc e)
      rw [if_neg e2, e1]
  · intro hs
    simp only [rep] at hs ⊢
    by_cases hsc : X.sink = c
    · rw [if_pos hsc] at hs ⊢
      have e1 := S.snk (hsc ▸ hc)
      rw [hsc, S.fc hc] at e1
      rw [if_pos e1.symm]
      exact ⟨S.a_pq hc hs, S.a_pq' hc hs⟩
    · rw [if_neg hsc] at hs ⊢
      obtain ⟨h1, h2⟩ := S.snk2 hs
      have e2 : Y.sink ≠ c' := by
        intro e; rw [e] at h2; exact hc' (h2 ▸ S.bY.2.1.1)
      rw [if_neg e2]
      exact ⟨h1, h2⟩

/-! ### Case (b): `Q = {c}` -/
theorem Sit.b_fp (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hQ : Q = {c})
    (hQ' : Q' = {c'}) : f p = p' := by
  have hp' : p' ∉ Q' := by rw [hQ', Finset.mem_singleton]; exact S.gY.pc_ne
  have h1 : (f (g p'), c') ∈ Y.edges := by rw [S.fg _ hp', S.gY.edge_c]; exact Or.inr rfl
  have h2 := S.inp _ (S.gQ _ hp') c' (by rw [hQ']; simp) h1
  obtain ⟨-, z, hz, hz'⟩ := mem_inputs.1 h2
  rw [hQ, Finset.mem_singleton] at hz
  rw [hz] at hz'
  rcases (S.gX.edge_c _).1 hz' with h3 | h3
  · exfalso; apply S.gY.pu_ne; rw [← S.fg _ hp', h3, S.fu]
  · rw [← h3, S.fg _ hp']

theorem case_b (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∈ Q) (h1 : Q.card = 1)
    {h : rep X c p X.sink ∈ keep X u c} {h' : rep Y c' p' Y.sink ∈ keep Y u' c'} :
    (contract X u c p t h).Iso (contract Y u' c' p' t h') := by
  have hQ : Q = {c} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
    rw [ha] at hc ⊢; rw [Finset.mem_singleton.1 hc]
  have hc' := S.cQ hc
  have hQ' : Q' = {c'} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (S.card.trans h1)
    rw [ha] at hc' ⊢; rw [Finset.mem_singleton.1 hc']
  have hq : q = c := by
    have := S.q_mem; rw [hQ] at this; exact Finset.mem_singleton.1 this
  have hq' : q' = c' := by
    have := S.bY.2.1.1; rw [hQ'] at this; exact Finset.mem_singleton.1 this
  have nQ : ∀ x ∈ keep X u c, x ∉ Q := fun x hx => by
    rw [hQ, Finset.mem_singleton]; exact (mem_keep.1 hx).2
  have nQ' : ∀ y ∈ keep Y u' c', y ∉ Q' := fun y hy => by
    rw [hQ', Finset.mem_singleton]; exact (mem_keep.1 hy).2
  have hpQ : p ∉ Q := nQ p S.gX.p_keep
  have fp := S.b_fp hQ hQ'
  refine contract_iso f g (fun x hx => ⟨S.keep_f hx (nQ x hx), S.gf x (nQ x hx)⟩)
    (fun y hy => ⟨S.symm.keep_f hy (nQ' y hy), S.fg y (nQ' y hy)⟩)
    (fun x hx => by rw [S.lab x (nQ x hx)]) (fun x hx y hy => ?_) ?_
  · unfold cE
    rw [S.edg _ _ (nQ x hx) (nQ y hy), ← hq', S.out y (nQ y hy), hq, ← fp]
    rw [show f x = f p ↔ x = p from ⟨S.finj (nQ x hx) hpQ, fun e => e ▸ rfl⟩]
  · simp only [rep]
    by_cases hsc : X.sink = c
    · have : Y.sink = c' := by rw [← hq']; exact (S.snk2 (by rw [hsc]; exact hc)).2
      rw [if_pos hsc, if_pos this, fp]
    · have hs : X.sink ∉ Q := by rw [hQ, Finset.mem_singleton]; exact hsc
      have e1 := S.snk hs
      have : Y.sink ≠ c' := by
        rw [← e1]; intro e; exact S.fQ _ hs (by rw [e]; exact hc')
      rw [if_neg hsc, if_neg this, e1]

/-! ### Case (c): `c ∈ Q`, `|Q| ≥ 2` -/
theorem Gad.rep_label (G : Gad X t u c p) (x : Fin X.n) :
    (X.label (rep X c p x)).erase (t, false) = (X.label x).erase (t, false) := by
  unfold rep; split_ifs with hx
  · rw [hx, G.lc, Finset.erase_idem]
  · rfl

theorem Sit.c_pQ (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∈ Q)
    (h2 : 2 ≤ Q.card) (hq : q = c) : p ∈ Q := by
  obtain ⟨x, hx, hxc⟩ := Finset.exists_mem_ne (by omega : 1 < Q.card) c
  have H := S.bX.2.1.2 x hx
  rw [hq] at H
  rcases Relation.ReflTransGen.cases_tail H with e | ⟨y, -, hy1, -, hy3⟩
  · exact absurd e.symm hxc
  · rcases (S.gX.edge_c y).1 hy3 with e | e
    · exact absurd (e ▸ hy1) S.u_nQ
    · exact e ▸ hy1

theorem Sit.c_path (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') {x z : Fin X.n}
    (hxc : x ≠ c) (H : X.AncIn Q x z) :
    (z ≠ c → KAnc X c p (Q.erase c) x z) ∧ (z = c → p ∈ Q ∧ KAnc X c p (Q.erase c) x p) := by
  induction H with
  | refl => exact ⟨fun _ => .refl, fun e => absurd e hxc⟩
  | @tail b z' _ st ih =>
    obtain ⟨hb, hz, he⟩ := st
    constructor
    · intro hzc
      by_cases hbc : b = c
      · obtain ⟨hpQ, hk⟩ := ih.2 hbc
        rw [hbc] at he
        exact hk.tail ⟨Finset.mem_erase.2 ⟨S.gX.pc_ne, hpQ⟩, Finset.mem_erase.2 ⟨hzc, hz⟩,
          Or.inr ⟨rfl, he⟩⟩
      · exact (ih.1 hbc).tail ⟨Finset.mem_erase.2 ⟨hbc, hb⟩, Finset.mem_erase.2 ⟨hzc, hz⟩,
          Or.inl he⟩
    · intro hzc
      by_cases hbc : b = c
      · exact ih.2 hbc
      · rw [hzc] at he
        rcases (S.gX.edge_c b).1 he with e | e
        · exact absurd (e ▸ hb) S.u_nQ
        · refine ⟨e ▸ hb, ?_⟩
          have := ih.1 hbc; rwa [e] at this

theorem Sit.c_block (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∈ Q)
    (h2 : 2 ≤ Q.card) : KBlock X u c p k (Q.erase c) (rep X c p q) where
  sub := fun x hx => by
    obtain ⟨hxc, hxQ⟩ := Finset.mem_erase.1 hx
    exact mem_keep.2 ⟨fun e => S.u_nQ (e ▸ hxQ), hxc⟩
  card := le_trans Finset.card_erase_le (blk_card S.bX S.frX)
  mem := by
    unfold rep; split_ifs with hq
    · exact Finset.mem_erase.2 ⟨S.gX.pc_ne, S.c_pQ hc h2 hq⟩
    · exact Finset.mem_erase.2 ⟨hq, S.q_mem⟩
  anc := fun x hx => by
    obtain ⟨hxc, hxQ⟩ := Finset.mem_erase.1 hx
    have H := S.c_path hxc (S.bX.2.1.2 x hxQ)
    unfold rep; split_ifs with hq
    · exact (H.2 hq).2
    · exact H.1 hq
  clos := fun x hx hne y hy hxy => by
    obtain ⟨hxc, hxQ⟩ := Finset.mem_erase.1 hx
    refine Finset.mem_erase.2 ⟨(mem_keep.1 hy).2, ?_⟩
    rcases hxy with he | ⟨hxp, he⟩
    · have hxq : x ≠ q := by
        intro e; apply hne; unfold rep
        rw [if_neg (by rw [← e]; exact hxc)]; exact e
      exact S.bX.2.2 x hxQ hxq (mem_consumers.2 he)
    · have hcq : c ≠ q := by
        intro e; apply hne; unfold rep; rw [if_pos e.symm]; exact hxp
      exact S.bX.2.2 c hc hcq (mem_consumers.2 he)
  nonax := fun x hx => S.gX.nonax (Finset.mem_erase.1 hx).1 (S.frX x (Finset.mem_erase.1 hx).2)

theorem Sit.c_sec (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∈ Q)
    (h2 : 2 ≤ Q.card) {x y : Fin X.n} (hx : x ∉ Q) (hy : y ∉ Q) :
    ¬ (x = p ∧ (c, y) ∈ X.edges) := by
  rintro ⟨hxp, he⟩
  have hcq : c = q := by
    by_contra hne; exact hy (S.bX.2.2 c hc hne (mem_consumers.2 he))
  exact hx (hxp ▸ S.c_pQ hc h2 hcq.symm)

theorem Sit.c_inp (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∈ Q)
    (h2 : 2 ≤ Q.card) {x : Fin X.n} (hxk : x ∈ keep X u c) (hx : x ∉ Q)
    (hin : x ∈ X.inputs Q) : ∃ z ∈ Q.erase c, cE X c p x z := by
  obtain ⟨-, z, hz, hxz⟩ := mem_inputs.1 hin
  by_cases hzc : z = c
  · rw [hzc] at hxz
    have hxp : x = p := by
      rcases (S.gX.edge_c x).1 hxz with e | e
      · exact absurd e (mem_keep.1 hxk).1
      · exact e
    have hcq : c ≠ q := fun e => hx (hxp ▸ S.c_pQ hc h2 e.symm)
    have hcs : c ≠ X.sink := fun e => hcq (e.trans (S.snk2 (e ▸ hc)).1)
    rcases Relation.ReflTransGen.cases_head (S.gX.lean c) with e | ⟨z', hz', -⟩
    · exact absurd e hcs
    · have hz'Q : z' ∈ Q := S.bX.2.2 c hc hcq (mem_consumers.2 hz')
      have hz'c : z' ≠ c := fun e => S.gX.no_loop c (e ▸ hz')
      exact ⟨z', Finset.mem_erase.2 ⟨hz'c, hz'Q⟩, Or.inr ⟨hxp, hz'⟩⟩
  · exact ⟨z, Finset.mem_erase.2 ⟨hzc, hz⟩, Or.inl hxz⟩

theorem Sit.c_out (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∈ Q)
    {x : Fin X.n} (hxk : x ∈ keep X u c) (hx : x ∉ Q) :
    cE X c p (rep X c p q) x ↔ (q, x) ∈ X.edges := by
  unfold rep cE
  split_ifs with hq
  · rw [S.gX.edge_p, hq]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact absurd h (mem_keep.1 hxk).2
      · exact h
    · intro h; exact Or.inr ⟨rfl, h⟩
  · constructor
    · rintro (h | ⟨-, h⟩)
      · exact h
      · exact absurd (S.bX.2.2 c hc (Ne.symm hq) (mem_consumers.2 h)) hx
    · exact Or.inl

theorem Sit.c_sink (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∈ Q)
    (h2 : 2 ≤ Q.card) :
    (X.sink ∈ Q ↔ rep X c p X.sink ∈ Q.erase c) ∧
      (X.sink ∈ Q → rep X c p X.sink = rep X c p q) := by
  have h3 : X.sink ∈ Q → rep X c p X.sink = rep X c p q := fun hs => by rw [(S.snk2 hs).1]
  refine ⟨⟨fun hs => by rw [h3 hs]; exact (S.c_block hc h2).mem, fun hs => ?_⟩, h3⟩
  by_contra hs'
  have : X.sink ≠ c := fun e => hs' (e ▸ hc)
  unfold rep at hs; rw [if_neg this] at hs
  exact hs' (Finset.mem_of_mem_erase hs)

set_option maxHeartbeats 400000 in
theorem case_c (S : Sit k X Y t u c p u' c' p' Q Q' f g q q') (hc : c ∈ Q) (h2 : 2 ≤ Q.card)
    {h : rep X c p X.sink ∈ keep X u c} {h' : rep Y c' p' Y.sink ∈ keep Y u' c'} :
    FrozenMove k (contract X u c p t h) (contract Y u' c' p' t h') := by
  have hc' := S.cQ hc
  have h2' : 2 ≤ Q'.card := S.card ▸ h2
  have nQ : ∀ x ∈ keep X u c, x ∉ Q.erase c → x ∉ Q := fun x hx hh hxQ =>
    hh (Finset.mem_erase.2 ⟨(mem_keep.1 hx).2, hxQ⟩)
  have nQ' : ∀ y ∈ keep Y u' c', y ∉ Q'.erase c' → y ∉ Q' := fun y hy hh hyQ =>
    hh (Finset.mem_erase.2 ⟨(mem_keep.1 hy).2, hyQ⟩)
  refine contract_move f g (S.c_block hc h2) (S.symm.c_block hc' h2')
    (fun x hx hxQ => ⟨S.keep_f hx (nQ x hx hxQ),
      fun hh => S.fQ x (nQ x hx hxQ) (Finset.mem_of_mem_erase hh), S.gf x (nQ x hx hxQ)⟩)
    (fun y hy hyQ => ⟨S.symm.keep_f hy (nQ' y hy hyQ),
      fun hh => S.gQ y (nQ' y hy hyQ) (Finset.mem_of_mem_erase hh), S.fg y (nQ' y hy hyQ)⟩)
    (by rw [S.gY.rep_label, S.gX.rep_label, S.lq]) (fun x hx hxQ => by rw [S.lab x (nQ x hx hxQ)])
    ?_ ?_ ?_ ?_ ?_
  · intro x hx hxQ y hy hyQ
    have hx' := nQ x hx hxQ
    have hy' := nQ y hy hyQ
    unfold cE
    rw [S.edg _ _ hx' hy']
    have a := S.c_sec hc h2 hx' hy'
    have b := S.symm.c_sec hc' h2' (S.fQ x hx') (S.fQ y hy')
    tauto
  · intro x hx hxQ y hy hxy
    have hx' := nQ x hx hxQ
    apply S.c_inp hc h2 hx hx'
    rcases hxy with h1 | ⟨h1, h3⟩
    · exact S.inp x hx' y (Finset.mem_of_mem_erase hy) h1
    · exact S.inp x hx' c' hc' (by rw [h1, S.gY.edge_c]; exact Or.inr rfl)
  · intro x hx hxQ
    have hx' := nQ x hx hxQ
    rw [S.symm.c_out hc' (S.keep_f hx hx') (S.fQ x hx'), S.c_out hc hx hx', S.out x hx']
  · intro hs
    have hsQ : X.sink ∉ Q := fun hh => hs ((S.c_sink hc h2).1.1 hh)
    have hsc : X.sink ≠ c := fun e => hsQ (e ▸ hc)
    have e1 := S.snk hsQ
    have hsc' : Y.sink ≠ c' := fun e => S.fQ _ hsQ (by rw [e1, e]; exact hc')
    simp only [rep]
    rw [if_neg hsc, if_neg hsc', e1]
  · intro hs
    have hsQ : X.sink ∈ Q := (S.c_sink hc h2).1.2 hs
    have hY : Y.sink ∈ Q' := by rw [(S.snk2 hsQ).2]; exact S.bY.2.1.1
    exact ⟨(S.c_sink hc h2).2 hsQ, (S.symm.c_sink hc' h2').2 hY⟩

end ReconfRes.Frozen.Dev.Q427.PartB
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartB
variable {V : Type} [DecidableEq V]
/-! ## Assembly -/
/-- `φ` extended to all nodes. -/
noncomputable def ext {X Y : ProofDag V} {Q : Finset (Fin X.n)} {Q' : Finset (Fin Y.n)}
    (φ : {i // i ∉ Q} ≃ {j // j ∉ Q'}) (x : Fin X.n) : Fin Y.n :=
  if hx : x ∈ Q then Y.sink else (φ ⟨x, hx⟩).1

theorem ext_eq {X Y : ProofDag V} {Q : Finset (Fin X.n)} {Q' : Finset (Fin Y.n)}
    (φ : {i // i ∉ Q} ≃ {j // j ∉ Q'}) {x : Fin X.n} (hx : x ∉ Q) :
    ext φ x = (φ ⟨x, hx⟩).1 := by
  simp [ext, hx]

theorem sit_of_move {k : ℕ} (hk : 1 ≤ k) {Φ : CNF V} {w s : ℕ} {t : V} {X Y : ProofDag V}
    (hX : Good Φ w s t X) (hY : Good Φ w s t Y) {u c p : Fin X.n} {u' c' p' : Fin Y.n}
    (G : Gad X t u c p) (G' : Gad Y t u' c' p') {Q : Finset (Fin X.n)}
    {Q' : Finset (Fin Y.n)} {φ : {i // i ∉ Q} ≃ {j // j ∉ Q'}}
    (hm : FrozenMoveVia k X Y Q Q' φ) :
    ∃ q q', Sit k X Y t u c p u' c' p' Q Q' (ext φ) (ext φ.symm) q q' := by
  have hM : Y.axiomMultiset = X.axiomMultiset :=
    ((proposition_3_3 k hk Φ w s).1 X Y ⟨hX.1, hY.1, Or.inl ⟨Q, Q', φ, hm⟩⟩).symm
  have hcard : 1 ≤ Multiset.card X.axiomMultiset := by
    have := Multiset.count_le_card {(t, true)} X.axiomMultiset
    rw [hX.2.1] at this; exact this
  have hsX : X.size + 1 ≤ 2 * Multiset.card X.axiomMultiset :=
    le_trans (Nat.succ_le_succ hX.1.2.2.2) hX.2.2.2
  have hsY : Y.size + 1 ≤ 2 * Multiset.card X.axiomMultiset := by
    rw [← hM]; exact le_trans (Nat.succ_le_succ hY.1.2.2.2) hY.2.2.2
  obtain ⟨hc1, -, -, -, -, -, -, hrev⟩ := (lemma_3_47 Φ X.axiomMultiset hcard).2 k X Y Q Q' φ hk
    hX.1.1 hX.1.2.1 rfl hsX hY.1.1 hY.1.2.1 hM hsY hm
  obtain ⟨⟨q, q', b1, b2, hlq, hl, he, hi, ho, hs1, hs2⟩, fr1, fr2⟩ := hm
  obtain ⟨⟨_, _, -, -, -, -, -, hi', -, -, -⟩, -, -⟩ := hrev
  refine ⟨q, q', G, G', b1, b2, hlq, fun x hx => ?_, fun x hx => ?_, fun y hy => ?_,
    fun y hy => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun x hx y hy hxy => ?_,
    fun y hy x hx hxy => ?_, fun x hx => ?_, fun hs => ?_, hs2, fr1, fr2, hc1⟩
  · rw [ext_eq φ hx]; exact (φ _).2
  · rw [ext_eq φ hx, ext_eq φ.symm (φ _).2]; simp
  · rw [ext_eq φ.symm hy]; exact (φ.symm _).2
  · rw [ext_eq φ.symm hy, ext_eq φ (φ.symm _).2]; simp
  · rw [ext_eq φ hx]; exact hl ⟨x, hx⟩
  · rw [ext_eq φ hx, ext_eq φ hy]; exact he ⟨x, hx⟩ ⟨y, hy⟩
  · rw [ext_eq φ hx] at hxy; exact hi ⟨x, hx⟩ y hy hxy
  · rw [ext_eq φ.symm hy] at hxy; exact hi' ⟨y, hy⟩ x hx hxy
  · rw [ext_eq φ hx]; exact ho ⟨x, hx⟩
  · rw [ext_eq φ hs]; exact hs1 hs

theorem proj_move {k : ℕ} (hk : 1 ≤ k) {Φ : CNF V} {w s : ℕ} {t : V} {X Y P Q : ProofDag V}
    (hX : Good Φ w s t X) (hY : Good Φ w s t Y) (h : FrozenMove k X Y)
    (hP : IsProj t X P) (hQ : IsProj t Y Q) : FrozenMove k P Q ∨ P.Iso Q := by
  obtain ⟨u, c, p, hh, G, rfl⟩ := gad_of_proj hX hP
  obtain ⟨u', c', p', hh', G', rfl⟩ := gad_of_proj hY hQ
  obtain ⟨B, B', φ, hm⟩ := h
  obtain ⟨q, q', S⟩ := sit_of_move hk hX hY G G' hm
  by_cases hc : c ∈ B
  · by_cases h1 : B.card = 1
    · exact Or.inr (case_b S hc h1)
    · exact Or.inl (case_c S hc (by have := Finset.card_pos.2 ⟨c, hc⟩; omega))
  · exact Or.inl (case_a S hc)

end ReconfRes.Frozen.Dev.Q427.PartB
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
alias proj_move := ReconfRes.Frozen.Dev.Q427.PartB.proj_move

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC1
variable {V : Type} [DecidableEq V]
/-! ## Generic helpers -/
theorem mem_parents (R : ProofDag V) (i j : Fin R.n) : j ∈ R.parents i ↔ (j, i) ∈ R.edges := by
  simp [ProofDag.parents]

theorem mem_consumers (R : ProofDag V) (i j : Fin R.n) :
    j ∈ R.consumers i ↔ (i, j) ∈ R.edges := by
  simp [ProofDag.consumers]

theorem iso_symm {X Y : ProofDag V} (h : X.Iso Y) : Y.Iso X := by
  obtain ⟨e, hl, he, hs⟩ := h
  refine ⟨e.symm, fun i => ?_, fun i j => ?_, ?_⟩
  · rw [← hl (e.symm i), Equiv.apply_symm_apply]
  · rw [← he (e.symm i) (e.symm j), Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · rw [← hs, Equiv.symm_apply_apply]

end ReconfRes.Frozen.Dev.Q427.PartC1
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
/-! ## Part C: generic facts and the lift -/
alias iso_symm := ReconfRes.Frozen.Dev.Q427.PartC1.iso_symm

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC1
variable {V : Type} [DecidableEq V]
variable {X Y : ProofDag V} (e : Fin X.n ≃ Fin Y.n)
  (hl : ∀ i, Y.label (e i) = X.label i) (he : ∀ i j, (e i, e j) ∈ Y.edges ↔ (i, j) ∈ X.edges)
include he in
theorem iso_parents (i : Fin X.n) : Y.parents (e i) = (X.parents i).map e.toEmbedding := by
  ext z
  rw [mem_parents, Finset.mem_map_equiv, mem_parents, ← he, Equiv.apply_symm_apply]

include he in
theorem iso_consumers (i : Fin X.n) : Y.consumers (e i) = (X.consumers i).map e.toEmbedding := by
  ext z
  rw [mem_consumers, Finset.mem_map_equiv, mem_consumers, ← he, Equiv.apply_symm_apply]

include he in
theorem iso_anc {i j : Fin X.n} (h : X.Anc i j) : Y.Anc (e i) (e j) := by
  unfold ProofDag.Anc at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail ((he _ _).2 hs)

end ReconfRes.Frozen.Dev.Q427.PartC1
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC1
variable {V : Type} [DecidableEq V]
theorem vars_mono {F F' : CNF V} (hF : F ⊆ F') {v : V} (h : v ∈ vars F) : v ∈ vars F' := by
  unfold vars at h ⊢
  rw [Finset.mem_biUnion] at h ⊢
  obtain ⟨E, hE, hv⟩ := h
  exact ⟨E, hF hE, hv⟩

theorem iso_isVertex {F : CNF V} {w s : ℕ} {X Y : ProofDag V} (h : X.Iso Y)
    (hX : IsVertex F w s X) : IsVertex F w s Y := by
  obtain ⟨e, hl, he, hs⟩ := h
  obtain ⟨⟨hacyc, hvars, hnode, hsinkc, hsinkl⟩, hlean, hw, hsz⟩ := hX
  have hl' : ∀ i, Y.label i = X.label (e.symm i) := fun i => by
    rw [← hl (e.symm i), Equiv.apply_symm_apply]
  have hsk : Y.sink = e X.sink := hs.symm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a b hab hanc
    obtain ⟨i, rfl⟩ := e.surjective a
    obtain ⟨j, rfl⟩ := e.surjective b
    have hanc' := iso_anc e.symm (fun a b => by
      rw [← he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]) hanc
    simp only [Equiv.symm_apply_apply] at hanc'
    exact hacyc i j ((he i j).1 hab) hanc'
  · intro i l hlab
    rw [hl'] at hlab
    exact hvars _ l hlab
  · intro i
    obtain ⟨x, rfl⟩ := e.surjective i
    rw [iso_parents e he, hl]
    rcases hnode x with ⟨hp, hF⟩ | ⟨p₁, p₂, hne, hp, v, hr⟩ | ⟨p, hp, hsub⟩
    · left; rw [hp]; exact ⟨by simp, hF⟩
    · right; left
      refine ⟨e p₁, e p₂, fun h => hne (e.injective h), ?_, v, ?_⟩
      · rw [hp]; simp
      · rw [hl, hl]; exact hr
    · right; right
      refine ⟨e p, ?_, ?_⟩
      · rw [hp]; simp
      · rw [hl]; exact hsub
  · rw [hsk, iso_consumers e he, hsinkc]; simp
  · rw [hsk, hl]; exact hsinkl
  · intro i
    obtain ⟨x, rfl⟩ := e.surjective i
    rw [hsk]; exact iso_anc e he (hlean x)
  · unfold ProofDag.width
    refine Finset.sup_le fun i _ => ?_
    rw [hl']
    exact le_trans (Finset.le_sup (f := fun i => (X.label i).card) (Finset.mem_univ _)) hw
  · have : Y.n = X.n := (Fin.equiv_iff_eq.mp ⟨e⟩).symm
    unfold ProofDag.size at hsz ⊢
    omega

end ReconfRes.Frozen.Dev.Q427.PartC1
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
alias iso_isVertex := ReconfRes.Frozen.Dev.Q427.PartC1.iso_isVertex

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC1
variable {V : Type} [DecidableEq V]
theorem isVertex_mono {F F' : CNF V} (hF : F ⊆ F') {w s : ℕ} {X : ProofDag V}
    (hX : IsVertex F w s X) : IsVertex F' w s X := by
  obtain ⟨⟨hacyc, hvars, hnode, hsinkc, hsinkl⟩, hlean, hw, hsz⟩ := hX
  refine ⟨⟨hacyc, fun i l hl => vars_mono hF (hvars i l hl), fun i => ?_, hsinkc, hsinkl⟩,
    hlean, hw, hsz⟩
  rcases hnode i with ⟨hp, hFi⟩ | h | h
  · exact Or.inl ⟨hp, hF hFi⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end ReconfRes.Frozen.Dev.Q427.PartC1
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
alias isVertex_mono := ReconfRes.Frozen.Dev.Q427.PartC1.isVertex_mono

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC1
variable {V : Type} [DecidableEq V]
theorem frozenConnected_mono {k : ℕ} {F F' : CNF V} (hF : F ⊆ F') {w s : ℕ} {X Y : ProofDag V}
    (h : FrozenConnected k F w s X Y) : FrozenConnected k F' w s X Y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
    exact Relation.ReflTransGen.tail ih
      ⟨isVertex_mono hF hab.1, isVertex_mono hF hab.2.1, hab.2.2⟩

end ReconfRes.Frozen.Dev.Q427.PartC1
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
alias frozenConnected_mono := ReconfRes.Frozen.Dev.Q427.PartC1.frozenConnected_mono

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
/-- The lift of the first `j` sources only. -/
def liftFirst (R : ProofDag V) (pos : Fin α → Fin R.n) (j : ℕ) (hj : j ≤ α) : ProofDag V :=
  lift (fun i : Fin j => C (Fin.castLE hj i)) (fun i => t (Fin.castLE hj i)) R
    (fun i => pos (Fin.castLE hj i))

/-- The formula of the stage `j`: the tagged clauses of the first `j` sources, the others plain. -/
def psi (j : ℕ) (hj : j ≤ α) : CNF V :=
  tagFormula (fun i : Fin j => C (Fin.castLE hj i)) (fun i => t (Fin.castLE hj i)) ∪
    (Finset.univ.filter fun i : Fin α => j ≤ i.val).image C

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC1
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V) (R : ProofDag V) (pos : Fin α → Fin R.n)
/-! ## Lift helpers (copied from `Solutions/ReconfRes/T60.lean`) -/
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

theorem E1 (x y : Fin R.n) :
    (oN R x, oN R y) ∈ (lift C t R pos).edges ↔ (x, y) ∈ R.edges := by
  refine (mem_lift_edges C t R pos _ _).trans ?_
  constructor
  · rintro (⟨x', y', h, h1, h2⟩ | ⟨i, h1, _⟩ | ⟨i, h1, _⟩)
    · rw [oN_inj R h1, oN_inj R h2] at h; exact h
    · exact absurd h1.symm (oN_ne_dN R _ _)
    · exact absurd h1.symm (oN_ne_uN R _ _)
  · intro h; exact Or.inl ⟨x, y, h, rfl, rfl⟩

theorem lift_label_old (x : Fin R.n) : (lift C t R pos).label (oN R x) = R.label x := by
  show Fin.addCases (motive := fun _ => Clause V) R.label
    (Fin.addCases (motive := fun _ => Clause V) (tagD C t) (tagU t)) (Fin.castAdd (α + α) x) = _
  simp [Fin.addCases_left]

end ReconfRes.Frozen.Dev.Q427.PartC1
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC1
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
/-! ## Part C targets -/
theorem liftFirst_top (R : ProofDag V) (pos : Fin α → Fin R.n) :
    liftFirst C t R pos α le_rfl = lift C t R pos := by
  rfl

end ReconfRes.Frozen.Dev.Q427.PartC1
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
alias liftFirst_top := ReconfRes.Frozen.Dev.Q427.PartC1.liftFirst_top

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC1
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
theorem tagFormula_sub_psi_top : tagFormula C t ⊆ psi C t α le_rfl := by
  intro E hE
  exact Finset.mem_union_left _ hE

end ReconfRes.Frozen.Dev.Q427.PartC1
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
alias tagFormula_sub_psi_top := ReconfRes.Frozen.Dev.Q427.PartC1.tagFormula_sub_psi_top

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC1
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
theorem liftFirst_zero_iso (R : ProofDag V) (pos : Fin α → Fin R.n) :
    (liftFirst C t R pos 0 (Nat.zero_le _)).Iso R := by
  set C' : Fin 0 → Clause V := fun i => C (Fin.castLE (Nat.zero_le _) i)
  set t' : Fin 0 → V := fun i => t (Fin.castLE (Nat.zero_le _) i)
  set pos' : Fin 0 → Fin R.n := fun i => pos (Fin.castLE (Nat.zero_le _) i)
  change (lift C' t' R pos').Iso R
  have hn : R.n + (0 + 0) = R.n := rfl
  have key : ∀ y : Fin (R.n + (0 + 0)), y = oN (α := 0) R (finCongr hn y) := by
    intro y; rfl
  refine ⟨finCongr hn, fun i => ?_, fun i j => ?_, rfl⟩
  · rw [key i, lift_label_old]; rfl
  · exact (E1 C' t' R pos' (finCongr hn i) (finCongr hn j)).symm

end ReconfRes.Frozen.Dev.Q427.PartC1
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
alias liftFirst_zero_iso := ReconfRes.Frozen.Dev.Q427.PartC1.liftFirst_zero_iso

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC1
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
theorem psi_zero_sub : psi C t 0 (Nat.zero_le _) ⊆ inventoryFormula C := by
  intro E hE
  simp [psi, tagFormula, inventoryFormula] at hE ⊢
  exact hE

end ReconfRes.Frozen.Dev.Q427.PartC1
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
alias psi_zero_sub := ReconfRes.Frozen.Dev.Q427.PartC1.psi_zero_sub

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC1
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
theorem psi_erase (ht : Function.Injective t) (hfresh : ∀ i j, ∀ l ∈ C j, l.1 ≠ t i)
    (j : ℕ) (hj : j + 1 ≤ α) :
    ∀ E ∈ psi C t (j + 1) hj, E ≠ {(t ⟨j, by omega⟩, true)} →
      E.erase (t ⟨j, by omega⟩, false) ∈ psi C t j (by omega) := by
  intro E hE hne
  set T : V := t ⟨j, by omega⟩ with hT
  have hfr : ∀ i, (T, false) ∉ C i := fun i h => hfresh ⟨j, by omega⟩ i _ h rfl
  simp only [psi, tagFormula, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_filter] at hE ⊢
  rcases hE with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, hi, rfl⟩
  · by_cases hij : i.val = j
    · right
      refine ⟨Fin.castLE hj i, by simp [hij], ?_⟩
      have : t (Fin.castLE hj i) = T := by
        rw [hT]; congr 1; ext; simp [hij]
      show C (Fin.castLE hj i) = (insert (t (Fin.castLE hj i), false) (C (Fin.castLE hj i))).erase _
      rw [this, Finset.erase_insert (hfr _)]
    · left; left
      have hi : i.val < j := by omega
      refine ⟨⟨i.val, hi⟩, ?_⟩
      have hne' : (t (Fin.castLE hj i), false) ≠ (T, false) := by
        intro h; apply hij
        have := ht (Prod.mk.inj h).1
        simpa using congrArg Fin.val this
      unfold tagD
      rw [Finset.erase_eq_of_notMem]
      · rfl
      · rw [Finset.mem_insert, not_or]
        exact ⟨hne'.symm, hfr _⟩
  · by_cases hij : i.val = j
    · exfalso; apply hne
      unfold tagU
      have : t (Fin.castLE hj i) = T := by
        rw [hT]; congr 1; ext; simp [hij]
      show ({(t (Fin.castLE hj i), true)} : Clause V) = _
      rw [this]
    · left; right
      have hi : i.val < j := by omega
      refine ⟨⟨i.val, hi⟩, ?_⟩
      unfold tagU
      rw [Finset.erase_eq_of_notMem]
      · rfl
      · simp
  · right
    exact ⟨i, by omega, by rw [Finset.erase_eq_of_notMem (hfr i)]⟩

end ReconfRes.Frozen.Dev.Q427.PartC1
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
alias psi_erase := ReconfRes.Frozen.Dev.Q427.PartC1.psi_erase

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC2
variable {V : Type} [DecidableEq V]
/-! ## Generic helpers -/
theorem mem_parents (R : ProofDag V) (i j : Fin R.n) : j ∈ R.parents i ↔ (j, i) ∈ R.edges := by
  simp [ProofDag.parents]

theorem mem_keep {X : ProofDag V} {u c x : Fin X.n} : x ∈ keep X u c ↔ x ≠ u ∧ x ≠ c := by
  simp [keep]

theorem rep_of_ne {X : ProofDag V} {c p x : Fin X.n} (h : x ≠ c) : rep X c p x = x := by
  simp [rep, h]

theorem card_keep {X : ProofDag V} {u c : Fin X.n} (huc : u ≠ c) :
    (keep X u c).card + 2 = X.n := by
  have : keep X u c = Finset.univ \ {u, c} := by ext x; simp [keep]
  rw [this, Finset.card_univ_sdiff, Fintype.card_fin, Finset.card_pair huc]
  have := Finset.card_le_univ ({u, c} : Finset (Fin X.n))
  rw [Fintype.card_fin, Finset.card_pair huc] at this
  omega

theorem mem_contract_edges {X : ProofDag V} {u c p : Fin X.n} {t : V}
    {h : rep X c p X.sink ∈ keep X u c} (a b : Fin (contract X u c p t h).n) :
    (a, b) ∈ (contract X u c p t h).edges ↔ ((kE X u c a).1, (kE X u c b).1) ∈ X.edges ∨
      ((kE X u c a).1 = p ∧ (c, (kE X u c b).1) ∈ X.edges) := by
  exact ⟨fun h' => (Finset.mem_filter.1 h').2, fun h' => Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩⟩

theorem contract_label {X : ProofDag V} {u c p : Fin X.n} {t : V}
    {h : rep X c p X.sink ∈ keep X u c} (i : Fin (contract X u c p t h).n) :
    (contract X u c p t h).label i = (X.label (kE X u c i).1).erase (t, false) := rfl

/-! ## Axiom-multiset facts -/
theorem count_one {X : ProofDag V} {U : Clause V} {a : Literal V} (ha : a ∈ U) {u : Fin X.n}
    (hpu : X.parents u = ∅) (hlu : X.label u = U) (huniq : ∀ y, a ∈ X.label y → y = u) :
    X.axiomMultiset.count U = 1 := by
  unfold ProofDag.axiomMultiset
  rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val, Finset.card_eq_one]
  refine ⟨u, ?_⟩
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩; exact huniq y (h ▸ ha)
  · rintro rfl; exact ⟨hpu, hlu.symm⟩

theorem no_other {X : ProofDag V} {U : Clause V} {a : Literal V} {u : Fin X.n}
    (hlu : X.label u = U) (huniq : ∀ y, a ∈ X.label y → y = u) :
    ∀ E ∈ X.axiomMultiset, E ≠ U → a ∉ E := by
  intro E hE hne ha
  unfold ProofDag.axiomMultiset at hE
  obtain ⟨y, _, rfl⟩ := Multiset.mem_map.1 hE
  exact hne (by rw [huniq y ha, hlu])

theorem card_axiomMultiset (X : ProofDag V) :
    Multiset.card X.axiomMultiset = (Finset.univ.filter fun i => X.parents i = ∅).card := by
  unfold ProofDag.axiomMultiset
  rw [Multiset.card_map]; rfl

end ReconfRes.Frozen.Dev.Q427.PartC2
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC2
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V) (R : ProofDag V) (pos : Fin α → Fin R.n)
/-! ## The lift API (after `Solutions/ReconfRes/T60.lean`) -/
/-- old node -/
abbrev oN (x : Fin R.n) : Fin (R.n + (α + α)) := Fin.castAdd (α + α) x

/-- tag-D node -/
abbrev dN (i : Fin α) : Fin (R.n + (α + α)) := Fin.natAdd R.n (Fin.castAdd α i)

/-- tag-U node -/
abbrev uN (i : Fin α) : Fin (R.n + (α + α)) := Fin.natAdd R.n (Fin.natAdd α i)

theorem oN_inj {x y : Fin R.n} (h : oN (α := α) R x = oN R y) : x = y := by
  have := congrArg Fin.val h; simpa [Fin.ext_iff] using this

theorem dN_inj {i j : Fin α} (h : dN R i = dN R j) : i = j := by
  have := congrArg Fin.val h; simpa [Fin.ext_iff] using this

theorem uN_inj {i j : Fin α} (h : uN R i = uN R j) : i = j := by
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

theorem e_oo (x y : Fin R.n) :
    (oN (α := α) R x, oN R y) ∈ (lift C t R pos).edges ↔ (x, y) ∈ R.edges := by
  rw [mem_lift_edges]
  constructor
  · rintro (⟨x', y', h, h1, h2⟩ | ⟨i, h1, _⟩ | ⟨i, h1, _⟩)
    · rw [← oN_inj R h1, ← oN_inj R h2]; exact h
    · exact absurd h1.symm (oN_ne_dN R _ _)
    · exact absurd h1.symm (oN_ne_uN R _ _)
  · intro h; exact Or.inl ⟨x, y, h, rfl, rfl⟩

theorem e_to_d (z : Fin (R.n + (α + α))) (i : Fin α) : (z, dN R i) ∉ (lift C t R pos).edges := by
  intro h
  have : z ∈ (lift C t R pos).parents (dN R i) := (mem_parents _ _ _).2 h
  rw [lift_parents_new_d] at this; exact Finset.notMem_empty _ this

theorem e_to_u (z : Fin (R.n + (α + α))) (i : Fin α) : (z, uN R i) ∉ (lift C t R pos).edges := by
  intro h
  have : z ∈ (lift C t R pos).parents (uN R i) := (mem_parents _ _ _).2 h
  rw [lift_parents_new_u] at this; exact Finset.notMem_empty _ this

theorem e_d (i : Fin α) (z : Fin (R.n + (α + α))) :
    (dN R i, z) ∈ (lift C t R pos).edges ↔ z = oN R (pos i) := by
  refine Iff.trans (mem_lift_edges C t R pos _ _) ?_
  constructor
  · rintro (⟨x, y, h, h1, h2⟩ | ⟨j, h1, h2⟩ | ⟨j, h1, h2⟩)
    · exact absurd h1 (oN_ne_dN R _ _)
    · rw [← dN_inj R h1, ← h2]
    · exact absurd h1.symm (dN_ne_uN R _ _)
  · rintro rfl; exact Or.inr (Or.inl ⟨i, rfl, rfl⟩)

theorem e_u (i : Fin α) (z : Fin (R.n + (α + α))) :
    (uN R i, z) ∈ (lift C t R pos).edges ↔ z = oN R (pos i) := by
  refine Iff.trans (mem_lift_edges C t R pos _ _) ?_
  constructor
  · rintro (⟨x, y, h, h1, h2⟩ | ⟨j, h1, h2⟩ | ⟨j, h1, h2⟩)
    · exact absurd h1 (oN_ne_uN R _ _)
    · exact absurd h1 (dN_ne_uN R _ _)
    · rw [← uN_inj R h1, ← h2]
  · rintro rfl; exact Or.inr (Or.inr ⟨i, rfl, rfl⟩)

theorem lift_label_old (x : Fin R.n) : (lift C t R pos).label (oN R x) = R.label x := by
  show Fin.addCases (motive := fun _ => Clause V) R.label (Fin.addCases (motive := fun _ => Clause V) (tagD C t) (tagU t)) (Fin.castAdd (α + α) x) = _
  simp [Fin.addCases_left]

theorem lift_label_d (i : Fin α) : (lift C t R pos).label (dN R i) = tagD C t i := by
  show Fin.addCases (motive := fun _ => Clause V) R.label (Fin.addCases (motive := fun _ => Clause V) (tagD C t) (tagU t)) (Fin.natAdd R.n (Fin.castAdd α i)) = _
  simp [Fin.addCases_right, Fin.addCases_left]

theorem lift_label_u (i : Fin α) : (lift C t R pos).label (uN R i) = tagU t i := by
  show Fin.addCases (motive := fun _ => Clause V) R.label (Fin.addCases (motive := fun _ => Clause V) (tagD C t) (tagU t)) (Fin.natAdd R.n (Fin.natAdd α i)) = _
  simp only [Fin.addCases_right]

/-- The only node of a lift containing the literal `t i0` is the unit node `uN i0`. -/
theorem tag_only (ht : Function.Injective t) (hfreshC : ∀ i k, ∀ l ∈ C k, l.1 ≠ t i) (i0 : Fin α)
    (hfreshR : ∀ x, ∀ l ∈ R.label x, l.1 ≠ t i0) (y : Fin (R.n + (α + α)))
    (hy : (t i0, true) ∈ (lift C t R pos).label y) : y = uN R i0 := by
  rcases fin3 R y with ⟨x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [lift_label_old] at hy; exact absurd rfl (hfreshR x _ hy)
  · rw [lift_label_d] at hy
    unfold tagD at hy
    rcases Finset.mem_insert.1 hy with h | h
    · simp at h
    · exact absurd rfl (hfreshC i0 i _ h)
  · rw [lift_label_u] at hy
    unfold tagU at hy
    rw [Finset.mem_singleton, Prod.mk.injEq] at hy
    rw [ht hy.1]

/-- A lift is good for any of its tags. -/
theorem good_generic (ht : Function.Injective t) (hfreshC : ∀ i k, ∀ l ∈ C k, l.1 ≠ t i)
    (i0 : Fin α) (hfreshR : ∀ x, ∀ l ∈ R.label x, l.1 ≠ t i0) {Φ : CNF V} {w s : ℕ}
    (hV : IsVertex Φ w s (lift C t R pos))
    (hcard : s + 1 ≤ 2 * (Finset.univ.filter fun y => (lift C t R pos).parents y = ∅).card) :
    Good Φ w s (t i0) (lift C t R pos) := by
  have hu := tag_only C t R pos ht hfreshC i0 hfreshR
  refine ⟨hV, ?_, ?_, ?_⟩
  · exact count_one (Finset.mem_singleton_self _) (lift_parents_new_u C t R pos i0)
      (lift_label_u C t R pos i0) hu
  · exact no_other (lift_label_u C t R pos i0) hu
  · rw [card_axiomMultiset]; exact hcard

end ReconfRes.Frozen.Dev.Q427.PartC2
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC2
variable {V : Type} [DecidableEq V]
theorem fresh_R {α : ℕ} {C : Fin α → Clause V} {t : Fin α → V}
    (hfresh : ∀ i j, ∀ l ∈ C j, l.1 ≠ t i)
    {R : ProofDag V} (hR : R.IsRefutationOf (inventoryFormula C)) (i : Fin α) (x : Fin R.n)
    (l : Literal V) (hl : l ∈ R.label x) : l.1 ≠ t i := by
  have h := hR.2.1 x l hl
  unfold vars inventoryFormula at h
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at h
  obtain ⟨_, ⟨k, rfl⟩, l', hl', heq⟩ := h
  rw [← heq]; exact hfresh i k l' hl'

end ReconfRes.Frozen.Dev.Q427.PartC2
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC2
variable {V : Type} [DecidableEq V]
variable {β : ℕ} (C : Fin (β + 1) → Clause V) (t : Fin (β + 1) → V) (R : ProofDag V)
  (pos : Fin (β + 1) → Fin R.n)
/-! ## Contracting the last tag of a lift -/
/-- The node of the `(β+1)`-lift corresponding to a node of the `β`-lift. -/
def gmap (y : Fin (R.n + (β + β))) : Fin (R.n + ((β + 1) + (β + 1))) :=
  Fin.addCases (motive := fun _ => Fin (R.n + ((β + 1) + (β + 1))))
    (fun x => if x = pos (Fin.last β) then dN R (Fin.last β) else oN R x)
    (Fin.addCases (motive := fun _ => Fin (R.n + ((β + 1) + (β + 1))))
      (fun i => dN R i.castSucc) (fun i => uN R i.castSucc)) y

theorem gmap_o (x : Fin R.n) : gmap R pos (oN (α := β) R x) =
    if x = pos (Fin.last β) then dN R (Fin.last β) else oN R x := by
  simp [gmap]

theorem gmap_d (i : Fin β) : gmap R pos (dN R i) = dN R i.castSucc := by
  simp [gmap]

theorem gmap_u (i : Fin β) : gmap R pos (uN R i) = uN R i.castSucc := by
  simp only [gmap, Fin.addCases_right]

theorem castSucc_ne_last' (i : Fin β) : i.castSucc ≠ Fin.last β := ne_of_lt (Fin.castSucc_lt_last i)

theorem gmap_keep (y : Fin (R.n + (β + β))) :
    gmap R pos y ∈ keep (lift C t R pos) (uN R (Fin.last β)) (oN R (pos (Fin.last β))) := by
  refine mem_keep.2 ?_
  rcases fin3 (α := β) R y with ⟨x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [gmap_o]
    split_ifs with hx
    · exact ⟨dN_ne_uN R _ _, fun h => oN_ne_dN R _ _ h.symm⟩
    · exact ⟨oN_ne_uN R _ _, fun h => hx (oN_inj R h)⟩
  · rw [gmap_d]
    exact ⟨dN_ne_uN R _ _, fun h => oN_ne_dN R _ _ h.symm⟩
  · rw [gmap_u]
    exact ⟨fun h => castSucc_ne_last' i (uN_inj R h), fun h => oN_ne_uN R _ _ h.symm⟩

theorem gmap_inj (hpos : Function.Injective pos) : Function.Injective (gmap R pos) := by
  intro a b h
  rcases fin3 (α := β) R a with ⟨x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
  rcases fin3 (α := β) R b with ⟨y, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ <;>
  simp only [gmap_o, gmap_d, gmap_u] at h
  · by_cases hx : x = pos (Fin.last β) <;> by_cases hy : y = pos (Fin.last β) <;>
      simp only [hx, hy, if_true, if_false] at h
    · rw [hx, hy]
    · exact absurd h.symm (oN_ne_dN R _ _)
    · exact absurd h (oN_ne_dN R _ _)
    · rw [oN_inj R h]
  · split_ifs at h with hx
    · exact absurd (dN_inj R h).symm (castSucc_ne_last' k)
    · exact absurd h (oN_ne_dN R _ _)
  · split_ifs at h with hx
    · exact absurd h (dN_ne_uN R _ _)
    · exact absurd h (oN_ne_uN R _ _)
  · split_ifs at h with hy
    · exact absurd (dN_inj R h) (castSucc_ne_last' i)
    · exact absurd h.symm (oN_ne_dN R _ _)
  · rw [Fin.castSucc_inj.1 (dN_inj R h)]
  · exact absurd h (dN_ne_uN R _ _)
  · split_ifs at h with hy
    · exact absurd h.symm (dN_ne_uN R _ _)
    · exact absurd h.symm (oN_ne_uN R _ _)
  · exact absurd h.symm (dN_ne_uN R _ _)
  · rw [Fin.castSucc_inj.1 (uN_inj R h)]

theorem card_keep_lift :
    (keep (lift C t R pos) (uN R (Fin.last β)) (oN R (pos (Fin.last β)))).card = R.n + (β + β) := by
  have := card_keep (X := lift C t R pos) (u := uN R (Fin.last β)) (c := oN R (pos (Fin.last β)))
    (fun h => oN_ne_uN R _ _ h.symm)
  change _ + 2 = R.n + ((β + 1) + (β + 1)) at this
  omega

/-- The contracted index of `gmap y`. -/
noncomputable def G (y : Fin (R.n + (β + β))) :
    Fin (keep (lift C t R pos) (uN R (Fin.last β)) (oN R (pos (Fin.last β)))).card :=
  (kE (lift C t R pos) (uN R (Fin.last β)) (oN R (pos (Fin.last β)))).symm ⟨_, gmap_keep C t R pos y⟩

theorem G_kE (y : Fin (R.n + (β + β))) :
    (kE (lift C t R pos) (uN R (Fin.last β)) (oN R (pos (Fin.last β))) (G C t R pos y)).1 =
      gmap R pos y := by
  simp [G]; rfl

theorem G_bij (hpos : Function.Injective pos) : Function.Bijective (G C t R pos) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b h => gmap_inj R pos hpos ?_, ?_⟩
  · have := congrArg (fun z => (kE (lift C t R pos) (uN R (Fin.last β))
      (oN R (pos (Fin.last β))) z).1) h
    simp only [G_kE] at this; exact this
  · simp only [Fintype.card_fin]; exact (card_keep_lift C t R pos).symm

theorem gmap_oN_iff (hpos : Function.Injective pos) (b : Fin (R.n + (β + β))) (k : Fin β) :
    b = oN (α := β) R (pos k.castSucc) ↔ gmap R pos b = oN R (pos k.castSucc) := by
  rcases fin3 (α := β) R b with ⟨y, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [gmap_o]
    split_ifs with hy
    · refine ⟨fun h => ?_, fun h => absurd h.symm (oN_ne_dN R _ _)⟩
      exact absurd (hpos ((oN_inj R h).symm.trans hy)) (castSucc_ne_last' k)
    · exact ⟨fun h => by rw [oN_inj R h], fun h => by rw [oN_inj R h]⟩
  · rw [gmap_d]
    exact iff_of_false (fun h => oN_ne_dN R _ _ h.symm) (fun h => oN_ne_dN R _ _ h.symm)
  · rw [gmap_u]
    exact iff_of_false (fun h => oN_ne_uN R _ _ h.symm) (fun h => oN_ne_uN R _ _ h.symm)

theorem edge_char (hpos : Function.Injective pos) (hax : ∀ i, R.parents (pos i) = ∅)
    (a b : Fin (R.n + (β + β))) :
    (a, b) ∈ (lift (fun i => C i.castSucc) (fun i => t i.castSucc) R
        (fun i => pos i.castSucc)).edges ↔
      ((gmap R pos a, gmap R pos b) ∈ (lift C t R pos).edges ∨
        (gmap R pos a = dN R (Fin.last β) ∧
          (oN R (pos (Fin.last β)), gmap R pos b) ∈ (lift C t R pos).edges)) := by
  have hno : ∀ x k, (x, pos k) ∉ R.edges := fun x k h => by
    have := (mem_parents R _ _).2 h; rw [hax] at this; exact Finset.notMem_empty _ this
  have nd : ∀ z (i : Fin (β + 1)), (z, dN R i) ∉ (lift C t R pos).edges := e_to_d C t R pos
  have nu : ∀ z (i : Fin (β + 1)), (z, uN R i) ∉ (lift C t R pos).edges := e_to_u C t R pos
  rcases fin3 (α := β) R a with ⟨x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rcases fin3 (α := β) R b with ⟨y, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [e_oo, gmap_o, gmap_o]
      by_cases hx : x = pos (Fin.last β) <;> by_cases hy : y = pos (Fin.last β)
      · subst hx; rw [if_pos hy, if_pos rfl, hy]
        exact iff_of_false (hno _ _) (by rintro (h | ⟨_, h⟩) <;> exact nd _ _ h)
      · subst hx; rw [if_neg hy, if_pos rfl, e_d, e_oo]
        refine ⟨fun h => Or.inr ⟨rfl, h⟩, ?_⟩
        rintro (h | ⟨_, h⟩)
        · exact absurd (oN_inj R h) hy
        · exact h
      · rw [if_pos hy, if_neg hx, hy]
        exact iff_of_false (hno _ _) (by rintro (h | ⟨_, h⟩) <;> exact nd _ _ h)
      · rw [if_neg hy, if_neg hx, e_oo]
        refine ⟨Or.inl, ?_⟩
        rintro (h | ⟨h, _⟩)
        · exact h
        · exact absurd h (oN_ne_dN R _ _)
    · rw [gmap_d]
      exact iff_of_false (e_to_d _ _ R _ _ _) (by rintro (h | ⟨_, h⟩) <;> exact nd _ _ h)
    · rw [gmap_u]
      exact iff_of_false (e_to_u _ _ R _ _ _) (by rintro (h | ⟨_, h⟩) <;> exact nu _ _ h)
  · rw [e_d, gmap_d, e_d]
    have hne : dN R i.castSucc ≠ dN R (Fin.last β) := fun h => castSucc_ne_last' i (dN_inj R h)
    rw [or_iff_left (fun h => hne h.1)]
    exact gmap_oN_iff R pos hpos b i
  · rw [e_u, gmap_u, e_u]
    have hne : uN R i.castSucc ≠ dN R (Fin.last β) := fun h => dN_ne_uN R _ _ h.symm
    rw [or_iff_left (fun h => hne h.1)]
    exact gmap_oN_iff R pos hpos b i

theorem label_char (hfreshC : ∀ i k, ∀ l ∈ C k, l.1 ≠ t i) (ht : Function.Injective t)
    (hfreshR : ∀ x, ∀ l ∈ R.label x, l.1 ≠ t (Fin.last β))
    (hlab : R.label (pos (Fin.last β)) = C (Fin.last β)) (y : Fin (R.n + (β + β))) :
    (lift (fun i => C i.castSucc) (fun i => t i.castSucc) R (fun i => pos i.castSucc)).label y =
      ((lift C t R pos).label (gmap R pos y)).erase (t (Fin.last β), false) := by
  rcases fin3 (α := β) R y with ⟨x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [lift_label_old, gmap_o]
    split_ifs with hx
    · rw [lift_label_d, hx, hlab]; simp only [tagD]
      rw [Finset.erase_insert (fun h => hfreshC _ _ _ h rfl)]
    · rw [lift_label_old, Finset.erase_eq_of_notMem (fun h => hfreshR x _ h rfl)]
  · rw [lift_label_d, gmap_d, lift_label_d]; simp only [tagD]
    rw [Finset.erase_eq_of_notMem]
    intro h
    rcases Finset.mem_insert.1 h with h | h
    · exact castSucc_ne_last' i (ht (Prod.mk.inj h).1).symm
    · exact hfreshC _ _ _ h rfl
  · rw [lift_label_u, gmap_u, lift_label_u]; simp only [tagU]
    rw [Finset.erase_eq_of_notMem]; simp

theorem proj_generic (hfreshC : ∀ i k, ∀ l ∈ C k, l.1 ≠ t i) (ht : Function.Injective t)
    (hfreshR : ∀ x, ∀ l ∈ R.label x, l.1 ≠ t (Fin.last β))
    (hpos : Function.Injective pos) (hax : ∀ i, R.parents (pos i) = ∅)
    (hlab : R.label (pos (Fin.last β)) = C (Fin.last β)) (hsink : R.sink ≠ pos (Fin.last β)) :
    ∃ P, IsProj (t (Fin.last β)) (lift C t R pos) P ∧
      P.Iso (lift (fun i => C i.castSucc) (fun i => t i.castSucc) R (fun i => pos i.castSucc)) := by
  have hsk : (lift C t R pos).sink ≠ oN R (pos (Fin.last β)) := fun h => hsink (oN_inj R h)
  have hk : rep (lift C t R pos) (oN R (pos (Fin.last β))) (dN R (Fin.last β))
      (lift C t R pos).sink ∈
      keep (lift C t R pos) (uN R (Fin.last β)) (oN R (pos (Fin.last β))) := by
    erw [rep_of_ne hsk]
    exact mem_keep.2 ⟨oN_ne_uN R _ _, hsk⟩
  refine ⟨contract _ _ _ _ (t (Fin.last β)) hk, ⟨_, _, _, hk, ?_, ?_, ?_, ?_, ?_, rfl⟩, ?_⟩
  · exact lift_label_u C t R pos _
  · exact lift_parents_new_u C t R pos _
  · exact (e_u C t R pos _ _).2 rfl
  · exact (e_d C t R pos _ _).2 rfl
  · exact dN_ne_uN R _ _
  have hG := G_bij C t R pos hpos
  refine ⟨(Equiv.ofBijective _ hG).symm, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨y, rfl⟩ := hG.2 i
    erw [Equiv.ofBijective_symm_apply_apply, contract_label, G_kE]
    exact label_char C t R pos hfreshC ht hfreshR hlab y
  · intro i k
    obtain ⟨a, rfl⟩ := hG.2 i
    obtain ⟨b, rfl⟩ := hG.2 k
    erw [Equiv.ofBijective_symm_apply_apply, Equiv.ofBijective_symm_apply_apply,
      mem_contract_edges, G_kE, G_kE]
    exact edge_char C t R pos hpos hax a b
  · have hs : (contract _ _ _ _ (t (Fin.last β)) hk).sink = G C t R pos (oN R R.sink) := by
      apply (kE (lift C t R pos) (uN R (Fin.last β)) (oN R (pos (Fin.last β)))).injective
      apply Subtype.ext
      rw [G_kE, gmap_o, if_neg hsink]
      change (kE _ _ _ ((kE _ _ _).symm ⟨_, hk⟩)).1 = _
      rw [Equiv.apply_symm_apply]
      exact rep_of_ne hsk
    rw [hs]; erw [Equiv.ofBijective_symm_apply_apply]
    rfl

end ReconfRes.Frozen.Dev.Q427.PartC2
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC2
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
/-! ## The targets -/
/-- The axiom nodes of `liftFirst (j+1)`: the `D`/`U` tag nodes and the untouched sources. -/
def axMap (R : ProofDag V) (pos : Fin α → Fin R.n) (j : ℕ) :
    Fin α ⊕ Fin (j + 1) → Fin (R.n + ((j + 1) + (j + 1))) :=
  Sum.elim (fun k => if h : k.val < j + 1 then dN (α := j + 1) R ⟨k.val, h⟩ else oN R (pos k))
    (fun i => uN R i)

theorem axioms_lb (R : ProofDag V) (pos : Fin α → Fin R.n) (hR : IsTightIndexed C R pos)
    (j : ℕ) (hj : j + 1 ≤ α) :
    α + (j + 1) ≤
      (Finset.univ.filter fun y => (liftFirst C t R pos (j + 1) hj).parents y = ∅).card := by
  have hidx := hR.2.2.2
  have hax : ∀ k, R.parents (pos k) = ∅ := fun k => (hidx.2.1 (pos k)).2 ⟨k, Finset.mem_univ _, rfl⟩
  have hpos : Function.Injective pos :=
    fun a b h => hidx.1 (Finset.mem_coe.2 (Finset.mem_univ a)) (Finset.mem_coe.2 (Finset.mem_univ b)) h
  have key := Finset.card_le_card_of_injOn (axMap R pos j) (s := Finset.univ)
    (t := Finset.univ.filter fun y => (liftFirst C t R pos (j + 1) hj).parents y = ∅) ?_ ?_
  · simpa using key
  · intro a _
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    rcases a with k | i
    · simp only [axMap, Sum.elim_inl]
      split_ifs with hk
      · exact lift_parents_new_d (fun i : Fin (j + 1) => C (Fin.castLE hj i))
          (fun i => t (Fin.castLE hj i)) R (fun i => pos (Fin.castLE hj i)) _
      · rw [Finset.eq_empty_iff_forall_notMem]
        intro z hz
        rcases (mem_lift_parents_old (fun i : Fin (j + 1) => C (Fin.castLE hj i))
          (fun i => t (Fin.castLE hj i)) R (fun i => pos (Fin.castLE hj i)) _ z (pos k) rfl).1 hz
          with ⟨x, hx, _⟩ | ⟨i, hi, _⟩ | ⟨i, hi, _⟩
        · rw [hax] at hx; exact Finset.notMem_empty _ hx
        · have := congrArg Fin.val (hpos hi); simp at this; omega
        · have := congrArg Fin.val (hpos hi); simp at this; omega
    · exact lift_parents_new_u (fun i : Fin (j + 1) => C (Fin.castLE hj i))
          (fun i => t (Fin.castLE hj i)) R (fun i => pos (Fin.castLE hj i)) _
  · intro a _ b _ h
    rcases a with k | i <;> rcases b with k' | i' <;> simp only [axMap, Sum.elim_inl, Sum.elim_inr] at h
    · split_ifs at h with h1 h2 h2
      · have := congrArg Fin.val (dN_inj R h); simp at this; rw [Fin.ext this]
      · exact absurd h.symm (oN_ne_dN R _ _)
      · exact absurd h (oN_ne_dN R _ _)
      · rw [hpos (oN_inj R h)]
    · split_ifs at h with h1
      · exact absurd h (dN_ne_uN R _ _)
      · exact absurd h (oN_ne_uN R _ _)
    · split_ifs at h with h1
      · exact absurd h.symm (dN_ne_uN R _ _)
      · exact absurd h.symm (oN_ne_uN R _ _)
    · rw [uN_inj R h]

/-- At every stage the lift of a tight refutation that is a vertex is good for the last tag. -/
theorem liftFirst_good (hC : ∀ i, (C i).Nonempty) (ht : Function.Injective t)
    (hfresh : ∀ i j, ∀ l ∈ C j, l.1 ≠ t i) (w : ℕ)
    (R : ProofDag V) (pos : Fin α → Fin R.n) (hR : IsTightIndexed C R pos)
    (j : ℕ) (hj : j + 1 ≤ α)
    (hV : IsVertex (psi C t (j + 1) hj) w (2 * α - 1 + 2 * (j + 1)) (liftFirst C t R pos (j + 1) hj)) :
    Good (psi C t (j + 1) hj) w (2 * α - 1 + 2 * (j + 1)) (t ⟨j, by omega⟩)
      (liftFirst C t R pos (j + 1) hj) := by
  have hlb : α + (j + 1) ≤ (Finset.univ.filter fun y => (lift (fun i : Fin (j + 1) =>
      C (Fin.castLE hj i)) (fun i => t (Fin.castLE hj i)) R
      (fun i => pos (Fin.castLE hj i))).parents y = ∅).card := axioms_lb C t R pos hR j hj
  have ht' : Function.Injective (fun i : Fin (j + 1) => t (Fin.castLE hj i)) :=
    fun a b h => Fin.castLE_injective hj (ht h)
  exact good_generic (fun i : Fin (j + 1) => C (Fin.castLE hj i)) (fun i => t (Fin.castLE hj i)) R
    (fun i => pos (Fin.castLE hj i)) ht' (fun i k => hfresh _ _) (Fin.last j)
    (fun x l hl => fresh_R hfresh hR.1 _ x l hl) hV (by omega)

end ReconfRes.Frozen.Dev.Q427.PartC2
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
alias liftFirst_good := ReconfRes.Frozen.Dev.Q427.PartC2.liftFirst_good

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC2
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
/-- Contracting the last tag of `liftFirst (j+1)` gives `liftFirst j` up to isomorphism. -/
theorem liftFirst_proj (hC : ∀ i, (C i).Nonempty) (ht : Function.Injective t)
    (hfresh : ∀ i j, ∀ l ∈ C j, l.1 ≠ t i)
    (R : ProofDag V) (pos : Fin α → Fin R.n) (hR : IsTightIndexed C R pos)
    (j : ℕ) (hj : j + 1 ≤ α) :
    ∃ P, IsProj (t ⟨j, by omega⟩) (liftFirst C t R pos (j + 1) hj) P ∧
      P.Iso (liftFirst C t R pos j (by omega)) := by
  have hidx := hR.2.2.2
  have hpos : Function.Injective pos :=
    fun a b h => hidx.1 (Finset.mem_coe.2 (Finset.mem_univ a)) (Finset.mem_coe.2 (Finset.mem_univ b)) h
  have ht' : Function.Injective (fun i : Fin (j + 1) => t (Fin.castLE hj i)) :=
    fun a b h => Fin.castLE_injective hj (ht h)
  have hpos' : Function.Injective (fun i : Fin (j + 1) => pos (Fin.castLE hj i)) :=
    fun a b h => Fin.castLE_injective hj (hpos h)
  have hsink : R.sink ≠ pos (Fin.castLE hj (Fin.last j)) := by
    intro h
    have h1 := hR.1.2.2.2.2
    rw [h, hidx.2.2 _ (Finset.mem_univ _)] at h1
    exact (hC _).ne_empty h1
  exact proj_generic (fun i : Fin (j + 1) => C (Fin.castLE hj i)) (fun i => t (Fin.castLE hj i)) R
    (fun i => pos (Fin.castLE hj i)) (fun i k => hfresh _ _) ht'
    (fun x l hl => fresh_R hfresh hR.1 _ x l hl) hpos'
    (fun i => (hidx.2.1 _).2 ⟨_, Finset.mem_univ _, rfl⟩)
    (hidx.2.2 _ (Finset.mem_univ _)) hsink

end ReconfRes.Frozen.Dev.Q427.PartC2
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
alias liftFirst_proj := ReconfRes.Frozen.Dev.Q427.PartC2.liftFirst_proj

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427.PartC1
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
theorem lift_inj (R₁ R₂ : ProofDag V) (pos₁ : Fin α → Fin R₁.n) (pos₂ : Fin α → Fin R₂.n)
    (h : lift C t R₁ pos₁ = lift C t R₂ pos₂) : R₁ = R₂ := by
  obtain ⟨n₁, l₁, e₁, s₁⟩ := R₁
  obtain ⟨n₂, l₂, e₂, s₂⟩ := R₂
  have hn : n₁ = n₂ := by
    have := congrArg ProofDag.n h
    simp only [lift] at this
    omega
  subst hn
  have h' := h
  simp only [lift, ProofDag.mk.injEq, heq_eq_eq, true_and] at h'
  obtain ⟨hl, he, hs⟩ := h'
  simp only [ProofDag.mk.injEq, heq_eq_eq, true_and]
  refine ⟨?_, ?_, ?_⟩
  · funext x
    have := congrFun hl (Fin.castAdd (α + α) x)
    simpa [Fin.addCases_left] using this
  · ext ⟨a, b⟩
    have k1 := E1 C t ⟨n₁, l₁, e₁, s₁⟩ pos₁ a b
    have k2 := E1 C t ⟨n₁, l₂, e₂, s₂⟩ pos₂ a b
    have k : (oN (α := α) (⟨n₁, l₁, e₁, s₁⟩ : ProofDag V) a,
        oN (α := α) (⟨n₁, l₁, e₁, s₁⟩ : ProofDag V) b) ∈ (lift C t ⟨n₁, l₁, e₁, s₁⟩ pos₁).edges ↔
        (oN (α := α) (⟨n₁, l₂, e₂, s₂⟩ : ProofDag V) a,
        oN (α := α) (⟨n₁, l₂, e₂, s₂⟩ : ProofDag V) b) ∈ (lift C t ⟨n₁, l₂, e₂, s₂⟩ pos₂).edges := by
      dsimp only [lift]
      rw [he]
      exact Iff.rfl
    exact k1.symm.trans (k.trans k2)
  · exact oN_inj (α := α) (⟨n₁, l₁, e₁, s₁⟩ : ProofDag V) hs

end ReconfRes.Frozen.Dev.Q427.PartC1
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
variable {α : ℕ} (C : Fin α → Clause V) (t : Fin α → V)
alias lift_inj := ReconfRes.Frozen.Dev.Q427.PartC1.lift_inj

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427
variable {V : Type} [DecidableEq V]
/-! ## Assembly (proved here from the stubs) -/
theorem good_of_connected {k : ℕ} (hk : 1 ≤ k) {Φ : CNF V} {w s : ℕ} {t : V} {X Y : ProofDag V}
    (hX : Good Φ w s t X) (h : FrozenConnected k Φ w s X Y) : Good Φ w s t Y := by
  induction h with
  | refl => exact hX
  | tail _ hst ih => exact good_of_step hk ih hst

/-- The one-tag contraction lemma. -/
theorem gcl {k : ℕ} (hk : 1 ≤ k) {Φ Φ' : CNF V} {w s : ℕ} {t : V}
    (hΦ' : ∀ E ∈ Φ, E ≠ {(t, true)} → E.erase (t, false) ∈ Φ')
    {X Y P Q : ProofDag V} (hX : Good Φ w s t X) (hXY : FrozenConnected k Φ w s X Y)
    (hP : IsProj t X P) (hQ : IsProj t Y Q) : FrozenConnected k Φ' w (s - 2) P Q := by
  induction hXY generalizing Q with
  | refl => rw [proj_unique hX hP hQ]; exact Relation.ReflTransGen.refl
  | @tail Z Y hXZ hZY ih =>
    have hZ : Good Φ w s t Z := good_of_connected hk hX hXZ
    have hY : Good Φ w s t Y := good_of_step hk hZ hZY
    obtain ⟨PZ, hPZ⟩ := exists_proj hZ
    have h1 := ih hPZ
    have hvZ := proj_isVertex hΦ' hZ hPZ
    have hvY := proj_isVertex hΦ' hY hQ
    refine h1.tail ⟨hvZ, hvY, ?_⟩
    rcases hZY with ⟨_, _, hiso | hmv | hmv⟩
    · exact Or.inl (proj_iso hZ hY hiso hPZ hQ)
    · rcases proj_move hk hZ hY hmv hPZ hQ with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
    · rcases proj_move hk hY hZ hmv hQ hPZ with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl (iso_symm h)

theorem vertex_right {k : ℕ} {F : CNF V} {w s : ℕ} {X Y : ProofDag V}
    (hX : IsVertex F w s X) (h : FrozenConnected k F w s X Y) : IsVertex F w s Y := by
  induction h with
  | refl => exact hX
  | tail _ hst _ => exact hst.2.1

/-- The stages, from `α` down to `0`. -/
theorem stages {α : ℕ} (C : Fin α → Clause V) (hC : ∀ i, (C i).Nonempty) (w : ℕ)
    (t : Fin α → V) (ht : Function.Injective t) (hfresh : ∀ i j, ∀ l ∈ C j, l.1 ≠ t i)
    (k : ℕ) (hk : 1 ≤ k)
    (R₁ R₂ : ProofDag V) (pos₁ : Fin α → Fin R₁.n) (pos₂ : Fin α → Fin R₂.n)
    (h₁ : IsTightIndexed C R₁ pos₁) (h₂ : IsTightIndexed C R₂ pos₂) :
    ∀ d j (hj : j + d = α),
      IsVertex (psi C t α le_rfl) w (2 * α - 1 + 2 * α) (liftFirst C t R₁ pos₁ α le_rfl) →
      IsVertex (psi C t α le_rfl) w (2 * α - 1 + 2 * α) (liftFirst C t R₂ pos₂ α le_rfl) →
      FrozenConnected k (psi C t α le_rfl) w (2 * α - 1 + 2 * α)
        (liftFirst C t R₁ pos₁ α le_rfl) (liftFirst C t R₂ pos₂ α le_rfl) →
      IsVertex (psi C t j (by omega)) w (2 * α - 1 + 2 * j) (liftFirst C t R₁ pos₁ j (by omega)) ∧
      IsVertex (psi C t j (by omega)) w (2 * α - 1 + 2 * j) (liftFirst C t R₂ pos₂ j (by omega)) ∧
      FrozenConnected k (psi C t j (by omega)) w (2 * α - 1 + 2 * j)
        (liftFirst C t R₁ pos₁ j (by omega)) (liftFirst C t R₂ pos₂ j (by omega)) := by
  intro d
  induction d with
  | zero =>
    intro j hj h1 h2 h3
    obtain rfl : j = α := by omega
    exact ⟨h1, h2, h3⟩
  | succ d ih =>
    intro j hj h1 h2 h3
    have hj1 : j + 1 ≤ α := by omega
    obtain ⟨v1, v2, c12⟩ := ih (j + 1) (by omega) h1 h2 h3
    have g1 := liftFirst_good C t hC ht hfresh w R₁ pos₁ h₁ j hj1 v1
    have g2 := liftFirst_good C t hC ht hfresh w R₂ pos₂ h₂ j hj1 v2
    obtain ⟨P₁, hP₁, i₁⟩ := liftFirst_proj C t hC ht hfresh R₁ pos₁ h₁ j hj1
    obtain ⟨P₂, hP₂, i₂⟩ := liftFirst_proj C t hC ht hfresh R₂ pos₂ h₂ j hj1
    have hΦ' := psi_erase C t ht hfresh j hj1
    have hc := gcl hk hΦ' g1 c12 hP₁ hP₂
    have hs : 2 * α - 1 + 2 * (j + 1) - 2 = 2 * α - 1 + 2 * j := by omega
    rw [hs] at hc
    have pv1 := proj_isVertex hΦ' g1 hP₁
    have pv2 := proj_isVertex hΦ' g2 hP₂
    rw [hs] at pv1 pv2
    have lv1 := iso_isVertex i₁ pv1
    have lv2 := iso_isVertex i₂ pv2
    refine ⟨lv1, lv2, ?_⟩
    refine Relation.ReflTransGen.head ⟨lv1, pv1, Or.inl (iso_symm i₁)⟩ ?_
    exact hc.tail ⟨pv2, lv2, Or.inl i₂⟩

end ReconfRes.Frozen.Dev.Q427
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen
open Dev.Q427 in
theorem chk_frozenConnected_of_lift_frozenConnected {V : Type} [DecidableEq V] (α : ℕ)
    (C : Fin α → Clause V) (hC : ∀ i, (C i).Nonempty) (w : ℕ)
    (hw : 1 + Finset.univ.sup (fun i => (C i).card) ≤ w)
    (t : Fin α → V) (ht : Function.Injective t) (hfresh : ∀ i j, ∀ l ∈ C j, l.1 ≠ t i)
    (k : ℕ) (hk : 1 ≤ k)
    (R₁ R₂ : ProofDag V) (pos₁ : Fin α → Fin R₁.n) (pos₂ : Fin α → Fin R₂.n)
    (h₁ : IsTightIndexed C R₁ pos₁) (h₂ : IsTightIndexed C R₂ pos₂)
    (hconn : FrozenConnected k (tagFormula C t) w (4 * α - 1) (lift C t R₁ pos₁) (lift C t R₂ pos₂)) :
    FrozenConnected k (inventoryFormula C) w (2 * α - 1) R₁ R₂ := by
  rcases Relation.ReflTransGen.cases_head hconn with heq | ⟨Z, hstep, _⟩
  · rw [lift_inj C t R₁ R₂ pos₁ pos₂ heq]; exact Relation.ReflTransGen.refl
  · have hv1 : IsVertex (tagFormula C t) w (4 * α - 1) (lift C t R₁ pos₁) := hstep.1
    have hv2 := vertex_right hv1 hconn
    have hα : 1 ≤ α := by
      have := h₁.2.2.1; have : 0 < R₁.n := Fin.pos R₁.sink
      change R₁.n + 1 ≤ 2 * α at *; omega
    have e4 : 4 * α - 1 = 2 * α - 1 + 2 * α := by omega
    rw [e4] at hv1 hv2 hconn
    have hsub := tagFormula_sub_psi_top C t
    have H := stages C hC w t ht hfresh k hk R₁ R₂ pos₁ pos₂ h₁ h₂ α 0 (by omega)
      (by rw [liftFirst_top]; exact isVertex_mono hsub hv1)
      (by rw [liftFirst_top]; exact isVertex_mono hsub hv2)
      (by rw [liftFirst_top, liftFirst_top]; exact frozenConnected_mono hsub hconn)
    obtain ⟨v1, v2, c12⟩ := H
    simp only [Nat.mul_zero, Nat.add_zero] at v1 v2 c12
    have hs0 := psi_zero_sub C t
    have v1' := isVertex_mono hs0 v1
    have v2' := isVertex_mono hs0 v2
    have i1 := liftFirst_zero_iso C t R₁ pos₁
    have i2 := liftFirst_zero_iso C t R₂ pos₂
    have r1 := iso_isVertex i1 v1'
    have r2 := iso_isVertex i2 v2'
    refine Relation.ReflTransGen.head ⟨r1, v1', Or.inl (iso_symm i1)⟩ ?_
    exact (frozenConnected_mono hs0 c12).tail ⟨v2', r2, Or.inl i2⟩

end ReconfRes.Frozen
end

open ReconfRes.Frozen in
theorem solution : type_of% @ReconfRes.Frozen.chk_frozenConnected_of_lift_frozenConnected := @ReconfRes.Frozen.chk_frozenConnected_of_lift_frozenConnected
