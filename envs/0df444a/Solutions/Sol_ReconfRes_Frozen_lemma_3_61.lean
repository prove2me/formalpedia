-- Prove2me | solution 1 for ReconfRes.Frozen.lemma_3_61
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T21:36:41.717203+00:00
-- url     : https://prove2.me/submissions/0a2d36c7-c588-4956-b514-27eb345dc133

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph
import Definitions.Def_ReconfRes_Frozen_VertexCover
import Definitions.Def_ReconfRes_Frozen_Construction
import Theorems.Thm_ReconfRes_Frozen_proposition_3_3
import Theorems.Thm_ReconfRes_Frozen_lemma_3_47
import Theorems.Thm_ReconfRes_Frozen_decoding_capacity_two

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427b
/-!
Blueprint for `ReconfRes.Frozen.lemma_3_61` (decoding at capacity two), reduced to the leaf
`decoding_capacity_two` (the tree analysis of Lemmas 3.56/3.61: `|X(R)| ≥ bK − 1`, `I(R)`
independent, unique pivots), which is to be published as its own statement.
-/
/-- The leaf (to be published as `ReconfRes.Frozen.decoding_capacity_two`). -/
theorem decoding_capacity_two (D : ConstrData) (hD : D.Valid) (R : ProofDag (CVar D.TV))
    (hR : D.IsTight R) (hW : R.width ≤ D.W) :
    D.b * D.K ≤ (D.selected R).card + 1 ∧ IsIndepSet D.J0 (D.decoded R) ∧
    ∀ (i : Fin R.n) (x y : CVar D.TV), R.HasPivot i x → R.HasPivot i y → x = y := by
  exact ReconfRes.Frozen.decoding_capacity_two D hD R hR hW

end ReconfRes.Frozen.Dev.Q427b
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427b.PartM
open ReconfRes.Frozen
variable {V : Type} [DecidableEq V]
theorem mem_parents (R : ProofDag V) (i j : Fin R.n) : j ∈ R.parents i ↔ (j, i) ∈ R.edges := by
  simp [ProofDag.parents]

theorem mem_consumers (R : ProofDag V) (i j : Fin R.n) :
    j ∈ R.consumers i ↔ (i, j) ∈ R.edges := by
  simp [ProofDag.consumers]

theorem mem_inputs (R : ProofDag V) (Q : Finset (Fin R.n)) (i : Fin R.n) :
    i ∈ R.inputs Q ↔ i ∉ Q ∧ ∃ j ∈ Q, (i, j) ∈ R.edges := by
  simp [ProofDag.inputs]

theorem ancIn_anc (R : ProofDag V) {Q : Finset (Fin R.n)} {a b : Fin R.n} (h : R.AncIn Q a b) :
    R.Anc a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail hs.2.2

/-- Transport of a pivot along a map of parents. -/
theorem hasPivot_transport {R R' : ProofDag V} {i : Fin R.n} {i' : Fin R'.n} {x : V}
    (ψ : Fin R.n → Fin R'.n) (h : R.HasPivot i x)
    (hpar : ∀ j', (j', i') ∈ R'.edges ↔ ∃ p, (p, i) ∈ R.edges ∧ ψ p = j')
    (hinj : ∀ p₁ p₂, (p₁, i) ∈ R.edges → (p₂, i) ∈ R.edges → ψ p₁ = ψ p₂ → p₁ = p₂)
    (hlab : ∀ p, (p, i) ∈ R.edges → R'.label (ψ p) = R.label p)
    (hli : R'.label i' = R.label i) : R'.HasPivot i' x := by
  obtain ⟨p₁, p₂, hne, hpar0, hres⟩ := h
  have h1 : (p₁, i) ∈ R.edges := by rw [← mem_parents, hpar0]; simp
  have h2 : (p₂, i) ∈ R.edges := by rw [← mem_parents, hpar0]; simp
  refine ⟨ψ p₁, ψ p₂, fun e => hne (hinj _ _ h1 h2 e), ?_, ?_⟩
  · ext j'
    rw [mem_parents, hpar]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have : p ∈ R.parents i := (mem_parents _ _ _).2 hp
      rw [hpar0] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl <;> simp
    · rintro (rfl | rfl)
      exacts [⟨p₁, h1, rfl⟩, ⟨p₂, h2, rfl⟩]
  · rw [hlab _ h1, hlab _ h2, hli]; exact hres

/-! ### Isomorphisms -/
theorem iso_symm {R R' : ProofDag V} (h : R.Iso R') : R'.Iso R := by
  obtain ⟨e, hl, he, hs⟩ := h
  refine ⟨e.symm, fun i => ?_, fun i j => ?_, ?_⟩
  · rw [← hl (e.symm i)]; simp
  · rw [← he]; simp
  · rw [← hs]; simp

theorem iso_pivot {R R' : ProofDag V} (e : Fin R.n ≃ Fin R'.n)
    (hl : ∀ i, R'.label (e i) = R.label i)
    (he : ∀ i j, (e i, e j) ∈ R'.edges ↔ (i, j) ∈ R.edges) {i : Fin R.n} {x : V}
    (h : R.HasPivot i x) : R'.HasPivot (e i) x := by
  refine hasPivot_transport e h (fun j' => ?_) (fun p₁ p₂ _ _ hh => e.injective hh)
    (fun p _ => hl p) (hl i)
  constructor
  · intro hj
    exact ⟨e.symm j', by rw [← he]; simpa using hj, by simp⟩
  · rintro ⟨p, hp, rfl⟩
    exact (he _ _).2 hp

theorem iso_anc {R R' : ProofDag V} (e : Fin R.n ≃ Fin R'.n)
    (he : ∀ i j, (e i, e j) ∈ R'.edges ↔ (i, j) ∈ R.edges) {a b : Fin R.n}
    (h : R.Anc a b) : R'.Anc (e a) (e b) := by
  unfold ProofDag.Anc at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail ((he _ _).2 hs)

end ReconfRes.Frozen.Dev.Q427b.PartM
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427b.PartM
open ReconfRes.Frozen
theorem selected_sub_of_iso (D : ConstrData) {R R' : ProofDag (CVar D.TV)} (h : R.Iso R') :
    D.selected R ⊆ D.selected R' := by
  obtain ⟨e, hl, he, -⟩ := h
  intro v hv
  simp only [ConstrData.selected, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  obtain ⟨x, y, z, h1, h2, h3, h4, h5⟩ := hv
  exact ⟨e x, e y, e z, iso_pivot e hl he h1, iso_pivot e hl he h2, iso_pivot e hl he h3,
    iso_anc e he h4, iso_anc e he h5⟩

/-- The decoder is invariant under isomorphism. -/
theorem selected_iso (D : ConstrData) {R R' : ProofDag (CVar D.TV)} (h : R.Iso R') :
    D.selected R = D.selected R' :=
  Finset.Subset.antisymm (selected_sub_of_iso D h) (selected_sub_of_iso D (iso_symm h))

end ReconfRes.Frozen.Dev.Q427b.PartM
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427b
/-! ## Stubs -/
alias selected_iso := ReconfRes.Frozen.Dev.Q427b.PartM.selected_iso

end ReconfRes.Frozen.Dev.Q427b
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427b.PartM
open ReconfRes.Frozen
variable {V : Type} [DecidableEq V] {k : ℕ} {R R' : ProofDag V} {Q : Finset (Fin R.n)}
  {Q' : Finset (Fin R'.n)} {φ : {i // i ∉ Q} ≃ {j // j ∉ Q'}} {q : Fin R.n} {q' : Fin R'.n}
/-! ### Moves -/
/-- The node map of a move: the block goes to its output `q'`. -/
def psi (Q : Finset (Fin R.n)) (Q' : Finset (Fin R'.n)) (φ : {i // i ∉ Q} ≃ {j // j ∉ Q'})
    (q' : Fin R'.n) (j : Fin R.n) : Fin R'.n :=
  if h : j ∈ Q then q' else (φ ⟨j, h⟩).1

theorem psi_of_mem {j : Fin R.n} (h : j ∈ Q) : psi Q Q' φ q' j = q' := dif_pos h

theorem psi_of_not_mem {j : Fin R.n} (h : j ∉ Q) : psi Q Q' φ q' j = (φ ⟨j, h⟩).1 := dif_neg h

theorem eq_q {R : ProofDag V} {Q : Finset (Fin R.n)} {q : Fin R.n} (hB : R.IsBlock k Q q)
    {p i : Fin R.n} (hp : p ∈ Q) (hi : i ∉ Q) (he : (p, i) ∈ R.edges) : p = q := by
  by_contra hne
  exact hi (hB.2.2 p hp hne ((mem_consumers _ _ _).2 he))

theorem move_parents (hB : R.IsBlock k Q q) (hB' : R'.IsBlock k Q' q')
    (hedge : ∀ i j : {i // i ∉ Q}, ((φ i).1, (φ j).1) ∈ R'.edges ↔ (i.1, j.1) ∈ R.edges)
    (hout : ∀ c : {i // i ∉ Q}, (q', (φ c).1) ∈ R'.edges ↔ (q, c.1) ∈ R.edges)
    (i : {i // i ∉ Q}) (j' : Fin R'.n) :
    (j', (φ i).1) ∈ R'.edges ↔ ∃ p, (p, i.1) ∈ R.edges ∧ psi Q Q' φ q' p = j' := by
  constructor
  · intro hj
    by_cases hj' : j' ∈ Q'
    · have hq : j' = q' := eq_q hB' hj' (φ i).2 hj
      rw [hq] at hj ⊢
      exact ⟨q, (hout i).1 hj, psi_of_mem hB.2.1.1⟩
    · obtain ⟨j, hjj⟩ : ∃ j, φ j = ⟨j', hj'⟩ := ⟨φ.symm ⟨j', hj'⟩, by simp⟩
      refine ⟨j.1, ?_, ?_⟩
      · rw [← hedge, hjj]; exact hj
      · rw [psi_of_not_mem j.2]
        rw [show (⟨j.1, j.2⟩ : {i // i ∉ Q}) = j from rfl, hjj]
  · rintro ⟨p, hp, rfl⟩
    by_cases hpQ : p ∈ Q
    · have hpq := eq_q hB hpQ i.2 hp
      rw [psi_of_mem hpQ]
      rw [hpq] at hp
      exact (hout i).2 hp
    · rw [psi_of_not_mem hpQ]; exact (hedge ⟨p, hpQ⟩ i).2 hp

theorem move_label (hB : R.IsBlock k Q q) (hlq : R'.label q' = R.label q)
    (hlab : ∀ i : {i // i ∉ Q}, R'.label (φ i) = R.label i)
    (i : {i // i ∉ Q}) (p : Fin R.n) (hp : (p, i.1) ∈ R.edges) :
    R'.label (psi Q Q' φ q' p) = R.label p := by
  by_cases hpQ : p ∈ Q
  · rw [eq_q hB hpQ i.2 hp, psi_of_mem hB.2.1.1, hlq]
  · rw [psi_of_not_mem hpQ, hlab]

theorem move_inj (hB : R.IsBlock k Q q) (hB' : R'.IsBlock k Q' q')
    (i : {i // i ∉ Q}) (p₁ p₂ : Fin R.n) (hp₁ : (p₁, i.1) ∈ R.edges) (hp₂ : (p₂, i.1) ∈ R.edges)
    (hh : psi Q Q' φ q' p₁ = psi Q Q' φ q' p₂) : p₁ = p₂ := by
  by_cases h1 : p₁ ∈ Q <;> by_cases h2 : p₂ ∈ Q
  · rw [eq_q hB h1 i.2 hp₁, eq_q hB h2 i.2 hp₂]
  · rw [psi_of_mem h1, psi_of_not_mem h2] at hh
    exact ((φ ⟨p₂, h2⟩).2 (by rw [← hh]; exact hB'.2.1.1)).elim
  · rw [psi_of_mem h2, psi_of_not_mem h1] at hh
    exact ((φ ⟨p₁, h1⟩).2 (by rw [hh]; exact hB'.2.1.1)).elim
  · rw [psi_of_not_mem h1, psi_of_not_mem h2] at hh
    simpa using congrArg Subtype.val (φ.injective (Subtype.ext hh))

theorem move_pivot (hB : R.IsBlock k Q q) (hB' : R'.IsBlock k Q' q')
    (hlq : R'.label q' = R.label q)
    (hlab : ∀ i : {i // i ∉ Q}, R'.label (φ i) = R.label i)
    (hedge : ∀ i j : {i // i ∉ Q}, ((φ i).1, (φ j).1) ∈ R'.edges ↔ (i.1, j.1) ∈ R.edges)
    (hout : ∀ c : {i // i ∉ Q}, (q', (φ c).1) ∈ R'.edges ↔ (q, c.1) ∈ R.edges)
    (i : {i // i ∉ Q}) {x : V} (h : R.HasPivot i.1 x) : R'.HasPivot (φ i).1 x :=
  hasPivot_transport (psi Q Q' φ q') h (move_parents hB hB' hedge hout i)
    (move_inj hB hB' i) (move_label hB hlq hlab i) (hlab i)

theorem move_anc_aux (hB : R.IsBlock k Q q) (hB' : R'.IsBlock k Q' q')
    (hedge : ∀ i j : {i // i ∉ Q}, ((φ i).1, (φ j).1) ∈ R'.edges ↔ (i.1, j.1) ∈ R.edges)
    (hout : ∀ c : {i // i ∉ Q}, (q', (φ c).1) ∈ R'.edges ↔ (q, c.1) ∈ R.edges)
    (hinp : ∀ i : {i // i ∉ Q}, i.1 ∈ R.inputs Q → (φ i).1 ∈ R'.inputs Q')
    {x : Fin R.n} (hx : x ∉ Q) {z : Fin R.n} (h : R.Anc x z) :
    (∀ hz : z ∉ Q, R'.Anc (φ ⟨x, hx⟩).1 (φ ⟨z, hz⟩).1) ∧ (z ∈ Q → R'.Anc (φ ⟨x, hx⟩).1 q') := by
  unfold ProofDag.Anc at h
  induction h with
  | refl => exact ⟨fun _ => Relation.ReflTransGen.refl, fun h => (hx h).elim⟩
  | @tail b c _ hbc ih =>
    by_cases hb : b ∈ Q <;> by_cases hc : c ∈ Q
    · exact ⟨fun h => (h hc).elim, fun _ => ih.2 hb⟩
    · refine ⟨fun hc' => ?_, fun h => (hc h).elim⟩
      have hbq := eq_q hB hb hc hbc
      rw [hbq] at hbc
      exact (ih.2 hb).tail ((hout ⟨c, hc'⟩).2 hbc)
    · refine ⟨fun h => (h hc).elim, fun _ => ?_⟩
      have hin : (φ ⟨b, hb⟩).1 ∈ R'.inputs Q' :=
        hinp ⟨b, hb⟩ ((mem_inputs _ _ _).2 ⟨hb, c, hc, hbc⟩)
      obtain ⟨-, j, hj, hje⟩ := (mem_inputs _ _ _).1 hin
      exact ((ih.1 hb).tail hje).trans (ancIn_anc _ (hB'.2.1.2 j hj))
    · refine ⟨fun hc' => ?_, fun h => (hc h).elim⟩
      exact (ih.1 hb).tail ((hedge ⟨b, hb⟩ ⟨c, hc'⟩).2 hbc)

end ReconfRes.Frozen.Dev.Q427b.PartM
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427b.PartM
open ReconfRes.Frozen
/-! ### The selected set along a move -/
/-- A node is a marker node of `v` if it has pivot `f v`, `a v` or `b v`. -/
def Marker (D : ConstrData) (R : ProofDag (CVar D.TV)) (v : D.TV) (n : Fin R.n) : Prop :=
  R.HasPivot n (CVar.f v) ∨ R.HasPivot n (CVar.hd (Head.a v)) ∨
    R.HasPivot n (CVar.hd (Head.b v))

theorem marker_inj (D : ConstrData) {R : ProofDag (CVar D.TV)}
    (hpiv : ∀ (i : Fin R.n) (x y : CVar D.TV), R.HasPivot i x → R.HasPivot i y → x = y)
    {v w : D.TV} {n : Fin R.n} (h1 : Marker D R v n) (h2 : Marker D R w n) : v = w := by
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    · have := hpiv _ _ _ h1 h2
      simpa using this

/-- The move lemma: a lost selected vertex has a marker node inside the block. -/
theorem lost_marker (D : ConstrData) {k : ℕ} {R R' : ProofDag (CVar D.TV)}
    {Q : Finset (Fin R.n)} {Q' : Finset (Fin R'.n)} {φ : {i // i ∉ Q} ≃ {j // j ∉ Q'}}
    {q : Fin R.n} {q' : Fin R'.n}
    (hB : R.IsBlock k Q q) (hB' : R'.IsBlock k Q' q')
    (hlq : R'.label q' = R.label q)
    (hlab : ∀ i : {i // i ∉ Q}, R'.label (φ i) = R.label i)
    (hedge : ∀ i j : {i // i ∉ Q}, ((φ i).1, (φ j).1) ∈ R'.edges ↔ (i.1, j.1) ∈ R.edges)
    (hout : ∀ c : {i // i ∉ Q}, (q', (φ c).1) ∈ R'.edges ↔ (q, c.1) ∈ R.edges)
    (hinp : ∀ i : {i // i ∉ Q}, i.1 ∈ R.inputs Q → (φ i).1 ∈ R'.inputs Q')
    {v : D.TV} (hv : v ∈ D.selected R \ D.selected R') : ∃ n ∈ Q, Marker D R v n := by
  rw [Finset.mem_sdiff] at hv
  obtain ⟨hv, hv'⟩ := hv
  simp only [ConstrData.selected, Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
  obtain ⟨x, y, z, h1, h2, h3, h4, h5⟩ := hv
  by_contra hno
  have hx : x ∉ Q := fun h => hno ⟨x, h, Or.inl h1⟩
  have hy : y ∉ Q := fun h => hno ⟨y, h, Or.inr (Or.inl h2)⟩
  have hz : z ∉ Q := fun h => hno ⟨z, h, Or.inr (Or.inr h3)⟩
  exact hv' ⟨_, _, _, move_pivot hB hB' hlq hlab hedge hout ⟨x, hx⟩ h1,
    move_pivot hB hB' hlq hlab hedge hout ⟨y, hy⟩ h2,
    move_pivot hB hB' hlq hlab hedge hout ⟨z, hz⟩ h3,
    (move_anc_aux hB hB' hedge hout hinp hx h4).1 hy,
    (move_anc_aux hB hB' hedge hout hinp hx h5).1 hz⟩

end ReconfRes.Frozen.Dev.Q427b.PartM
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427b.PartN
/-! ## Independent-set paths -/
theorem isStep_symm {τ : Type} [DecidableEq τ] (G : SimpleGraph τ) (K : ℕ) :
    ∀ {A B : Finset τ}, ISStep G K A B → ISStep G K B A := by
  intro A B ⟨hA, hB, cA, cB, h⟩
  refine ⟨hB, hA, cB, cA, ?_⟩
  rcases h with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
  · exact Or.inr ⟨v, Finset.mem_insert_self _ _, (Finset.erase_insert hv).symm⟩
  · exact Or.inl ⟨v, Finset.notMem_erase _ _, (Finset.insert_erase hv).symm⟩

theorem rtg_symm {α : Type} {r : α → α → Prop} (hr : ∀ {x y : α}, r x y → r y x) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hr hbc) ih

theorem indep_mono {τ : Type} {G : SimpleGraph τ} {A B : Finset τ} (h : IsIndepSet G A)
    (hBA : B ⊆ A) : IsIndepSet G B :=
  fun u hu v hv => h u (hBA hu) v (hBA hv)

theorem conn_sdiff {τ : Type} [DecidableEq τ] (G : SimpleGraph τ) (K : ℕ) (T : Finset τ)
    (hT : IsIndepSet G T) (S : Finset τ) :
    S ⊆ T → K ≤ (T \ S).card → ISConnected G K (T \ S) T := by
  induction S using Finset.induction_on with
  | empty => intro _ _; simp only [Finset.sdiff_empty]; exact Relation.ReflTransGen.refl
  | @insert a S haS ih =>
    intro hsub hcard
    have haT : a ∈ T := hsub (Finset.mem_insert_self _ _)
    have hsub' : S ⊆ T := (Finset.subset_insert _ _).trans hsub
    have hmono : T \ insert a S ⊆ T \ S :=
      Finset.sdiff_subset_sdiff (le_refl T) (Finset.subset_insert _ _)
    have hcard' : K ≤ (T \ S).card := hcard.trans (Finset.card_le_card hmono)
    refine Relation.ReflTransGen.head ?_ (ih hsub' hcard')
    refine ⟨indep_mono hT Finset.sdiff_subset, indep_mono hT Finset.sdiff_subset, hcard, hcard',
      Or.inl ⟨a, by simp, ?_⟩⟩
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · intro ⟨hxT, hxS⟩
      by_cases hxa : x = a
      · exact Or.inl hxa
      · exact Or.inr ⟨hxT, fun h => h.elim hxa hxS⟩
    · rintro (rfl | ⟨hxT, hx⟩)
      · exact ⟨haT, haS⟩
      · exact ⟨hxT, fun h => hx (Or.inr h)⟩

/-- Independent-set paths through a large common part. -/
theorem isConnected_of_inter {τ : Type} [DecidableEq τ] (G : SimpleGraph τ) (K : ℕ)
    (A B : Finset τ) (hA : IsIndepSet G A) (hB : IsIndepSet G B) (hAB : K ≤ (A ∩ B).card) :
    ISConnected G K A B := by
  have e1 : A \ (A \ B) = A ∩ B := by ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  have e2 : B \ (B \ A) = A ∩ B := by ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  have h1 : ISConnected G K (A \ (A \ B)) A :=
    conn_sdiff G K A hA _ Finset.sdiff_subset (by rw [e1]; exact hAB)
  have h2 : ISConnected G K (B \ (B \ A)) B :=
    conn_sdiff G K B hB _ Finset.sdiff_subset (by rw [e2]; exact hAB)
  rw [e1] at h1; rw [e2] at h2
  exact (rtg_symm (isStep_symm G K) h1).trans h2

/-! ## Counting -/
theorem card_eq_sum_groups {n b : ℕ} (S : Finset (Fin n × Fin b)) :
    S.card = ∑ u : Fin n, (Finset.univ.filter fun c : Fin b => (u, c) ∈ S).card := by
  have : S.card = (Finset.univ.filter fun x : Fin n × Fin b => x ∈ S).card := by
    congr 1; ext x; simp
  rw [this, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.card_filter]

theorem arith1 (b n K I X : ℕ) (h : b * K ≤ X + 1) (hX : X ≤ b * I + n) (hb : n + 2 ≤ b) :
    K ≤ I := by
  by_contra hc
  have : b * (I + 1) ≤ b * K := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_add, Nat.mul_one] at this
  omega

theorem sum_bound {n : ℕ} (f g : Fin n → ℕ) (I : Finset (Fin n)) (b : ℕ)
    (h : ∀ u, f u ≤ (if u ∈ I then b else 1) + g u) :
    ∑ u, f u ≤ b * I.card + n + ∑ u, g u := by
  have h1 : ∑ u, f u ≤ ∑ u, (b * (if u ∈ I then 1 else 0) + 1 + g u) := by
    refine Finset.sum_le_sum fun u _ => (h u).trans ?_
    split_ifs <;> simp
  refine h1.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp

/-- Counting: many selected twins give at least `K` decoded vertices. -/
theorem decoded_card (D : ConstrData) (R : ProofDag (CVar D.TV))
    (h : D.b * D.K ≤ (D.selected R).card + 1) : D.K ≤ (D.decoded R).card := by
  have hX := card_eq_sum_groups (D.selected R)
  have hs := sum_bound (fun u => (Finset.univ.filter fun c : Fin (D.n + 2 * D.k + 2) =>
      (u, c) ∈ D.selected R).card) (fun _ => 0) (D.decoded R) D.b (by
    intro u
    by_cases hu : u ∈ D.decoded R
    · rw [if_pos hu]
      have := Finset.card_le_univ (Finset.univ.filter fun c : Fin (D.n + 2 * D.k + 2) =>
        (u, c) ∈ D.selected R)
      simp only [Fintype.card_fin] at this
      simpa using this
    · rw [if_neg hu]
      simp only [ConstrData.decoded, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      omega)
  simp only [Finset.sum_const_zero, add_zero] at hs
  exact arith1 D.b D.n D.K _ _ h (hX ▸ hs) (by simp only [ConstrData.b]; omega)

end ReconfRes.Frozen.Dev.Q427b.PartN
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427b
alias decoded_card := ReconfRes.Frozen.Dev.Q427b.PartN.decoded_card

end ReconfRes.Frozen.Dev.Q427b
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427b.PartN
theorem arith2 (b n k K I X Y : ℕ) (h : b * K ≤ X + 1) (hX : X ≤ b * I + n + Y)
    (hY : Y ≤ 2 * k) (hb : b = n + 2 * k + 2) : K ≤ I := by
  by_contra hc
  have : b * (I + 1) ≤ b * K := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_add, Nat.mul_one] at this
  omega

/-- Counting: few lost twins keep `K` common decoded vertices. -/
theorem decoded_inter_card (D : ConstrData) (R R' : ProofDag (CVar D.TV))
    (h : D.b * D.K ≤ (D.selected R).card + 1)
    (h' : (D.selected R \ D.selected R').card ≤ 2 * D.k) :
    D.K ≤ (D.decoded R ∩ D.decoded R').card := by
  have hX := card_eq_sum_groups (D.selected R)
  have hXX := card_eq_sum_groups (D.selected R \ D.selected R')
  let g := fun u => (Finset.univ.filter fun c : Fin (D.n + 2 * D.k + 2) => (u, c) ∈ D.selected R)
  let g' := fun u => (Finset.univ.filter fun c : Fin (D.n + 2 * D.k + 2) => (u, c) ∈ D.selected R')
  have hd : ∀ u, (Finset.univ.filter fun c : Fin (D.n + 2 * D.k + 2) => (u, c) ∈ D.selected R \ D.selected R') =
      g u \ g' u := by
    intro u; ext c; simp [g, g']
  have hs := sum_bound (fun u => (g u).card) (fun u => (g u \ g' u).card)
      (D.decoded R ∩ D.decoded R') D.b (by
    intro u
    have hsplit : (g u).card = (g u ∩ g' u).card + (g u \ g' u).card :=
      (Finset.card_inter_add_card_sdiff _ _).symm
    by_cases hu : u ∈ D.decoded R ∩ D.decoded R'
    · rw [if_pos hu]
      have := Finset.card_le_univ (g u)
      simp only [Fintype.card_fin] at this
      simp only [ConstrData.b]; omega
    · rw [if_neg hu]
      rw [Finset.mem_inter] at hu
      by_cases h1 : u ∈ D.decoded R
      · have h2 : u ∉ D.decoded R' := fun h2 => hu ⟨h1, h2⟩
        simp only [ConstrData.decoded, Finset.mem_filter, Finset.mem_univ, true_and] at h2
        have : (g u ∩ g' u).card ≤ (g' u).card := Finset.card_le_card Finset.inter_subset_right
        have : (g' u).card ≤ 1 := by simp only [g']; omega
        omega
      · simp only [ConstrData.decoded, Finset.mem_filter, Finset.mem_univ, true_and] at h1
        have : (g u).card ≤ 1 := by simp only [g]; omega
        omega)
  have e2 : ∑ u, (g u \ g' u).card = (D.selected R \ D.selected R').card := by
    rw [hXX]; exact Finset.sum_congr rfl fun u _ => by rw [hd u]
  rw [e2] at hs
  exact arith2 D.b D.n D.k D.K _ _ _ h (hX ▸ hs) h' rfl

/-! ## Tightness along steps -/
theorem parents_iso_empty {V : Type} [DecidableEq V] {R R' : ProofDag V} (e : Fin R.n ≃ Fin R'.n)
    (hE : ∀ i j, (e i, e j) ∈ R'.edges ↔ (i, j) ∈ R.edges) (i : Fin R.n) :
    R'.parents (e i) = ∅ ↔ R.parents i = ∅ := by
  simp only [ProofDag.parents, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
  constructor
  · intro h j hj; exact h ((hE j i).2 hj)
  · intro h x hx; obtain ⟨j, rfl⟩ := e.surjective x; exact h ((hE j i).1 hx)

theorem axiomMultiset_iso {V : Type} [DecidableEq V] {R R' : ProofDag V} (h : R.Iso R') :
    R'.axiomMultiset = R.axiomMultiset := by
  obtain ⟨e, hL, hE, -⟩ := h
  unfold ProofDag.axiomMultiset
  rw [← Finset.map_univ_equiv e, Finset.filter_map, Finset.map_val, Multiset.map_map]
  have : (fun x => R'.parents x = ∅) ∘ e.toEmbedding = fun i => R.parents i = ∅ := by
    funext i; exact propext (parents_iso_empty e hE i)
  simp only [this]
  congr 1
  funext i; exact hL i

/-- Tightness is preserved along a frozen step. -/
theorem tight_of_step (D : ConstrData) (hD : D.Valid) {R R' : ProofDag (CVar D.TV)}
    (hR : D.IsTight R) (h : FrozenStep D.k D.formula D.W (2 * D.α - 1) R R') : D.IsTight R' := by
  obtain ⟨v1, v2, hst⟩ := h
  have hk : 1 ≤ D.k := by have := hD.2.2.2.1; omega
  have hax : R'.axiomMultiset = R.axiomMultiset := by
    rcases hst with hiso | hm | hm
    · exact axiomMultiset_iso hiso
    · exact ((proposition_3_3 D.k hk D.formula D.W (2 * D.α - 1)).1 R R'
        ⟨v1, v2, Or.inl hm⟩).symm
    · exact ((proposition_3_3 D.k hk D.formula D.W (2 * D.α - 1)).1 R R'
        ⟨v1, v2, Or.inr hm⟩).symm
  have hpos : 1 ≤ R.size := by
    unfold ProofDag.size; have := R.sink.2; omega
  have h4 := hR.2.2.2
  have h5 := v2.2.2.2
  exact ⟨v2.1, v2.2.1, hax.trans hR.2.2.1, by omega⟩

end ReconfRes.Frozen.Dev.Q427b.PartN
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427b
alias tight_of_step := ReconfRes.Frozen.Dev.Q427b.PartN.tight_of_step

alias decoded_inter_card := ReconfRes.Frozen.Dev.Q427b.PartN.decoded_inter_card

end ReconfRes.Frozen.Dev.Q427b
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427b.PartN
/-! ## Trees and the source count -/
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

theorem heads_card (D : ConstrData) (hD : D.Valid) : D.heads.card + 2 = 4 * D.m := by
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
  have hh := heads_card D hD
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

end ReconfRes.Frozen.Dev.Q427b.PartN
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427b
alias srcs_card := ReconfRes.Frozen.Dev.Q427b.PartN.srcs_card

end ReconfRes.Frozen.Dev.Q427b
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427b.PartM
open ReconfRes.Frozen
/-- A frozen move between tight refutations loses at most `k` selected twins (each lost twin has
a marker pivot node inside the replaced block). -/
theorem selected_move (D : ConstrData) (hD : D.Valid) {k : ℕ} (hk : 1 ≤ k) {R R' : ProofDag (CVar D.TV)}
    (hR : D.IsTight R) (hR' : D.IsTight R')
    (hpiv : ∀ (i : Fin R.n) (x y : CVar D.TV), R.HasPivot i x → R.HasPivot i y → x = y)
    {Q : Finset (Fin R.n)} {Q' : Finset (Fin R'.n)} {φ : {i // i ∉ Q} ≃ {j // j ∉ Q'}}
    (hmv : FrozenMoveVia k R R' Q Q' φ) :
    (D.selected R \ D.selected R').card ≤ k := by
  have h47 := (lemma_3_47 D.formula R.axiomMultiset (by
    rw [hR.2.2.1]; unfold ConstrData.inventory; simp only [Multiset.card_map]
    have : Src.CA ∈ D.srcs := by unfold ConstrData.srcs; simp
    exact Finset.card_pos.mpr ⟨_, this⟩)).2 k R R' Q Q' φ hk hR.1 hR.2.1 rfl
    (by rw [hR.2.2.1]; unfold ConstrData.inventory; simp; have := hR.2.2.2
        rw [Q427b.srcs_card D hD]; omega)
    hR'.1 hR'.2.1 (by rw [hR.2.2.1, hR'.2.2.1])
    (by rw [hR.2.2.1]; unfold ConstrData.inventory; simp; have := hR'.2.2.2
        rw [Q427b.srcs_card D hD]; omega) hmv
  have hinp : ∀ i : {i // i ∉ Q}, i.1 ∈ R.inputs Q → (φ i).1 ∈ R'.inputs Q' :=
    fun i h => (h47.2.2.2.2.1 i).1 h
  obtain ⟨⟨q, q', hB, hB', hlq, hlab, hedge, -, hout, -, -⟩, hax, -⟩ := hmv
  have hQk : Q.card ≤ k := by
    have h := hB.1
    rwa [Finset.filter_true_of_mem] at h
    intro i hi
    exact Finset.nonempty_iff_ne_empty.2 (hax i hi)
  have key := fun v (hv : v ∈ D.selected R \ D.selected R') =>
    lost_marker D hB hB' hlq hlab hedge hout hinp hv
  classical
  let g : D.TV → Fin R.n := fun v =>
    if h : ∃ n ∈ Q, Marker D R v n then h.choose else q
  have hg : ∀ v ∈ D.selected R \ D.selected R', g v ∈ Q ∧ Marker D R v (g v) := by
    intro v hv
    have h := key v hv
    simp only [g, dif_pos h]
    exact h.choose_spec
  refine (Finset.card_le_card_of_injOn g (fun v hv => (hg v hv).1) ?_).trans hQk
  intro v hv w hw hvw
  exact marker_inj D hpiv (hg v hv).2 (hvw ▸ (hg w hw).2)

end ReconfRes.Frozen.Dev.Q427b.PartM
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen.Dev.Q427b
alias selected_move := ReconfRes.Frozen.Dev.Q427b.PartM.selected_move

alias isConnected_of_inter := ReconfRes.Frozen.Dev.Q427b.PartN.isConnected_of_inter

/-! ## Assembly -/
theorem tight_width {D : ConstrData} {R R' : ProofDag (CVar D.TV)}
    (h : FrozenStep D.k D.formula D.W (2 * D.α - 1) R R') : R'.width ≤ D.W := h.2.1.2.2.1

theorem part2 (D : ConstrData) (hD : D.Valid) {R R' : ProofDag (CVar D.TV)}
    (hR : D.IsTight R) (hR' : D.IsTight R') (hW : R.width ≤ D.W) (hW' : R'.width ≤ D.W)
    (hm : FrozenMove D.k R R') :
    (symmDiff (D.selected R) (D.selected R')).card ≤ 2 * D.k ∧
      D.K ≤ (D.decoded R ∩ D.decoded R').card := by
  have hk : 1 ≤ D.k := by have := hD.2.2.2.1; omega
  obtain ⟨Q, Q', φ, hmv⟩ := hm
  obtain ⟨c1, -, p1⟩ := decoding_capacity_two D hD R hR hW
  obtain ⟨c2, -, p2⟩ := decoding_capacity_two D hD R' hR' hW'
  have l1 := selected_move D hD hk hR hR' p1 hmv
  have hrev : FrozenMoveVia D.k R' R Q' Q φ.symm := by
    have h47 := (lemma_3_47 D.formula R.axiomMultiset (by
      rw [hR.2.2.1]; unfold ConstrData.inventory; simp only [Multiset.card_map]
      have : Src.CA ∈ D.srcs := by unfold ConstrData.srcs; simp
      exact Finset.card_pos.mpr ⟨_, this⟩)).2 D.k R R' Q Q' φ hk hR.1 hR.2.1 rfl
      (by rw [hR.2.2.1]; unfold ConstrData.inventory; simp; have := hR.2.2.2; rw [srcs_card D hD]; omega)
      hR'.1 hR'.2.1 (by rw [hR.2.2.1, hR'.2.2.1])
      (by rw [hR.2.2.1]; unfold ConstrData.inventory; simp; have := hR'.2.2.2; rw [srcs_card D hD]; omega) hmv
    exact h47.2.2.2.2.2.2.2
  have l2 := selected_move D hD hk hR' hR p2 hrev
  refine ⟨?_, decoded_inter_card D R R' c1 (by omega)⟩
  rw [symmDiff_def, Finset.sup_eq_union]
  exact (Finset.card_union_le _ _).trans (by omega)

end ReconfRes.Frozen.Dev.Q427b
end

section
open MultiplierAssoc206.Resolution
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ReconfRes.Frozen
open Dev.Q427b in
theorem chk_lemma_3_61 (D : ConstrData) (hD : D.Valid) :
    (∀ R : ProofDag (CVar D.TV), D.IsTight R → R.width ≤ D.W →
      IsIndepSet D.J0 (D.decoded R) ∧ D.K ≤ (D.decoded R).card) ∧
    (∀ R R' : ProofDag (CVar D.TV), D.IsTight R → D.IsTight R' →
      FrozenAdj D.k D.formula D.W (2 * D.α - 1) R R' →
      (symmDiff (D.selected R) (D.selected R')).card ≤ 2 * D.k ∧
      D.K ≤ (D.decoded R ∩ D.decoded R').card) ∧
    (∀ R R' : ProofDag (CVar D.TV), D.IsTight R → R.width ≤ D.W →
      FrozenConnected D.k D.formula D.W (2 * D.α - 1) R R' →
      ISConnected D.J0 D.K (D.decoded R) (D.decoded R')) := by
  refine ⟨fun R hR hW => ?_, fun R R' hR hR' hadj => ?_, fun R R' hR hW hc => ?_⟩
  · obtain ⟨c, hi, -⟩ := decoding_capacity_two D hD R hR hW
    exact ⟨hi, decoded_card D R c⟩
  · obtain ⟨v1, v2, hm | hm⟩ := hadj
    · exact part2 D hD hR hR' v1.2.2.1 v2.2.2.1 hm
    · obtain ⟨a, b⟩ := part2 D hD hR' hR v2.2.2.1 v1.2.2.1 hm
      rw [symmDiff_comm, Finset.inter_comm]; exact ⟨a, b⟩
  · have key : ∀ Z, FrozenConnected D.k D.formula D.W (2 * D.α - 1) R Z →
        D.IsTight Z ∧ Z.width ≤ D.W ∧ ISConnected D.J0 D.K (D.decoded R) (D.decoded Z) := by
      intro Z hZ
      induction hZ with
      | refl => exact ⟨hR, hW, Relation.ReflTransGen.refl⟩
      | @tail Y Z _ hst ih =>
        obtain ⟨tY, wY, cY⟩ := ih
        have tZ := tight_of_step D hD tY hst
        have wZ := tight_width hst
        refine ⟨tZ, wZ, ?_⟩
        obtain ⟨-, -, hiso | hm | hm⟩ := hst
        · rw [show D.decoded Z = D.decoded Y by unfold ConstrData.decoded; rw [selected_iso D hiso]]
          exact cY
        · obtain ⟨cY', iY, -⟩ := decoding_capacity_two D hD Y tY wY
          obtain ⟨cZ', iZ, -⟩ := decoding_capacity_two D hD Z tZ wZ
          exact cY.trans (isConnected_of_inter D.J0 D.K _ _ iY iZ (part2 D hD tY tZ wY wZ hm).2)
        · obtain ⟨cY', iY, -⟩ := decoding_capacity_two D hD Y tY wY
          obtain ⟨cZ', iZ, -⟩ := decoding_capacity_two D hD Z tZ wZ
          have := (part2 D hD tZ tY wZ wY hm).2
          rw [Finset.inter_comm] at this
          exact cY.trans (isConnected_of_inter D.J0 D.K _ _ iY iZ this)
    exact (key R' hc).2.2

end ReconfRes.Frozen
end

open ReconfRes.Frozen in
theorem solution : type_of% @ReconfRes.Frozen.chk_lemma_3_61 := @ReconfRes.Frozen.chk_lemma_3_61
