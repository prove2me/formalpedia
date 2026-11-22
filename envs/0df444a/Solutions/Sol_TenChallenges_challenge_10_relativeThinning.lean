-- Prove2me | solution 1 for TenChallenges.challenge_10_relativeThinning
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T11:03:40.723171+00:00
-- url     : https://prove2.me/submissions/16eb3a09-77b5-45fe-b8e8-45999905c387

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice

/-! # Relative thinning of a countable graph -/

set_option autoImplicit false

universe u

namespace TenChallenges.Continuation.ThinningSelection

/-- A countable relation admits finite outgoing selections of prescribed sizes
with finite incoming selections on `C \ T` if each finite forbidden subset of
`C \ T` leaves only finitely many sources outside it short of their quotas. -/
theorem exists_outgoing_selection {V : Type u} [Countable V] (R : V → V → Prop)
    (C T : Set V) (k : V → ℕ)
    (henough : ∀ x ∈ C, (k x : ℕ∞) ≤ {y | R x y}.encard)
    (hfinite : ∀ F : Set V, F.Finite → F ⊆ C \ T →
      {x | x ∈ C ∧ x ∉ F ∧ {y | R x y ∧ y ∉ F}.encard < (k x : ℕ∞)}.Finite) :
    ∃ A : V → Finset V,
      (∀ x ∈ C, (A x).card = k x ∧ ∀ y ∈ A x, R x y) ∧
      ∀ y ∈ C \ T, {x | x ∈ C ∧ y ∈ A x}.Finite := by
  classical
  let : Encodable V := Encodable.ofCountable V
  let forbidden (n : ℕ) : Set V := {y | Encodable.encode y < n ∧ y ∈ C \ T}
  let viable (x : V) (n : ℕ) : Prop := (k x : ℕ∞) ≤ {y | R x y ∧ y ∉ forbidden n}.encard
  let cutoff (x : V) : ℕ := Nat.findGreatest (viable x) (Encodable.encode x)
  have hcutoff : ∀ x ∈ C, viable x (cutoff x) := fun x hx =>
    Nat.findGreatest_spec (P := viable x) (Nat.zero_le _) (by
      simpa [viable, forbidden] using henough x hx)
  have hselect : ∀ x ∈ C, ∃ s : Finset V, s.card = k x ∧
      ∀ y ∈ s, R x y ∧ y ∉ forbidden (cutoff x) := fun x hx =>
    let ⟨t, ht, hcard⟩ := Set.exists_subset_encard_eq (hcutoff x hx)
    let hfin : t.Finite := Set.encard_ne_top_iff.mp fun htop =>
      ENat.natCast_ne_top (k x) (hcard.symm.trans htop)
    ⟨hfin.toFinset,
      ENat.natCast_inj.mp (by
        rw [← Set.encard_coe_eq_coe_finsetCard, hfin.coe_toFinset, hcard]),
      fun y hy => ht (hfin.mem_toFinset.mp hy)⟩
  let A (x : V) : Finset V := if hx : x ∈ C then (hselect x hx).choose else ∅
  have hA : ∀ x ∈ C, (A x).card = k x ∧
      ∀ y ∈ A x, R x y ∧ y ∉ forbidden (cutoff x) := fun x hx => by
    simpa only [A, dif_pos hx] using (hselect x hx).choose_spec
  refine ⟨A, fun x hx => ⟨(hA x hx).1, fun y hy => ((hA x hx).2 y hy).1⟩, ?_⟩
  intro y hy
  exact
    let n := Encodable.encode y + 1
    let hcodes : {x : V | Encodable.encode x < n}.Finite :=
      (Set.finite_lt_nat n).preimage
        (Encodable.encode_injective : Function.Injective (Encodable.encode : V → ℕ)).injOn
    let hshort := hfinite (forbidden n) (hcodes.subset fun _ hx => hx.1) (fun _ hx => hx.2)
    (hcodes.union hshort).subset fun x hx =>
      (lt_or_ge (Encodable.encode x) n).elim Or.inl fun hnx => Or.inr
        ⟨hx.1, fun hxF => (Nat.not_lt_of_ge hnx) hxF.1,
          lt_of_not_ge fun hv =>
            let hle : n ≤ cutoff x := Nat.le_findGreatest (P := viable x) hnx hv
            ((hA x hx.1).2 y hx.2).2 ⟨lt_of_lt_of_le (Nat.lt_succ_self _) hle, hy⟩⟩

end TenChallenges.Continuation.ThinningSelection

namespace TenChallenges.Continuation.ThinningGraph


variable {V : Type u} (G : SimpleGraph V)

/-- A finite set of locally finite vertices can exhaust the quota of only finitely many vertices. -/
theorem finite_deficient_of_graph (C T : Set V) (k : V → ℕ) {J : SimpleGraph V}
    (hJG : J ≤ G)
    (hquota : ∀ v ∈ C, (k v : ℕ∞) ≤ (J.neighborSet v).encard)
    (hfin : ∀ w ∈ C \ T, (J.neighborSet w).Finite)
    (F : Set V) (hF : F.Finite) (hFsub : F ⊆ C \ T) :
    {v | v ∈ C ∧ v ∉ F ∧ {w | G.Adj v w ∧ w ∉ F}.encard < (k v : ℕ∞)}.Finite := by
  have hfinUnion : (⋃ w ∈ F, J.neighborSet w).Finite :=
    Set.Finite.biUnion hF fun w hw => hfin w (hFsub hw)
  refine hfinUnion.subset ?_
  intro v hv
  by_contra hvnot
  have hsub : J.neighborSet v ⊆ {w | G.Adj v w ∧ w ∉ F} := by
    intro w hw
    exact ⟨hJG hw, fun hwF => hvnot (Set.mem_iUnion₂.mpr ⟨w, hwF, J.adj_symm hw⟩)⟩
  exact (not_lt_of_ge ((hquota v hv.1).trans (Set.encard_le_encard hsub))) hv.2.2

private def selectionGraph (C : Set V) (A : V → Finset V)
    (hA : ∀ v ∈ C, ∀ w ∈ A v, G.Adj v w) : SimpleGraph V where
  Adj v w := (v ∈ C ∧ w ∈ A v) ∨ (w ∈ C ∧ v ∈ A w)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun v h =>
    let hv := h.elim id id
    G.irrefl (hA v hv.1 v hv.2)⟩

/-- Symmetrizing outgoing selections retains the quotas and local finiteness. -/
theorem graph_of_outgoing_selection (S C T : Set V) (k : V → ℕ)
    (hboundary : ∀ v ∈ C, G.neighborSet v ⊆ S ∪ C) {A : V → Finset V}
    (hA : ∀ v ∈ C, (A v).card = k v ∧ ∀ w ∈ A v, G.Adj v w)
    (hfin : ∀ w ∈ C \ T, {v | v ∈ C ∧ w ∈ A v}.Finite) :
    ∃ J : SimpleGraph V, J ≤ G ∧
      (∀ v ∈ C, (k v : ℕ∞) ≤ (J.neighborSet v).encard) ∧
      (∀ w ∈ C \ T, (J.neighborSet w).Finite) ∧
      (∀ v w, J.Adj v w → (v ∈ C ∨ w ∈ C) ∧ v ∈ S ∪ C ∧ w ∈ S ∪ C) := by
  let J := selectionGraph G C A (fun v hv => (hA v hv).2)
  have hJG : J ≤ G := by
    intro v w h
    exact h.elim (fun h => (hA v h.1).2 w h.2)
      (fun h => ((hA w h.1).2 v h.2).symm)
  refine ⟨J, hJG, ?_, ?_, ?_⟩
  · intro v hv
    have hsub : (A v : Set V) ⊆ J.neighborSet v := fun _ hw => Or.inl ⟨hv, hw⟩
    simpa only [Set.encard_coe_eq_coe_finsetCard, (hA v hv).1] using Set.encard_le_encard hsub
  · intro w hw
    exact ((A w).finite_toSet.union (hfin w hw)).subset
      fun _ h => h.elim (fun h => Or.inl h.2) Or.inr
  · intro v w h
    have hadj := hJG h
    rcases h with ⟨hv, _⟩ | ⟨hw, _⟩
    · exact ⟨Or.inl hv, Or.inr hv, hboundary v hv hadj⟩
    · exact ⟨Or.inr hw, hboundary w hw hadj.symm, Or.inr hw⟩

end TenChallenges.Continuation.ThinningGraph

namespace TenChallenges.Continuation

/-- A graph can retain the prescribed finite neighbour quotas, with finite degree at
each vertex of `C \ T`, exactly when every finite subset of `C \ T` leaves only
finitely many vertices of `C` outside it with a deficit. The retained edges all
meet `C` and have both endpoints in `S ∪ C`. -/
theorem relative_thinning_iff {V : Type u} [Countable V] (G : SimpleGraph V)
    (S C T : Set V) (k : V → ℕ)
    (hboundary : ∀ v ∈ C, G.neighborSet v ⊆ S ∪ C)
    (henough : ∀ v ∈ C, (k v : ℕ∞) ≤ (G.neighborSet v).encard) :
    (∀ F : Set V, F.Finite → F ⊆ C \ T →
      {v | v ∈ C ∧ v ∉ F ∧ {w | G.Adj v w ∧ w ∉ F}.encard < (k v : ℕ∞)}.Finite) ↔
    ∃ J : SimpleGraph V, J ≤ G ∧
      (∀ v ∈ C, (k v : ℕ∞) ≤ (J.neighborSet v).encard) ∧
      (∀ w ∈ C \ T, (J.neighborSet w).Finite) ∧
      (∀ v w, J.Adj v w → (v ∈ C ∨ w ∈ C) ∧ v ∈ S ∪ C ∧ w ∈ S ∪ C) :=
  ⟨fun h =>
    let ⟨_, hA, hfin⟩ := ThinningSelection.exists_outgoing_selection G.Adj C T k henough h
    ThinningGraph.graph_of_outgoing_selection G S C T k hboundary hA hfin,
   fun ⟨_, hJG, hquota, hfin, _⟩ =>
    ThinningGraph.finite_deficient_of_graph G C T k hJG hquota hfin⟩

end TenChallenges.Continuation

theorem solution {V : Type u} [Countable V] (G : SimpleGraph V)
    (S C T : Set V) (k : V → ℕ)
    (hboundary : ∀ v ∈ C, G.neighborSet v ⊆ S ∪ C)
    (henough : ∀ v ∈ C, (k v : ℕ∞) ≤ (G.neighborSet v).encard) :
    (∀ F : Set V, F.Finite → F ⊆ C \ T →
      {v | v ∈ C ∧ v ∉ F ∧ {w | G.Adj v w ∧ w ∉ F}.encard < (k v : ℕ∞)}.Finite) ↔
    ∃ J : SimpleGraph V, J ≤ G ∧
      (∀ v ∈ C, (k v : ℕ∞) ≤ (J.neighborSet v).encard) ∧
      (∀ w ∈ C \ T, (J.neighborSet w).Finite) ∧
      (∀ v w, J.Adj v w → (v ∈ C ∨ w ∈ C) ∧ v ∈ S ∪ C ∧ w ∈ S ∪ C) :=
  TenChallenges.Continuation.relative_thinning_iff G S C T k hboundary henough

#print axioms solution
