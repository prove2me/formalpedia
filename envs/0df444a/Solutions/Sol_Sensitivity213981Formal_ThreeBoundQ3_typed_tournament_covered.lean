-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundQ3.typed_tournament_covered
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:32:24.616417+00:00
-- url     : https://prove2.me/submissions/9d8f637e-d94a-4138-96fe-bcfcb02167f1

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_Q3Enumeration
import Definitions.Def_Sensitivity213981Formal_TournamentHighRows
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundQ2_orientations_complete
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundQ2_outCount_orientation_eq_card


namespace Sensitivity213981Formal
section
/-
Semantic high-row bounds for the graded q2/q3 transfer.

The finite high set is connected to actual guard failure sets: every arc to
a high head selects a guard-true child and therefore consumes a failure of
its tail. The tournament edge double count is proved here, not assumed.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace TournamentHighRows
open scoped Classical BigOperators

variable {V X : Type}







theorem mem_arcs (R : V → V → Prop) (S : Finset V) (v w : V) :
    (v,w) ∈ arcs R S ↔ v ∈ S ∧ w ∈ S ∧ R v w := by
  classical
  constructor
  · intro h
    have hf := Finset.mem_filter.mp h
    have hp := Finset.mem_product.mp hf.1
    exact ⟨hp.1, hp.2, hf.2⟩
  · rintro ⟨hv,hw,hR⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv,hw⟩,hR⟩

theorem reverse_arcs_card (R : V → V → Prop) (S : Finset V) :
    (arcs (fun v w => R w v) S).card = (arcs R S).card := by
  classical
  refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
  · intro p hp
    rcases p with ⟨v,w⟩
    rcases (mem_arcs _ S v w).1 hp with ⟨hv,hw,hR⟩
    exact (mem_arcs R S w v).2 ⟨hw,hv,hR⟩
  · intro p hp q hq heq
    exact Prod.swap_injective heq
  · intro p hp
    rcases p with ⟨v,w⟩
    rcases (mem_arcs R S v w).1 hp with ⟨hv,hw,hR⟩
    exact ⟨(w,v), (mem_arcs _ S w v).2 ⟨hw,hv,hR⟩, rfl⟩

theorem arcs_disjoint_reverse (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) : Disjoint (arcs R S) (arcs (fun v w => R w v) S) := by
  classical
  apply Finset.disjoint_left.mpr
  rintro ⟨v,w⟩ hp hq
  have hvw := ((mem_arcs R S v w).1 hp).2.2
  have hwv := ((mem_arcs _ S v w).1 hq).2.2
  have hne : v ≠ w := by
    intro he
    subst w
    exact hR.loopless v hvw
  exact ((hR.orient v w hne).1 hvw) hwv

theorem arcs_union_reverse (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) :
    arcs R S ∪ arcs (fun v w => R w v) S = S.offDiag := by
  classical
  ext p
  rcases p with ⟨v,w⟩
  simp only [Finset.mem_union, mem_arcs, Finset.mem_offDiag]
  constructor
  · rintro (⟨hv,hw,hvw⟩ | ⟨hv,hw,hwv⟩)
    · refine ⟨hv,hw,?_⟩
      intro he
      subst w
      exact hR.loopless v hvw
    · refine ⟨hv,hw,?_⟩
      intro he
      subst w
      exact hR.loopless v hwv
  · rintro ⟨hv,hw,hne⟩
    by_cases hvw : R v w
    · exact Or.inl ⟨hv,hw,hvw⟩
    · exact Or.inr ⟨hv,hw,(hR.orient w v hne.symm).2 hvw⟩

/-- Every unordered pair contributes exactly one directed edge. -/
theorem twice_arcs_card (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) : 2 * (arcs R S).card = S.card * S.card - S.card := by
  classical
  have h := Finset.card_union_of_disjoint (arcs_disjoint_reverse R hR S)
  rw [arcs_union_reverse R hR S, reverse_arcs_card R S, Finset.offDiag_card] at h
  omega

theorem arcs_eq_union_rows (R : V → V → Prop) (S : Finset V) :
    arcs R S = S.biUnion (fun v => ({v} : Finset V).product (outNeighbors R S v)) := by
  classical
  ext p
  rcases p with ⟨v,w⟩
  constructor
  · intro hp
    rcases (mem_arcs R S v w).1 hp with ⟨hv,hw,hR⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨v,hv,Finset.mem_product.mpr ⟨Finset.mem_singleton_self v,?_⟩⟩
    exact Finset.mem_filter.mpr ⟨hw,hR⟩
  · intro hp
    obtain ⟨u,hu,hp⟩ := Finset.mem_biUnion.mp hp
    rcases Finset.mem_product.mp hp with ⟨hvu,hw⟩
    have heq : v = u := Finset.mem_singleton.mp hvu
    subst u
    rcases Finset.mem_filter.mp hw with ⟨hw,hR⟩
    exact (mem_arcs R S v w).2 ⟨hu,hw,hR⟩

theorem arcs_card_le_sum_out (R : V → V → Prop) (S : Finset V) :
    (arcs R S).card ≤  ∑ v ∈ S, (outNeighbors R S v).card := by
  classical
  rw [arcs_eq_union_rows R S]
  calc
    (S.biUnion (fun v => ({v} : Finset V).product (outNeighbors R S v))).card
        ≤  ∑ v ∈ S, (({v} : Finset V).product (outNeighbors R S v)).card :=
      Finset.card_biUnion_le
    _ = ∑ v ∈ S, (outNeighbors R S v).card := by simp

/-- Necessary budget inequality for every finite tournament and every budget vector. -/
theorem budget_sum_bound (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) (budget : V → ℕ)
    (hbudget : ∀ v ∈ S, (outNeighbors R S v).card ≤  budget v) :
    S.card * (S.card - 1) ≤  2 * ∑ v ∈ S, budget v := by
  have hsum : (arcs R S).card ≤  ∑ v ∈ S, budget v :=
    (arcs_card_le_sum_out R S).trans (Finset.sum_le_sum hbudget)
  have htwice := Nat.mul_le_mul_left 2 hsum
  rw [twice_arcs_card R hR S] at htwice
  simpa only [Nat.mul_sub_left_distrib, Nat.mul_one] using htwice



section GuardSemantics
variable [Fintype V]















end GuardSemantics
end TournamentHighRows








end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/-
Canonical numbering and actual tournament-degree bridge for the executable
q2 enumerator.  This connects combinatorial coverage to finite tournaments,
without replacing sensitivity charging by numerical assumptions.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundQ2
open scoped Classical BigOperators

























theorem card_filter_equiv {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → Prop) [DecidablePred p] :
    ((Finset.univ : Finset A).filter fun a => p (e a)).card =
      ((Finset.univ : Finset B).filter p).card := by
  classical
  apply Finset.card_bij (fun a _ => e a)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ hab
    exact e.injective hab
  · intro b hb
    exact ⟨e.symm b, by simpa using hb, e.apply_symm_apply b⟩

theorem length_filter_ofFn {A : Type} {n : ℕ} (f : Fin n → A) (p : A → Bool) :
    ((List.ofFn f).filter p).length =
      ((Finset.univ : Finset (Fin n)).filter fun i => p (f i) = true).card := by
  rw [List.ofFn_eq_map, ← List.countP_eq_length_filter, List.countP_map]
  symm
  simpa [Function.comp_def] using
    (List.nodup_finRange n).card_eq_countP (P := fun i => p (f i) = true)



end ThreeBoundQ2





end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- A complete executable eleven-type enumerator, with canonical budget order.
   The exact records retain all 41 coordinates used by the q3 transfer. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundQ3






export ThreeBoundQ2 (edges outCount orientations directedEdges orientationBits)





theorem typeLists_complete (lo : ℕ) (ts : List Kind)
    (hs : ts.Pairwise (fun a b => orderKey a≤ orderKey b))
    (hlo : ∀t∈ts,lo≤ orderKey t) : ts∈typeLists lo ts.length := by
  induction ts generalizing lo with
  | nil => simp [typeLists]
  | cons t ts ih =>
    obtain ⟨ht,hs⟩ := List.pairwise_cons.mp hs
    simp only [List.length_cons,typeLists]
    apply List.mem_flatMap.mpr
    refine ⟨t,List.mem_finRange t,?_⟩
    rw [if_pos (hlo t (by simp))]
    exact List.mem_map.mpr ⟨ts,ih (orderKey t) hs ht,rfl⟩









theorem allCases_complete (ts : List Kind) (ds : List Bool)
    (hn : ts.length≤ 9) (hs : ts.Pairwise (fun a b => orderKey a≤ orderKey b))
    (ht : allowedTypes ts) (hlen : ds.length=(edges ts.length).length)
    (hb : ∀v : Fin ts.length,outCount (edges ts.length) ds v≤ budget (ts.get v)) :
    (ts,ds)∈allCases := by
  apply List.mem_flatMap.mpr
  refine ⟨ts.length,List.mem_range.mpr (by omega),?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨ts,typeLists_complete 0 ts hs (fun _ _ => Nat.zero_le _),?_⟩
  rw [casesFor,if_pos ht]
  exact List.mem_map.mpr ⟨ds,ThreeBoundQ2.orientations_complete _ _ _ hlen hb,rfl⟩





theorem records_complete (ts : List Kind) (ds : List Bool)
    (hn : ts.length≤ 9) (hs : ts.Pairwise (fun a b => orderKey a≤ orderKey b))
    (ht : allowedTypes ts) (hlen : ds.length=(edges ts.length).length)
    (hb : ∀v : Fin ts.length,outCount (edges ts.length) ds v≤ budget (ts.get v)) :
    record (ts,ds)∈records :=
  List.mem_map.mpr ⟨(ts,ds),allCases_complete ts ds hn hs ht hlen hb,rfl⟩

end ThreeBoundQ3



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Canonical numbering and every sorted prefix budget for the q3 enumerator. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundQ3
open scoped Classical BigOperators

 theorem exists_sorted_numbering {V : Type} [Fintype V] (tag : V → Kind) :
    ∃ e : Fin (Fintype.card V) ≃ V, Monotone (fun i => orderKey (tag (e i))) := by
  classical
  let idx := Fintype.equivFin V
  let key : V → ℕ ×ₗ Fin (Fintype.card V) := fun v => toLex (orderKey (tag v),idx v)
  have hinj : Function.Injective key := by
    intro a b h
    apply idx.injective
    exact congrArg (fun p => (ofLex p).2) h
  letI : LinearOrder V := LinearOrder.lift' key hinj
  let e := Fintype.orderIsoFinOfCardEq V rfl
  refine ⟨e.toEquiv,?_⟩
  intro i j hij
  exact Prod.Lex.monotone_fst (key (e i)) (key (e j)) (e.monotone hij)

theorem prefix_budget_bound {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : TournamentHighRows.IsTournament R) (b : Fin n → ℕ)
    (hb : ∀ v, ((Finset.univ : Finset (Fin n)).filter (R v)).card≤ b v)
    (k : ℕ) (hk : k≤ n) :
    k*(k-1)/2≤ ((List.ofFn b).take k).sum := by
  classical
  let K : Finset (Fin n) := Finset.univ.filter fun v => v.val< k
  have hK : K.card=k := by
    simpa only [K,Fin.card_filter_val_lt,Nat.min_eq_right hk]
  have hh := TournamentHighRows.budget_sum_bound R hR K b ?_
  · rw [hK] at hh
    rw [List.sum_take_ofFn]
    change k*(k-1)/2≤ ∑ v∈K,b v
    omega
  · intro v hv
    apply le_trans (Finset.card_le_card ?_) (hb v)
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2⟩

theorem typed_tournament_covered {V : Type} [Fintype V]
    (R : V → V → Prop) (hR : TournamentHighRows.IsTournament R) (tag : V → Kind)
    (hn : Fintype.card V≤ 9)
    (hp : ∀ q : Fin 4,
      ((Finset.univ : Finset V).filter fun v => positivePrefix q.val (tag v)=true).card≤ 2*q.val+1)
    (hb : ∀ v,((Finset.univ : Finset V).filter (R v)).card≤ budget (tag v)) :
    ∃ (ts : List Kind) (ds : List Bool) (e : Fin ts.length ≃ V),
      ts.Pairwise (fun a b => orderKey a≤ orderKey b) ∧
      (∀i,ts.get i=tag (e i)) ∧
      ds=orientationBits (fun i j => R (e i) (e j)) ∧ record (ts,ds)∈records := by
  classical
  obtain ⟨e₀,he₀⟩ := exists_sorted_numbering tag
  let ts := List.ofFn fun i => tag (e₀ i)
  have hlen : ts.length=Fintype.card V := List.length_ofFn
  let e : Fin ts.length ≃ V := (finCongr hlen).trans e₀
  have hget : ∀i,ts.get i=tag (e i) := by
    intro i
    simp [ts,e,List.get_eq_getElem]
    apply congrArg (fun j => tag (e₀ j))
    apply Fin.ext
    rfl
  have hsorted : ts.Pairwise (fun a b => orderKey a≤ orderKey b) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact he₀ hij.le
  let R' : Fin ts.length → Fin ts.length → Prop := fun i j => R (e i) (e j)
  have hR' : TournamentHighRows.IsTournament R' := by
    constructor
    · exact fun i => hR.loopless (e i)
    · intro i j hij
      exact hR.orient (e i) (e j) (fun h => hij (e.injective h))
  have hout : ∀i, ((Finset.univ : Finset (Fin ts.length)).filter (R' i)).card≤ budget (ts.get i) := by
    intro i
    rw [hget]
    have hc := ThreeBoundQ2.card_filter_equiv e (fun v => R (e i) v)
    exact hc ▸ hb (e i)
  have hp' (q : ℕ) : (ts.filter (positivePrefix q)).length =
      ((Finset.univ : Finset V).filter fun v => positivePrefix q (tag v)=true).card := by
    rw [ThreeBoundQ2.length_filter_ofFn]
    exact ThreeBoundQ2.card_filter_equiv e₀ (fun v => positivePrefix q (tag v)=true)
  have ht : allowedTypes ts := by
    constructor
    · intro k
      have hh := prefix_budget_bound R' hR' (fun v => budget (ts.get v)) hout k.val (by omega)
      have hmap : ts.map budget=List.ofFn (fun v : Fin ts.length => budget (ts.get v)) := by
        simpa only [List.ofFn_get,Function.comp_def] using
          (List.map_ofFn (f := ts.get) (g := budget))
      rwa [List.map_take,hmap]
    · intro q
      rw [hp']
      exact hp q
  refine ⟨ts,orientationBits R',e,hsorted,hget,rfl,?_⟩
  apply records_complete ts (orientationBits R')
  · simpa only [hlen] using hn
  · exact hsorted
  · exact ht
  · simp [ThreeBoundQ2.orientationBits]
  · intro i
    rw [ThreeBoundQ2.outCount_orientation_eq_card R' hR']
    exact hout i

end ThreeBoundQ3



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V : Type} [inst : Fintype.{0} V] (R : V → V → Prop)
  (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R)
  (tag : V → Sensitivity213981Formal.ThreeBoundQ3.Kind)
  (hn :
    @LE.le.{0} Nat instLENat (@Fintype.card.{0} V inst) (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
  (hp :
    ∀ (q : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
      @LE.le.{0} Nat instLENat
        (@Finset.card.{0} V
          (@Finset.filter.{0} V
            (fun (v : V) =>
              @Eq.{1} Bool
                (Sensitivity213981Formal.ThreeBoundQ3.positivePrefix
                  (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q) (tag v))
                Bool.true)
            (fun (a : V) =>
              instDecidableEqBool
                (Sensitivity213981Formal.ThreeBoundQ3.positivePrefix
                  (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q) (tag a))
                Bool.true)
            (@Finset.univ.{0} V inst)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (hb :
    ∀ (v : V),
      @LE.le.{0} Nat instLENat
        (@Finset.card.{0} V
          (@Finset.filter.{0} V (R v) (fun (a : V) => Classical.propDecidable (R v a)) (@Finset.univ.{0} V inst)))
        (Sensitivity213981Formal.ThreeBoundQ3.budget (tag v))),
  @Exists.{1} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
    fun (ts : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) =>
    @Exists.{1} (List.{0} Bool) fun (ds : List.{0} Bool) =>
      @Exists.{1} (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
        fun (e : Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V) =>
        And
          (@List.Pairwise.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind
            (fun (a b : Sensitivity213981Formal.ThreeBoundQ3.Kind) =>
              @LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundQ3.orderKey a)
                (Sensitivity213981Formal.ThreeBoundQ3.orderKey b))
            ts)
          (And
            (∀ (i : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)),
              @Eq.{1} Sensitivity213981Formal.ThreeBoundQ3.Kind
                (@List.get.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts i)
                (tag
                  (@DFunLike.coe.{1, 1, 1}
                    (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                    (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) => V)
                    (@EquivLike.toFunLike.{1, 1, 1}
                      (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                      (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V
                      (@Equiv.instEquivLike.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                        V))
                    e i)))
            (And
              (@Eq.{1} (List.{0} Bool) ds
                (@Sensitivity213981Formal.ThreeBoundQ2.orientationBits
                  (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)
                  (fun (i j : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                    R
                      (@DFunLike.coe.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                        (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                        (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) => V)
                        (@EquivLike.toFunLike.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V
                          (@Equiv.instEquivLike.{1, 1}
                            (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V))
                        e i)
                      (@DFunLike.coe.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                        (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                        (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) => V)
                        (@EquivLike.toFunLike.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V
                          (@Equiv.instEquivLike.{1, 1}
                            (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V))
                        e j))
                  fun (a b : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                  Classical.propDecidable
                    (R
                      (@DFunLike.coe.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                        (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                        (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) => V)
                        (@EquivLike.toFunLike.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V
                          (@Equiv.instEquivLike.{1, 1}
                            (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V))
                        e a)
                      (@DFunLike.coe.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                        (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                        (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) => V)
                        (@EquivLike.toFunLike.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V)
                          (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V
                          (@Equiv.instEquivLike.{1, 1}
                            (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) V))
                        e b))))
              (@Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
                Sensitivity213981Formal.ThreeBoundQ3.records
                (Sensitivity213981Formal.ThreeBoundQ3.record
                  (@Prod.mk.{0, 0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) (List.{0} Bool) ts ds))))) := @Sensitivity213981Formal.ThreeBoundQ3.typed_tournament_covered
