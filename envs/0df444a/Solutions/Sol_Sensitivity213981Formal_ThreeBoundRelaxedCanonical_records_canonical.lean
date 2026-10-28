-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRelaxedCanonical.records_canonical
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:05:25.510647+00:00
-- url     : https://prove2.me/submissions/b939b849-c2df-4c6b-9183-df98f6d14229

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_Q3OrientationTournament
import Definitions.Def_Sensitivity213981Formal_RelaxedCanonical
import Definitions.Def_Sensitivity213981Formal_RelaxedDegreeNecessity
import Definitions.Def_Sensitivity213981Formal_RelaxedOrientation
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundQ2_outCount_orientation_eq_card
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundQ3RecordFields_incoming_orientation_eq_card
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRelaxedCanonical_ofOrientation_record
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRelaxedDegree_row_total
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRelaxedDegree_sum_out_on
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundSaturated_orientations_sound


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



@[simp] theorem mem_edges {n : ℕ} (i j : Fin n) :
    (i,j) ∈ edges n ↔ i <  j := by
  simp [edges]

theorem edges_nodup (n : ℕ) : (edges n).Nodup := by
  unfold edges
  apply List.nodup_flatMap.mpr
  constructor
  · intro i _
    exact ((List.nodup_finRange n).filter _).map (fun _ _ h => congrArg Prod.snd h)
  · apply (List.nodup_finRange n).imp
    intro a b hab p hp hq
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hp
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hq
    exact hab (congrArg Prod.fst (hi.trans hj.symm))





















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
/- Canonical sorting preserves every coordinate of the relaxed q3 record. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace ThreeBoundRelaxedCanonical
open ThreeBoundQ3 ThreeBoundRelaxed









theorem kind_mono {a b : State} (h : a ≤  b) : orderKey a.kind ≤  orderKey b.kind :=
  Prod.Lex.monotone_fst (key a) (key b) h

theorem previous_of_le {a b : State} (h : a ≤  b) : previousLE (some a) b := by
  intro hk
  have hh := (Prod.Lex.toLex_le_toLex').mp (show key a ≤  key b from h)
  have hb := hh.2 (congrArg orderKey hk)
  exact Prod.Lex.toLex_le_toLex.mp hb

theorem canonical_of_pairwise (ss : List State) (hs : ss.Pairwise (· ≤  ·))
    (p : Option State) (hp : ∀ s ∈ ss, previousLE p s) : Canonical p ss := by
  induction ss generalizing p with
  | nil => trivial
  | cons s ss ih =>
      obtain ⟨hh,ht⟩ := List.pairwise_cons.mp hs
      exact ⟨hp s (by simp),ih ht (some s) (fun t ht => previous_of_le (hh t ht))⟩



theorem canonical_perm (ss : List State) : (canonical ss).Perm ss := List.mergeSort_perm _ _

theorem canonical_sorted (ss : List State) : (canonical ss).Pairwise (· ≤  ·) :=
  List.pairwise_mergeSort' (· ≤  ·) ss

theorem canonical_canonical (ss : List State) : Canonical none (canonical ss) :=
  canonical_of_pairwise _ (canonical_sorted ss) none (by intro s hs; trivial)

theorem kinds_sorted (ss : List State) :
    ((canonical ss).map State.kind).Pairwise (fun a b => orderKey a ≤  orderKey b) := by
  rw [List.pairwise_map]
  exact (canonical_sorted ss).imp fun h => kind_mono h

theorem canonical_kinds (ss : List State)
    (hs : (ss.map State.kind).Pairwise (fun a b => orderKey a ≤  orderKey b)) :
    (canonical ss).map State.kind = ss.map State.kind := by
  apply List.Perm.eq_of_pairwise (le := fun a b : Kind => orderKey a ≤  orderKey b)
    (fun a b _ _ hab hba => orderKey_injective (Nat.le_antisymm hab hba))
    (kinds_sorted ss) hs
  exact (canonical_perm ss).map _

theorem sorted_residual_perm (ss tt : List State) (hp : ss.Perm tt) :
    ((ss.map fun s => budget s.kind-s.out).insertionSort (· ≤  ·)) =
      ((tt.map fun s => budget s.kind-s.out).insertionSort (· ≤  ·)) := by
  have h := (List.perm_insertionSort (· ≤  ·) (ss.map fun s => budget s.kind-s.out)).trans
    ((hp.map _).trans (List.perm_insertionSort (· ≤  ·) (tt.map fun s => budget s.kind-s.out)).symm)
  exact h.eq_of_pairwise' (List.pairwise_insertionSort _ _) (List.pairwise_insertionSort _ _)

theorem record_perm (ss tt : List State) (hp : ss.Perm tt) :
    ThreeBoundRelaxed.record ss = ThreeBoundRelaxed.record tt := by
  have ht (k : Kind) : (ss.filter fun s => s.kind=k).length =
      (tt.filter fun s => s.kind=k).length := (hp.filter _).length_eq
  have he : ((ss.filter fun s => isGuard s.kind).map fun s => budget s.kind-s.out).sum =
      ((tt.filter fun s => isGuard s.kind).map fun s => budget s.kind-s.out).sum :=
    ((hp.filter _).map _).sum_eq
  have hh (k : Kind) (h : ℕ) : (ss.filter fun s => s.kind=k ∧ min 2 s.incoming=h).length =
      (tt.filter fun s => s.kind=k ∧ min 2 s.incoming=h).length := (hp.filter _).length_eq
  dsimp only [ThreeBoundRelaxed.record]
  simp only [ht,he,hh,sorted_residual_perm ss tt hp,hp.length_eq]

theorem weightSum_perm (ss tt : List State) (hp : ss.Perm tt) : weightSum ss=weightSum tt := by
  funext k
  exact (hp.map _).sum_eq



theorem ofOrientation_length (ts : List Kind) (ds : List Bool) :
    (ofOrientation ts ds).length=ts.length := by simp [ofOrientation]

theorem ofOrientation_kinds (ts : List Kind) (ds : List Bool) :
    (ofOrientation ts ds).map State.kind=ts := by
  simp only [ofOrientation,List.map_map,Function.comp_def,List.finRange,List.map_ofFn]
  exact List.ofFn_get ts



end ThreeBoundRelaxedCanonical





end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Every full edge-bit list encodes an actual tournament. This inverse bridge
   lets finite enumeration certificates use ordinary tournament counting. -/


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ThreeBoundOrientation
open ThreeBoundQ2







theorem isTournament {n : ℕ} (ds : List Bool) :
    TournamentHighRows.IsTournament (relation (n := n) ds) := by
  constructor
  · intro v
    simp [relation]
  · intro v w hvw
    rcases lt_or_gt_of_ne hvw with h | h
    · have hh : ¬w< v := not_lt_of_ge h.le
      cases hd : direction ds (v,w) <;> simp [relation,h,hh,hd]
    · have hh : ¬v< w := not_lt_of_ge h.le
      cases hd : direction ds (w,v) <;> simp [relation,h,hh,hd]

theorem reverse_bit {n : ℕ} (ds : List Bool) (e : Fin n × Fin n)
    (he : e∈edges n) : decide (relation ds e.2 e.1) = direction ds e := by
  have h := (mem_edges e.1 e.2).mp he
  have hh : ¬e.2< e.1 := not_lt_of_ge h.le
  cases hd : direction ds e <;> simp [relation,h,hh,hd]

theorem bits_eq {n : ℕ} (ds : List Bool)
    (hlen : ds.length=(edges n).length) :
    orientationBits (relation (n := n) ds)=ds := by
  unfold orientationBits
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hd
    have he : i< (edges n).length := by simpa using hi
    rw [List.getElem_map]
    rw [reverse_bit ds _ (List.getElem_mem he)]
    unfold direction
    rw [(edges_nodup n).idxOf_getElem i]
    simp [hd]

theorem outCount_eq_card {n : ℕ} (ds : List Bool)
    (hlen : ds.length=(edges n).length) (v : Fin n) :
    outCount (edges n) ds v =
      ((Finset.univ : Finset (Fin n)).filter (relation ds v)).card := by
  simpa only [bits_eq ds hlen] using
    outCount_orientation_eq_card _ (isTournament ds) v



end ThreeBoundOrientation




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Necessary degree and guard-incoming statistics of every actual tournament.
These exact identities justify the finite relaxed-state coverage checker. -/


set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundRelaxedDegree
open TournamentHighRows
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V]







theorem sum_reverse (R : V → V → Prop) (S : Finset V) :
    (∑ v ∈ S, (S.filter fun u => R u v).card)=∑ v ∈ S, (S.filter (R v)).card := by
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_comm



theorem out_le_pred (R : V → V → Prop) (hR : IsTournament R) (v : V) :
    outDegree R v ≤  Fintype.card V-1 := by
  have hh := row_total R hR Finset.univ v
  simp only [indicator,Finset.mem_univ,if_true,Finset.card_univ] at hh
  unfold outDegree
  omega

theorem local_incoming_bounds (R : V → V → Prop) (hR : IsTournament R) (G : Finset V) (v : V) :
    G.card-indicator G v-outDegree R v ≤  guardIncoming R G v ∧
    guardIncoming R G v ≤  min (G.card-indicator G v) (Fintype.card V-1-outDegree R v) := by
  have hg := row_total R hR G v
  have hu := row_total R hR Finset.univ v
  simp only [indicator,Finset.mem_univ,if_true,Finset.card_univ] at hu
  have hO : (G.filter (R v)).card ≤  outDegree R v :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  have hI : guardIncoming R G v ≤  (Finset.univ.filter fun u => R u v).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  change (G.filter (R v)).card+guardIncoming R G v=G.card-indicator G v at hg
  change outDegree R v+(Finset.univ.filter fun u => R u v).card=Fintype.card V-1 at hu
  omega

theorem sum_outDegree (R : V → V → Prop) (hR : IsTournament R) :
    (∑ v, outDegree R v)=Fintype.card V*(Fintype.card V-1)/2 := by
  simpa only [outDegree,Finset.card_univ] using sum_out_on R hR Finset.univ

theorem sum_guardIncoming_guard (R : V → V → Prop) (hR : IsTournament R) (G : Finset V) :
    (∑ v ∈ G, guardIncoming R G v)=G.card*(G.card-1)/2 := by
  unfold guardIncoming
  rw [sum_reverse]
  exact sum_out_on R hR G

theorem sum_guardIncoming (R : V → V → Prop) (G : Finset V) :
    (∑ v, guardIncoming R G v)=∑ v ∈ G, outDegree R v := by
  simp only [guardIncoming,outDegree,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_comm

theorem sum_guardIncoming_indicator (R : V → V → Prop) (G : Finset V) :
    (∑ v, guardIncoming R G v)=∑ v, if v ∈ G then outDegree R v else 0 := by
  rw [sum_guardIncoming]
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (fun v : V => v ∈ G)=G := by ext v; simp
  rw [he]

theorem sum_guardIncoming_int_balance (R : V → V → Prop) (G : Finset V) :
    (∑ v, ((guardIncoming R G v : ℤ)-(if v ∈ G then (outDegree R v : ℤ) else 0)))=0 := by
  have hh := congrArg (fun z : ℕ => (z : ℤ)) (sum_guardIncoming_indicator R G)
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_zero] at hh
  rw [Finset.sum_sub_distrib,hh,sub_self]

end
end ThreeBoundRelaxedDegree




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Every exact q3 orientation record has a canonical feasible relaxed state. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

namespace ThreeBoundRelaxedCanonical
open ThreeBoundQ3 ThreeBoundRelaxed ThreeBoundRelaxedDegree
open scoped Classical BigOperators
noncomputable section



theorem guards_card (ts : List Kind) : (guards ts).card=guardCount ts := by
  have h := ThreeBoundQ2.length_filter_ofFn ts.get isGuard
  simpa only [List.ofFn_get,guardCount,guards] using h.symm

theorem guards_indicator (ts : List Kind) (v : Fin ts.length) :
    ThreeBoundRelaxedDegree.indicator (guards ts) v = ThreeBoundRelaxed.indicator (ts.get v) := by
  simp only [ThreeBoundRelaxedDegree.indicator,ThreeBoundRelaxed.indicator,guards,
    Finset.mem_filter,Finset.mem_univ,true_and]

theorem eq_filter_card_decision {V : Type} [Fintype V] (p : V → Prop)
    (d₁ d₂ : DecidablePred p) (c : ℕ)
    (h : c=(@Finset.filter V p d₁ Finset.univ).card) :
    c=(@Finset.filter V p d₂ Finset.univ).card := by
  have he : d₂=d₁ := Subsingleton.elim _ _
  rw [he]
  exact h

theorem orientation_out (ts : List Kind) (ds : List Bool)
    (hlen : ds.length=(edges ts.length).length) (v : Fin ts.length) :
    outCount (edges ts.length) ds v = outDegree (ThreeBoundOrientation.relation ds) v :=
  eq_filter_card_decision (ThreeBoundOrientation.relation ds v) _ _ _
    (ThreeBoundOrientation.outCount_eq_card ds hlen v)

theorem orientation_incoming (ts : List Kind) (ds : List Bool)
    (hlen : ds.length=(edges ts.length).length) (v : Fin ts.length) :
    ThreeBoundQ3RecordFields.incoming ts ds v =
      guardIncoming (ThreeBoundOrientation.relation ds) (guards ts) v := by
  have h := ThreeBoundQ3RecordFields.incoming_orientation_eq_card ts
    (ThreeBoundOrientation.relation ds) (ThreeBoundOrientation.isTournament ds) v
  rw [ThreeBoundOrientation.bits_eq ds hlen] at h
  rw [h]
  unfold guardIncoming guards
  rw [Finset.filter_filter]
  exact eq_filter_card_decision
    (fun u => isGuard (ts.get u)=true ∧ ThreeBoundOrientation.relation ds u v) _ _ _ rfl

theorem ofOrientation_local (ts : List Kind) (ds : List Bool)
    (hlen : ds.length=(edges ts.length).length)
    (hb : ∀ v : Fin ts.length, outCount (edges ts.length) ds v ≤  budget (ts.get v)) :
    ∀ s ∈ ofOrientation ts ds, Local ts.length (guardCount ts) s := by
  intro s hs
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hs
  have hR := ThreeBoundOrientation.isTournament (n:=ts.length) ds
  have ho := out_le_pred (ThreeBoundOrientation.relation ds) hR v
  have hi := local_incoming_bounds (ThreeBoundOrientation.relation ds) hR (guards ts) v
  rw [guards_card,guards_indicator,← orientation_out ts ds hlen v,
    ← orientation_incoming ts ds hlen v,Fintype.card_fin] at hi
  rw [← orientation_out ts ds hlen v,Fintype.card_fin] at ho
  exact ⟨le_min ho (hb v),hi⟩

theorem cast_edge_count (n : ℕ) :
    ((n*(n-1)/2 : ℕ) : ℤ) = (n : ℤ)*((n : ℤ)-1)/2 := by
  by_cases hn : n=0
  · subst n
    norm_num
  · rw [Int.natCast_ediv,Int.natCast_mul,Int.natCast_sub (by omega : 1≤ n)]
    norm_num

theorem orientation_weight_sum (ts : List Kind) (ds : List Bool)
    (hlen : ds.length=(edges ts.length).length) (k : Fin 3) :
    weightSum (ofOrientation ts ds) k =
      ∑ v : Fin ts.length, weight
        ⟨ts.get v,outDegree (ThreeBoundOrientation.relation ds) v,
          guardIncoming (ThreeBoundOrientation.relation ds) (guards ts) v⟩ k := by
  simp only [weightSum,ofOrientation,List.map_map,List.finRange,List.map_ofFn,List.sum_ofFn,
    Function.comp_def,orientation_out ts ds hlen,orientation_incoming ts ds hlen]

theorem ofOrientation_weight (ts : List Kind) (ds : List Bool)
    (hlen : ds.length=(edges ts.length).length) :
    weightSum (ofOrientation ts ds)=target ts := by
  funext k
  rw [orientation_weight_sum ts ds hlen]
  have hR := ThreeBoundOrientation.isTournament (n:=ts.length) ds
  fin_cases k
  · simp only [weight,target,Fin.val_zero,if_true]
    rw [← Nat.cast_sum,sum_outDegree _ hR,Fintype.card_fin]
    exact cast_edge_count ts.length
  · simp only [weight,target,Fin.val_one,one_ne_zero,if_false,if_true]
    rw [← Finset.sum_filter]
    change (∑ v ∈ guards ts, (guardIncoming (ThreeBoundOrientation.relation ds) (guards ts) v : ℤ)) = _
    rw [← Nat.cast_sum,sum_guardIncoming_guard _ hR,guards_card]
    exact cast_edge_count (guardCount ts)
  · simp only [weight,target,Fin.reduceFinMk,OfNat.ofNat_ne_zero,show (2:ℕ)≠1 by decide,
      if_false,Nat.cast_ite,Nat.cast_zero]
    have h := sum_guardIncoming_int_balance (ThreeBoundOrientation.relation ds) (guards ts)
    simpa only [guards,Finset.mem_filter,Finset.mem_univ,true_and] using h

theorem typeLists_sound (lo n : ℕ) (ts : List Kind) (ht : ts ∈ typeLists lo n) :
    ts.length=n ∧ ts.Pairwise (fun a b => orderKey a≤ orderKey b) ∧
      ∀ t ∈ ts, lo≤ orderKey t := by
  induction n generalizing lo ts with
  | zero =>
      have he : ts=[] := by simpa only [typeLists,List.mem_singleton] using ht
      subst ts
      exact ⟨rfl,by simp,by simp⟩
  | succ n ih =>
      rw [typeLists] at ht
      obtain ⟨t,_,hrest⟩ := List.mem_flatMap.mp ht
      by_cases hlo : lo≤ orderKey t
      · rw [if_pos hlo] at hrest
        obtain ⟨rest,hr,rfl⟩ := List.mem_map.mp hrest
        obtain ⟨hlen,hs,ht⟩ := ih (orderKey t) rest hr
        refine ⟨by simp only [List.length_cons,hlen],List.pairwise_cons.mpr ⟨ht,hs⟩,?_⟩
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hlo
        · exact hlo.trans (ht u hu)
      · rw [if_neg hlo] at hrest
        contradiction

theorem records_canonical (xs : List ℕ) (hx : xs ∈ ThreeBoundQ3.records) :
    ∃ ss : List State,
      xs=ThreeBoundRelaxed.record ss ∧ allowedTypes (ss.map State.kind) ∧
      (ss.map State.kind).Pairwise (fun a b => orderKey a≤ orderKey b) ∧ ss.length≤ 9 ∧
      (∀ s∈ss,Local ss.length (guardCount (ss.map State.kind)) s) ∧
      Canonical none ss ∧ weightSum ss=target (ss.map State.kind) := by
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hx
  obtain ⟨n,hn,hcases⟩ := List.mem_flatMap.mp hc
  obtain ⟨ts,hts,hcases⟩ := List.mem_flatMap.mp hcases
  by_cases ha : allowedTypes ts
  · rw [casesFor,if_pos ha] at hcases
    obtain ⟨ds,hds,rfl⟩ := List.mem_map.mp hcases
    obtain ⟨hlen,hsorted,_⟩ := typeLists_sound 0 n ts hts
    obtain ⟨hdir,hbudget⟩ := ThreeBoundSaturated.orientations_sound
      (edges ts.length) ds (fun v => budget (ts.get v)) hds
    let ss := canonical (ofOrientation ts ds)
    have hp : ss.Perm (ofOrientation ts ds) := canonical_perm _
    have hk : ss.map State.kind=ts := by
      rw [canonical_kinds _ (by simpa only [ofOrientation_kinds] using hsorted),ofOrientation_kinds]
    have hsize : ss.length=ts.length := hp.length_eq.trans (ofOrientation_length ts ds)
    refine ⟨ss,?_,by rwa [hk],by rwa [hk],?_,?_,canonical_canonical _,?_⟩
    · exact ((record_perm ss _ hp).trans (ofOrientation_record ts ds)).symm
    · rw [hsize,hlen]
      exact Nat.le_of_lt_succ (List.mem_range.mp hn)
    · intro s hs
      rw [hsize,hk]
      exact ofOrientation_local ts ds hdir hbudget s (hp.mem_iff.mp hs)
    · rw [hk,weightSum_perm ss _ hp]
      exact ofOrientation_weight ts ds hdir
  · simp only [casesFor,if_neg ha,List.not_mem_nil] at hcases

end
end ThreeBoundRelaxedCanonical





end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (xs : List.{0} Nat)
  (hx :
    @Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
      Sensitivity213981Formal.ThreeBoundQ3.records xs),
  @Exists.{1} (List.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State)
    fun (ss : List.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State) =>
    And (@Eq.{1} (List.{0} Nat) xs (Sensitivity213981Formal.ThreeBoundRelaxed.record ss))
      (And
        (Sensitivity213981Formal.ThreeBoundQ3.allowedTypes
          (@List.map.{0, 0} Sensitivity213981Formal.ThreeBoundRelaxed.State Sensitivity213981Formal.ThreeBoundQ3.Kind
            Sensitivity213981Formal.ThreeBoundRelaxed.State.kind ss))
        (And
          (@List.Pairwise.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind
            (fun (a b : Sensitivity213981Formal.ThreeBoundQ3.Kind) =>
              @LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundQ3.orderKey a)
                (Sensitivity213981Formal.ThreeBoundQ3.orderKey b))
            (@List.map.{0, 0} Sensitivity213981Formal.ThreeBoundRelaxed.State Sensitivity213981Formal.ThreeBoundQ3.Kind
              Sensitivity213981Formal.ThreeBoundRelaxed.State.kind ss))
          (And
            (@LE.le.{0} Nat instLENat (@List.length.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State ss)
              (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
            (And
              (∀ (s : Sensitivity213981Formal.ThreeBoundRelaxed.State),
                @Membership.mem.{0, 0} Sensitivity213981Formal.ThreeBoundRelaxed.State
                    (List.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State)
                    (@List.instMembership.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State) ss s →
                  Sensitivity213981Formal.ThreeBoundRelaxed.Local
                    (@List.length.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State ss)
                    (Sensitivity213981Formal.ThreeBoundRelaxed.guardCount
                      (@List.map.{0, 0} Sensitivity213981Formal.ThreeBoundRelaxed.State
                        Sensitivity213981Formal.ThreeBoundQ3.Kind Sensitivity213981Formal.ThreeBoundRelaxed.State.kind
                        ss))
                    s)
              (And
                (Sensitivity213981Formal.ThreeBoundRelaxed.Canonical
                  (@Option.none.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State) ss)
                (@Eq.{1} ((k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) → Int)
                  (Sensitivity213981Formal.ThreeBoundRelaxed.weightSum ss)
                  (Sensitivity213981Formal.ThreeBoundRelaxed.target
                    (@List.map.{0, 0} Sensitivity213981Formal.ThreeBoundRelaxed.State
                      Sensitivity213981Formal.ThreeBoundQ3.Kind Sensitivity213981Formal.ThreeBoundRelaxed.State.kind
                      ss)))))))) := @Sensitivity213981Formal.ThreeBoundRelaxedCanonical.records_canonical
