-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundQ3ActualRecordFields.all_record_fields
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:34:50.747024+00:00
-- url     : https://prove2.me/submissions/fa761148-9a01-4de2-8b84-409859d73a23

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_GradedCandidates
import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_Q3RecordFields
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
import Mathlib.Data.Finset.Powerset
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
/- Exact meanings of the 41 fields of the executable q3 record. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundQ3RecordFields
open ThreeBoundQ3 ThreeBoundNumeric
open ThreeBoundQ2 (length_filter_ofFn  )
open scoped Classical BigOperators
noncomputable section















theorem record_explicit (ts : List Kind) (ds : List Bool) :
    record (ts,ds) =
    [typeCount ts 0,typeCount ts 1,typeCount ts 2,typeCount ts 3,
     typeCount ts 4,typeCount ts 5,typeCount ts 6,typeCount ts 7,
     typeCount ts 8,typeCount ts 9,typeCount ts 10,external ts ds,
     histogram ts ds 0 1,histogram ts ds 0 2,histogram ts ds 1 1,histogram ts ds 1 2,
     histogram ts ds 2 1,histogram ts ds 2 2,histogram ts ds 3 1,histogram ts ds 3 2,
     histogram ts ds 4 1,histogram ts ds 4 2,histogram ts ds 5 1,histogram ts ds 5 2,
     histogram ts ds 6 1,histogram ts ds 6 2,histogram ts ds 7 1,histogram ts ds 7 2,
     histogram ts ds 8 1,histogram ts ds 8 2,histogram ts ds 9 1,histogram ts ds 9 2,
     histogram ts ds 10 1,histogram ts ds 10 2,residualPrefix ts ds 1,residualPrefix ts ds 2,
     residualPrefix ts ds 3,residualPrefix ts ds 4,residualPrefix ts ds 5,residualPrefix ts ds 6,
     residualPrefix ts ds 7] := rfl



theorem record_type (ts : List Kind) (ds : List Bool) (k : Kind) :
    recordOfList (record (ts,ds)) k.val = typeCount ts k := by
  rw [record_explicit]
  fin_cases k <;> rfl

theorem record_external (ts : List Kind) (ds : List Bool) :
    recordOfList (record (ts,ds)) 11 = external ts ds := by
  rw [record_explicit]
  rfl

theorem record_histogram (ts : List Kind) (ds : List Bool) (k : Kind) (h : Fin 2) :
    recordOfList (record (ts,ds)) (12+2*k.val+h.val) = histogram ts ds k (h.val+1) := by
  rw [record_explicit]
  fin_cases k <;> fin_cases h <;> rfl

theorem record_prefix (ts : List Kind) (ds : List Bool) (k : Fin 7) :
    recordOfList (record (ts,ds)) (34+k.val) = residualPrefix ts ds (k.val+1) := by
  rw [record_explicit]
  fin_cases k <;> rfl

theorem typeCount_eq_card (ts : List Kind) (k : Kind) :
    typeCount ts k = ((Finset.univ : Finset (Fin ts.length)).filter fun v => ts.get v = k).card := by
  have he := length_filter_ofFn ts.get (fun u => decide (u=k))
  simpa only [typeCount,List.ofFn_get,decide_eq_true_eq] using he

theorem finRange_filter_length {m : ℕ} (p : Fin m → Bool) :
    ((List.finRange m).filter p).length =
      ((Finset.univ : Finset (Fin m)).filter fun v => p v = true).card := by
  rw [← List.countP_eq_length_filter]
  symm
  simpa using (List.nodup_finRange m).card_eq_countP (P := fun v => p v = true)

theorem histogram_eq_card (ts : List Kind) (ds : List Bool) (k : Kind) (h : ℕ) :
    histogram ts ds k h = ((Finset.univ : Finset (Fin ts.length)).filter
      fun v => ts.get v = k ∧ min 2 (incoming ts ds v) = h).card := by
  unfold histogram
  simpa only [decide_eq_true_eq] using finRange_filter_length
    (fun v : Fin ts.length => decide (ts.get v = k ∧ min 2 (incoming ts ds v) = h))



theorem external_eq_sum (ts : List Kind) (ds : List Bool) :
    external ts ds = ∑ v ∈ (Finset.univ : Finset (Fin ts.length)).filter
      (fun v => isGuard (ts.get v) = true), _root_.Sensitivity213981Formal.ThreeBoundQ3RecordFields.residual ts ds v := by
  unfold external
  have hnd : (((List.finRange ts.length).filter fun v => isGuard (ts.get v))).Nodup :=
    (List.nodup_finRange _).filter _
  rw [← List.sum_toFinset (_root_.Sensitivity213981Formal.ThreeBoundQ3RecordFields.residual ts ds) hnd]
  congr 1
  ext v
  simp

end
end ThreeBoundQ3RecordFields





end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Transport the exact record fields to the actual high candidate heads. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundActualRecordFields
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundGradedCandidates ThreeBoundGradedCover ThreeBoundActualHeadCosts
open ThreeBoundHeadExpressions ThreeBoundAllKindHeadCosts ThreeBoundActualKindFilters
open ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundQ2 ThreeBoundRecordFields
open ThreeBoundActualEnumeration
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]





theorem card_filter_numbering {A : Type} [Fintype A] (H : Finset V) (e : A ≃ H) (p : V → Prop) :
    ((Finset.univ : Finset A).filter fun a => p (e a).val).card = (H.filter p).card := by
  apply Finset.card_bij (fun a _ => (e a).val)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨(e a).property,(Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ hab
    exact e.injective (Subtype.ext hab)
  · intro w hw
    let wH : H := ⟨w,(Finset.mem_filter.mp hw).1⟩
    refine ⟨e.symm wH,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · simpa only [e.apply_symm_apply] using (Finset.mem_filter.mp hw).2
    · simp only [e.apply_symm_apply,wH]















theorem sorted_nat_eq_of_perm (xs ys : List ℕ) (h : xs.Perm ys) :
    xs.mergeSort (· ≤  ·) = ys.mergeSort (· ≤  ·) := by
  exact ((List.mergeSort_perm xs (· ≤  ·)).trans
    (h.trans (List.mergeSort_perm ys (· ≤  ·)).symm)).eq_of_pairwise'
    (List.pairwise_mergeSort' (· ≤  ·) xs) (List.pairwise_mergeSort' (· ≤  ·) ys)







end
end ThreeBoundActualRecordFields






end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact transportation of all q3 record fields to a numbered actual high set. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundQ3ActualRecordFields
open ThreeBoundNumeric ThreeBoundQ3 ThreeBoundQ3RecordFields
open ThreeBoundQ2 (outCount_orientation_eq_card)
open ThreeBoundActualRecordFields (card_filter_numbering sorted_nat_eq_of_perm)
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V]

theorem typeCount_transport (ts : List Kind) (H : Finset V) (tag : V → Kind)
    (e : Fin ts.length ≃ H) (hget : ∀ k, ts.get k = tag (e k).val) (kind : Kind) :
    ThreeBoundQ3RecordFields.typeCount ts kind = (H.filter fun w => tag w = kind).card := by
  rw [typeCount_eq_card]
  simp_rw [hget]
  convert card_filter_numbering H e (fun w => tag w = kind) using 1 <;>
    congr 1 <;> ext a <;> simp

theorem outCount_transport (ts : List Kind) (H : Finset V) (R : V → V → Prop)
    (hR : TournamentHighRows.IsTournament R) (e : Fin ts.length ≃ H) (w : Fin ts.length) :
    outCount (edges ts.length) (orientationBits (fun k l => R (e k).val (e l).val)) w =
      (H.filter (R (e w).val)).card := by
  have hRE : TournamentHighRows.IsTournament (fun k l => R (e k).val (e l).val) := by
    constructor
    · exact fun k => hR.loopless _
    · intro k l hkl
      exact hR.orient _ _ (fun he => hkl (e.injective (Subtype.ext he)))
  rw [outCount_orientation_eq_card _ hRE]
  exact card_filter_numbering H e (fun v => R (e w).val v)

theorem incoming_transport (ts : List Kind) (H G : Finset V) (tag : V → Kind)
    (R : V → V → Prop) (hR : TournamentHighRows.IsTournament R)
    (e : Fin ts.length ≃ H) (hget : ∀ k, ts.get k = tag (e k).val)
    (hG : G = H.filter fun w => isGuard (tag w) = true) (w : Fin ts.length) :
    ThreeBoundQ3RecordFields.incoming ts (orientationBits (fun k l => R (e k).val (e l).val)) w =
      (G.filter fun v => R v (e w).val).card := by
  have hRE : TournamentHighRows.IsTournament (fun k l => R (e k).val (e l).val) := by
    constructor
    · exact fun k => hR.loopless _
    · intro k l hkl
      exact hR.orient _ _ (fun he => hkl (e.injective (Subtype.ext he)))
  rw [incoming_orientation_eq_card _ _ hRE]
  simp_rw [hget]
  rw [hG,Finset.filter_filter]
  convert card_filter_numbering H e (fun v => isGuard (tag v) = true ∧ R v (e w).val) using 1 <;>
    congr 1 <;> ext a <;> simp

theorem histogram_transport (ts : List Kind) (H G : Finset V) (tag : V → Kind)
    (R : V → V → Prop) (hR : TournamentHighRows.IsTournament R)
    (e : Fin ts.length ≃ H) (hget : ∀ k, ts.get k = tag (e k).val)
    (hG : G = H.filter fun w => isGuard (tag w) = true) (kind : Kind) (hits : ℕ) :
    histogram ts (orientationBits (fun k l => R (e k).val (e l).val)) kind hits =
      (H.filter fun w => tag w = kind ∧ min 2 (G.filter fun v => R v w).card = hits).card := by
  rw [histogram_eq_card]
  simp_rw [hget,incoming_transport ts H G tag R hR e hget hG]
  convert card_filter_numbering H e
    (fun w => tag w = kind ∧ min 2 (G.filter fun v => R v w).card = hits) using 1 <;>
      congr 1 <;> ext a <;> simp

theorem residual_transport (ts : List Kind) (H : Finset V) (tag : V → Kind)
    (R : V → V → Prop) (hR : TournamentHighRows.IsTournament R)
    (e : Fin ts.length ≃ H) (hget : ∀ k, ts.get k = tag (e k).val)
    (count : V → ℕ) (hc : ∀ w ∈ H, count w = budget (tag w)) (w : Fin ts.length) :
    _root_.Sensitivity213981Formal.ThreeBoundQ3RecordFields.residual ts (orientationBits (fun k l => R (e k).val (e l).val)) w =
      count (e w).val - (H.filter (R (e w).val)).card := by
  rw [_root_.Sensitivity213981Formal.ThreeBoundQ3RecordFields.residual,hget,outCount_transport ts H R hR e w,← hc (e w).val (e w).property]

theorem external_transport (ts : List Kind) (H G : Finset V) (tag : V → Kind)
    (R : V → V → Prop) (hR : TournamentHighRows.IsTournament R)
    (e : Fin ts.length ≃ H) (hget : ∀ k, ts.get k = tag (e k).val)
    (hG : G = H.filter fun w => isGuard (tag w) = true)
    (count : V → ℕ) (hc : ∀ w ∈ H, count w = budget (tag w)) :
    external ts (orientationBits (fun k l => R (e k).val (e l).val)) =
      ∑ w ∈ G, (count w - (H.filter (R w)).card) := by
  rw [external_eq_sum,Finset.sum_filter]
  simp_rw [hget,residual_transport ts H tag R hR e hget count hc]
  rw [e.sum_comp (fun w : H =>
    if isGuard (tag w.val) = true then count w.val-(H.filter (R w.val)).card else 0)]
  rw [Finset.univ_eq_attach]
  rw [Finset.sum_attach H (fun w =>
    if isGuard (tag w) = true then count w-(H.filter (R w)).card else 0)]
  rw [hG,Finset.sum_filter]

theorem numbering_perm (ts : List Kind) (H : Finset V) (e : Fin ts.length ≃ H) :
    ((List.finRange ts.length).map fun k => (e k).val).Perm H.toList := by
  have hinj : Function.Injective (fun k : Fin ts.length => (e k).val) := by
    intro a b hab
    exact e.injective (Subtype.ext hab)
  apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).map hinj) H.nodup_toList).mpr
  intro w
  constructor
  · rintro hw
    obtain ⟨k,_,he⟩ := List.mem_map.mp hw
    exact Finset.mem_toList.mpr (he ▸ (e k).property)
  · intro hw
    have hwH := Finset.mem_toList.mp hw
    refine List.mem_map.mpr ⟨e.symm ⟨w,hwH⟩,List.mem_finRange _,?_⟩
    simp

theorem sortedResiduals_transport (ts : List Kind) (H : Finset V) (tag : V → Kind)
    (R : V → V → Prop) (hR : TournamentHighRows.IsTournament R)
    (e : Fin ts.length ≃ H) (hget : ∀ k, ts.get k = tag (e k).val)
    (count : V → ℕ) (hc : ∀ w ∈ H, count w = budget (tag w)) :
    sortedResiduals ts (orientationBits (fun k l => R (e k).val (e l).val)) =
      (H.toList.map fun w => count w-(H.filter (R w)).card).mergeSort (· ≤  ·) := by
  unfold sortedResiduals
  apply sorted_nat_eq_of_perm
  have hp := (numbering_perm ts H e).map (fun w => count w-(H.filter (R w)).card)
  rw [List.map_map] at hp
  have he : ((List.finRange ts.length).map
      (_root_.Sensitivity213981Formal.ThreeBoundQ3RecordFields.residual ts (orientationBits (fun k l => R (e k).val (e l).val)))) =
      ((List.finRange ts.length).map fun k => count (e k).val-(H.filter (R (e k).val)).card) := by
    apply List.map_congr_left
    intro k _
    exact residual_transport ts H tag R hR e hget count hc k
  rw [he]
  exact hp

theorem residualPrefix_transport (ts : List Kind) (H : Finset V) (tag : V → Kind)
    (R : V → V → Prop) (hR : TournamentHighRows.IsTournament R)
    (e : Fin ts.length ≃ H) (hget : ∀ k, ts.get k = tag (e k).val)
    (count : V → ℕ) (hc : ∀ w ∈ H, count w = budget (tag w)) (k : ℕ) (hk : k ≤  H.card) :
    residualPrefix ts (orientationBits (fun a b => R (e a).val (e b).val)) k =
      (((H.toList.map fun w => count w-(H.filter (R w)).card).mergeSort (· ≤  ·)).take k).sum := by
  have hlen : ts.length = H.card := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_congr e
  rw [residualPrefix,if_pos (by omega),sortedResiduals_transport ts H tag R hR e hget count hc]

/-- All scalar record fields agree exactly with the corresponding actual
    finite-head statistics. The residual prefixes use the same sorted values. -/
theorem all_record_fields (ts : List Kind) (ds : List Bool)
    (H G : Finset V) (tag : V → Kind) (R : V → V → Prop)
    (hR : TournamentHighRows.IsTournament R) (e : Fin ts.length ≃ H)
    (hget : ∀ k, ts.get k = tag (e k).val)
    (hdirs : ds = orientationBits (fun k l => R (e k).val (e l).val))
    (hG : G = H.filter fun w => isGuard (tag w) = true)
    (count : V → ℕ) (hc : ∀ w ∈ H, count w = budget (tag w)) :
    let r := recordOfList (record (ts,ds))
    (∀ kind : Kind, r kind.val = (H.filter fun w => tag w = kind).card) ∧
    r 11 = (∑ w ∈ G, (count w-(H.filter (R w)).card)) ∧
    (∀ (kind : Kind) (hits : Fin 2), r (12+2*kind.val+hits.val) =
      (H.filter fun w => tag w = kind ∧
        min 2 (G.filter fun v => R v w).card = hits.val+1).card) ∧
    (∀ k : Fin 7, k.val+1 ≤  H.card → r (34+k.val) =
      (((H.toList.map fun w => count w-(H.filter (R w)).card).mergeSort (· ≤  ·)).take (k.val+1)).sum) := by
  subst ds
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · intro kind
    rw [record_type]
    exact typeCount_transport ts H tag e hget kind
  · rw [record_external]
    exact external_transport ts H G tag R hR e hget hG count hc
  · intro kind hits
    rw [record_histogram]
    exact histogram_transport ts H G tag R hR e hget hG kind (hits.val+1)
  · intro k hk
    rw [record_prefix]
    exact residualPrefix_transport ts H tag R hR e hget count hc (k.val+1) hk

end
end ThreeBoundQ3ActualRecordFields



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V : Type} [Fintype.{0} V] (ts : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) (ds : List.{0} Bool)
  (H G : Finset.{0} V) (tag : V → Sensitivity213981Formal.ThreeBoundQ3.Kind) (R : V → V → Prop)
  (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R)
  (e :
    Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
      (@Subtype.{1} V fun (x : V) =>
        @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
  (hget :
    ∀ (k : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)),
      @Eq.{1} Sensitivity213981Formal.ThreeBoundQ3.Kind (@List.get.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts k)
        (tag
          (@Subtype.val.{1} V
            (fun (x : V) =>
              @Membership.mem.{0, 0} V (Finset.{0} V)
                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
            (@DFunLike.coe.{1, 1, 1}
              (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                (@Subtype.{1} V fun (x : V) =>
                  @Membership.mem.{0, 0} V (Finset.{0} V)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
              (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
              (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                @Subtype.{1} V fun (x : V) =>
                  @Membership.mem.{0, 0} V (Finset.{0} V)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
              (@EquivLike.toFunLike.{1, 1, 1}
                (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                (@Subtype.{1} V fun (x : V) =>
                  @Membership.mem.{0, 0} V (Finset.{0} V)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                (@Equiv.instEquivLike.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)))
              e k))))
  (hdirs :
    @Eq.{1} (List.{0} Bool) ds
      (@Sensitivity213981Formal.ThreeBoundQ2.orientationBits
        (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)
        (fun (k l : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
          R
            (@Subtype.val.{1} V
              (fun (x : V) =>
                @Membership.mem.{0, 0} V (Finset.{0} V)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                  @Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (@Subtype.{1} V fun (x : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                  (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                  (@Equiv.instEquivLike.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (@Subtype.{1} V fun (x : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)))
                e k))
            (@Subtype.val.{1} V
              (fun (x : V) =>
                @Membership.mem.{0, 0} V (Finset.{0} V)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                  @Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (@Subtype.{1} V fun (x : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                  (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                  (@Equiv.instEquivLike.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (@Subtype.{1} V fun (x : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)))
                e l)))
        fun (a b : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
        Classical.propDecidable
          (R
            (@Subtype.val.{1} V
              (fun (x : V) =>
                @Membership.mem.{0, 0} V (Finset.{0} V)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                  @Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (@Subtype.{1} V fun (x : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                  (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                  (@Equiv.instEquivLike.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (@Subtype.{1} V fun (x : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)))
                e a))
            (@Subtype.val.{1} V
              (fun (x : V) =>
                @Membership.mem.{0, 0} V (Finset.{0} V)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                (fun (x : Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)) =>
                  @Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (@Subtype.{1} V fun (x : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x))
                  (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                  (@Subtype.{1} V fun (x : V) =>
                    @Membership.mem.{0, 0} V (Finset.{0} V)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)
                  (@Equiv.instEquivLike.{1, 1} (Fin (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts))
                    (@Subtype.{1} V fun (x : V) =>
                      @Membership.mem.{0, 0} V (Finset.{0} V)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H x)))
                e b)))))
  (hG :
    @Eq.{1} (Finset.{0} V) G
      (@Finset.filter.{0} V
        (fun (w : V) => @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundQ3.isGuard (tag w)) Bool.true)
        (fun (a : V) => instDecidableEqBool (Sensitivity213981Formal.ThreeBoundQ3.isGuard (tag a)) Bool.true) H))
  (count : V → Nat)
  (hc :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H w →
        @Eq.{1} Nat (count w) (Sensitivity213981Formal.ThreeBoundQ3.budget (tag w))),
  have r : Sensitivity213981Formal.ThreeBoundNumeric.Q2Record :=
    Sensitivity213981Formal.ThreeBoundNumeric.recordOfList
      (Sensitivity213981Formal.ThreeBoundQ3.record
        (@Prod.mk.{0, 0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) (List.{0} Bool) ts ds));
  And
    (∀ (kind : Sensitivity213981Formal.ThreeBoundQ3.Kind),
      @Eq.{1} Nat
        (r
          (@Fin.val
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            kind))
        (@Finset.card.{0} V
          (@Finset.filter.{0} V (fun (w : V) => @Eq.{1} Sensitivity213981Formal.ThreeBoundQ3.Kind (tag w) kind)
            (fun (a : V) =>
              instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (tag a) kind)
            H)))
    (And
      (@Eq.{1} Nat (r (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
        (@Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid G fun (w : V) =>
          @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (count w)
            (@Finset.card.{0} V (@Finset.filter.{0} V (R w) (fun (a : V) => Classical.propDecidable (R w a)) H))))
      (And
        (∀ (kind : Sensitivity213981Formal.ThreeBoundQ3.Kind)
          (hits : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
          @Eq.{1} Nat
            (r
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Fin.val
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      kind)))
                (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) hits)))
            (@Finset.card.{0} V
              (@Finset.filter.{0} V
                (fun (w : V) =>
                  And (@Eq.{1} Sensitivity213981Formal.ThreeBoundQ3.Kind (tag w) kind)
                    (@Eq.{1} Nat
                      (@Min.min.{0} Nat instMinNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Finset.card.{0} V
                          (@Finset.filter.{0} V (fun (v : V) => R v w) (fun (a : V) => Classical.propDecidable (R a w))
                            G)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) hits)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (fun (a : V) =>
                  @instDecidableAnd (@Eq.{1} Sensitivity213981Formal.ThreeBoundQ3.Kind (tag a) kind)
                    (@Eq.{1} Nat
                      (@Min.min.{0} Nat instMinNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Finset.card.{0} V
                          (@Finset.filter.{0} V (fun (v : V) => R v a)
                            (fun (a_1 : V) => Classical.propDecidable (R a_1 a)) G)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) hits)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (instDecidableEqFin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (tag a) kind)
                    (instDecidableEqNat
                      (@Min.min.{0} Nat instMinNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Finset.card.{0} V
                          (@Finset.filter.{0} V (fun (v : V) => R v a)
                            (fun (a_1 : V) => Classical.propDecidable (R a_1 a)) G)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) hits)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                H)))
        (∀ (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))),
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) k)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Finset.card.{0} V H) →
            @Eq.{1} Nat
              (r
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34)))
                  (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) k)))
              (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)
                (@List.take.{0} Nat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) k)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@List.mergeSort.{0} Nat
                    (@List.map.{0, 0} V Nat
                      (fun (w : V) =>
                        @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (count w)
                          (@Finset.card.{0} V
                            (@Finset.filter.{0} V (R w) (fun (a : V) => Classical.propDecidable (R w a)) H)))
                      (@Finset.toList.{0} V H))
                    fun (x1 x2 : Nat) => @Decidable.decide (@LE.le.{0} Nat instLENat x1 x2) (Nat.decLe x1 x2))))))) := @Sensitivity213981Formal.ThreeBoundQ3ActualRecordFields.all_record_fields
