-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.contains_sound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:55:40.443552+00:00
-- url     : https://prove2.me/submissions/4427befc-b861-469c-b6c2-799cc27196d0

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedPackedRecords
import Definitions.Def_Sensitivity213981Formal_RelaxedPackedTreeData
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
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith


namespace Sensitivity213981Formal
section
/- Linear packed keys for the exact forty-one-field degree record. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ThreeBoundRelaxedPacked
open ThreeBoundQ3 ThreeBoundRelaxed















theorem histFields_eq (ss : List State) : histFields ss=
    (List.finRange 11).flatMap (fun t => [1,2].map fun h =>
      (ss.filter fun s => s.kind=t ∧ min 2 s.incoming=h).length) := by
  simp only [histFields,histIndices,List.map_flatMap]
  rfl

theorem record_eq (ss : List State) : record ss=core ss++prefixes ss := by
  simp only [ThreeBoundRelaxed.record,core,typeFields,external,prefixes,histFields_eq]
  rfl

theorem core_length (ss : List State) : (core ss).length=34 := by
  simp [core,typeFields,histFields,histIndices,List.length_flatMap]

theorem record_length (ss : List State) : (record ss).length=41 := by
  rw [record_eq,List.length_append,core_length]
  simp [prefixes]

theorem ofDigits_map_add {α : Type} (b : ℕ) (is : List α) (f g : α→ℕ) :
    Nat.ofDigits b (is.map fun i=>f i+g i)=
      Nat.ofDigits b (is.map f)+Nat.ofDigits b (is.map g) := by
  induction is with
  | nil => simp
  | cons i is ih =>
      simp only [List.map_cons,Nat.ofDigits_cons,ih]
      ring

theorem counts_cons {α : Type} (is : List α) (p : α→State→Bool) (s : State) (ss : List State) :
    Nat.ofDigits radix (is.map fun i=>((s::ss).filter (p i)).length)=
      Nat.ofDigits radix (is.map fun i=>([s].filter (p i)).length)+
      Nat.ofDigits radix (is.map fun i=>(ss.filter (p i)).length) := by
  rw [← ofDigits_map_add]
  congr 1
  apply List.map_congr_left
  intro i hi
  by_cases h : p i s=true <;> simp [h,Nat.add_comm]

theorem external_cons (s : State) (ss : List State) :
    external (s::ss)=external [s]+external ss := by
  unfold external
  by_cases h : isGuard s.kind=true <;> simp [h]




theorem coreCode_cons (s : State) (ss : List State) :
    coreCode (s::ss)=singleCode s+coreCode ss := by
  have ht := counts_cons (List.finRange 11).reverse
    (fun t s=>decide (s.kind=t)) s ss
  have hh := counts_cons histIndices.reverse
    (fun p s=>decide (s.kind=p.1 ∧ min 2 s.incoming=p.2)) s ss
  simp only [coreCode,singleCode,core,List.reverse_append,Nat.ofDigits_append,
    List.length_append,typeFields,histFields,← List.map_reverse,List.length_reverse,
    List.length_map,List.length_finRange,List.length_singleton,List.reverse_cons,
    List.reverse_nil,List.nil_append,Nat.ofDigits_singleton]
  rw [ht,hh,external_cons]
  ring

theorem coreCode_nil : coreCode []=0 := by
  decide +kernel

theorem coreCode_sum (ss : List State) : coreCode ss=(ss.map singleCode).sum := by
  induction ss with
  | nil => exact coreCode_nil
  | cons s ss ih => simp only [coreCode_cons,ih,List.map_cons,List.sum_cons]





theorem digits_eq (xs : List ℕ) : digits xs=Nat.ofDigits radix xs := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [digits,Nat.ofDigits_cons,ih]





end ThreeBoundRelaxedPacked

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
namespace ThreeBoundRelaxedPacked
theorem single0 : validSingle 0=true := by decide +kernel
theorem single1 : validSingle 1=true := by decide +kernel
theorem single2 : validSingle 2=true := by decide +kernel
theorem single3 : validSingle 3=true := by decide +kernel
theorem single4 : validSingle 4=true := by decide +kernel
theorem single5 : validSingle 5=true := by decide +kernel
theorem single6 : validSingle 6=true := by decide +kernel
theorem single7 : validSingle 7=true := by decide +kernel
theorem single8 : validSingle 8=true := by decide +kernel
theorem single9 : validSingle 9=true := by decide +kernel
theorem single10 : validSingle 10=true := by decide +kernel
theorem all_single (k : ThreeBoundQ3.Kind) : validSingle k=true := by
  fin_cases k
  · exact single0
  · exact single1
  · exact single2
  · exact single3
  · exact single4
  · exact single5
  · exact single6
  · exact single7
  · exact single8
  · exact single9
  · exact single10
theorem singleCode_fast (s : ThreeBoundRelaxed.State) (ho : s.out≤ 4) (hi : s.incoming≤ 8) :
    singleCode s=fastSingle s := by
  have h := List.all_eq_true.mp (all_single s.kind) s.out (List.mem_range.mpr (by omega))
  have hh := List.all_eq_true.mp h s.incoming (List.mem_range.mpr (by omega))
  exact of_decide_eq_true hh
end ThreeBoundRelaxedPacked


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000
namespace ThreeBoundRelaxedPacked
open ThreeBoundQ3 ThreeBoundRelaxed
open ThreeBoundEndpoint22Records (decodeRow)

theorem fastKey_eq (ss : List State) (ho : ∀ s∈ss,s.out≤ 4) (hi : ∀ s∈ss,s.incoming≤ 8) :
    fastKey ss=Nat.ofDigits radix (ThreeBoundRelaxed.record ss).reverse := by
  have hc : (ss.map fastSingle).sum=coreCode ss := by
    rw [coreCode_sum]
    have hm : ss.map fastSingle=ss.map singleCode := by
      apply List.map_congr_left
      intro s hs
      exact (singleCode_fast s (ho s hs) (hi s hs)).symm
    exact congrArg List.sum hm
  rw [record_eq,List.reverse_append,Nat.ofDigits_append]
  change radix^7*(ss.map fastSingle).sum+digits (prefixes ss).reverse = _
  rw [digits_eq]
  rw [hc]
  have hl : (prefixes ss).reverse.length=7 := by simp [prefixes]
  rw [hl]
  change radix^7*coreCode ss+Nat.ofDigits radix (prefixes ss).reverse =
    Nat.ofDigits radix (prefixes ss).reverse+radix^7*coreCode ss
  exact Nat.add_comm _ _



theorem budget_le_four (k : Kind) : budget k≤ 4 := by
  fin_cases k <;> decide



theorem sum_bound (xs : List ℕ) (h : ∀ x∈xs,x≤ 4) : xs.sum≤ 4*xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha := h a (by simp)
      have ht := ih (fun x hx=>h x (by simp [hx]))
      simp only [List.sum_cons,List.length_cons]
      omega



theorem residual_sum_bound (ss : List State) :
    (ss.map fun s=>budget s.kind-s.out).sum≤ 4*ss.length := by
  have h := sum_bound (ss.map fun s=>budget s.kind-s.out) (by
    intro x hx
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
    exact (Nat.sub_le _ _).trans (budget_le_four s.kind))
  simpa only [List.length_map] using h



theorem record_bounded (ss : List State) (hn : ss.length≤ 9) :
    ∀ x∈ThreeBoundRelaxed.record ss,x< radix := by
  intro x hx
  rw [record_eq] at hx
  rcases List.mem_append.mp hx with hx | hx
  · simp only [core,List.mem_append,List.mem_singleton] at hx
    rcases hx with (hx | rfl) | hx
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
      have h := List.length_filter_le (fun s:State=>s.kind=t) ss
      dsimp [radix]
      omega
    · have h := residual_sum_bound (ss.filter fun s=>isGuard s.kind)
      have hl := List.length_filter_le (fun s:State=>isGuard s.kind) ss
      change external ss< radix
      dsimp only [external] at *
      dsimp [radix]
      omega
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
      have h := List.length_filter_le (fun s:State=>s.kind=p.1 ∧ min 2 s.incoming=p.2) ss
      dsimp [radix]
      omega
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hx
    split_ifs
    · have hb := sum_bound (((ss.map fun s=>budget s.kind-s.out).insertionSort (·≤ ·)).take k) (by
        intro x hx
        have hx' := List.mem_of_mem_take hx
        have hx'' : x∈ss.map (fun s=>budget s.kind-s.out) := by simpa using hx'
        obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx''
        exact (Nat.sub_le _ _).trans (budget_le_four s.kind))
      have hl : (((ss.map fun s=>budget s.kind-s.out).insertionSort (·≤ ·)).take k).length≤ ss.length := by
        simp only [List.length_take,List.length_insertionSort,List.length_map]
        exact min_le_right _ _
      dsimp [radix]
      omega
    · decide



theorem decode_length (n code : ℕ) : (decodeRow n code).length=n := by
  induction n generalizing code with
  | zero => rfl
  | succ n ih => simp only [decodeRow,List.length_cons,ih]



theorem decode_bounded (n code : ℕ) : ∀ x∈decodeRow n code,x< radix := by
  induction n generalizing code with
  | zero => simp [decodeRow]
  | succ n ih =>
      intro x hx
      simp only [decodeRow,List.mem_cons] at hx
      rcases hx with rfl | hx
      · split_ifs
        · decide
        · have h := Nat.mod_lt code (by decide : 0< 16)
          dsimp [radix]
          omega
      · exact ih _ _ hx

theorem digits_append (xs ys : List ℕ) :
    digits (xs++ys)=digits xs+radix^xs.length*digits ys := by
  simp only [digits_eq,Nat.ofDigits_append]

theorem keyAux_eq (n code acc : ℕ) :
    keyAux n code acc=acc*radix^n+digits (decodeRow n code).reverse := by
  induction n generalizing code acc with
  | zero => simp [keyAux,decodeRow,digits]
  | succ n ih =>
      rw [keyAux,ih,decodeRow,List.reverse_cons,digits_append]
      simp only [List.length_reverse,decode_length,digits,Nat.mul_zero,Nat.add_zero,pow_succ]
      ring

theorem keyOfCode_eq (n code : ℕ) :
    keyOfCode n code=Nat.ofDigits radix (decodeRow n code).reverse := by
  simpa only [keyOfCode,Nat.zero_mul,Nat.zero_add,digits_eq] using keyAux_eq n code 0

theorem Tree.contains_sound (t : Tree) (hk : t.checkKeys=true) (ss : List State)
    (hn : ss.length≤ 9) (ho : ∀ s∈ss,s.out≤ 4) (hi : ∀ s∈ss,s.incoming≤ 8)
    (h : t.contains (fastKey ss)=true) : ThreeBoundRelaxed.record ss∈t.rows := by
  induction t with
  | leaf key code =>
      have he : fastKey ss=key := of_decide_eq_true h
      have he' : key=Nat.ofDigits radix (decodeRow 41 code).reverse := by
        rw [← keyOfCode_eq]
        exact of_decide_eq_true hk
      rw [fastKey_eq ss ho hi] at he
      have hh := Nat.ofDigits_inj_of_len_eq (b:=radix) (by decide)
        (L1:=(ThreeBoundRelaxed.record ss).reverse) (L2:=(decodeRow 41 code).reverse)
        (by simp only [List.length_reverse,record_length,decode_length])
        (by simpa only [List.mem_reverse] using record_bounded ss hn)
        (by simpa only [List.mem_reverse] using decode_bounded 41 code)
        (he.trans he')
      have heq : ThreeBoundRelaxed.record ss=decodeRow 41 code := List.reverse_injective hh
      simp only [Tree.rows,List.mem_singleton,heq]
  | branch pivot left right hl hr =>
      have hh : left.checkKeys=true ∧ right.checkKeys=true := by simpa only [Tree.checkKeys,Bool.and_eq_true] using hk
      simp only [Tree.contains] at h
      split at h
      · exact List.mem_append_left _ (hl hh.1 h)
      · exact List.mem_append_right _ (hr hh.2 h)

end ThreeBoundRelaxedPacked


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (t : Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree)
  (hk : @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys t) Bool.true)
  (ss : List.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State)
  (hn :
    @LE.le.{0} Nat instLENat (@List.length.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State ss)
      (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
  (ho :
    ∀ (s : Sensitivity213981Formal.ThreeBoundRelaxed.State),
      @Membership.mem.{0, 0} Sensitivity213981Formal.ThreeBoundRelaxed.State
          (List.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State)
          (@List.instMembership.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State) ss s →
        @LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundRelaxed.State.out s)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
  (hi :
    ∀ (s : Sensitivity213981Formal.ThreeBoundRelaxed.State),
      @Membership.mem.{0, 0} Sensitivity213981Formal.ThreeBoundRelaxed.State
          (List.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State)
          (@List.instMembership.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State) ss s →
        @LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundRelaxed.State.incoming s)
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
  (h :
    @Eq.{1} Bool
      (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.contains
        (Sensitivity213981Formal.ThreeBoundRelaxedPacked.fastKey ss) t)
      Bool.true),
  @Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
    (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.rows t) (Sensitivity213981Formal.ThreeBoundRelaxed.record ss) := @Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.contains_sound
