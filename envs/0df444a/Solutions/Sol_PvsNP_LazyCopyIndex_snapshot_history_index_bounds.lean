-- Prove2me | solution 1 for PvsNP.LazyCopyIndex.snapshot_history_index_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T17:19:05.189926+00:00
-- url     : https://prove2.me/submissions/ea583a0d-0db7-4dae-9f31-a9bcc02121c8

import Definitions.Def_PvsNP_SnapshotHistoryIndex
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Size
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false

namespace PvsNP.SourceIntervalMap

theorem boundaries_card (history : List Patch) :
    (boundaries history).card ≤ 2*history.length := by
  induction history with
  | nil => simp [boundaries]
  | cons p history ih =>
    have a := Finset.card_insert_le (s := insert p.finish (boundaries history)) (a := p.start)
    have b := Finset.card_insert_le (s := boundaries history) (a := p.finish)
    simp only [boundaries,List.length_cons]
    omega

end PvsNP.SourceIntervalMap

namespace PvsNP.SourceIntervalMap

theorem rank_le_size (cuts : Finset ℕ) (i : ℕ) : rank cuts i ≤ cuts.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem rank_comparison {cuts : Finset ℕ} {cut : ℕ}
    (present : cut ∈ cuts) (i : ℕ) : rank cuts cut ≤ rank cuts i ↔ cut ≤ i := by
  constructor
  · intro bound
    by_contra! before
    have less : cuts.filter (fun q => q ≤ i) ⊂ cuts.filter (fun q => q ≤ cut) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · intro p h
        obtain ⟨mem,within⟩ := Finset.mem_filter.mp h
        exact Finset.mem_filter.mpr ⟨mem,within.trans before.le⟩
      · intro same
        have cutIn : cut ∈ cuts.filter (fun q => q ≤ cut) := Finset.mem_filter.mpr ⟨present,le_rfl⟩
        rw [← same, Finset.mem_filter] at cutIn
        omega
    exact (not_le_of_gt (Finset.card_lt_card less)) bound
  · intro order
    apply Finset.card_le_card
    intro q h
    obtain ⟨mem,within⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨mem,within.trans order⟩

end PvsNP.SourceIntervalMap

namespace PvsNP.PersistentIntervalIndex

theorem ownerAt_halves {d : ℕ} (t : Tree (d+1)) (i : ℕ) :
    ownerAt t i =
      if i < 2^d then ownerAt (halves t).1 i else ownerAt (halves t).2 (i-2^d) := by
  cases t with
  | uniform owner => simp [ownerAt,halves]
  | fork l r => rfl

theorem assign_exact (owner : ℕ) {d : ℕ} (t : Tree d) (lo hi i : ℕ)
    (inside : i < 2^d) :
    ownerAt (assign owner d t lo hi).1 i =
      if lo ≤ i ∧ i < hi then owner else ownerAt t i := by
  induction d generalizing lo hi i with
  | zero =>
    simp only [pow_zero,Nat.lt_one_iff] at inside
    subst i
    by_cases covers : lo=0 ∧ 0<hi
    · simp [assign,covers,ownerAt]
    · simp [assign,covers]
  | succ d ih =>
    have full : (2:ℕ)^(d+1) = 2^d+2^d := by rw [pow_succ,Nat.mul_two]
    by_cases vacant : hi ≤ lo
    · have outside : ¬ (lo ≤ i ∧ i < hi) := by omega
      simp [assign,vacant,outside]
    by_cases all : lo = 0 ∧ 2^(d+1) ≤ hi
    · have inRange : lo ≤ i ∧ i < hi := ⟨by omega,inside.trans_le all.2⟩
      simp only [assign,if_neg vacant,if_pos all,if_pos inRange,ownerAt]
    rw [full] at inside
    rw [ownerAt_halves t]
    by_cases left : hi ≤ 2^d
    · by_cases small : i < 2^d
      · simpa only [assign,if_neg vacant,if_neg all,if_pos left,ownerAt,if_pos small] using
          ih (halves t).1 lo hi i small
      · have outside : ¬ (lo ≤ i ∧ i < hi) := by omega
        simp [assign,vacant,all,left,ownerAt,small,outside]
    · by_cases right : 2^d ≤ lo
      · by_cases small : i < 2^d
        · have outside : ¬ (lo ≤ i ∧ i < hi) := by omega
          simp [assign,vacant,all,left,right,ownerAt,small,outside]
        · have agree : (lo-2^d ≤ i-2^d ∧ i-2^d < hi-2^d) ↔ (lo ≤ i ∧ i < hi) := by omega
          simpa only [assign,if_neg vacant,if_neg all,if_neg left,if_pos right,ownerAt,
            if_neg small,agree] using ih (halves t).2 (lo-2^d) (hi-2^d) (i-2^d) (by omega)
      · by_cases small : i < 2^d
        · have agree : (lo ≤ i ∧ i < 2^d) ↔ (lo ≤ i ∧ i < hi) := by omega
          simpa only [assign,if_neg vacant,if_neg all,if_neg left,if_neg right,ownerAt,
            if_pos small,agree] using ih (halves t).1 lo (2^d) i small
        · have agree : (0 ≤ i-2^d ∧ i-2^d < hi-2^d) ↔ (lo ≤ i ∧ i < hi) := by omega
          simpa only [assign,if_neg vacant,if_neg all,if_neg left,if_neg right,ownerAt,
            if_neg small,agree] using ih (halves t).2 0 (hi-2^d) (i-2^d) (by omega)

theorem assign_full (owner : ℕ) {d : ℕ} (t : Tree d) :
    assign owner d t 0 (2^d) = (.uniform owner,1) := by
  cases d with
  | zero => simp [assign]
  | succ d => simp [assign]

theorem assign_prefix_visits (owner : ℕ) {d : ℕ} (t : Tree d) (hi : ℕ) :
    (assign owner d t 0 hi).2 ≤ 2*d+1 := by
  induction d generalizing hi with
  | zero => simp only [assign]; split <;> rfl
  | succ d ih =>
    have positive : 0 < (2:ℕ)^d := Nat.pow_pos (by decide)
    simp only [assign]
    split
    · omega
    split
    · omega
    split
    · have h := ih (halves t).1 hi
      omega
    · rw [if_neg (not_le_of_gt positive),assign_full]
      have h := ih (halves t).2 (hi-2^d)
      omega

theorem assign_suffix_visits (owner : ℕ) {d : ℕ} (t : Tree d) (lo : ℕ) :
    (assign owner d t lo (2^d)).2 ≤ 2*d+1 := by
  induction d generalizing lo with
  | zero => simp only [assign]; split <;> rfl
  | succ d ih =>
    have positive : 0 < (2:ℕ)^d := Nat.pow_pos (by decide)
    have full : (2:ℕ)^(d+1) = 2^d+2^d := by rw [pow_succ,Nat.mul_two]
    have beyond : ¬ 2^(d+1) ≤ (2:ℕ)^d := by rw [full]; omega
    have shifted : (2:ℕ)^(d+1)-2^d = 2^d := by rw [full,Nat.add_sub_cancel]
    simp only [assign]
    split
    · omega
    split
    · omega
    split
    · rw [shifted]
      have h := ih (halves t).2 (lo-2^d)
      omega
    · rw [shifted,assign_full]
      have h := ih (halves t).1 lo
      omega

theorem assign_visits (owner : ℕ) {d : ℕ} (t : Tree d) (lo hi : ℕ) :
    (assign owner d t lo hi).2 ≤ 4*d+1 := by
  induction d generalizing lo hi with
  | zero => simp only [assign]; split <;> rfl
  | succ d ih =>
    simp only [assign]
    split
    · omega
    split
    · omega
    split
    · have h := ih (halves t).1 lo hi
      omega
    split
    · have h := ih (halves t).2 (lo-2^d) (hi-2^d)
      omega
    · have left := assign_suffix_visits owner (halves t).1 lo
      have right := assign_prefix_visits owner (halves t).2 (hi-2^d)
      omega

theorem probe_exact {d : ℕ} (t : Tree d) (i : ℕ) :
    (probe t i).1 = ownerAt t i ∧ (probe t i).2 ≤ d+1 := by
  induction t generalizing i with
  | uniform owner => simp [probe,ownerAt]
  | @fork d l r ihl ihr =>
    by_cases left : i < 2^d
    · obtain ⟨eq,cost⟩ := ihl i
      exact ⟨by simpa [probe,ownerAt,left] using eq,by simp [probe,left]; omega⟩
    · obtain ⟨eq,cost⟩ := ihr (i-2^d)
      exact ⟨by simpa [probe,ownerAt,left] using eq,by simp [probe,left]; omega⟩

end PvsNP.PersistentIntervalIndex

namespace PvsNP.LazyCopyIndex

open PvsNP.SourceIntervalMap
open PvsNP.PersistentIntervalIndex

theorem winner_le (history : List Instruction) (i : ℕ) : winner history i ≤ history.length := by
  induction history with
  | nil => simp [winner]
  | cons c rest ih =>
    by_cases active : (target c).contains i
    · simp [winner,active]
    · simpa [winner,active] using ih.trans (Nat.le_succ _)

@[simp] theorem entry_push_lt {d : ℕ} (index : Array (Entry d)) (c : Entry d)
    {time : ℕ} (h : time < index.size) : entry (index.push c) time = entry index time := by
  simp [entry,Array.getElem?_push,h,Nat.ne_of_lt h]

@[simp] theorem entry_push_last {d : ℕ} (index : Array (Entry d)) (c : Entry d) :
    entry (index.push c) index.size = c := by
  simp [entry]

theorem build_size (cuts : Finset ℕ) (d : ℕ) (history : List Instruction) :
    (build cuts d history).1.size = history.length+1 := by
  induction history with
  | nil => rfl
  | cons c rest ih => simp [build,ih]

theorem build_visits (cuts : Finset ℕ) (d : ℕ) (history : List Instruction) :
    (build cuts d history).2 ≤ (4*d+1)*history.length := by
  induction history with
  | nil => simp [build]
  | cons c rest ih =>
    have current := assign_visits (rest.length+1)
      (entry (build cuts d rest).1 rest.length).root
      (rank cuts (target c).start) (rank cuts (target c).finish)
    simp only [build,List.length_cons,Nat.mul_succ]
    omega

theorem mem_cuts {cuts : Finset ℕ} {history : List Instruction}
    (contains : cutsOf history ⊆ cuts) (c : Instruction) (mem : c ∈ history) :
    (target c).start ∈ cuts ∧ (target c).finish ∈ cuts := by
  induction history with
  | nil => simp at mem
  | cons t rest ih =>
    rcases List.mem_cons.mp mem with rfl | in_tail
    · exact ⟨contains (by simp [cutsOf,boundaries]),contains (by simp [cutsOf,boundaries])⟩
    · apply ih
      · intro i hit
        exact contains (by simp [cutsOf,boundaries] at hit ⊢; tauto)
      · exact in_tail

theorem rank_contains {cuts : Finset ℕ} (c : Instruction) (i : ℕ)
    (lo : (target c).start ∈ cuts) (hi : (target c).finish ∈ cuts) :
    (rank cuts (target c).start ≤ rank cuts i ∧ rank cuts i < rank cuts (target c).finish) ↔
      (target c).contains i := by
  change _ ↔ (target c).start ≤ i ∧ i < (target c).finish
  rw [rank_comparison lo]
  simp only [← not_le,rank_comparison hi]

theorem pushed (cuts : Finset ℕ) (d : ℕ) (c : Instruction) (rest : List Instruction) :
    (build cuts d (c::rest)).1 =
      (build cuts d rest).1.push
        ⟨(assign (rest.length+1) d (entry (build cuts d rest).1 rest.length).root
          (rank cuts (target c).start) (rank cuts (target c).finish)).1,some c⟩ :=
  rfl

theorem current (cuts : Finset ℕ) (d : ℕ) (c : Instruction) (rest : List Instruction) :
    entry (build cuts d (c::rest)).1 (rest.length+1) =
      ⟨(assign (rest.length+1) d (entry (build cuts d rest).1 rest.length).root
          (rank cuts (target c).start) (rank cuts (target c).finish)).1,some c⟩ := by
  rw [pushed,← build_size cuts d rest,entry_push_last,build_size]

theorem entry_from_past (cuts : Finset ℕ) (d : ℕ) (c : Instruction) (rest : List Instruction)
    {time : ℕ} (earlier : time ≤ rest.length) :
    entry (build cuts d (c::rest)).1 time = entry (build cuts d rest).1 time := by
  rw [pushed,entry_push_lt]
  rw [build_size]
  omega

theorem build_exact (cuts : Finset ℕ) (d : ℕ) (history : List Instruction)
    (coverage : cutsOf history ⊆ cuts) (room : cuts.card < 2^d) (i : ℕ) :
    ownerAt (entry (build cuts d history).1 history.length).root (rank cuts i) = winner history i := by
  induction history with
  | nil => rfl
  | cons c rest ih =>
    have valid := mem_cuts coverage c (List.mem_cons_self ..)
    have inner : cutsOf rest ⊆ cuts := by
      intro k hit
      apply coverage
      simp [cutsOf,boundaries] at hit ⊢
      tauto
    simp only [List.length_cons]
    rw [current,assign_exact _ _ _ _ _ ((rank_le_size cuts i).trans_lt room),ih inner]
    have same := rank_contains c i valid.1 valid.2
    by_cases active : (target c).contains i
    · simp only [winner,if_pos active,if_pos (same.mpr active)]
    · simp only [winner,if_neg active,if_neg (fun hit => active (same.mp hit))]

end PvsNP.LazyCopyIndex

namespace PvsNP.LazyCopyIndex

open PvsNP.SourceIntervalMap
open PvsNP.PersistentIntervalIndex

theorem resolve_visits {d : ℕ} (index : Array (Entry d)) (cuts : Finset ℕ) (initial : Origins)
    (time address : ℕ) :
    let report := resolve index cuts initial time address
    report.nodeVisits ≤ (d+1)*report.probes ∧ report.probes ≤ time+1 := by
  induction time using Nat.strong_induction_on generalizing address with
  | h time ih =>
    rw [resolve]
    dsimp only
    have cost := (probe_exact (entry index time).root (rank cuts address)).2
    split
    · rename_i live
      split
      · simp [cost]
      · simp [cost]
      · rename_i source dest width hit
        have earlier : (probe (entry index time).root (rank cuts address)).1-1 < time := by omega
        have ⟨part, few⟩ := ih _ earlier (source+(address-dest))
        dsimp only
        rw [Nat.mul_succ]
        omega
    · simp [cost]

theorem resolve_old {d : ℕ} (index : Array (Entry d)) (newer : Entry d)
    (cuts : Finset ℕ) (initial : Origins) (time address : ℕ) (older : time < index.size) :
    resolve (index.push newer) cuts initial time address = resolve index cuts initial time address := by
  induction time using Nat.strong_induction_on generalizing address with
  | h time ih =>
    conv_lhs => rw [resolve]
    conv_rhs => rw [resolve]
    simp only [entry_push_lt _ _ older]
    split
    · rename_i live
      have feasible : (probe (entry index time).root (rank cuts address)).1 < index.size := by omega
      rw [entry_push_lt _ _ feasible]
      split
      · rfl
      · rfl
      · have prior : (probe (entry index time).root (rank cuts address)).1-1 < time := by omega
        rw [ih _ prior _ (prior.trans older)]
    · rfl

theorem resolve_same_writer {d : ℕ} (index : Array (Entry d))
    (cuts : Finset ℕ) (initial : Origins) (time₁ time₂ address owner : ℕ)
    (smaller : owner ≤ time₁) (larger : owner ≤ time₂)
    (first : ownerAt (entry index time₁).root (rank cuts address) = owner)
    (second : ownerAt (entry index time₂).root (rank cuts address) = owner) :
    (resolve index cuts initial time₁ address).origin =
      (resolve index cuts initial time₂ address).origin := by
  conv_lhs => rw [resolve]
  conv_rhs => rw [resolve]
  simp only [(probe_exact (entry index time₁).root (rank cuts address)).1,
    (probe_exact (entry index time₂).root (rank cuts address)).1,first,second]
  by_cases positive : 0 < owner
  · simp only [dif_pos (show 0 < owner ∧ owner ≤ time₁ from ⟨positive,smaller⟩),
      dif_pos (show 0 < owner ∧ owner ≤ time₂ from ⟨positive,larger⟩)]
    split <;> rfl
  · have zero : owner=0 := by omega
    simp [zero]

theorem resolve_exact (cuts : Finset ℕ) (d : ℕ) (history : List Instruction)
    (coverage : cutsOf history ⊆ cuts) (enough : cuts.card < 2^d)
    (initial : Origins) (address : ℕ) :
    (resolve (build cuts d history).1 cuts initial history.length address).origin =
      eval history initial address := by
  induction history generalizing address with
  | nil => simp [resolve,build,entry,blank,probe,eval]
  | cons c rest ih =>
    let older := (build cuts d rest).1
    let newer := (build cuts d (c::rest)).1
    have inner : cutsOf rest ⊆ cuts := by
      intro k hit
      apply coverage
      simp [cutsOf,boundaries] at hit ⊢
      tauto
    have oldOwner := build_exact cuts d rest inner enough address
    have newOwner := build_exact cuts d (c::rest) coverage enough address
    change ownerAt (entry newer (rest.length+1)).root (rank cuts address) =
      winner (c::rest) address at newOwner
    change ownerAt (entry older rest.length).root (rank cuts address) = winner rest address at oldOwner
    have before (x : ℕ) :
        resolve newer cuts initial rest.length x = resolve older cuts initial rest.length x := by
      unfold newer
      rw [pushed]
      apply resolve_old
      simp [build_size]
    change (resolve newer cuts initial (rest.length+1) address).origin =
      applyOp c (eval rest initial) address
    by_cases active : (target c).contains address
    · simp only [winner,if_pos active] at newOwner
      conv_lhs => rw [resolve]
      simp only [(probe_exact (entry newer (rest.length+1)).root (rank cuts address)).1,
        newOwner,dif_pos (show 0 < rest.length+1 ∧ rest.length+1 ≤ rest.length+1 by omega)]
      have command : (entry newer (rest.length+1)).code = some c := by
        unfold newer
        rw [current]
      rw [command]
      cases c with
      | direct p =>
        change p.contains address at active
        simp [applyOp,applyPatch,active]
      | copy source dest width =>
        have inside : dest ≤ address ∧ address < dest+width := active
        simp only [applyOp,snapshotCopy,if_pos inside,Nat.add_sub_cancel]
        rw [before,ih inner]
    · simp only [winner,if_neg active] at newOwner
      have same : ownerAt (entry newer rest.length).root (rank cuts address) =
          winner rest address := by
        rw [show entry newer rest.length = entry older rest.length from
          entry_from_past cuts d c rest le_rfl,oldOwner]
      have cap := winner_le rest address
      rw [resolve_same_writer newer cuts initial (rest.length+1) rest.length address (winner rest address)
        (cap.trans (Nat.le_succ _)) cap newOwner same,before,ih inner]
      cases c with
      | direct p =>
        change ¬ p.contains address at active
        simp [applyOp,applyPatch,active]
      | copy source dest width =>
        have outside : ¬ (dest ≤ address ∧ address < dest+width) := active
        simp [applyOp,snapshotCopy,outside]

end PvsNP.LazyCopyIndex

namespace PvsNP.SourceIntervalMap

theorem rank_of_cut (cuts : Finset ℕ) (i : Fin cuts.card) :
    rank cuts (cuts.orderEmbOfFin rfl i) = i.val+1 := by
  let emb := cuts.orderEmbOfFin (k := cuts.card) rfl
  have eq : (cuts.filter (fun x => x ≤ emb i)) = (Finset.Iic i).map emb.toEmbedding := by
    ext x
    constructor
    · intro h
      obtain ⟨inside,atMost⟩ := Finset.mem_filter.mp h
      let j := (cuts.orderIsoOfFin rfl).symm ⟨x,inside⟩
      have address : emb j = x := by
        change (↑((cuts.orderIsoOfFin rfl) j) : ℕ) = x
        simp [j]
      exact Finset.mem_map.mpr ⟨j,Finset.mem_Iic.mpr (emb.le_iff_le.mp (address ▸ atMost)),address⟩
    · intro h
      obtain ⟨j,atMost,eq⟩ := Finset.mem_map.mp h
      change emb j = x at eq
      subst x
      exact Finset.mem_filter.mpr ⟨cuts.orderEmbOfFin_mem rfl j,emb.monotone (Finset.mem_Iic.mp atMost)⟩
  change (cuts.filter (fun x => x ≤ emb i)).card = i.val+1
  rw [eq,Finset.card_map,Fin.card_Iic]

private theorem boundary_key (cuts : Finset ℕ) (address j : ℕ) (fits : j < cuts.card) :
    ((cuts.sort).toArray[j]?.getD 0 ≤ address) ↔ j < rank cuts address := by
  let i : Fin cuts.card := ⟨j,fits⟩
  have len : j < cuts.sort.length := by simpa using fits
  have readEq : ((cuts.sort).toArray[j]?.getD 0) = cuts.orderEmbOfFin rfl i := by
    rw [Finset.orderEmbOfFin_apply]
    rw [List.getElem?_toArray,List.getElem?_eq_getElem len]
    rfl
  rw [readEq,← rank_comparison (cuts.orderEmbOfFin_mem rfl i),rank_of_cut]
  change (j+1 ≤ rank cuts address) ↔ j < rank cuts address
  omega

theorem upperSearch_exact (array : Array ℕ) (address endRank : ℕ)
    (boundary : ∀ j, j < array.size → (array[j]?.getD 0 ≤ address ↔ j < endRank))
    (fuel lo len : ℕ) (enough : len < 2^fuel) (fits : lo+len ≤ array.size)
    (window : lo ≤ endRank ∧ endRank ≤ lo+len) :
    (upperSearch array address fuel lo len).1 = endRank ∧
      (upperSearch array address fuel lo len).2 ≤ fuel := by
  induction fuel generalizing lo len with
  | zero =>
    simp only [pow_zero] at enough
    have exact : lo=endRank := by omega
    simp [upperSearch,exact]
  | succ fuel ih =>
    by_cases empty : len=0
    · have exact : lo=endRank := by omega
      simp [upperSearch,empty,exact]
    · have useful : lo+len/2 < array.size := by omega
      have small : len/2 < 2^fuel := by rw [pow_succ] at enough; omega
      have small' : len-(len/2+1) < 2^fuel := by omega
      by_cases right : array[lo+len/2]?.getD 0 ≤ address
      · have after := (boundary _ useful).mp right
        obtain ⟨res,cost⟩ := ih (lo+len/2+1) (len-(len/2+1)) small' (by omega) ⟨by omega,by omega⟩
        simp only [upperSearch,if_neg empty,if_pos right]
        exact ⟨res,Nat.succ_le_succ cost⟩
      · have before : endRank ≤ lo+len/2 := by
          by_contra! lt
          exact right ((boundary _ useful).mpr lt)
        obtain ⟨res,cost⟩ := ih lo (len/2) small (by omega) ⟨by omega,by omega⟩
        simp only [upperSearch,if_neg empty,if_neg right]
        exact ⟨res,Nat.succ_le_succ cost⟩

theorem searchRank_exact (cuts : Finset ℕ) (address : ℕ) :
    (searchRank cuts.sort.toArray address).1 = rank cuts address ∧
      (searchRank cuts.sort.toArray address).2 ≤ cuts.card.size := by
  let array := cuts.sort.toArray
  have len : array.size = cuts.card := by simp [array]
  have boundary (j : ℕ) (fits : j < array.size) :
      (array[j]?.getD 0 ≤ address ↔ j < rank cuts address) := boundary_key cuts address j (by omega)
  have search := upperSearch_exact array address _ boundary array.size.size 0 array.size
    (Nat.lt_size_self _) (by simp) ⟨Nat.zero_le _,by rw [Nat.zero_add,len]; exact rank_le_size _ _⟩
  simpa [searchRank,array,len] using search

end PvsNP.SourceIntervalMap

namespace PvsNP.LazyCopyIndex

open PvsNP.SourceIntervalMap
open PvsNP.PersistentIntervalIndex

theorem buildFast_exact (cuts : Finset ℕ) (d : ℕ) (history : List Instruction) :
    let fast := buildFast cuts.sort.toArray d history
    fast.1 = (build cuts d history).1 ∧
      fast.2 ≤ (4*d+1+2*cuts.card.size)*history.length := by
  induction history with
  | nil => simp [buildFast,build]
  | cons c rest ih =>
    obtain ⟨prior,cost⟩ := ih
    obtain ⟨lo,left⟩ := searchRank_exact cuts (target c).start
    obtain ⟨hi,right⟩ := searchRank_exact cuts (target c).finish
    have visits := assign_visits (rest.length+1) (entry (build cuts d rest).1 rest.length).root
      (rank cuts (target c).start) (rank cuts (target c).finish)
    simp only [buildFast,build,List.length_cons,prior,lo,hi,Nat.mul_succ]
    constructor
    · trivial
    · omega

theorem resolveFast_exact {d : ℕ} (index : Array (Entry d)) (cuts : Finset ℕ)
    (initial : Origins) (time address : ℕ) :
    let fast := resolveFast index cuts.sort.toArray initial time address
    let slow := resolve index cuts initial time address
    fast.origin = slow.origin ∧ fast.probes = slow.probes ∧
      fast.nodeVisits ≤ (d+1+cuts.card.size)*fast.probes := by
  induction time using Nat.strong_induction_on generalizing address with
  | h time ih =>
    rw [resolveFast,resolve]
    dsimp only
    obtain ⟨r,rankCost⟩ := searchRank_exact cuts address
    have askCost := (probe_exact (entry index time).root (rank cuts address)).2
    rw [r]
    split
    · rename_i live
      split
      · rename_i eq
        simp
        omega
      · rename_i eq
        simp
        omega
      · rename_i src dst len eq
        have earlier : (probe (entry index time).root (rank cuts address)).1-1 < time := by omega
        have ⟨meaning,visits,actual⟩ := ih _ earlier (src+(address-dst))
        dsimp only
        refine ⟨meaning,by omega,?_⟩
        rw [Nat.mul_succ]
        omega
    · rename_i expired
      simp
      omega

theorem recoverFast_from_original (history : List Instruction) (initial : Origins) (address : ℕ) :
    let cuts := cutsOf history
    let keys := cuts.sort.toArray
    let depth := cuts.card.size
    let table := buildFast keys depth history
    let result := resolveFast table.1 keys initial history.length address
    result.origin = eval history initial address ∧
      table.2 ≤ (6*depth+1)*history.length ∧
      result.nodeVisits ≤ (2*depth+1)*result.probes ∧
      result.probes ≤ history.length+1 := by
  let cuts := cutsOf history
  let depth := cuts.card.size
  have ⟨records,bound⟩ := buildFast_exact cuts depth history
  have exactData := resolveFast_exact (build cuts depth history).1 cuts initial history.length address
  have original := resolve_exact cuts depth history (by intro _ h; exact h) (Nat.lt_size_self _) initial address
  have maxProbes := (resolve_visits (build cuts depth history).1 cuts initial history.length address).2
  dsimp only
  rw [records]
  exact ⟨exactData.1.trans original,by simpa [depth,show 4*depth+1+2*depth=6*depth+1 by omega] using bound,
    by simpa [depth,show depth+1+depth=2*depth+1 by omega] using exactData.2.2,
    exactData.2.1.trans_le maxProbes⟩

end PvsNP.LazyCopyIndex

open PvsNP.LazyCopyIndex PvsNP.SourceIntervalMap

theorem solution (history : List Instruction) (initial : Origins) (address : ℕ) :
    let cuts := cutsOf history
    let keys := cuts.sort.toArray
    let depth := cuts.card.size
    let table := buildFast keys depth history
    let result := resolveFast table.1 keys initial history.length address
    result.origin = eval history initial address ∧
      table.2 ≤ (6*depth+1)*history.length ∧
      result.nodeVisits ≤ (2*depth+1)*result.probes ∧
      result.probes ≤ history.length+1 ∧
      cuts.card ≤ 2*history.length := by
  have ⟨origin, buildBound, visitBound, probeBound⟩ :=
    recoverFast_from_original history initial address
  exact ⟨origin, buildBound, visitBound, probeBound, by
    simpa [cutsOf] using boundaries_card (history.map target)⟩
