-- Prove2me | solution 1 for PvsNP.OnlineRegionRead.exact_two_phase_record
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T04:44:18.686657+00:00
-- url     : https://prove2.me/submissions/8ececad7-0494-4a13-8488-20af0e0041ca

import Definitions.Def_OnlineExecutionLog

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace PvsNP.OnlineRegionRead

open WorkBoundarySplice

variable {Q Γ : Type}

theorem Segment.reads_interval {M : Program Q Γ} {word : Word} {mask : ℤ → Bool}
    {owner : Bool} {a b : Cursor Q Γ} {reads : List ℕ} {n : ℕ}
    (run : Segment M word mask owner a b reads n) :
    reads = List.range' a.input reads.length ∧ b.input = a.input + reads.length := by
  induction run with
  | refl a => simp
  | @next a mid b scanned more n _ event _ ih =>
      cases cmd : M a.work.state (a.work.tape a.work.head) with
      | localStep q value d =>
          simp only [tick,cmd,Option.some.injEq,Prod.mk.injEq] at event
          obtain ⟨rfl,rfl⟩ := event
          simpa using ih
      | read next =>
          simp only [tick,cmd,Option.some.injEq,Prod.mk.injEq] at event
          obtain ⟨rfl,rfl⟩ := event
          refine ⟨?_,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih.2⟩
          simp only [Option.toList_some,List.singleton_append,List.length_cons,List.range'_succ]
          exact congrArg (a.input :: ·) ih.1
      | halt => simp [tick,cmd] at event

theorem Aligned.of_stamp_eq {a b : Cursor Q Γ} (same : a.stamp = b.stamp) : Aligned a b :=
  ⟨congrArg Stamp.control same,congrArg Stamp.head same,congrArg Stamp.input same⟩

private theorem Routes.congr_above {r s : ℕ → Bool} {log : List (LogEntry Q Γ)}
    {start : ℕ} (h : Routes r start log)
    (ordered : (start :: log.map (fun e => e.atEnd.input)).Pairwise (· ≤ ·))
    (same : ∀ i, start ≤ i → r i = s i) : Routes s start log := by
  induction log generalizing start with
  | nil => trivial
  | cons event tail ih =>
      have mono : start ≤ event.atEnd.input := List.rel_of_pairwise_cons ordered (by simp)
      refine ⟨fun i earlier later => (same i earlier).symm.trans (h.1 i earlier later),?_⟩
      exact ih h.2 ordered.tail (fun i hi => same i (mono.trans hi))

theorem routeFrom_realizes (log : List (LogEntry Q Γ)) (start : ℕ)
    (ordered : (start :: log.map (fun e => e.atEnd.input)).Pairwise (· ≤ ·)) :
    Routes (routeFrom log) start log := by
  induction log generalizing start with
  | nil => trivial
  | cons event tail ih =>
      refine ⟨fun i _ later => by simp [routeFrom,later],?_⟩
      exact (ih _ ordered.tail).congr_above ordered.tail (fun i hi => by simp [routeFrom,not_lt_of_ge hi])

private theorem segment_index {M : Program Q Γ} {word : Word} {mask : ℤ → Bool}
    {owner : Bool} {a z : Cursor Q Γ} {reads : List ℕ} {n : ℕ}
    (h : Segment M word mask owner a z reads n) {i : ℕ} (hi : i ∈ reads) :
    a.input ≤ i ∧ i < z.input := by
  have interval := h.reads_interval
  rw [interval.1,List.mem_range'] at hi
  obtain ⟨j,bound,eq⟩ := hi
  rw [interval.2]
  omega

private theorem ordered_add {M : Program Q Γ} {word : Word} {mask : ℤ → Bool}
    {owner : Bool} {a z : Cursor Q Γ} {reads : List ℕ} {n : ℕ} {rest : List ℕ}
    (h : Segment M word mask owner a z reads n) (tail : (z.input :: rest).Pairwise (· ≤ ·)) :
    (a.input :: z.input :: rest).Pairwise (· ≤ ·) := by
  have grow : a.input ≤ z.input := by rw [h.reads_interval.2]; omega
  apply List.pairwise_cons.mpr
  refine ⟨?_,tail⟩
  intro i hi
  rcases List.mem_cons.mp hi with eq|mem
  · simpa [eq] using grow
  · exact grow.trans (List.rel_of_pairwise_cons tail mem)

theorem Logged.ordered {M : Program Q Γ} {word : Word} {mask : Bool → ℤ → Bool} {strip : List ℤ}
    {phase : Bool} {a z : Cursor Q Γ} {log : List (LogEntry Q Γ)}
    (run : Logged M word mask strip phase a log z) :
    (a.input :: log.map (fun e => e.atEnd.input)).Pairwise (· ≤ ·) := by
  induction run with
  | finish _ seg atEnd =>
      cases atEnd
      exact ordered_add seg (by simp)
  | cross _ seg _ atEnd _ ih =>
      cases atEnd
      exact ordered_add seg ih
  | handoff _ seg atEnd _ _ ih =>
      cases atEnd
      exact ordered_add seg ih

private theorem reads_follow {M : Program Q Γ} {word : Word} {mask : ℤ → Bool}
    {owner : Bool} {a z : Cursor Q Γ} {reads : List ℕ} {n : ℕ}
    (seg : Segment M word mask owner a z reads n) {stamp : Stamp Q} (eq : z.stamp = stamp)
    {route : ℕ → Bool}
    (follows : ∀ i, a.input ≤ i → i < stamp.input → route i = owner) :
    ∀ i ∈ reads, route i = owner := by
  intro i hi
  obtain ⟨earlier,later⟩ := segment_index seg hi
  exact follows i earlier (congrArg Stamp.input eq ▸ later)

private theorem same_values {a b : Cursor Q Γ} {strip : List ℤ}
    (eq : strip.map a.work.tape = strip.map b.work.tape) {z : ℤ} (inside : z ∈ strip) :
    a.work.tape z = b.work.tape z := by
  induction strip with
  | nil => simp at inside
  | cons i rest ih =>
      have both := List.cons.inj eq
      rcases List.mem_cons.mp inside with h|h
      · simpa [h] using both.1
      · exact ih both.2 h

theorem Logged.align {M : Program Q Γ} {one zero : Word} {mask : Bool → ℤ → Bool} {strip : List ℤ}
    (covered : ∀ p, mask false p ≠ mask true p → p ∈ strip)
    {phase : Bool} {a a' b b' : Cursor Q Γ} {log : List (LogEntry Q Γ)}
    (left : Logged M one mask strip phase a log a') (right : Logged M zero mask strip phase b log b')
    (same : Aligned a b) {route : ℕ → Bool} (routes : Routes route a.input log) :
    ∃ last : Bool, JointTrace M one zero route (mask phase) a b (mask last) a' b' := by
  induction left generalizing b b' with
  | finish _ seg stamp =>
      cases right with
      | finish _ seg' stamp' =>
          have endAgree := Aligned.of_stamp_eq (stamp.trans stamp'.symm)
          refine ⟨_,.segment same endAgree seg seg' ?_ ?_ (.refl _ _ _)⟩
          · intro truth i hi
            exact (reads_follow seg stamp routes.1 i hi).trans truth
          · intro falsity i hi
            have control := reads_follow seg' stamp' (by simpa only [same.input] using routes.1)
            exact (control i hi).trans falsity
  | cross _ seg _ stamp _ ih =>
      cases right with
      | cross _ seg' _ stamp' next =>
          have endAgree := Aligned.of_stamp_eq (stamp.trans stamp'.symm)
          obtain ⟨last,tail⟩ := ih next endAgree (by simpa only [← congrArg Stamp.input stamp,Cursor.stamp] using routes.2)
          refine ⟨last,.segment same endAgree seg seg' ?_ ?_ tail⟩
          · intro truth i hi
            exact (reads_follow seg stamp routes.1 i hi).trans truth
          · intro falsity i hi
            have control := reads_follow seg' stamp' (by simpa only [same.input] using routes.1)
            exact (control i hi).trans falsity
  | handoff _ seg stamp snap _ ih =>
      cases right with
      | handoff _ seg' stamp' snap' next =>
          have endAgree := Aligned.of_stamp_eq (stamp.trans stamp'.symm)
          obtain ⟨last,tail⟩ := ih next endAgree (by simpa only [← congrArg Stamp.input stamp,Cursor.stamp] using routes.2)
          refine ⟨last,.segment same endAgree seg seg' ?_ ?_ (.handoff ?_ tail)⟩
          · intro truth i hi
            exact (reads_follow seg stamp routes.1 i hi).trans truth
          · intro falsity i hi
            have control := reads_follow seg' stamp' (by simpa only [same.input] using routes.1)
            exact (control i hi).trans falsity
          · intro p changed
            exact same_values (snap.trans snap'.symm) (covered p changed)

/-- Equal records suffice for the hybrid replay certificate. The raw input
routing is reconstructed from recorded input indices and region ownership. -/
theorem Logged.joint_from_record {M : Program Q Γ} {one zero : Word}
    {mask : Bool → ℤ → Bool} {strip : List ℤ}
    (covered : ∀ p, mask false p ≠ mask true p → p ∈ strip)
    {phase : Bool} {a a' b b' : Cursor Q Γ} {log : List (LogEntry Q Γ)}
    (left : Logged M one mask strip phase a log a') (right : Logged M zero mask strip phase b log b')
    (same : Aligned a b) :
    ∃ last : Bool, JointTrace M one zero (routeFrom log) (mask phase) a b (mask last) a' b' :=
  left.align covered right same (routeFrom_realizes log a.input left.ordered)

theorem Run.counted {M : Program Q Γ} {word : Word} {a z : Cursor Q Γ} {n : ℕ}
    (run : Run M word a z n) (mask : ℤ → Bool) :
    ∃ changes reads, CountedRun M word mask a z n changes reads := by
  induction run with
  | refl => exact ⟨0,[],.refl _⟩
  | next event _ ih =>
      obtain ⟨_,_,tail⟩ := ih
      exact ⟨_,_,.next event tail⟩

private theorem scan_index {M : Program Q Γ} {word : Word} {a b : Cursor Q Γ} {scan : Option ℕ}
    (step : tick M word a = some (b,scan)) :
    a.input ≤ b.input ∧ (∀ i ∈ scan.toList, i = a.input ∧ i < b.input) := by
  cases act : M a.work.state (a.work.tape a.work.head) with
  | localStep q x d =>
      simp [tick,act] at step
      obtain ⟨rfl,rfl⟩ := step
      simp
  | read receive =>
      simp [tick,act] at step
      obtain ⟨rfl,rfl⟩ := step
      simp
  | halt => simp [tick,act] at step

theorem CountedRun.input_mono {M : Program Q Γ} {word : Word} {mask : ℤ → Bool} {a z : Cursor Q Γ}
    {n c : ℕ} {reads : List (ℕ × Bool)} (run : CountedRun M word mask a z n c reads) :
    a.input ≤ z.input := by
  induction run with
  | refl => rfl
  | next step _ ih => exact (scan_index step).1.trans ih

theorem CountedRun.read_interval {M : Program Q Γ} {word : Word} {mask : ℤ → Bool} {a z : Cursor Q Γ}
    {n c : ℕ} {reads : List (ℕ × Bool)} (run : CountedRun M word mask a z n c reads)
    {i : ℕ} {b : Bool} (observed : (i,b) ∈ reads) :
    a.input ≤ i ∧ i < z.input := by
  induction run with
  | refl => simp at observed
  | next step tail ih =>
      rcases List.mem_append.mp observed with here | after
      · simp only [scannedOwners,List.mem_map,Prod.mk.injEq] at here
        obtain ⟨j,hj,rfl,_⟩ := here
        obtain ⟨eq,small⟩ := (scan_index step).2 _ hj
        exact ⟨eq.ge,small.trans_le tail.input_mono⟩
      · obtain ⟨lo,hi⟩ := ih after
        exact ⟨(scan_index step).1.trans lo,hi⟩

private theorem Logged.prepend_inside {M : Program Q Γ} {word : Word} {mask : Bool → ℤ → Bool}
    {strip : List ℤ} {phase : Bool} {a b z : Cursor Q Γ} {log : List (LogEntry Q Γ)}
    {scan : Option ℕ} (trace : Logged M word mask strip phase b log z)
    (step : tick M word a = some (b,scan)) (same : mask phase a.work.head = mask phase b.work.head) :
    Logged M word mask strip phase a log z := by
  cases trace with
  | finish owner seg mark => exact .finish (same.trans owner) (.next (same.trans owner) step seg) mark
  | cross owner seg different mark rest =>
      exact .cross (same.trans owner) (.next (same.trans owner) step seg) different mark rest
  | handoff owner seg mark cells rest =>
      exact .handoff (same.trans owner) (.next (same.trans owner) step seg) mark cells rest

private theorem Logged.first_owner {M : Program Q Γ} {word : Word} {mask : Bool → ℤ → Bool}
    {strip : List ℤ} {phase : Bool} {a z : Cursor Q Γ} {log : List (LogEntry Q Γ)}
    (trace : Logged M word mask strip phase a log z) :
    ∃ event rest, log = event :: rest ∧ event.owner = mask phase a.work.head ∧ a.input ≤ event.atEnd.input := by
  cases trace with
  | finish owner seg stamp =>
      exact ⟨_,[],rfl,owner.symm,by rw [← congrArg Stamp.input stamp]; simp only [Cursor.stamp]; rw [seg.reads_interval.2]; omega⟩
  | cross owner seg _ stamp _ =>
      exact ⟨_,_,rfl,owner.symm,by rw [← congrArg Stamp.input stamp]; simp only [Cursor.stamp]; rw [seg.reads_interval.2]; omega⟩
  | handoff owner seg stamp _ _ =>
      exact ⟨_,_,rfl,owner.symm,by rw [← congrArg Stamp.input stamp]; simp only [Cursor.stamp]; rw [seg.reads_interval.2]; omega⟩

private theorem Logged.prepend_one {M : Program Q Γ} {word : Word} {mask : Bool → ℤ → Bool}
    {strip : List ℤ} {phase : Bool} {a b z : Cursor Q Γ} {log : List (LogEntry Q Γ)}
    {scan : Option ℕ} (tail : Logged M word mask strip phase b log z)
    (step : tick M word a = some (b,scan)) :
    ∃ updated, Logged M word mask strip phase a updated z ∧
      updated.length = ownerChange (mask phase) a b + log.length ∧
      (∀ i, b.input ≤ i → routeFrom updated i = routeFrom log i) ∧
      (∀ i ∈ scan.toList, routeFrom updated i = mask phase a.work.head) := by
  classical
  by_cases same : mask phase a.work.head = mask phase b.work.head
  · refine ⟨log,tail.prepend_inside step same,by simp [ownerChange,same],fun _ _ => rfl,?_⟩
    intro i read
    obtain ⟨first,rest,logEq,own,large⟩ := tail.first_owner
    have small := ((scan_index step).2 i read).2.trans_le large
    rw [logEq]
    simp [routeFrom,small,own,same]
  · let first : LogEntry Q Γ := ⟨mask phase a.work.head,b.stamp,.cross⟩
    have seg : Segment M word (mask phase) first.owner a b scan.toList 1 := by
      simpa using Segment.next (c := b) rfl step (.refl b)
    have longer : Logged M word mask strip phase a (first :: log) z :=
      .cross rfl seg (Ne.symm same) rfl tail
    refine ⟨first :: log,longer,by simp [ownerChange,same,Nat.add_comm],?_,?_⟩
    · intro i large
      simp [first,Cursor.stamp,routeFrom,not_lt_of_ge large]
    · intro i read
      have small := ((scan_index step).2 i read).2
      simp [first,Cursor.stamp,routeFrom,small]

/-- Extending a record back over a real run adds precisely one entry per
ownership change. Its route matches every actual read and it leaves the
route of the existing future unchanged. -/
theorem CountedRun.prepend_record {M : Program Q Γ} {word : Word} {mask : Bool → ℤ → Bool}
    {strip : List ℤ} {phase : Bool} {a b z : Cursor Q Γ} {n c : ℕ}
    {reads : List (ℕ × Bool)} {log : List (LogEntry Q Γ)}
    (run : CountedRun M word (mask phase) a b n c reads)
    (record : Logged M word mask strip phase b log z) :
    ∃ updated, Logged M word mask strip phase a updated z ∧ updated.length = c + log.length ∧
      (∀ i, b.input ≤ i → routeFrom updated i = routeFrom log i) ∧
      (∀ item ∈ reads, routeFrom updated item.1 = item.2) := by
  induction run with
  | refl => exact ⟨log,record,by simp,fun _ _ => rfl,by simp⟩
  | next event tail ih =>
      obtain ⟨inner,innerRecord,innerLength,innerFuture,innerOwners⟩ := ih record
      obtain ⟨whole,wholeRecord,wholeLength,wholeFuture,wholeOwners⟩ := innerRecord.prepend_one event
      refine ⟨whole,wholeRecord,by rw [wholeLength,innerLength,Nat.add_assoc],?_,?_⟩
      · intro i future
        exact (wholeFuture i (tail.input_mono.trans future)).trans (innerFuture i future)
      · intro item observed
        rcases List.mem_append.mp observed with current|later
        · obtain ⟨i,found,rfl⟩ := List.mem_map.mp current
          exact wholeOwners i found
        · have after := (tail.read_interval later).1
          exact (wholeFuture item.1 after).trans (innerOwners item later)

theorem CountedRun.after_transfer {M : Program Q Γ} {word : Word} {mask : Bool → ℤ → Bool}
    {strip : List ℤ} {a z : Cursor Q Γ} {n c : ℕ} {reads : List (ℕ × Bool)}
    (run : CountedRun M word (mask true) a z n c reads) :
    ∃ log, Logged M word mask strip true a log z ∧ log.length = c+1 ∧
      (∀ item ∈ reads, routeFrom log item.1 = item.2) := by
  let endLog : List (LogEntry Q Γ) := [⟨mask true z.work.head,z.stamp,.finish⟩]
  have finish : Logged M word mask strip true z endLog z :=
    .finish rfl (.refl z) rfl
  obtain ⟨log,record,length,_,owners⟩ := run.prepend_record finish
  exact ⟨log,record,length,owners⟩

/-- Split an actual run at one handoff. The record consists of precisely
the ownership changes in the two parts, one handoff, and one terminal stamp. -/
theorem extract_record {M : Program Q Γ} {word : Word} {mask : Bool → ℤ → Bool}
    (strip : List ℤ) {a middle z : Cursor Q Γ} {n m c d : ℕ} {p q : List (ℕ × Bool)}
    (first : CountedRun M word (mask false) a middle n c p)
    (second : CountedRun M word (mask true) middle z m d q) :
    ∃ log, Logged M word mask strip false a log z ∧ log.length = c+d+2 ∧
      ∀ item ∈ p ++ q, routeFrom log item.1 = item.2 := by
  obtain ⟨tail,tailRecord,tailLength,tailOwners⟩ := second.after_transfer (strip := strip)
  let entry : LogEntry Q Γ := ⟨mask false middle.work.head,middle.stamp,.handoff (strip.map middle.work.tape)⟩
  have midRecord : Logged M word mask strip false middle (entry :: tail) z :=
    .handoff rfl (.refl middle) rfl rfl tailRecord
  obtain ⟨whole,trace,length,future,owners⟩ := first.prepend_record midRecord
  refine ⟨whole,trace,by simp only [length,List.length_cons,tailLength]; omega,?_⟩
  intro item observed
  rcases List.mem_append.mp observed with earlier|later
  · exact owners item earlier
  · have lo := (second.read_interval later).1
    rw [future item.1 lo]
    simp [entry,Cursor.stamp,routeFrom,not_lt_of_ge lo,tailOwners item later]

end PvsNP.OnlineRegionRead

open PvsNP.OnlineRegionRead

theorem solution
    {Q Γ : Type} {M : Program Q Γ} {word : Word} {mask : Bool → ℤ → Bool}
    (strip : List ℤ) (covered : ∀ p, mask false p ≠ mask true p → p ∈ strip)
    {a mid z : Cursor Q Γ} {n m c d : ℕ} {p q : List (ℕ × Bool)}
    (first : CountedRun M word (mask false) a mid n c p)
    (second : CountedRun M word (mask true) mid z m d q) :
    ∃ log, Logged M word mask strip false a log z ∧ log.length = c+d+2 ∧
      (∀ item ∈ p ++ q, routeFrom log item.1 = item.2) ∧
      ∀ {other : Word} {b b' : Cursor Q Γ},
        Logged M other mask strip false b log b' → Aligned a b →
        ∃ last : Bool, JointTrace M word other (routeFrom log) (mask false) a b (mask last) z b' := by
  obtain ⟨log,record,length,owners⟩ := extract_record strip first second
  refine ⟨log,record,length,owners,?_⟩
  exact fun otherRecord aligned => record.joint_from_record covered otherRecord aligned

#print axioms solution
