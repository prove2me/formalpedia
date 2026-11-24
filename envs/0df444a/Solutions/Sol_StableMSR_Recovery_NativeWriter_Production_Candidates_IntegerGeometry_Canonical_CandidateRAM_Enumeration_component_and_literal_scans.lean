-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration.component_and_literal_scans
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T01:37:57.693972+00:00
-- url     : https://prove2.me/submissions/6f8e2427-d266-4f74-9ec8-361d07f459cf

import Definitions.Def_StableMSR_CanonicalRegionalCompiler
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration
open SingleCircuit TightLanguage
set_option autoImplicit false
set_option maxHeartbeats 2000000
abbrev Seen := Finset ℕ
def rounds {A:Type} (f:A→A) (s:A) : ℕ→A
  | 0=>s | k+1=>f (rounds f s k)
theorem rounds_shift {A:Type} (f:A→A) (s:A) (k:ℕ) : rounds f s (k+1)=rounds f (f s) k:=by
  induction k with | zero=>rfl | succ k ih=>change f (rounds f s (k+1))=f (rounds f (f s) k);rw [ih]
theorem constant_rounds {A:Type} {f:A→A} {s:A} (h:f s=s) (k:ℕ) : rounds f s k=s:=by
  induction k with | zero=>rfl | succ k ih=>simp [rounds,ih,h]

theorem fixed_after (f:Seen→Seen) (U:Seen) (ext:∀s,s⊆U → s⊆f s) (cap:∀s,s⊆U → f s⊆U)
    (k:ℕ) (s:Seen) (hs:s⊆U) (enough:U.card ≤ s.card+k) : f (rounds f s k)=rounds f s k:=by
  induction k generalizing s with
  | zero=>
    have eq:s=U:=Finset.eq_of_subset_of_card_le hs (by omega)
    exact Finset.Subset.antisymm ((cap s hs).trans eq.symm.subset) (ext s hs)
  | succ k ih=>
    by_cases fix:f s=s
    · rw [constant_rounds fix];exact fix
    have lt:s.card<(f s).card:=by
      by_contra! le
      exact fix (Finset.eq_of_subset_of_card_le (ext s hs) le).symm
    rw [rounds_shift]
    exact ih (f s) (cap s hs) (by omega)

def advance (e:ℕ→ℕ→Bool) (U s:Seen) : Seen:=
  U.filter (fun u=>u∈s ∨ ∃z∈s,e z u=true)
@[simp] theorem mem_advance (e:ℕ→ℕ→Bool) (U s:Seen) (u:ℕ) :
  u∈advance e U s ↔ u∈U ∧ (u∈s ∨ ∃z∈s,e z u=true):=by classical simp [advance]

def mark (e:ℕ→ℕ→Bool) (s:Seen) (u:ℕ) : Seen:=
  if ∃z∈s,e z u=true then insert u s else s
def propagate (e:ℕ→ℕ→Bool) (us:List ℕ) (s:Seen):=us.foldl (mark e) s

theorem mark_ext (e:ℕ→ℕ→Bool) (s:Seen) (u:ℕ) : s⊆mark e s u:=by
  classical unfold mark;split <;> simp_all
theorem swept_ext (e:ℕ→ℕ→Bool) (us:List ℕ) (s:Seen) : s⊆propagate e us s:=by
  induction us generalizing s with
  | nil=>rfl
  | cons u us ih=>exact (mark_ext e s u).trans (ih _)

theorem swept_hits (e:ℕ→ℕ→Bool) (us:List ℕ) {u z:ℕ} (hu:u∈us) (s:Seen) (hz:z∈s) (edge:e z u=true) :
    u∈propagate e us s:=by
  classical
  induction us generalizing s with
  | nil=>simp at hu
  | cons a us ih=>
    rcases List.mem_cons.mp hu with eq|mem
    · subst a
      have put:u∈mark e s u:=by simp [mark,show ∃j∈s,e j u=true from ⟨z,hz,edge⟩]
      exact swept_ext e us _ put
    · exact ih mem _ (mark_ext e s a hz)

theorem swept_within (e:ℕ→ℕ→Bool) (U C:Seen) (closed:advance e U C⊆C)
    (us:List ℕ) (allow:∀u∈us,u∈U) (s:Seen) (start:s⊆C) : propagate e us s⊆C:=by
  classical
  induction us generalizing s with
  | nil=>exact start
  | cons u us ih=>
    apply ih (fun a ha=>allow a (by simp [ha]))
    unfold mark
    split
    · next yes=>
        obtain ⟨z,hz,edge⟩:=yes
        exact Finset.insert_subset (closed ((mem_advance ..).2 ⟨allow u (by simp),Or.inr ⟨z,start hz,edge⟩⟩)) start
    · exact start

theorem synchronous_asynchronous (e:ℕ→ℕ→Bool) (us:List ℕ) (s:Seen) (k:ℕ)
    (hs:s⊆us.toFinset) (enough:us.toFinset.card ≤ s.card+k) :
    rounds (propagate e us) s k=rounds (advance e us.toFinset) s k:=by
  classical
  let U:=us.toFinset
  let f:=advance e U
  have ex:∀a:Seen,a⊆U → a⊆f a:=by
    intro a sub i hi;exact (mem_advance ..).2 ⟨sub hi,Or.inl hi⟩
  have cap:∀a:Seen,a⊆U → f a⊆U:=by intro a _ i hi;exact ((mem_advance ..).1 hi).1
  have grows (j:ℕ) : s⊆rounds f s j ∧ rounds f s j⊆U:=by
    induction j with
    | zero=>exact ⟨Finset.Subset.rfl,hs⟩
    | succ j ih=>exact ⟨ih.1.trans (ex _ ih.2),cap _ ih.2⟩
  let C:=rounds f s k
  have stable:f C=C:=fixed_after f U ex cap k s hs enough
  have within (j:ℕ) : rounds (propagate e us) s j⊆C:=by
    induction j with
    | zero=>exact (grows k).1
    | succ j ih=>exact swept_within e U C stable.subset us (by simp [U]) _ ih
  have faster (j:ℕ) : rounds f s j⊆rounds (propagate e us) s j:=by
    induction j with
    | zero=>rfl
    | succ j ih=>
      intro u hu
      obtain ⟨allowed,h⟩:=(mem_advance ..).1 hu
      rcases h with seed|⟨z,hz,edge⟩
      · exact swept_ext e us _ (ih seed)
      · exact swept_hits e us (by simpa [U] using allowed) _ (ih hz) edge
  exact Finset.Subset.antisymm (within k) (faster k)

def passList (e:ℕ→ℕ→Bool) (us seen:List ℕ):=us.filter fun u=>seen.contains u || seen.any (fun z=>e z u)
theorem list_advance (e:ℕ→ℕ→Bool) (us seen:List ℕ) :
    (passList e us seen).toFinset=advance e us.toFinset seen.toFinset:=by
  classical ext u;simp [passList]
theorem ref_rounds (d:Instance) (us:List ℕ) (v k:ℕ) :
    ((List.range k).foldl (fun seen _=>passList d.edge us seen) [v]).toFinset =
      rounds (advance d.edge us.toFinset) {v} k:=by
  induction k with
  | zero=>simp [rounds]
  | succ k ih=>rw [List.range_succ,List.foldl_append];simp [rounds,list_advance,ih]
theorem restore_order (us:List ℕ) (p:ℕ→Bool) :
    us.filter (fun u=>decide (u∈(us.filter p).toFinset))=us.filter p:=by
  apply List.filter_congr
  intro u mem
  cases h:p u <;> simp [h,mem]

theorem ordered_component (d:Instance) (us:List ℕ) (v:ℕ) (hu:us.toFinset.card≤d.n) (hv:v∈us) (hn:0<d.n) :
    us.filter (fun u=>decide (u∈rounds (propagate d.edge us) {v} d.n))=TightLanguage.pieceAt d us v:=by
  classical
  have h:=synchronous_asynchronous d.edge us ({v}:Seen) d.n (by simpa using hv) (by simpa using (show us.toFinset.card≤1+d.n by omega))
  rw [h,←ref_rounds]
  obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : d.n≠0)
  unfold TightLanguage.pieceAt
  rw [hk,List.range_succ,List.foldl_append]
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
  change us.filter (fun u=>decide (u∈(passList d.edge us _).toFinset))=passList d.edge us _
  exact restore_order _ _
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration


namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration
open SingleCircuit TightLanguage
set_option autoImplicit false
set_option maxHeartbeats 1750000

def buckets {A:Type} (key:A→ℕ) (n:ℕ) (ls:List A) :=
  (List.range n).flatMap fun i=>ls.filter (fun a=>key a==i)

theorem buckets_count {A:Type} [DecidableEq A] (key:A→ℕ) (n:ℕ) (ls:List A) (a:A) :
    (buckets key n ls).count a=if key a<n then ls.count a else 0:=by
  induction n with
  | zero=>simp [buckets]
  | succ n ih=>
    have chunk: (ls.filter (fun a=>key a==n)).count a=if key a=n then ls.count a else 0:=by
      split
      · next eq=>apply List.count_filter;simpa using eq
      · next ne=>exact List.count_eq_zero_of_not_mem (by simp [ne])
    simp only [buckets,List.range_succ,List.flatMap_append,List.flatMap_singleton,List.count_append] at ih ⊢
    rw [ih,chunk]
    split_ifs <;> omega

theorem buckets_perm {A:Type} [DecidableEq A] (key:A→ℕ) (n:ℕ) (ls:List A) (bound:∀a∈ls,key a<n) :
    (buckets key n ls).Perm ls:=by
  apply List.perm_iff_count.mpr
  intro a
  rw [buckets_count]
  by_cases h:a∈ls
  · simp [bound _ h]
  · simp [List.count_eq_zero_of_not_mem h]

/-- Nonempty distinct partition blocks have distinct first indices. Scanning
their first indices emits exactly the lexicographically sorted lists. -/
theorem ordered_literals (n:ℕ) (rows:List (List ℕ))
    (bound:∀a∈rows,a.headD n<n)
    (unique:∀a∈rows,∀b∈rows,a.headD n=b.headD n → a=b) :
    (List.range n).flatMap (fun i=>rows.filter (fun a=>a.headD n==i))=
      rows.mergeSort (fun a b=>decide (a≤b)):=by
  let key:=fun a:List ℕ=>a.headD n
  let bs:=buckets key n rows
  have perm:bs.Perm rows:=buckets_perm key n rows bound
  have sorted:bs.Pairwise (·≤·):=by
    apply List.pairwise_flatMap.mpr
    constructor
    · intro i _
      apply List.Pairwise.imp_mem.mpr
      apply List.pairwise_of_forall
      intro a b ha hb
      have ax:=List.mem_filter.mp ha;have bx:=List.mem_filter.mp hb
      have eq:=unique a ax.1 b bx.1 ((beq_iff_eq.mp ax.2).trans (beq_iff_eq.mp bx.2).symm)
      exact eq.le
    · apply List.pairwise_lt_range.imp
      intro i j ij a ha b hb
      have ax:=List.mem_filter.mp ha;have bx:=List.mem_filter.mp hb
      have ai:a.headD n=i:=beq_iff_eq.mp ax.2
      have bj:b.headD n=j:=beq_iff_eq.mp bx.2
      have an:=bound a ax.1;have bn:=bound b bx.1
      cases a with
      | nil=>simp at an
      | cons a as=>
        cases b with
        | nil=>simp at bn
        | cons b bs=>
          change a=i at ai;change b=j at bj
          exact le_of_lt (List.cons_lt_cons_iff.mpr (Or.inl (by omega)))
  exact (perm.trans (List.mergeSort_perm _ _).symm).eq_of_pairwise' sorted (List.pairwise_mergeSort' _ _)

theorem separated_heads (n:ℕ) (rows:List (List ℕ)) (bound:∀a∈rows,a.headD n<n)
    (disjoint:∀a∈rows,∀b∈rows,a≠b → ∀q∈a,q∉b) :
    ∀a∈rows,∀b∈rows,a.headD n=b.headD n → a=b:=by
  intro a am b bm eq
  by_contra ne
  have ax:=bound a am;have bx:=bound b bm
  cases a with
  | nil=>simp at ax
  | cons a as=>
    cases b with
    | nil=>simp at bx
    | cons b bs=>
      change a=b at eq
      exact disjoint _ am _ bm ne a (by simp) (by simp [eq])

theorem fold_rounds {A:Type} (f:A→A) (s:A) (k:ℕ) :
    (List.range k).foldl (fun a _=>f a) s = rounds f s k :=by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [List.range_succ,List.foldl_append];simp [rounds,ih]
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration


open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
theorem solution :
    (∀(d:Instance) (xs:List ℕ) (v:ℕ),xs.toFinset.card≤d.n → v∈xs → 0<d.n →
      let mark:=fun (s:Finset ℕ) (u:ℕ)=>if ∃z∈s,d.edge z u=true then insert u s else s
      let out:=(List.range d.n).foldl (fun s _=>xs.foldl mark s) ({v}:Finset ℕ)
      xs.filter (fun u=>decide (u∈out))=TightLanguage.pieceAt d xs v) ∧
    ∀(n:ℕ) (rows:List (List ℕ)),(∀a∈rows,a.headD n<n) →
      (∀a∈rows,∀b∈rows,a≠b → ∀q∈a,q∉b) →
      (List.range n).flatMap (fun i=>rows.filter (fun a=>a.headD n==i))=
        rows.mergeSort (fun a b=>decide (a≤b)) := by
  constructor
  · intro d xs v cap seed pos
    change xs.filter (fun u=>decide (u∈(List.range d.n).foldl (fun s _=>propagate d.edge xs s) ({v}:Seen)))=_
    rw [fold_rounds]
    exact ordered_component d xs v cap seed pos
  · intro n rows bounded separate
    exact ordered_literals n rows bounded (separated_heads n rows bounded separate)
