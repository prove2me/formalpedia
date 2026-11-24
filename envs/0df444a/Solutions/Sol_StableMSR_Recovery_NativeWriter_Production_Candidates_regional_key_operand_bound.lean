-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.regional_key_operand_bound
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T23:47:49.85185+00:00
-- url     : https://prove2.me/submissions/a2db2b2f-85b1-4312-8df5-cbd2d13436ba

import Definitions.Def_StableMSR_UnfilteredSeparatorCandidates
set_option linter.all false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.KeyCode
open SingleCircuit
set_option autoImplicit false

def pairs (a:Assignment) := a.flatMap (fun q=>[q.1,q.2])
def digits (key:Key) := key.1.map Nat.succ ++ [0] ++ pairs key.2
end StableMSR.Recovery.NativeWriter.Production.Candidates.KeyCode
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.KeyCode
open OracleQueries SingleCircuit TightLanguage
set_option autoImplicit false
set_option maxHeartbeats 1400000

def VerticesOK (n:ℕ) (c:List ℕ) := c.length≤n ∧ ∀v∈c,v<n
def LabelsOK (n K:ℕ) (a:Assignment) := ∀p∈a,p.1<n ∧ p.2<K
def Good (n K:ℕ) (key:Key) := VerticesOK n key.1 ∧ key.2.length≤n ∧ LabelsOK n K key.2
def Named (enc:Key→ℕ) (n K:ℕ) (op:Candidates.Instr) : Prop :=
  match op with | .need id | .seal id=>∃key,enc key=id ∧ Good n K key | _=>True

theorem VerticesOK.filter {n:ℕ} {c:List ℕ} (ok:VerticesOK n c) (f:ℕ→Bool) :
    VerticesOK n (c.filter f):=⟨(List.length_filter_le ..).trans ok.1,fun v h=>ok.2 v (List.mem_filter.mp h).1⟩
theorem VerticesOK.erase {n:ℕ} {c:List ℕ} (ok:VerticesOK n c) (v:ℕ) :
    VerticesOK n (c.erase v):=⟨(List.length_erase_le ..).trans ok.1,fun z h=>ok.2 z (List.mem_of_mem_erase h)⟩
theorem vertices_ok (d:Instance) : VerticesOK d.n (vertices d) :=
  VerticesOK.filter (c:=List.range d.n) ⟨by simp,fun _ h=>List.mem_range.mp h⟩ _
theorem rim_ok (d:Instance) (c:List ℕ) : VerticesOK d.n (rimOf d c) := (vertices_ok d).filter _
theorem part_ok (d:Instance) (c:List ℕ) (ok:VerticesOK d.n c) (t:List ℕ) (ht:t∈parts d c) : VerticesOK d.n t:=by
  obtain ⟨v,hv,eq⟩:=List.mem_filterMap.mp ht
  dsimp only at eq;split at eq
  · simp only [Option.some.injEq] at eq;subst t
    unfold pieceAt
    apply List.foldlRecOn (motive:=VerticesOK d.n)
    · exact ⟨by have:=ok.2 v hv;simp;omega,by simpa using ok.2 v hv⟩
    · intro _ _ _ _;exact ok.filter _
  · simp at eq

theorem assigned_ok (d:Instance) (K:ℕ) (labels:∀v x,x∈d.menu v → x<K)
    (s:List ℕ) (a:Assignment) (av:a∈assignments d s) (vs:∀v∈s,v<d.n) :
    a.length=s.length ∧ LabelsOK d.n K a := by
  induction s generalizing a with
  | nil=>simp [assignments] at av;subst a;simp [LabelsOK]
  | cons v s ih=>
    obtain ⟨x,hx,h⟩:=List.mem_flatMap.mp av
    obtain ⟨a',ha,rfl⟩:=List.mem_map.mp h
    obtain ⟨len,valid⟩:=ih a' ha (fun t ht=>vs t (by simp [ht]))
    refine ⟨by simpa using len,?_⟩
    intro p hp;rcases List.mem_cons.mp hp with eq|inside
    · subst p;exact ⟨vs v (by simp),labels v x hx⟩
    · exact valid p inside

theorem restrict_ok {n K:ℕ} (s:List ℕ) (hs:VerticesOK n s) (a:Assignment) (hk:0<K) (va:LabelsOK n K a) :
    (restricted s a).length≤n ∧ LabelsOK n K (restricted s a) := by
  refine ⟨by simpa [restricted] using hs.1,?_⟩
  intro p hp;obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hp
  refine ⟨hs.2 v hv,?_⟩
  unfold value
  cases h:a.find? (fun z=>z.1==v) with
  | none=>exact hk
  | some q=>exact (va q (List.mem_of_find?_eq_some h)).2

theorem named_tape (enc:Key→ℕ) (d:Instance) (w K:ℕ) (hk:0<K) (labels:∀v x,x∈d.menu v → x<K) :
    ∀op∈tape enc d w,Named enc d.n K op := by
  have tr (c:List ℕ) (a:Assignment) (v x:ℕ) (hc:VerticesOK d.n c) (av:LabelsOK d.n K a)
      (vin:v∈c) (xin:x∈d.menu v) : ∀op∈trial enc d c a v x,Named enc d.n K op:=by
    have row:LabelsOK d.n K ((v,x)::a):=by
      intro p hp;rcases List.mem_cons.mp hp with eq|old
      · subst p;exact ⟨hc.2 v vin,labels v x xin⟩
      · exact av _ old
    intro op h
    simp only [trial,List.mem_append,List.mem_map,List.mem_singleton] at h
    rcases h with ((⟨_,_,rfl⟩|⟨k,mem,rfl⟩)|rfl)
    · trivial
    · obtain ⟨t,ht,rfl⟩:=List.mem_map.mp mem
      exact ⟨_,rfl,part_ok d _ (hc.erase v) t ht,restrict_ok _ (rim_ok d t) _ hk row⟩
    · trivial
  have ent (c:List ℕ) (a:Assignment) (g:Good d.n K (c,a)) : ∀op∈entry enc d c a,Named enc d.n K op:=by
    intro op h;rcases List.mem_append.mp h with inRow|last
    · obtain ⟨v,hv,hm⟩:=List.mem_flatMap.mp inRow
      obtain ⟨x,hx,hc⟩:=List.mem_flatMap.mp hm
      exact tr c a v x g.1 g.2.2 hv hx _ hc
    · obtain rfl:=List.mem_singleton.mp last;exact ⟨_,rfl,g⟩
  have visit (k:ℕ) (s c:List ℕ) (hc:VerticesOK d.n c) : ∀op∈visitTape enc d k s c,Named enc d.n K op:=by
    intro op h;unfold visitTape at h;split at h
    · next test=>
      have eq:rimOf d c=s:=(by simpa only [Bool.and_eq_true,beq_iff_eq] using test : c.length=k+1 ∧ rimOf d c=s).2
      have vs:VerticesOK d.n s:=eq ▸ rim_ok d c
      obtain ⟨a,ha,inside⟩:=List.mem_flatMap.mp h
      obtain ⟨len,good⟩:=assigned_ok d K labels s a ha vs.2
      exact ent c a ⟨hc,len ▸ vs.1,good⟩ op inside
    · simp at h
  intro op mem
  rcases List.mem_append.mp mem with rows|last
  · rcases List.mem_append.mp rows with table|roots
    · obtain ⟨k,hk',hs⟩:=List.mem_flatMap.mp table
      obtain ⟨s,_,hc⟩:=List.mem_flatMap.mp hs
      obtain ⟨c,cm,inside⟩:=List.mem_flatMap.mp hc
      exact visit k s c (part_ok d _ ((vertices_ok d).filter _) c cm) _ inside
    · obtain ⟨c,hc,rfl⟩:=List.mem_map.mp roots
      exact ⟨_,rfl,part_ok d _ (vertices_ok d) c hc,by simp,by simp [LabelsOK]⟩
  · obtain rfl:=List.mem_singleton.mp last;trivial

end StableMSR.Recovery.NativeWriter.Production.Candidates.KeyCode
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.KeyCode
open OracleQueries SingleCircuit TightLanguage
open scoped Classical
set_option autoImplicit false

theorem digit_budget {n K:ℕ} (key:Key) (g:Good n K key) :
    (digits key).length≤3*n+1 ∧ (digits key).sum≤n*(2*n+K) := by
  have cs (c:List ℕ) (vs:∀v∈c,v<n) : (c.map Nat.succ).sum≤c.length*n:=by
    induction c with
    | nil=>simp
    | cons v c ih=>
      have h:=ih (fun t ht=>vs t (by simp [ht]))
      have v0:=vs v (by simp)
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul];omega
  have ps (a:Assignment) (lb:LabelsOK n K a) :
      (pairs a).length=2*a.length ∧ (pairs a).sum≤a.length*(n+K):=by
    induction a with
    | nil=>simp [pairs]
    | cons v a ih=>
      obtain ⟨len,sz⟩:=ih (fun q h=>lb q (by simp [h]))
      obtain ⟨v0,v1⟩:=lb v (by simp)
      change ((v.1::v.2::pairs a).length=_) ∧ ((v.1::v.2::pairs a).sum≤_)
      simp only [List.length_cons,List.sum_cons,len,Nat.add_mul,Nat.one_mul];omega
  obtain ⟨len,sz⟩:=ps key.2 g.2.2
  have a: (key.1.map Nat.succ).sum≤n*n:=(cs key.1 g.1.2).trans (Nat.mul_le_mul_right n g.1.1)
  have b:(pairs key.2).sum≤n*(n+K):=sz.trans (Nat.mul_le_mul_right _ g.2.1)
  have l:=g.1.1;have r:=g.2.1
  simp only [digits,List.length_append,List.length_map,List.length_singleton,List.sum_append,List.sum_singleton,Nat.add_zero,len]
  exact ⟨by omega,by nlinarith⟩

theorem menu_values (x:World) (W:Cluster x.n) (R:ℝ) (h:ℕ) :
    ∀v a,a∈(SingleCodes.instanceOf x W R h).menu v → a<(h+1)*x.n^(2*(h+1)) := by
  intro v a mem
  simp only [SingleCodes.instanceOf,SingleCodes.lookup] at mem
  split at mem
  · have hw: a∈SingleCodes.words x.n h:=(List.mem_filter.mp mem).1
    obtain ⟨g,gg,more⟩:=List.mem_flatMap.mp hw
    obtain ⟨u,uu,rfl⟩:=List.mem_map.mp more
    have hg:=List.mem_range.mp gg
    have hu:=List.mem_range.mp uu
    change u<x.n^(2*(h+1)) at hu
    have b:=Nat.mul_le_mul_right (h+1) (Nat.succ_le_of_lt hu)
    change u*(h+1)+g<(h+1)*_;rw [Nat.succ_mul,Nat.mul_comm (x.n^_) (h+1)] at b;omega
  · simp at mem

theorem scene_key_bound (x:World) (W:Cluster x.n) (R:ℝ) (h w:ℕ) (enc:Key→ℕ) (hn:1≤x.n) (op:Candidates.Instr)
    (mem:op∈tape enc (SingleCodes.instanceOf x W R h) w) (id:ℕ) (use:op=.need id ∨ op=.seal id) :
    ∃key:Key,enc key=id ∧ (digits key).length≤3*x.n+1 ∧ (digits key).sum≤x.n*(2*x.n+(h+1)*x.n^(2*(h+1))) := by
  let K:=(h+1)*x.n^(2*(h+1))
  have hk:0<K:=Nat.mul_pos (by omega) (Nat.pow_pos hn)
  have hit:=named_tape enc _ w K hk (menu_values x W R h) op mem
  have obtainKey:∃key,enc key=id ∧ Good x.n K key:=by rcases use with rfl|rfl <;> exact hit
  obtain ⟨key,eq,good⟩:=obtainKey
  exact ⟨key,eq,digit_budget key good⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.KeyCode
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates
theorem solution
    (x:World) (W:Cluster x.n) (R:ℝ) (h w:ℕ) (enc:Key→ℕ) (hn:1≤x.n) (op:Candidates.Instr)
    (mem:op∈tape enc (SingleCodes.instanceOf x W R h) w) (id:ℕ)
    (use:op=.need id ∨ op=.seal id) :
    ∃key:Key,enc key=id ∧
      let ds:=key.1.map Nat.succ ++ [0] ++ key.2.flatMap (fun q=>[q.1,q.2])
      ds.length≤3*x.n+1 ∧ ds.sum≤x.n*(2*x.n+(h+1)*x.n^(2*(h+1))) := StableMSR.Recovery.NativeWriter.Production.Candidates.KeyCode.scene_key_bound x W R h w enc hn op mem id use
