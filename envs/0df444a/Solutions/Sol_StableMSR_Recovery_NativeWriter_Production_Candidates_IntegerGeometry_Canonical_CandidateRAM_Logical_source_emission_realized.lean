-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.source_emission_realized
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T02:18:07.596307+00:00
-- url     : https://prove2.me/submissions/0650e1ca-7cc8-4508-8438-a18bda91c0fa

import Definitions.Def_StableMSR_LogicalCandidateProgram
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000

inductive Steps : Code→Banks→Banks→ℕ→Prop where
  | skip (s:Banks) : Steps .skip s s 1
  | atom (o:IOp) (s:Banks) : Steps (.atom o) s (o.act s) 1
  | seq {p q s t u i j} : Steps p s t i → Steps q t u j → Steps (.seq p q) s u (1+i+j)
  | yes {a b p q s t i} : s.reg a ≤ s.reg b → Steps p s t i → Steps (.cond a b p q) s t (1+i)
  | no {a b p q s t i} : ¬s.reg a ≤ s.reg b → Steps q s t i → Steps (.cond a b p q) s t (1+i)
  | stop {a b p s} : ¬s.reg a ≤ s.reg b → Steps (.loop a b p) s s 1
  | more {a b p s t u i j} : s.reg a ≤ s.reg b → Steps p s t i → Steps (.loop a b p) t u j →
      Steps (.loop a b p) s u (1+i+j)
theorem Steps.schedule {p:Code} {s t:Banks} {k:ℕ} (ex:Steps p s t k) (ks:List Code) (F:ℕ) :
    run (k+F) (p::ks) s=run F ks t:=by
  induction ex generalizing ks F with
  | skip|atom=>simp [Nat.add_comm 1,run]
  | seq first second ih jh=>
    rename_i p q s t u i j
    rw [show 1+i+j+F=(i+(j+F))+1 by omega,run,ih,jh]
  | yes flag first ih=>
    rename_i a b p q s t i
    rw [show 1+i+F=(i+F)+1 by omega,run,if_pos flag,ih]
  | no flag first ih=>
    rename_i a b p q s t i
    rw [show 1+i+F=(i+F)+1 by omega,run,if_neg flag,ih]
  | stop flag=>rw [show 1+F=F+1 by omega,run,if_neg flag]
  | more flag first again ih jh=>
    rename_i a b p s t u i j
    rw [show 1+i+j+F=(i+(j+F))+1 by omega,run,if_pos flag,ih,jh]

def straight : Code→Bool
  | .skip|.atom _=>true | .seq p q=>straight p && straight q | _=>false
def weight : Code→ℕ | .seq p q=>1+weight p+weight q | _=>1
def action : Code→Banks→Banks
  | .skip,s=>s | .atom o,s=>o.act s | .seq p q,s=>action q (action p s) | _,s=>s
theorem straight_steps (p:Code) (s:Banks) (ok:straight p=true) : Steps p s (action p s) (weight p):=by
  induction p generalizing s with
  | skip=>exact .skip _
  | atom o=>exact .atom _ _
  | seq p q ih jh=>
    obtain ⟨a,b⟩:=Bool.and_eq_true_iff.mp ok
    exact .seq (ih _ a) (jh _ b)
  | cond|loop=>contradiction
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2000000
def costPrefix : List Code→ℕ
  | []=>0 | p::xs=>1+weight p+costPrefix xs
def actPrefix : List Code→Banks→Banks
  | [],s=>s | p::xs,s=>actPrefix xs (action p s)
theorem prepend_steps (xs ys:List Code) (s t:Banks) (z:ℕ) (simple:∀p∈xs,straight p=true)
    (tail:Steps (seqs ys) (actPrefix xs s) t z) :
    Steps (seqs (xs++ys)) s t (costPrefix xs+z):=by
  induction xs generalizing s with
  | nil=>simpa [costPrefix,actPrefix] using tail
  | cons p xs ih=>
    obtain ⟨a,b⟩:=List.forall_mem_cons.mp simple
    have h:=Steps.seq (straight_steps p s a) (ih (action p s) b tail)
    simpa only [List.cons_append,seqs,List.foldr_cons,costPrefix,Nat.add_assoc] using h

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 1400000

def multiplyBody (dst a:ℕ):=seqs [add dst dst a,dec 10]
theorem add_loop (dst a A K prev:ℕ) (s:Banks) (hd:64≤dst) (ha:64≤a) (ne:a≠dst)
    (one:s.reg 6=1) (src:s.reg a=(A:ℤ)) (cnt:s.reg 10=(K:ℤ)) (acc:s.reg dst=(prev:ℤ)) :
    ∃t z,Steps (.loop 6 10 (multiplyBody dst a)) s t z ∧ z≤1+6*K ∧
      t.reg dst=((prev+K*A:ℕ):ℤ) ∧ t.mem=s.mem ∧ ∀j,j≠10 → j≠dst → t.reg j=s.reg j:=by
  induction K generalizing s prev with
  | zero=>
    have no:¬s.reg 6 ≤ s.reg 10:=by rw [one,cnt];decide
    exact ⟨s,_,.stop no,by omega,by simpa using acc,rfl,by simp⟩
  | succ k ih=>
    have yes:s.reg 6 ≤ s.reg 10:=by rw [one,cnt];simp
    let u:=action (multiplyBody dst a) s
    have ex:Steps (multiplyBody dst a) s u 5:=straight_steps _ _ rfl
    have keep (j:ℕ) (n:j≠10) (p:j≠dst) : u.reg j=s.reg j:=by
      simp [u,multiplyBody,seqs,action,add,dec,IOp.act,Banks.put,Function.update_apply,n,p]
    have counter:u.reg 10=(k:ℤ):=by
      simp [u,multiplyBody,seqs,action,add,dec,IOp.act,Banks.put,Function.update_apply,show 10≠dst by omega,cnt]
    have sum:u.reg dst=((prev+A:ℕ):ℤ):=by
      simp [u,multiplyBody,seqs,action,add,dec,IOp.act,Banks.put,Function.update_apply,show dst≠10 by omega,acc,src]
    obtain ⟨t,z,rec,tm,val,mem,fr⟩:=ih (prev+A) u
      ((keep _ (by omega) (by omega)).trans one) ((keep _ (by omega) ne).trans src) counter sum
    refine ⟨t,_,.more yes ex rec,by omega,?_,mem,?_⟩
    · rw [val];push_cast;ring
    · intro j n p;exact (fr _ n p).trans (keep _ n p)

theorem multiply_run (dst a b A B:ℕ) (s:Banks) (hd:64≤dst) (ha:64≤a) (hb:64≤b) (ne:a≠dst)
    (one:s.reg 6=1) (left:s.reg a=(A:ℤ)) (right:s.reg b=(B:ℤ)) :
    ∃t k,Steps (mul dst a b) s t k ∧ k≤8+6*B ∧
      t.reg dst=((A*B:ℕ):ℤ) ∧ t.mem=s.mem ∧ ∀j,j≠10 → j≠dst → t.reg j=s.reg j:=by
  let u:=(IOp.set dst 0).act ((IOp.copy 10 b).act s)
  have keep (j:ℕ) (n:j≠10) (p:j≠dst):u.reg j=s.reg j:=by
    simp [u,IOp.act,Banks.put,Function.update_apply,n,p]
  have ten:u.reg 10=(B:ℤ):=by simp [u,IOp.act,Banks.put,Function.update_apply,show 10≠dst by omega,right]
  have zero:u.reg dst=0:=by simp [u,IOp.act,Banks.put]
  obtain ⟨t,z,loop,tm,v,mem,fr⟩:=add_loop dst a A B 0 u hd ha ne
    ((keep _ (by omega) (by omega)).trans one) ((keep _ (by omega) ne).trans left) ten zero
  have ex:Steps (mul dst a b) s t _:=.seq (.atom _ _) (.seq (.atom _ _) (.seq loop (.skip _)))
  refine ⟨t,_,ex,by omega,by simpa [Nat.mul_comm] using v,mem,?_⟩
  intro j n p;exact (fr _ n p).trans (keep _ n p)
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 3700000
set_option maxRecDepth 32000

def headerOps : List Code:=[
  setc 864 0,setc 865 79,sub 863 864 865,setc 866 64,sub 862 863 866,
  lshift 867 82 9,sub 861 862 867,st 861 218,setc 874 0,setc 875 79,
  sub 873 874 875,setc 876 128,sub 872 873 876,lshift 877 82 9,
  sub 871 872 877,st 871 219,setc 882 0]

theorem header_time : costPrefix headerOps≤140:=by decide
def outside (j:ℕ) : Code→Bool
  | .skip=>true | .seq a b=>outside j a && outside j b
  | .atom (.store _ _)=>true
  | .atom (.set d _)|.atom (.copy d _)|.atom (.inc d)|.atom (.dec d)|
    .atom (.add d _ _)|.atom (.sub d _ _)|.atom (.load d _)=>decide (j≠d)
  | _=>false
theorem outside_keeps (j:ℕ) (p:Code) (s:Banks) (h:outside j p=true) : (action p s).reg j=s.reg j:=by
  induction p generalizing s with
  | skip=>rfl
  | atom o=>cases o <;> simp [outside] at h <;> simp [action,IOp.act,Banks.write,Banks.put,h]
  | seq a b ih jh=>
    obtain ⟨x,y⟩:=Bool.and_eq_true_iff.mp h
    exact (jh _ y).trans (ih _ x)
  | cond|loop=>contradiction
theorem prefix_keep (j:ℕ) (s:Banks) (xs:List Code) (h:xs.all (outside j)=true) :
    (actPrefix xs s).reg j=s.reg j:=by
  induction xs generalizing s with
  | nil=>rfl
  | cons a xs ih=>
    simp only [List.all_cons,Bool.and_eq_true] at h
    obtain ⟨x,y⟩:=h
    exact (ih _ y).trans (outside_keeps j a s x)
theorem header_frame (s:Banks) (j:ℕ) (lo:j<861): (actPrefix headerOps s).reg j=s.reg j:=by
  apply prefix_keep
  simp [headerOps,outside,setc,sub,lshift,seqs,cp,add,st]
  omega
theorem header_memory (s:Banks) (i:ℕ) (index:s.reg 82=(i:ℤ)) :
    (actPrefix headerOps s).mem=Function.update (Function.update s.mem (inputCell 1 i) (s.reg 218))
      (inputCell 2 i) (s.reg 219):=by
  let off:=fun a:ℤ=> -79-a-512*(i:ℤ)
  have first:inputCell 1 i=off 64:=by simp [inputCell,cell,word,off];ring
  have second:inputCell 2 i=off 128:=by simp [inputCell,cell,word,off];ring
  rw [first,second]
  simp [headerOps,actPrefix,action,seqs,lshift,setc,cp,sub,add,st,IOp.act,Banks.put,Banks.write,index,off]
  congr 2 <;> ring

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

theorem put_same (s:Banks) (j:ℕ) (a b:ℤ) : (s.put j a).put j b=s.put j b:=by
  cases s
  simp [Banks.put,Function.update_idem]
theorem copy_doublings (j:ℕ) (s:Banks) (k:ℕ) (v:ℤ) :
    action (seqs (List.replicate k (add j j j))) (s.put j v)=s.put j ((2:ℤ)^k*v):=by
  induction k generalizing v with
  | zero=>simp [seqs,action]
  | succ k ih=>
    simp only [List.replicate_succ,seqs,List.foldr_cons,action,add,IOp.act]
    change action (seqs (List.replicate k (add j j j))) ((s.put j v).put j (_+_))=_
    simp only [Banks.put,Function.update_self] at *
    rw [Function.update_idem]
    convert ih (v+v) using 2 <;> rw [pow_succ] <;> ring
theorem shift_action (s:Banks) (dst src k:ℕ):
    action (lshift dst src k) s=s.put dst ((2:ℤ)^k*s.reg src):=by
  exact copy_doublings dst s k (s.reg src)
def keepsReg (j:ℕ) : Code→Bool
  | .skip=>true | .seq a b|.cond _ _ a b=>keepsReg j a && keepsReg j b
  | .loop _ _ p=>keepsReg j p
  | .atom (.store _ _)=>true
  | .atom (.set d _)|.atom (.copy d _)|.atom (.inc d)|.atom (.dec d)|
    .atom (.add d _ _)|.atom (.sub d _ _)|.atom (.load d _)=>decide (j≠d)
theorem Steps.reg_kept {p:Code} {s t:Banks} {k:ℕ} (ex:Steps p s t k) (j:ℕ) (h:keepsReg j p=true) :
    t.reg j=s.reg j:=by
  induction ex with
  | skip|stop=>rfl
  | atom o s=>cases o <;> simp [keepsReg] at h <;> simp [IOp.act,Banks.write,Banks.put,h]
  | seq _ _ ih jh|more _ _ _ ih jh=>
    first | exact (jh (Bool.and_eq_true_iff.mp h).2).trans (ih (Bool.and_eq_true_iff.mp h).1)
          | exact (jh h).trans (ih h)
  | yes _ _ ih=>exact ih (Bool.and_eq_true_iff.mp h).1
  | no _ _ ih=>exact ih (Bool.and_eq_true_iff.mp h).2

/-- An indexed loop visits 0 through n-1. A uniform bound on one body
execution gives the bound on all instructions and loop guards. -/
theorem bounded_loop (ix last n cap:ℕ) (body:Code) (P:ℕ→Banks→Prop) (ne:ix≠last)
    (step:∀i<n,∀s:Banks,P i s → s.reg ix=(i:ℤ) → s.reg last=(n:ℤ)-1 →
      ∃t k,Steps body s t k ∧ k≤cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) ((IOp.inc ix).act t))
    (i rem:ℕ) (len:i+rem=n) (s:Banks) (start:P i s) (idx:s.reg ix=(i:ℤ)) (lim:s.reg last=(n:ℤ)-1) :
    ∃t k,Steps (.loop ix last (seqs [body,inc ix])) s t k ∧ k≤1+rem*(cap+5) ∧ P n t :=by
  induction rem generalizing i s with
  | zero=>
    have eq:i=n:=by omega
    exact ⟨s,1,.stop (by rw [idx,lim];omega),by omega,eq ▸ start⟩
  | succ r ih=>
    have lt:i<n:=by omega
    obtain ⟨u,k,ex,tim,idx',lim',next⟩:=step i lt s start idx lim
    let v:=(IOp.inc ix).act u
    have vi:v.reg ix=((i+1:ℕ):ℤ):=by simp [v,IOp.act,Banks.put,idx',idx]
    have vl:v.reg last=(n:ℤ)-1:=by simp [v,IOp.act,Banks.put,Ne.symm ne,lim',lim]
    obtain ⟨t,z,more,tm,out⟩:=ih (i+1) (by omega) v next vi vl
    have full:Steps (seqs [body,inc ix]) s v (1+k+(1+1+1)):=.seq ex (.seq (.atom _ _) (.skip _))
    exact ⟨t,_,.more (by rw [idx,lim];omega) full more,by rw [Nat.succ_mul];omega,out⟩

def setupFor (ix last len:ℕ) (s:Banks) := (IOp.dec last).act ((IOp.copy last len).act ((IOp.set ix 0).act s))
theorem for_run (ix last len n cap:ℕ) (body:Code) (P:ℕ→Banks→Prop)
    (ne:ix≠last) (dis:len≠ix) (s:Banks) (size:s.reg len=(n:ℤ))
    (start:P 0 (setupFor ix last len s))
    (step:∀i<n,∀s:Banks,P i s → s.reg ix=(i:ℤ) → s.reg last=(n:ℤ)-1 →
      ∃t k,Steps body s t k ∧ k≤cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) ((IOp.inc ix).act t)) :
    ∃t k,Steps (forN ix last len body) s t k ∧ k≤9+n*(cap+5) ∧ P n t :=by
  let u:=setupFor ix last len s
  have fi:u.reg ix=0:=by simp [u,setupFor,IOp.act,Banks.put,ne]
  have last':u.reg last=(n:ℤ)-1:=by simp [u,setupFor,IOp.act,Banks.put,dis,size]
  obtain ⟨t,z,loop,tm,out⟩:=bounded_loop ix last n cap body P ne step 0 n (by omega) u start fi last'
  refine ⟨t,_,.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.seq loop (.skip _)))),by omega,out⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

def bitPre : List Code:=[setc 889 0,setc 890 79,sub 888 889 890,setc 891 192,sub 887 888 891]
def bitTail:List Code:=[add 893 894 221,lshift 892 893 9,sub 886 887 892,
  readCell 898 220 221,st 886 898]
def bitBody:Code:=seqs (bitPre ++ mul 894 82 64 :: bitTail)
def tagTest := Code.cond 218 882 (.cond 882 218 (setc 880 1) (setc 880 0)) (setc 880 0)
def bitCopy := forN 221 884 64 bitBody
def bumpOutput := [setc 903 1,add 901 82 903,cp 82 901]

theorem bitPrefixReg (s:Banks) (j:ℕ) (h:j<887) : (actPrefix bitPre s).reg j=s.reg j:=by
  apply prefix_keep
  simp [bitPre,outside,setc,sub];omega
theorem bitTail_effect (t:Banks) (n row base i:ℕ) (h887:t.reg 887= -271)
    (prod:t.reg 894=((row*n:ℕ):ℤ)) (idx:t.reg 221=(i:ℤ)) (ptr:t.reg 220=(base:ℤ)) :
    (action (seqs bitTail) t).mem=
      Function.update t.mem (inputCell 3 (row*n+i)) (t.mem (cell 7 (base+i))):=by
  have a:inputCell 3 (row*n+i) = -271-512*((row:ℤ)*n+i):=by simp [inputCell,cell,word];ring
  have b:cell 7 (base+i) = -95-64*((base:ℤ)+i):=by simp [cell,word];ring
  rw [a,b]
  simp [bitTail,action,seqs,shift_action,addr,readCell,setc,add,sub,ld,st,IOp.act,Banks.put,Banks.write,h887,prod,idx,ptr]

theorem write_one (s:Banks) (n row base i:ℕ) (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ))
    (ord:s.reg 82=(row:ℤ)) (ptr:s.reg 220=(base:ℤ)) (idx:s.reg 221=(i:ℤ)) :
    ∃t k,Steps bitBody s t k ∧ k≤160+6*n ∧
      t.mem=Function.update s.mem (inputCell 3 (row*n+i)) (s.mem (cell 7 (base+i))) :=by
  let u:=actPrefix bitPre s
  obtain ⟨t,k,mulRun,tm,res,mem,regs⟩:=multiply_run 894 82 64 row n u
    (by decide) (by decide) (by decide) (by decide)
    ((bitPrefixReg s 6 (by decide)).trans one) ((bitPrefixReg s 82 (by decide)).trans ord) ((bitPrefixReg s 64 (by decide)).trans sz)
  let v:=action (seqs bitTail) t
  have tail:Steps (seqs bitTail) t v (weight (seqs bitTail)):=straight_steps _ _ (by decide)
  have both:=prepend_steps bitPre (mul 894 82 64::bitTail) s _ _ (by decide) (Steps.seq mulRun tail)
  have small:costPrefix bitPre+weight (seqs bitTail)≤149:=by decide
  have off:t.reg 887= -271:=(regs _ (by decide) (by decide)).trans rfl
  have mem':t.mem=s.mem:=mem
  refine ⟨v,_,both,by omega,?_⟩
  have idx':t.reg 221=(i:ℤ):=(regs _ (by decide) (by decide)).trans ((bitPrefixReg _ _ (by decide)).trans idx)
  have ptr':t.reg 220=(base:ℤ):=(regs _ (by decide) (by decide)).trans ((bitPrefixReg _ _ (by decide)).trans ptr)
  exact (bitTail_effect t n row base i off res idx' ptr').trans (by rw [mem'])

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

theorem input_injective {a b i j:ℕ} (ha:a<8) (hb:b<8) :
    inputCell a i=inputCell b j ↔ a=b ∧ i=j:=by
  unfold inputCell cell word;push_cast
  constructor
  · intro h;constructor <;> omega
  · rintro ⟨rfl,rfl⟩;rfl
theorem scratch_ne_input (b a j:ℕ) : cell 7 b≠inputCell a j:=by
  unfold inputCell cell word;push_cast;omega
def tapeAddress (q:ℤ) : Prop := ∃i:ℕ,q=cell 5 i
def scratchAddress (q:ℤ) : Prop := ∃i:ℕ,q=cell 7 i
theorem scratch_not_tape {q:ℤ} (h:scratchAddress q) : ¬tapeAddress q:=by
  rintro ⟨i,rfl⟩
  obtain ⟨j,e⟩:=h
  unfold cell word at e;push_cast at e;omega
theorem input_is_tape (a j:ℕ) : tapeAddress (inputCell a j):=⟨8*j+a,rfl⟩

/-- Exactly the portion of one physical record that the output routine owns. -/
def recordAddress (n row:ℕ) (tag:ℤ) (q:ℤ) :=
  q=inputCell 1 row ∨ q=inputCell 2 row ∨ (tag=0 ∧ ∃j<n,q=inputCell 3 (row*n+j))
theorem record_is_tape {n row:ℕ} {tag q:ℤ} (h:recordAddress n row tag q) : tapeAddress q:=by
  rcases h with rfl|rfl|⟨_,j,_,rfl⟩ <;> apply input_is_tape

def fieldsAt (n row:ℕ) (m:ℤ→ℤ) (e:Instr) :=
  m (inputCell 1 row)=e.tag ∧ m (inputCell 2 row)=e.arg ∧
  ∀mask,e=.lit mask → ∀j<n,m (inputCell 3 (row*n+j))=(if mask.contains j then 1 else 0)
def prefixAt (n:ℕ) (m:ℤ→ℤ) (xs:List Instr) :=
  ∀j (hj:j<xs.length),fieldsAt n j m xs[j]

theorem oldFields (n r j:ℕ) (old:j<r) (e:Instr) (tag:ℤ) (m m':ℤ→ℤ)
    (h:fieldsAt n j m e) (frame:∀q,¬recordAddress n r tag q → m' q=m q) : fieldsAt n j m' e:=by
  obtain ⟨ht,ha,hm⟩:=h
  have scalar (l:ℕ) (hl:l=1 ∨ l=2) : ¬recordAddress n r tag (inputCell l j):=by
    rcases hl with rfl|rfl <;> rintro (eq|eq|⟨_,k,_,eq⟩) <;>
      have t:=(input_injective (by decide) (by decide)).1 eq <;> omega
  refine ⟨(frame _ (scalar 1 (by simp))).trans ht,(frame _ (scalar 2 (by simp))).trans ha,?_⟩
  intro mask eq k hk
  apply (frame _ ?_).trans (hm mask eq k hk)
  rintro (eq|eq|⟨_,v,hv,eq⟩) <;> have t:=(input_injective (by decide) (by decide)).1 eq
  · omega
  · omega
  · have le: (j+1)*n≤r*n:=Nat.mul_le_mul_right _ old
    rw [Nat.succ_mul] at le;omega

theorem prefix_snoc (n:ℕ) (xs:List Instr) (e:Instr) (m m':ℤ→ℤ)
    (before:prefixAt n m xs) (new:fieldsAt n xs.length m' e)
    (frame:∀q,¬recordAddress n xs.length e.tag q → m' q=m q) : prefixAt n m' (xs++[e]):=by
  intro j hj
  by_cases h:j<xs.length
  · rw [List.getElem_append_left h]
    exact oldFields n xs.length j h _ _ m m' (before j h) frame
  · have eq:j=xs.length:=by simp at hj;omega
    subst j;simpa using new

theorem prefix_unchanged (n:ℕ) (xs:List Instr) (m m':ℤ→ℤ) (before:prefixAt n m xs)
    (same:∀q,tapeAddress q → m' q=m q) : prefixAt n m' xs:=by
  intro j hj
  obtain ⟨h,a,b⟩:=before j hj
  refine ⟨(same _ (input_is_tape ..)).trans h,(same _ (input_is_tape ..)).trans a,?_⟩
  intro mask eq k hk;exact (same _ (input_is_tape ..)).trans (b mask eq k hk)

theorem header_closes (n:ℕ) (xs:List Instr) (m:ℤ→ℤ) (before:prefixAt n m xs):
    Input n (Function.update m (inputCell 0 0) (xs.length:ℤ)) xs:=by
  refine ⟨Function.update_self ..,?_⟩
  intro j hj
  obtain ⟨h,a,b⟩:=before j hj
  have nonzero (l k:ℕ) (hl:l<8) (nz:l≠0) : inputCell l k≠inputCell 0 0:=
    fun eq=>nz ((input_injective hl (by decide)).1 eq).1
  refine ⟨(Function.update_of_ne (nonzero 1 j (by decide) (by decide)) ..).trans h,
    (Function.update_of_ne (nonzero 2 j (by decide) (by decide)) ..).trans a,?_⟩
  intro mask eq k hk
  exact (Function.update_of_ne (nonzero 3 _ (by decide) (by decide)) ..).trans (b mask eq k hk)

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

def copied (m:ℤ→ℤ) (base row n k:ℕ) (t:Banks):=
  (∀j<k,t.mem (inputCell 3 (row*n+j))=m (cell 7 (base+j))) ∧
  ∀q,(∀j<k,q≠inputCell 3 (row*n+j)) → t.mem q=m q
theorem copy_advance (m:ℤ→ℤ) (base row n i:ℕ) (s t:Banks) (h:copied m base row n i s)
    (upd:t.mem=Function.update s.mem (inputCell 3 (row*n+i)) (s.mem (cell 7 (base+i)))) :
    copied m base row n (i+1) t:=by
  obtain ⟨data,frame⟩:=h
  constructor
  · intro j hj
    rw [upd]
    by_cases eq:j=i
    · subst j;rw [Function.update_self];exact frame _ (fun k _=>scratch_ne_input (base+i) 3 (row*n+k))
    · rw [Function.update_of_ne]
      · exact data j (by omega)
      · intro h;have e:=(input_injective (by decide) (by decide)).1 h;omega
  · intro q outside
    rw [upd,Function.update_of_ne (outside i (by omega))]
    exact frame _ (fun j hj=>outside j (by omega))

theorem copy_mask_run (s:Banks) (n row base:ℕ) (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ))
    (ord:s.reg 82=(row:ℤ)) (ptr:s.reg 220=(base:ℤ)) :
    ∃t k,Steps bitCopy s t k ∧ k≤9+n*(165+6*n) ∧ copied s.mem base row n n t:=by
  let P:=fun i (u:Banks)=>u.reg 6=1 ∧ u.reg 64=(n:ℤ) ∧ u.reg 82=(row:ℤ) ∧
    u.reg 220=(base:ℤ) ∧ copied s.mem base row n i u
  have init:P 0 (setupFor 221 884 64 s):=by
    exact ⟨one,sz,ord,ptr,by intro j hj;omega,by intro q _;rfl⟩
  have next (i:ℕ) (hi:i<n) (u:Banks) (good:P i u) (idx:u.reg 221=(i:ℤ)) (_:u.reg 884=(n:ℤ)-1) :
      ∃t k,Steps bitBody u t k ∧ k≤160+6*n ∧ t.reg 221=u.reg 221 ∧ t.reg 884=u.reg 884 ∧ P (i+1) ((IOp.inc 221).act t):=by
    obtain ⟨a,b,c,d,copied⟩:=good
    obtain ⟨t,k,ex,tm,mem⟩:=write_one u n row base i a b c d idx
    have new:=copy_advance _ _ _ _ _ u t copied mem
    exact ⟨t,k,ex,tm,ex.reg_kept 221 (by decide),ex.reg_kept 884 (by decide),
      (ex.reg_kept 6 (by decide)).trans a,(ex.reg_kept 64 (by decide)).trans b,
      (ex.reg_kept 82 (by decide)).trans c,(ex.reg_kept 220 (by decide)).trans d,new⟩
  obtain ⟨t,k,ex,tm,h⟩:=for_run 221 884 64 n (160+6*n) bitBody P (by decide) (by decide) s sz init next
  exact ⟨t,k,ex,by simpa only [show 160+6*n+5=165+6*n by omega] using tm,h.2.2.2.2⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

theorem emit_record (s:Banks) (n row base:ℕ) (e:Instr)
    (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ)) (ord:s.reg 82=(row:ℤ))
    (tag:s.reg 218=e.tag) (arg:s.reg 219=e.arg)
    (mask:∀ms,e=.lit ms → s.reg 220=(base:ℤ) ∧
      ∀j<n,s.mem (cell 7 (base+j))=(if ms.contains j then 1 else 0)) :
    ∃t k,Steps proc_output s t k ∧ k ≤ 200+n*(165+6*n) ∧
      t.reg 82=((row+1:ℕ):ℤ) ∧ fieldsAt n row t.mem e ∧
      ∀q,¬recordAddress n row e.tag q → t.mem q=s.mem q:=by
  let u:=actPrefix headerOps s
  have ut:u.reg 218=e.tag:=(header_frame s 218 (by decide)).trans tag
  have uz:u.reg 882=0:=rfl
  let v:=(IOp.set 880 (if e.tag=0 then 1 else 0)).act u
  have nonneg:0 ≤ e.tag:=by cases e <;> simp [Instr.tag]
  obtain ⟨ka,ha,runA⟩ : ∃ka,ka ≤ 3 ∧ Steps tagTest u v ka:=by
    by_cases z:e.tag=0
    · refine ⟨1+(1+1),by decide,?_⟩
      unfold tagTest
      refine .yes (by rw [ut,uz,z]) (.yes (i:=1) (by rw [uz,ut,z]) ?_)
      simpa [v,z,setc] using Steps.atom (.set 880 1) u
    · refine ⟨1+1,by decide,?_⟩
      unfold tagTest
      refine .no (i:=1) (by rw [ut,uz];omega) ?_
      simpa [v,z,setc] using Steps.atom (.set 880 0) u
  have vr (j:ℕ) (h:j<861): v.reg j=s.reg j:=by
    change (u.put 880 _).reg j=_
    simpa only [Banks.put,Function.update_of_ne (show j≠880 by omega)] using header_frame s j h
  have vb:v.reg 880=(if e.tag=0 then 1 else 0):=by simp [v,IOp.act,Banks.put]
  have vo:v.reg 6=1:=(vr 6 (by decide)).trans one
  have vm:v.mem=Function.update (Function.update s.mem (inputCell 1 row) e.tag) (inputCell 2 row) e.arg:=by
    change u.mem=_
    rw [←tag,←arg];exact header_memory s row ord
  let guard:=Code.cond 6 880 bitCopy .skip
  obtain ⟨r,kb,runB,hb,after⟩ : ∃r kb,Steps guard v r kb ∧ kb ≤ 10+n*(165+6*n) ∧
      (if e.tag=0 then copied v.mem base row n n r else r.mem=v.mem):=by
    by_cases z:e.tag=0
    · have isLit:∃ms,e=.lit ms:=by cases e <;> simp_all [Instr.tag]
      obtain ⟨ms,hm⟩:=isLit
      obtain ⟨r,k,ex,tm,c⟩:=copy_mask_run v n row base vo ((vr _ (by decide)).trans sz)
        ((vr _ (by decide)).trans ord) ((vr _ (by decide)).trans (mask ms hm).1)
      exact ⟨r,1+k,.yes (by rw [vo,vb,if_pos z]) ex,by omega,by simpa [z] using c⟩
    · exact ⟨v,2,.no (by rw [vo,vb,if_neg z];decide) (.skip _),by omega,by simp [z]⟩
  let t:=action (seqs bumpOutput) r
  have bump:Steps (seqs bumpOutput) r t 7:=straight_steps _ r (by decide)
  have tail:Steps (seqs (tagTest::guard::bumpOutput)) u t (1+ka+(1+kb+7)):=.seq runA (.seq runB bump)
  have ex:=prepend_steps headerOps (tagTest::guard::bumpOutput) s t _ (by decide) tail
  have keep (q:ℤ) (off:∀j<n,q≠inputCell 3 (row*n+j)):r.mem q=v.mem q:=by
    by_cases z:e.tag=0
    · rw [if_pos z] at after;exact after.2 q off
    · rw [if_neg z] at after;rw [after]
  have hscalar (a:ℕ) (h:a=1 ∨ a=2):r.mem (inputCell a row)=v.mem (inputCell a row):=by
    apply keep;intro j _ eq
    rcases h with rfl|rfl <;> have f:=(input_injective (by decide) (by decide)).1 eq <;> omega
  have ne:inputCell 1 row≠inputCell 2 row:=by intro eq;have f:=(input_injective (by decide) (by decide)).1 eq;omega
  have fields:fieldsAt n row t.mem e:=by
    change fieldsAt n row r.mem e
    refine ⟨?_,?_,?_⟩
    · rw [hscalar 1 (by simp),vm,Function.update_of_ne ne,Function.update_self]
    · rw [hscalar 2 (by simp),vm,Function.update_self]
    · intro ms eq j hj
      have z:e.tag=0:=by rw [eq];rfl
      rw [if_pos z] at after
      rw [after.1 j hj,vm,Function.update_of_ne (scratch_ne_input (base+j) 2 row),
        Function.update_of_ne (scratch_ne_input (base+j) 1 row)]
      exact (mask ms eq).2 j hj
  have rt:r.reg 82=(row:ℤ):=(runB.reg_kept 82 (by decide)).trans ((vr _ (by decide)).trans ord)
  refine ⟨t,_,ex,by have a:=header_time;omega,?_,fields,?_⟩
  · change r.reg 82+1=_;rw [rt];norm_cast
  · intro q off;change r.mem q=s.mem q
    have h1:q≠inputCell 1 row:=fun h=>off (.inl h)
    have h2:q≠inputCell 2 row:=fun h=>off (.inr (.inl h))
    have same:r.mem q=v.mem q:=by
      by_cases z:e.tag=0
      · exact keep q (fun j hj eq=>off (.inr (.inr ⟨z,j,hj,eq⟩)))
      · rw [if_neg z] at after;rw [after]
    rw [same,vm,Function.update_of_ne h2,Function.update_of_ne h1]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 1800000

def quotientBody (b:ℕ) := seqs [sub 10 10 b,inc 11]
theorem subtract_loop (b B R Q prev:ℕ) (s:Banks) (hb:64≤b) (rem:R<B)
    (src:s.reg b=(B:ℤ)) (num:s.reg 10=((Q*B+R:ℕ):ℤ)) (acc:s.reg 11=(prev:ℤ)) :
    ∃t k,Steps (.loop b 10 (quotientBody b)) s t k ∧ k≤1+8*Q ∧
      t.reg 10=(R:ℤ) ∧ t.reg 11=((prev+Q:ℕ):ℤ) ∧ t.mem=s.mem ∧
      ∀j,j≠10 → j≠11 → t.reg j=s.reg j:=by
  induction Q generalizing s prev with
  | zero=>
    have no:¬s.reg b ≤ s.reg 10:=by rw [src,num];simp;exact rem
    exact ⟨s,_,.stop no,by omega,by simpa using num,by simpa using acc,rfl,by simp⟩
  | succ q ih=>
    have yes:s.reg b ≤ s.reg 10:=by rw [src,num];exact_mod_cast (by rw [Nat.succ_mul];omega : B≤(q+1)*B+R)
    let u:=action (quotientBody b) s
    have exec:Steps (quotientBody b) s u (weight (quotientBody b)):=straight_steps _ _ (by rfl)
    have stays (j:ℕ) (a:j≠10) (b':j≠11) : u.reg j=s.reg j:=by
      simp [u,quotientBody,seqs,action,sub,inc,IOp.act,Banks.put,Function.update_apply,a,b']
    have div:u.reg b=(B:ℤ):=(stays b (by omega) (by omega)).trans src
    have next:u.reg 10=((q*B+R:ℕ):ℤ):=by
      simp [u,quotientBody,seqs,action,sub,inc,IOp.act,Banks.put,num,src];ring
    have up:u.reg 11=((prev+1:ℕ):ℤ):=by simp [u,quotientBody,seqs,action,sub,inc,IOp.act,Banks.put,acc]
    obtain ⟨t,k,run,tm,n10,n11,mem,regs⟩:=ih (prev+1) u div next up
    have size:weight (quotientBody b)=5:=rfl
    refine ⟨t,_,.more yes exec run,by omega,n10,?_,mem,?_⟩
    · simpa only [show prev+1+q=prev+(q+1) by omega] using n11
    · intro j a b';exact (regs _ a b').trans (stays _ a b')

/-- Quotient and remainder use exactly one subtraction per unit of quotient.
Both results satisfy the same uniform bound and preserve the entire memory. -/
theorem divrem_run (which:Bool) (dst a b A B:ℕ) (s:Banks) (ha:64≤a) (hb:64≤b) (hd:64≤dst)
    (pos:0<B) (one:s.reg 6=1) (sa:s.reg a=(A:ℤ)) (sb:s.reg b=(B:ℤ)) :
    ∃t k,Steps (divrem which dst a b) s t k ∧ k≤20+8*(A/B) ∧
      t.reg dst=((if which then A/B else A%B:ℕ):ℤ) ∧ t.mem=s.mem ∧
      ∀j,j≠10 → j≠11 → j≠dst → t.reg j=s.reg j:=by
  let u:=(IOp.set 11 0).act ((IOp.copy 10 a).act s)
  have frame (j:ℕ) (a':j≠10) (b':j≠11) : u.reg j=s.reg j:=by
    simp [u,IOp.act,Banks.put,Function.update_apply,a',b']
  have ub:u.reg b=(B:ℤ):=(frame _ (by omega) (by omega)).trans sb
  have ua:u.reg 10=(((A/B)*B+A%B:ℕ):ℤ):=by
    change s.reg a=_
    rw [sa,Nat.div_add_mod']
  obtain ⟨t,k,r,tm,n10,n11,mem,regs⟩:=subtract_loop b B (A%B) (A/B) 0 u hb (Nat.mod_lt _ pos) ub ua rfl
  have test:u.reg 6≤u.reg b:=by rw [frame _ (by decide) (by decide),one,ub];exact_mod_cast pos
  let i:=if which then 11 else 10
  let y:=(IOp.copy dst i).act t
  have ex:Steps (divrem which dst a b) s y _ :=
    .seq (.atom _ _) (.seq (.atom _ _) (.seq (.yes test r) (.seq (.atom _ _) (.skip _))))
  refine ⟨y,_,ex,by omega,?_,mem,?_⟩
  · change (t.put dst (t.reg i)).reg dst=_
    simp only [Banks.put,Function.update_self]
    cases which <;> simp_all [i]
  · intro j j10 j11 diff
    have keep:y.reg j=t.reg j:=by simp [y,IOp.act,Banks.put,Function.update_apply,diff]
    exact keep.trans ((regs _ j10 j11).trans (frame _ j10 j11))
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 22000

def clearOne := seqs [addr 8,st 12 7,inc 8,dec 15]
theorem clear_shape (s:Banks) (base:ℕ) (h:s.reg 8=(base:ℤ)) (zero:s.reg 7=0) :
    let t:=action clearOne s
    t.reg 6=s.reg 6 ∧ t.reg 7=s.reg 7 ∧ t.reg 8=s.reg 8+1 ∧ t.reg 15=s.reg 15-1 ∧
    (∀j,64≤j → t.reg j=s.reg j) ∧ t.mem=Function.update s.mem (cell 7 base) 0:=by
  have shift:action (lshift 12 8 6) s = s.put 12 (64*s.reg 8):=by
    simp [lshift,seqs,action,cp,add,IOp.act,Banks.put,Function.update_idem]
    congr 2;ring
  simp only [clearOne,addr,seqs,List.foldr,action,shift,st,inc,dec,setc,sub,IOp.act]
  simp [Banks.put,Banks.write,Function.update_apply,zero,h,cell,word]
  constructor
  · intro j hj;split_ifs <;> omega
  · congr 1;ring

def Clean (m:ℤ→ℤ) (base i:ℕ) (s:Banks) :=
  (∀j < i,s.mem (cell 7 (base+j))=0) ∧
  ∀q:ℤ,(∀j < i,q≠cell 7 (base+j)) → s.mem q=m q

theorem clean_succ {m:ℤ→ℤ} {base i:ℕ} {s t:Banks} (h:Clean m base i s)
    (eq:t.mem=Function.update s.mem (cell 7 (base+i)) 0) : Clean m base (i+1) t:=by
  constructor
  · intro j hj
    by_cases same:j=i
    · subst j;rw [eq];simp
    · have ne:cell 7 (base+j)≠cell 7 (base+i):=by intro bad;unfold cell word at bad;push_cast at bad;omega
      rw [eq,Function.update_of_ne ne,h.1 _ (by omega)]
  · intro q outside;rw [eq,Function.update_of_ne (outside i (by omega))]
    exact h.2 q (fun j hj=>outside j (by omega))

theorem clear_loop (m:ℤ→ℤ) (dst base i rest:ℕ) (hd:64≤dst) (s:Banks)
    (one:s.reg 6=1) (zero:s.reg 7=0) (cursor:s.reg 8=((base+i:ℕ):ℤ)) (remaining:s.reg 15=(rest:ℤ))
    (save:s.reg dst=(base:ℤ)) (clean:Clean m base i s) :
    ∃t z,Steps (.loop 6 15 clearOne) s t z ∧ z≤1+63*rest ∧
      t.reg 8=((base+(i+rest):ℕ):ℤ) ∧ t.reg dst=(base:ℤ) ∧ Clean m base (i+rest) t:=by
  induction rest generalizing s i with
  | zero=>
    have stop:¬s.reg 6 ≤ s.reg 15:=by rw [one,remaining];decide
    exact ⟨_,_,.stop stop,by omega,by simpa using cursor,save,by simpa using clean⟩
  | succ k ih=>
    have go:s.reg 6 ≤ s.reg 15:=by rw [one,remaining];omega
    let t:=action clearOne s
    have ex:Steps clearOne s t (weight clearOne):=straight_steps _ _ (by decide)
    have sz:weight clearOne≤62:=by decide
    obtain ⟨r6,r7,r8,r15,high,wrote⟩:=clear_shape s (base+i) cursor zero
    obtain ⟨u,z,tail,tm,head,regs,cleared⟩:=ih (i+1) t (r6.trans one) (r7.trans zero)
      (by rw [show t.reg 8=s.reg 8+1 from r8,cursor];push_cast;ring)
      (by rw [show t.reg 15=s.reg 15-1 from r15,remaining];push_cast;ring)
      ((high dst hd).trans save) (clean_succ clean wrote)
    refine ⟨u,_,.more go ex tail,by omega,?_,regs,?_⟩
    · simpa only [show i+(k+1)=i+1+k by omega] using head
    · simpa only [show i+(k+1)=i+1+k by omega] using cleared

theorem allocate_run (dst len base L:ℕ) (hd:64≤dst) (hl:64≤len) (ne:dst≠len) (s:Banks)
    (one:s.reg 6=1) (zero:s.reg 7=0) (cursor:s.reg 8=(base:ℤ)) (length:s.reg len=(L:ℤ)) :
    ∃F t,F≤64*(1+L) ∧ run F [allocate dst len] s=some t ∧
      t.reg dst=(base:ℤ) ∧ t.reg 8=((base+L:ℕ):ℤ) ∧ Clean s.mem base L t:=by
  let u:=(IOp.copy dst 8).act s
  let v:=(IOp.copy 15 len).act u
  have initial:Clean s.mem base 0 v:=by constructor <;> simp [v,u,IOp.act,Banks.put]
  have a (j:ℕ) (j15:j≠15) (jd:j≠dst) : v.reg j=s.reg j:=by
    simp [v,u,IOp.act,Banks.put,Function.update_of_ne j15,Function.update_of_ne jd]
  obtain ⟨t,z,ev,tm,top,rd,hc⟩:=clear_loop s.mem dst base 0 L hd v
    ((a 6 (by decide) (by omega)).trans one) ((a 7 (by decide) (by omega)).trans zero)
    (by simpa using (a 8 (by decide) (by omega)).trans cursor)
    (by simp [v,u,IOp.act,Banks.put,Function.update_of_ne (Ne.symm ne),length])
    (by simp [v,u,IOp.act,Banks.put,Function.update_of_ne (by omega:dst≠15),cursor]) initial
  have ex:Steps (allocate dst len) s t (1+1+(1+1+(1+z+1))):=
    .seq (.atom _ _) (.seq (.atom _ _) (.seq ev (.skip _)))
  refine ⟨1+1+(1+1+(1+z+1)),t,by omega,?_,rd,by simpa using top,by simpa using hc⟩
  simpa [run] using ex.schedule [] 0
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
structure Rel (n:ℕ) (input:ℤ → ℤ) (s:State) (b:Banks) : Prop where
  regs : ∀j,visible j=true → b.reg j=s.reg j
  heap : ∀i,b.mem (cell 7 i)=s.heap i
  other : ∀q,¬tapeAddress q → ¬scratchAddress q → b.mem q=input q
  records : prefixAt n b.mem s.output
  count : s.closed=true → b.mem (inputCell 0 0)=(s.output.length:ℤ)
theorem initial_rel (n:ℕ) (b:Banks) : Rel n b.mem (initial b) b:=
  ⟨fun _ _=>rfl,fun _=>rfl,fun _ _ _=>rfl,by intro j hj;simp [initial] at hj,by simp [initial]⟩
theorem Rel.assign {n input s b} (h:Rel n input s b) (dst:ℕ) (v:ℤ) (u:Banks)
    (correct:u.reg dst=v) (frame:∀j,visible j=true → j≠dst → u.reg j=b.reg j) (mem:u.mem=b.mem) :
    Rel n input (s.assign dst v) u:=by
  refine ⟨?_,by rw [mem];exact h.heap,by rw [mem];exact h.other,by rw [mem];exact h.records,by rw [mem];exact h.count⟩
  intro j vis
  by_cases eq:j=dst
  · subst j;simpa [State.assign] using correct
  · simpa [State.assign,eq] using (frame j vis eq).trans (h.regs j vis)
theorem Rel.put {n input s b} (h:Rel n input s b) (dst:ℕ) (v:ℤ):Rel n input (s.assign dst v) (b.put dst v):=
  h.assign dst v _ (by simp [Banks.put]) (by intro j _ ne;simp [Banks.put,ne]) rfl
theorem raw_other (q:ℤ) (h:rawInput q=true) : ¬tapeAddress q ∧ ¬scratchAddress q:=by
  simp [rawInput] at h
  constructor <;> rintro ⟨j,rfl⟩ <;> unfold cell word at h <;> push_cast at h <;> omega
theorem offset_inj {a b:ℕ} (h:cell 7 a=cell 7 b):a=b:=by unfold cell word at h;push_cast at h;omega
theorem visible_tmp {j:ℕ} (vis:visible j=true) : (j<10 ∨ 15<j) ∧ j≠221 ∧ (j<861 ∨ 903<j):=by
  simpa [visible,and_assoc] using vis
theorem Rel.scratch {n input s b} (h:Rel n input s b) (u:Banks) (heap:ℕ → ℤ)
    (regs:∀j,visible j=true → u.reg j=s.reg j) (items:∀i,u.mem (cell 7 i)=heap i)
    (frame:∀q,¬scratchAddress q → u.mem q=b.mem q) : Rel n input {s with heap:=heap} u:=by
  refine ⟨regs,items,fun q a c=>(frame q c).trans (h.other q a c),?_,?_⟩
  · apply prefix_unchanged n _ b.mem _ h.records
    intro q a;exact frame q (fun c=>scratch_not_tape c a)
  · intro c;exact (frame _ (fun g=>scratch_not_tape g (input_is_tape 0 0))).trans (h.count c)
theorem Rel.closing {n input s b} (h:Rel n input s b) :
    Rel n input {s with closed:=true} (b.write (inputCell 0 0) (s.output.length:ℤ)):=by
  have fin:=header_closes n _ _ h.records
  refine ⟨h.regs,?_,?_,fin.2,fun _=>fin.1⟩
  · intro i;change Function.update _ _ _ _=_
    rw [Function.update_of_ne (scratch_ne_input i 0 0),h.heap]
  · intro q nt ns;change Function.update _ _ _ _=_
    rw [Function.update_of_ne (show q≠inputCell 0 0 from fun eq=>nt (eq ▸ input_is_tape 0 0)),h.other q nt ns]
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
def Sim {n:ℕ} {input:ℤ → ℤ} {s:State} {b:Banks} (_:Rel n input s b) (op:Operation) :=
  ∀t k,op.next n input s=some (t,k) →
    ∃u z,Steps op.lower b u z ∧ z ≤ k ∧ Rel n input t u
theorem sim_regular {n input s b} (h:Rel n input s b) (o:IOp) (safe:IRegular o=true):Sim h (.regular o):=by
  intro t k step
  change regularNext input s o=some (t,k) at step
  cases o with
  | set d v=>
    simp only [regularNext,Option.some.injEq,Prod.mk.injEq] at step
    obtain ⟨rfl,rfl⟩:=step
    exact ⟨_,1,.atom _ _,le_rfl,h.put d v⟩
  | copy d a|inc d|dec d|add d a c|sub d a c=>
    simp only [regularNext,Option.some.injEq,Prod.mk.injEq] at step
    obtain ⟨rfl,rfl⟩:=step
    simp [IRegular] at safe
    refine ⟨_,1,.atom _ _,le_rfl,?_⟩
    simp only [IOp.act]
    first
    | rw [h.regs _ safe];apply h.put
    | rw [h.regs _ safe.2];apply h.put
    | rw [h.regs _ safe.1.2,h.regs _ safe.2];apply h.put
  | load d a=>
    obtain ⟨_,av⟩:=Bool.and_eq_true_iff.mp safe
    simp only [regularNext] at step
    split at step <;> try contradiction
    rename_i raw
    obtain ⟨rfl,rfl⟩:=Option.some.inj step
    have ⟨x,y⟩:=raw_other _ raw
    refine ⟨_,1,.atom _ _,le_rfl,?_⟩
    simp only [IOp.act,h.regs _ av,h.other _ x y];apply h.put
  | store a v=>
    obtain ⟨av,vv⟩:=Bool.and_eq_true_iff.mp safe
    simp only [regularNext] at step
    split at step <;> try contradiction
    rename_i good
    obtain ⟨rfl,rfl⟩:=Option.some.inj step
    refine ⟨_,1,.atom _ _,le_rfl,?_⟩
    simp only [IOp.act,h.regs _ av,h.regs _ vv,good.1,good.2]
    exact h.closing

theorem sim_multiply {n input s b} (h:Rel n input s b) (d a c:ℕ)
    (safe:(Operation.multiply d a c).safe=true) :Sim h (.multiply d a c):=by
  intro t k step
  simp [Operation.safe,high] at safe
  obtain ⟨⟨⟨⟨dv,dh⟩,av,ah⟩,cv,ch⟩,ne⟩:=safe
  simp only [Operation.next] at step
  split at step <;> try contradiction
  rename_i flags
  obtain ⟨one,pa,pc⟩:=flags
  obtain ⟨rfl,rfl⟩:=Option.some.inj step
  obtain ⟨u,z,ex,tm,res,mem,fr⟩:=multiply_run d a c (s.reg a).toNat (s.reg c).toNat b dh ah ch ne
    ((h.regs 6 (by decide)).trans one) (by rw [h.regs _ av,Int.toNat_of_nonneg pa])
    (by rw [h.regs _ cv,Int.toNat_of_nonneg pc])
  refine ⟨u,z,ex,tm,h.assign d _ _ ?_ (fun j vis jd=>fr j (by have f:=visible_tmp vis;omega) jd) mem⟩
  simpa [Int.toNat_of_nonneg pa,Int.toNat_of_nonneg pc] using res

theorem sim_divide {n input s b} (h:Rel n input s b) (q:Bool) (d a c:ℕ)
    (safe:(Operation.divide q d a c).safe=true) :Sim h (.divide q d a c):=by
  intro t k step
  simp [Operation.safe,high] at safe
  obtain ⟨⟨⟨_,dh⟩,av,ah⟩,cv,ch⟩:=safe
  simp only [Operation.next] at step
  split at step <;> try contradiction
  rename_i flags
  obtain ⟨one,pa,pc⟩:=flags
  obtain ⟨rfl,rfl⟩:=Option.some.inj step
  obtain ⟨u,z,ex,tm,res,mem,fr⟩:=divrem_run q d a c (s.reg a).toNat (s.reg c).toNat b ah ch dh
    (by omega) ((h.regs 6 (by decide)).trans one) (by rw [h.regs _ av,Int.toNat_of_nonneg pa])
    (by rw [h.regs _ cv,Int.toNat_of_nonneg (by omega:0 ≤ s.reg c)])
  exact ⟨u,z,ex,tm,h.assign d _ _ res (fun j vis jd=>fr j (by have f:=visible_tmp vis;omega)
    (by have f:=visible_tmp vis;omega) jd) mem⟩
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

theorem shift_shape (d a k:ℕ) : straight (lshift d a k)=true ∧ weight (lshift d a k)=3+2*k:=by
  suffices h:straight (seqs (List.replicate k (add d d d)))=true ∧
      weight (seqs (List.replicate k (add d d d)))=1+2*k by
    change (true && straight (seqs (List.replicate k (add d d d))))=true ∧
      1+1+weight (seqs (List.replicate k (add d d d)))=_
    simp [h.1,h.2];omega
  induction k with
  | zero=>exact ⟨rfl,rfl⟩
  | succ k ih=>
    simp only [List.replicate_succ]
    change (true && straight (seqs (List.replicate k (add d d d))))=true ∧
      1+1+weight (seqs (List.replicate k (add d d d)))=_
    simp [ih.1,ih.2];omega

theorem reads_word (s:Banks) (d a i j:ℕ) (idx:s.reg a+s.reg i=(j:ℤ)):
    (action (readCell d a i) s).reg d=s.mem (cell 7 j) ∧ (action (readCell d a i) s).mem=s.mem:=by
  have adr:cell 7 j= -95-64*(j:ℤ):=by simp [cell,word];ring
  simp [readCell,addr,seqs,action,shift_action,add,setc,sub,ld,IOp.act,Banks.put,idx,adr]
theorem writes_word (s:Banks) (a i v j:ℕ) (hv:64 ≤ v) (idx:s.reg a+s.reg i=(j:ℤ)):
    (action (writeCell a i v) s).mem=Function.update s.mem (cell 7 j) (s.reg v):=by
  have adr:cell 7 j= -95-64*(j:ℤ):=by simp [cell,word];ring
  simp [writeCell,addr,seqs,action,shift_action,add,setc,sub,st,IOp.act,Banks.put,Banks.write,idx,adr,
    Function.update_of_ne (show v≠12 by omega),Function.update_of_ne (show v≠13 by omega),
    Function.update_of_ne (show v≠14 by omega)]

namespace Logical
theorem sim_shift {n input s b} (h:Rel n input s b) (d a k:ℕ) (av:visible a=true) :Sim h (.shift d a k):=by
  intro t z step
  obtain ⟨rfl,rfl⟩:=Option.some.inj step
  obtain ⟨st,wt⟩:=shift_shape d a k
  obtain ex:=straight_steps (lshift d a k) b st
  rw [shift_action,h.regs a av] at ex
  exact ⟨_,_,ex,le_of_eq wt,h.put ..⟩
theorem sim_fetch {n input s b} (h:Rel n input s b) (d a i:ℕ) (safe:(Operation.fetch d a i).safe=true):
    Sim h (.fetch d a i):=by
  simp [Operation.safe,high] at safe
  obtain ⟨⟨⟨_,_⟩,av,_⟩,iv,_⟩:=safe
  intro t k step
  simp only [Operation.next] at step
  split at step <;> try contradiction
  rename_i pos
  obtain ⟨rfl,rfl⟩:=Option.some.inj step
  let u:=action (readCell d a i) b
  have ex:Steps (readCell d a i) b u (weight (readCell d a i)):=straight_steps _ _ rfl
  have ⟨read,mem⟩:=reads_word b d a i (s.reg a+s.reg i).toNat
    (by rw [h.regs _ av,h.regs _ iv,Int.toNat_of_nonneg pos])
  refine ⟨u,_,ex,by exact of_decide_eq_true rfl,h.assign d _ u (read.trans (h.heap _)) ?_ mem⟩
  intro j vis jd
  apply ex.reg_kept
  have v:=visible_tmp vis
  simp [readCell,addr,seqs,keepsReg,lshift,add,setc,sub,cp,ld,jd]
  repeat' constructor <;> omega

theorem sim_save {n input s b} (h:Rel n input s b) (a i v:ℕ) (safe:(Operation.save a i v).safe=true):
    Sim h (.save a i v):=by
  simp [Operation.safe,high] at safe
  obtain ⟨⟨⟨av,_⟩,iv,_⟩,vv,vh⟩:=safe
  intro t k step
  simp only [Operation.next] at step
  split at step <;> try contradiction
  rename_i pos
  obtain ⟨rfl,rfl⟩:=Option.some.inj step
  let j:=(s.reg a+s.reg i).toNat
  let u:=action (writeCell a i v) b
  have ex:Steps (writeCell a i v) b u (weight (writeCell a i v)):=straight_steps _ _ rfl
  have mem:=writes_word b a i v j vh (by rw [h.regs _ av,h.regs _ iv];exact (Int.toNat_of_nonneg pos).symm)
  refine ⟨u,_,ex,by exact of_decide_eq_true rfl,h.scratch u _ ?_ ?_ ?_⟩
  · intro key vis
    apply (ex.reg_kept key ?_).trans (h.regs key vis)
    have z:=visible_tmp vis
    simp [writeCell,addr,seqs,keepsReg,lshift,add,setc,sub,cp,st]
    repeat' constructor <;> omega
  · intro r;change u.mem (cell 7 r)=Function.update s.heap j (s.reg v) r
    rw [show u.mem=_ from mem,h.regs _ vv]
    by_cases eq:r=j
    · subst r;simp
    · rw [Function.update_of_ne (fun g=>eq (offset_inj g)),Function.update_of_ne eq,h.heap]
  · intro q outside;rw [show u.mem=_ from mem,Function.update_of_ne (show q≠cell 7 j from fun eq=>outside ⟨j,eq⟩)]
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 22000

theorem allocate_steps (dst len base L:ℕ) (hd:64≤dst) (hl:64≤len) (ne:dst≠len) (s:Banks)
    (one:s.reg 6=1) (zero:s.reg 7=0) (cursor:s.reg 8=(base:ℤ)) (length:s.reg len=(L:ℤ)) :
    ∃F t,F≤64*(1+L) ∧ Steps (allocate dst len) s t F ∧
      t.reg dst=(base:ℤ) ∧ t.reg 8=((base+L:ℕ):ℤ) ∧ Clean s.mem base L t:=by
  let u:=(IOp.copy dst 8).act s
  let v:=(IOp.copy 15 len).act u
  have initial:Clean s.mem base 0 v:=by constructor <;> simp [v,u,IOp.act,Banks.put]
  have a (j:ℕ) (j15:j≠15) (jd:j≠dst) : v.reg j=s.reg j:=by
    simp [v,u,IOp.act,Banks.put,Function.update_of_ne j15,Function.update_of_ne jd]
  obtain ⟨t,z,ev,tm,top,rd,hc⟩:=clear_loop s.mem dst base 0 L hd v
    ((a 6 (by decide) (by omega)).trans one) ((a 7 (by decide) (by omega)).trans zero)
    (by simpa using (a 8 (by decide) (by omega)).trans cursor)
    (by simp [v,u,IOp.act,Banks.put,Function.update_of_ne (Ne.symm ne),length])
    (by simp [v,u,IOp.act,Banks.put,Function.update_of_ne (by omega:dst≠15),cursor]) initial
  have ex:Steps (allocate dst len) s t (1+1+(1+1+(1+z+1))):=
    .seq (.atom _ _) (.seq (.atom _ _) (.seq ev (.skip _)))
  refine ⟨1+1+(1+1+(1+z+1)),t,by omega,ex,rd,by simpa using top,by simpa using hc⟩
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
theorem sim_alloc {n input s b} (h:Rel n input s b) (d len:ℕ) (safe:(Operation.alloc d len).safe=true):
    Sim h (.alloc d len):=by
  simp [Operation.safe,high] at safe
  obtain ⟨⟨⟨_,hd⟩,lv,hl⟩,ne⟩:=safe
  intro t k step
  simp only [Operation.next] at step
  split at step <;> try contradiction
  rename_i good
  obtain ⟨one,zero,cursor,length⟩:=good
  obtain ⟨rfl,rfl⟩:=Option.some.inj step
  let a:=(s.reg 8).toNat
  let L:=(s.reg len).toNat
  obtain ⟨z,u,tm,ex,dst,newtop,clean⟩:=allocate_steps d len a L hd hl ne b
    ((h.regs 6 (by decide)).trans one) ((h.regs 7 (by decide)).trans zero)
    ((h.regs 8 (by decide)).trans (Int.toNat_of_nonneg cursor).symm)
    ((h.regs len lv).trans (Int.toNat_of_nonneg length).symm)
  have frame (q:ℤ) (off:¬scratchAddress q):u.mem q=b.mem q:=
    clean.2 q (fun i _ eq=>off ⟨a+i,eq⟩)
  have regs (j:ℕ) (vis:visible j=true) (jd:j≠d) (j8:j≠8):u.reg j=b.reg j:=by
    apply ex.reg_kept;have f:=visible_tmp vis
    simp [allocate,addr,seqs,keepsReg,lshift,add,setc,sub,cp,inc,dec,st,jd,j8]
    repeat' constructor <;> omega
  refine ⟨u,z,ex,tm,?_,?_,fun q g f=>(frame q f).trans (h.other q g f),?_,?_⟩
  · intro j vis
    change u.reg j=Function.update (Function.update s.reg d (a:ℤ)) 8 ((a+L:ℕ):ℤ) j
    by_cases j8:j=8
    · subst j;simpa using newtop
    · rw [Function.update_of_ne j8];by_cases jd:j=d
      · subst j;simpa using dst
      · rw [Function.update_of_ne jd];exact (regs j vis jd j8).trans (h.regs j vis)
  · intro i;change u.mem (cell 7 i)=if a ≤ i ∧ i<a+L then 0 else s.heap i
    split_ifs with yes
    · obtain ⟨j,rfl⟩:=Nat.exists_eq_add_of_le yes.1
      exact clean.1 j (by omega)
    · apply (clean.2 _ ?_).trans (h.heap i)
      intro j hj eq;have pos:=offset_inj eq;omega
  · exact prefix_unchanged n _ _ _ h.records (fun q yes=>frame q (fun g=>scratch_not_tape g yes))
  · intro closed;exact (frame _ (fun g=>scratch_not_tape g (input_is_tape 0 0))).trans (h.count closed)
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
theorem record_mask (n:ℕ) (s:State) (t:s.reg 218=(record n s).tag)
    (ok:s.bitsOK n (record n s)=true) (ms:List ℕ) (eq:record n s=.lit ms) :
    s.reg 220=((s.reg 220).toNat:ℤ) ∧ ∀j<n,s.heap ((s.reg 220).toNat+j)=(if ms.contains j then 1 else 0):=by
  rw [eq] at t ok
  change s.reg 218=0 at t
  simp [State.bitsOK,List.all_eq_true] at ok
  have same:(List.range n).filter (fun j=>s.heap ((s.reg 220).toNat+j)==1)=ms:=by
    simpa [record,t] using eq
  refine ⟨(Int.toNat_of_nonneg ok.1).symm,?_⟩
  intro j hj
  rw [←same]
  have val:=ok.2 j hj
  rcases val with a|a <;> simp [a,List.contains_iff_mem,hj]
theorem out_keeps (j:ℕ) (vis:visible j=true) (ne:j≠82) : keepsReg j proc_output=true:=by
  have v:=visible_tmp vis
  simp [proc_output,forN,mul,readCell,addr,lshift,seqs,keepsReg,setc,cp,add,sub,inc,dec,ld,st]
  repeat' constructor <;> omega
theorem sim_output {n input s b} (h:Rel n input s b) : Sim h .output:=by
  intro next cost step
  simp only [Operation.next] at step
  split at step <;> try contradiction
  rename_i flags
  obtain ⟨before,one,sz,ord,tag,arg,bits⟩:=flags
  obtain ⟨rfl,rfl⟩:=Option.some.inj step
  obtain ⟨t,k,run,tm,ordinal,fresh,frame⟩:=emit_record b n s.output.length (s.reg 220).toNat
    (record n s) ((h.regs _ (by decide)).trans one) ((h.regs _ (by decide)).trans sz)
    ((h.regs _ (by decide)).trans ord) ((h.regs _ (by decide)).trans tag) ((h.regs _ (by decide)).trans arg)
    (by intro ms eq
        obtain ⟨ptr,vals⟩:=record_mask n s tag bits ms eq
        exact ⟨(h.regs _ (by decide)).trans ptr,fun j hj=>(h.heap _).trans (vals j hj)⟩)
  refine ⟨t,k,run,tm,?_,?_,?_,prefix_snoc n _ _ _ _ h.records fresh frame,?_⟩
  · intro j vis
    change t.reg j=Function.update s.reg 82 (s.reg 82+1) j
    by_cases same:j=82
    · subst j;rw [Function.update_self,ord,ordinal];norm_cast
    · rw [Function.update_of_ne same];exact (run.reg_kept j (out_keeps j vis same)).trans (h.regs j vis)
  · intro i;apply (frame _ ?_).trans (h.heap i)
    intro bad;exact scratch_not_tape (show scratchAddress (cell 7 i) from ⟨i,rfl⟩) (record_is_tape bad)
  · intro q a c;exact (frame q (fun bad=>a (record_is_tape bad))).trans (h.other q a c)
  · intro a;change s.closed=true at a;rw [before] at a;contradiction
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option autoImplicit false
set_option maxRecDepth 35000
set_option maxHeartbeats 3000000
theorem lower_code_name_push : src_code_name_push.lower=proc_code_name_push:=rfl
theorem lower_component : src_component.lower=proc_component:=rfl
theorem lower_rim : src_rim.lower=proc_rim:=rfl
theorem lower_first : src_first.lower=proc_first:=rfl
theorem lower_equal_rows : src_equal_rows.lower=proc_equal_rows:=rfl
theorem lower_name_key : src_name_key.lower=proc_name_key:=rfl
theorem lower_imat : src_imat.lower=proc_imat:=rfl
theorem lower_data_for_vertex : src_data_for_vertex.lower=proc_data_for_vertex:=rfl
theorem lower_build_geometry : src_build_geometry.lower=proc_build_geometry:=rfl
theorem lower_fits : src_fits.lower=proc_fits:=rfl
theorem lower_trial : src_trial.lower=proc_trial:=rfl
theorem lower_visit : src_visit.lower=proc_visit:=rfl
theorem lower_all_cuts : src_all_cuts.lower=proc_all_cuts:=rfl
theorem lower_generate : src_generate.lower=proc_generate:=rfl
theorem candidate_lower (h w:ℕ) : (candidate h w).lower=code h w:=rfl
theorem candidate_safe (h w:ℕ) : (candidate h w).safe=true:=by
  have safe:src_generate.safe=true:=by decide
  simpa only [candidate,chain,List.foldr,Program.safe,Operation.safe,IRegular,visible,safe]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
theorem sim_op {n input s b} (h:Rel n input s b) (o:Operation) (safe:o.safe=true):Sim h o:=by
  cases o with
  | regular o=>exact sim_regular h o safe
  | multiply d a c=>exact sim_multiply h d a c safe
  | divide q d a c=>exact sim_divide h q d a c safe
  | shift d a k=>exact sim_shift h d a k (Bool.and_eq_true_iff.mp safe).2
  | fetch d a i=>exact sim_fetch h d a i safe
  | save a i v=>exact sim_save h a i v safe
  | alloc d l=>exact sim_alloc h d l safe
  | output=>exact sim_output h

theorem Executes.realize {n input p s t k} (run:Executes n input p s t k) (safe:p.safe=true)
    {b:Banks} (rel:Rel n input s b) :
    ∃u z,Steps p.lower b u z ∧ z ≤ k ∧ Rel n input t u:=by
  induction run generalizing b with
  | skip=>exact ⟨_,1,.skip _,le_rfl,rel⟩
  | op step=>exact sim_op rel _ safe _ _ step
  | seq x y ih jh=>
    obtain ⟨p,q⟩:=Bool.and_eq_true_iff.mp safe
    obtain ⟨u,a,first,atime,mid⟩:=ih p rel
    obtain ⟨v,c,second,ctime,fin⟩:=jh q mid
    exact ⟨v,_,.seq first second,by omega,fin⟩
  | yes flag x ih=>
    obtain ⟨⟨⟨a,c⟩,p⟩,_⟩:( _ ∧ _ ) ∧ _:=by simpa [Program.safe] using safe
    obtain ⟨u,z,ex,tm,fin⟩:=ih p rel
    exact ⟨u,_,.yes (by rwa [rel.regs _ a,rel.regs _ c]) ex,by omega,fin⟩
  | no flag y ih=>
    obtain ⟨⟨⟨a,c⟩,_⟩,q⟩:( _ ∧ _ ) ∧ _:=by simpa [Program.safe] using safe
    obtain ⟨u,z,ex,tm,fin⟩:=ih q rel
    exact ⟨u,_,.no (by rwa [rel.regs _ a,rel.regs _ c]) ex,by omega,fin⟩
  | stop flag=>
    obtain ⟨⟨a,c⟩,_⟩:(_ ∧ _) ∧ _:=by simpa [Program.safe] using safe
    exact ⟨b,_,.stop (by rwa [rel.regs _ a,rel.regs _ c]),le_rfl,rel⟩
  | more flag first again ih jh=>
    obtain ⟨⟨a,c⟩,p⟩:(_ ∧ _) ∧ _:=by simpa [Program.safe] using safe
    obtain ⟨u,z,ex,tm,mid⟩:=ih p rel
    obtain ⟨v,w,tail,tm',fin⟩:=jh safe mid
    exact ⟨v,_,.more (by rwa [rel.regs _ a,rel.regs _ c]) ex tail,by omega,fin⟩

theorem realize_candidate (n h w:ℕ) (s:Banks) (t:State) (charge:ℕ)
    (valid:Executes n s.mem (candidate h w) (initial s) t charge) (closed:t.closed=true) :
    ∃k u,k ≤ charge ∧ run k [code h w] s=some u ∧
      (∀q:ℤ,(∀i:ℕ,q≠cell 5 i ∧ q≠cell 7 i) → u.mem q=s.mem q) ∧ Input n u.mem t.output:=by
  obtain ⟨u,k,ex,tm,rel⟩:=valid.realize (candidate_safe h w) (initial_rel n s)
  rw [candidate_lower] at ex
  refine ⟨k,u,tm,by simpa [run] using ex.schedule [] 0,?_,rel.count closed,rel.records⟩
  intro q all;exact rel.other q (fun ⟨i,eq⟩=>(all i).1 eq) (fun ⟨i,eq⟩=>(all i).2 eq)
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
theorem solution (n h w:ℕ) (s:CandidateRAM.Banks) (t:Logical.State) (charge:ℕ)
    (valid:Logical.Executes n s.mem (Logical.candidate h w) (Logical.initial s) t charge)
    (closed:t.closed=true) :
    ∃k u,k ≤ charge ∧ CandidateRAM.run k [CandidateRAM.code h w] s=some u ∧
      (∀q:ℤ,(∀i:ℕ,q≠cell 5 i ∧ q≠cell 7 i) → u.mem q=s.mem q) ∧ Candidates.Input n u.mem t.output := Logical.realize_candidate n h w s t charge valid closed
