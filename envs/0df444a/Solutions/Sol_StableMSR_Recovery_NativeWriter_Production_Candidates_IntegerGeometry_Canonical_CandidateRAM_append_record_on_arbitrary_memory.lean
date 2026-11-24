-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.append_record_on_arbitrary_memory
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T02:15:01.240808+00:00
-- url     : https://prove2.me/submissions/b3c78d0b-e98d-4007-a10c-dd4a16cc4bc7

import Definitions.Def_StableMSR_CandidateInterpreter
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

open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
theorem solution
    (s:Banks) (n row base:ℕ) (e:Instr)
    (one:s.reg 6=1) (sz:s.reg 64=(n:ℤ)) (ord:s.reg 82=(row:ℤ))
    (tag:s.reg 218=e.tag) (arg:s.reg 219=e.arg)
    (mask:∀ms,e=.lit ms → s.reg 220=(base:ℤ) ∧
      ∀j<n,s.mem (cell 7 (base+j))=(if ms.contains j then 1 else 0)) :
    ∃t k,k ≤ 200+n*(165+6*n) ∧ run k [proc_output] s=some t ∧
      t.reg 82=((row+1:ℕ):ℤ) ∧ t.mem (inputCell 1 row)=e.tag ∧ t.mem (inputCell 2 row)=e.arg ∧
      (∀ms,e=.lit ms → ∀j<n,t.mem (inputCell 3 (row*n+j))=(if ms.contains j then 1 else 0)) ∧
      ∀q,q≠inputCell 1 row → q≠inputCell 2 row →
        (e.tag=0 → ∀j<n,q≠inputCell 3 (row*n+j)) → t.mem q=s.mem q := by
  obtain ⟨t,k,ex,tm,ord,fields,fr⟩:=emit_record s n row base e one sz ord tag arg mask
  refine ⟨t,k,tm,by simpa [run] using ex.schedule [] 0,ord,fields.1,fields.2.1,fields.2.2,?_⟩
  intro q a b c;apply fr; rintro (h|h|⟨z,j,hj,h⟩)
  · exact a h
  · exact b h
  · exact c z j hj h
