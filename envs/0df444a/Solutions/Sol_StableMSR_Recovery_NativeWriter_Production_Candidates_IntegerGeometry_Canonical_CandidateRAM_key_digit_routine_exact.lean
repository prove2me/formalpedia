-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.key_digit_routine_exact
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T01:29:31.732879+00:00
-- url     : https://prove2.me/submissions/691466fd-1ff1-4a92-b742-75f7591374e1

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

def doubleBody := seqs [seqs [add 280 128 128,cp 128 280],inc 130]
theorem repeat_digit (a i rem:ℕ) (s:Banks) (idx:s.reg 130=(i:ℤ))
    (stop:s.reg 279=(i:ℤ)+(rem:ℤ)-1) (val:s.reg 128=(Naming.push a i:ℤ)) :
    ∃t z,Steps (.loop 130 279 doubleBody) s t z ∧ z≤1+12*rem ∧
       t.reg 128=(Naming.push a (i+rem):ℤ) ∧ t.mem=s.mem:=by
  induction rem generalizing i s with
  | zero=>
    have no:¬s.reg 130 ≤ s.reg 279:=by rw [idx,stop];omega
    exact ⟨_,_,.stop no,by omega,by simpa using val,rfl⟩
  | succ k ih=>
    have yes:s.reg 130 ≤ s.reg 279:=by rw [idx,stop];omega
    let v:=action doubleBody s
    have step:Steps doubleBody s v (weight doubleBody):=straight_steps _ _ (by decide)
    have ticks:weight doubleBody≤11:=by decide
    have idv:v.reg 130=((i+1:ℕ):ℤ):=by simp [v,doubleBody,seqs,action,add,cp,inc,IOp.act,Banks.put,idx]
    have endv:v.reg 279=((i+1:ℕ):ℤ)+(k:ℤ)-1:=by
      change s.reg 279=_;rw [stop];push_cast;ring
    have value:v.reg 128=(Naming.push a (i+1):ℤ):=by
      simp [v,doubleBody,seqs,action,add,cp,inc,IOp.act,Banks.put,val,Naming.push];ring
    obtain ⟨t,z,again,tm,out,mem⟩:=ih (i+1) v idv endv value
    refine ⟨t,_,.more yes step again,by omega,?_,mem⟩
    exact (show i+1+k=i+(k+1) by omega) ▸ out

theorem name_push_run (s:Banks) (a digit:ℕ) (value:s.reg 128=(a:ℤ)) (arg:s.reg 129=(digit:ℤ)) :
    ∃F t,F≤48*(1+digit) ∧ run F [proc_code_name_push] s=some t ∧
      t.reg 131=(Naming.push a digit:ℤ) ∧ t.mem=s.mem:=by
  let pre:List Code:=[lshift 275 128 1,setc 277 1,add 274 275 277,cp 128 274]
  let u:=actPrefix pre s
  have us:u.reg 128=(Naming.push a 0:ℤ):=by
    simp [u,pre,actPrefix,action,lshift,seqs,cp,add,setc,IOp.act,Banks.put,value,Naming.push];ring
  let v:=(IOp.dec 279).act ((IOp.copy 279 129).act ((IOp.set 130 0).act u))
  have endv:v.reg 279=(0:ℤ)+(digit:ℤ)-1:=by simp [v,IOp.act,Banks.put,show u.reg 129=s.reg 129 by rfl,arg]
  obtain ⟨t,z,loop,bound,out,frame⟩:=repeat_digit a 0 digit v rfl endv us
  have doLoop:Steps (forN 130 279 129 (seqs [add 280 128 128,cp 128 280])) u t
      (1+1+(1+1+(1+1+(1+z+1)))):=
    .seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.seq loop (.skip _))))
  let y:=(IOp.copy 131 128).act t
  have last:Steps (seqs [forN 130 279 129 (seqs [add 280 128 128,cp 128 280]),cp 131 128]) u y _ :=
    .seq doLoop (.seq (.atom _ _) (.skip _))
  have ex:=prepend_steps pre _ s _ _ (by decide) last
  have sz:costPrefix pre≤20:=by decide
  change Steps proc_code_name_push s y _ at ex
  refine ⟨costPrefix pre+(1+(1+1+(1+1+(1+1+(1+z+1))))+(1+1+1)),y,?_,?_,?_,frame⟩
  · exact (show costPrefix pre+(1+(1+1+(1+1+(1+1+(1+z+1))))+(1+1+1))≤48*(1+digit) by omega)
  · simpa [run] using ex.schedule [] 0
  · change t.reg 128=_;simpa using out
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM


open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
theorem solution (s:Banks) (a digit:ℕ) (value:s.reg 128=(a:ℤ)) (arg:s.reg 129=(digit:ℤ)) :
    ∃F t,F≤48*(1+digit) ∧ run F [proc_code_name_push] s=some t ∧
      t.reg 131=(Naming.push a digit:ℤ) ∧ t.mem=s.mem := CandidateRAM.name_push_run s a digit value arg
