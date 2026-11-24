-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.scratch_allocation_exact
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T01:29:27.782538+00:00
-- url     : https://prove2.me/submissions/b9ae2480-82d3-4826-afb0-7e4e5f6d037a

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


open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
theorem solution (dst len base L:ℕ) (hd:64≤dst) (hl:64≤len) (ne:dst≠len) (s:Banks)
    (one:s.reg 6=1) (zero:s.reg 7=0) (cursor:s.reg 8=(base:ℤ)) (length:s.reg len=(L:ℤ)) :
    ∃F t,F≤64*(1+L) ∧ run F [allocate dst len] s=some t ∧ t.reg dst=(base:ℤ) ∧ t.reg 8=((base+L:ℕ):ℤ) ∧
    (∀j<L,t.mem (cell 7 (base+j))=0) ∧ ∀q:ℤ,(∀j<L,q≠cell 7 (base+j)) → t.mem q=s.mem q := CandidateRAM.allocate_run dst len base L hd hl ne s one zero cursor length
