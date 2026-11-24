-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.native_tight_key_encoder
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T23:49:17.791727+00:00
-- url     : https://prove2.me/submissions/fa2c2591-9379-4a2a-84e6-bfbf75b3300a

import Definitions.Def_StableMSR_UnfilteredSeparatorCandidates
set_option linter.all false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
namespace StableMSR.Recovery.NativeWriter.Relative.Machine
open Compiler
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 14000
def line : List Op → Cmd | []=>.skip | o::os=>.seq (.atom o) (line os)
noncomputable def perform {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) : List Op → Store
  | []=>s | o::os=>perform d (o.eval d s) os
theorem line_exec {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (os : List Op) :
    Executes d (line os) s (perform d s os) os.length := by
  induction os generalizing s with
  | nil=>exact .skip _
  | cons o os ih=>simpa only [line,perform,List.length_cons,Nat.add_comm 1] using Executes.seq (.atom o s) (ih (o.eval d s))

end StableMSR.Recovery.NativeWriter.Relative.Machine
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.KeyCode
open SingleCircuit
set_option autoImplicit false

def pairs (a:Assignment) := a.flatMap (fun q=>[q.1,q.2])
def digits (key:Key) := key.1.map Nat.succ ++ [0] ++ pairs key.2
def push (a:ℕ) : ℕ→ℕ | 0=>2*a+1 | z+1=>2*push a z
def code : List ℕ→ℕ | []=>0 | z::zs=>push (code zs) z
def name (key:Key) := code (digits key).reverse

theorem push_pos (a z:ℕ) : 0<push a z := by induction z <;> simp [push] <;> omega
theorem push_inj (a b x y:ℕ) (h:push a x=push b y) : a=b ∧ x=y := by
  induction x generalizing y with
  | zero=>cases y <;> simp only [push] at h <;> omega
  | succ x ih=>
    cases y with
    | zero=>simp only [push] at h;omega
    | succ y=>
      simp only [push] at h
      obtain ⟨eq,eq'⟩:=ih y (by omega);exact ⟨eq,by omega⟩

theorem code_inj : Function.Injective code := by
  intro xs;induction xs with
  | nil=>
    intro ys h;cases ys with
    | nil=>rfl
    | cons y ys=>have :=push_pos (code ys) y;change 0=push (code ys) y at h;omega
  | cons x xs ih=>
    intro ys h;cases ys with
    | nil=>have :=push_pos (code xs) x;change push (code xs) x=0 at h;omega
    | cons y ys=>
      obtain ⟨tail,eq⟩:=push_inj _ _ _ _ h
      rw [eq,ih tail]

theorem pair_inj : Function.Injective pairs := by
  intro xs;induction xs with
  | nil=>intro ys h;cases ys <;> simp_all [pairs]
  | cons p xs ih=>
    intro ys h;cases ys with
    | nil=>simp [pairs] at h
    | cons q ys=>
      change p.1::p.2::pairs xs=q.1::q.2::pairs ys at h
      simp only [List.cons.injEq] at h
      rw [Prod.ext h.1 h.2.1,ih h.2.2]

theorem split_digits (c c' a a':List ℕ)
    (h:c.map Nat.succ++(0::a)=c'.map Nat.succ++(0::a')) : c=c' ∧ a=a' := by
  induction c generalizing c' with
  | nil=>cases c' <;> simp_all
  | cons p c ih=>
    cases c' with
    | nil=>simp at h
    | cons q c'=>
      simp only [List.map_cons,List.cons_append,List.cons.injEq,Nat.succ.injEq] at h
      obtain ⟨he,ha⟩:=ih c' h.2;exact ⟨by rw [h.1,he],ha⟩

theorem name_injective : Function.Injective name := by
  rintro ⟨c,a⟩ ⟨c',a'⟩ h
  have eq:=congrArg List.reverse (code_inj h)
  simp only [List.reverse_reverse,digits,List.append_assoc,List.singleton_append] at eq
  obtain ⟨cEq,aEq⟩:=split_digits _ _ _ _ eq
  exact Prod.ext cEq (pair_inj aEq)

theorem accumulated (xs:List ℕ) : xs.foldl push 0=code xs.reverse := by
  induction xs using List.reverseRecOn with
  | nil=>rfl
  | append_singleton xs a ih=>simp [List.foldl_append,ih,code]

end StableMSR.Recovery.NativeWriter.Production.Candidates.KeyCode
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.KeyCode
open Compiler OracleQueries Relative.Machine SingleCircuit
set_option autoImplicit false
set_option maxHeartbeats 1400000

def initialOps : List Op := [.pointerConst 6 0,.pointerConst 8 (inputCell 6 0),.integerLoad 8 8,
  .pointerConst 9 (inputCell 7 0),.pointerConst 10 512,.pointerConst 11 1]
def headOps : List Op := [.integerLoad 12 9,.pointerAdd 6 6 6,.pointerInc 6]
def doubleOps : List Op := [.pointerAdd 6 6 6,.pointerDec 12]
def doubleLoop := Cmd.whileDo (.pointerLE 11 12) (line doubleOps)
def tailOps : List Op := [.pointerSub 9 9 10,.pointerDec 8]
def digitCmd := Cmd.seq (line headOps) (.seq doubleLoop (line tailOps))
def scan := Cmd.whileDo (.pointerLE 11 8) digitCmd
def command := Cmd.seq (line initialOps) scan

theorem push_eq (a z:ℕ) : push a z=2^z*(2*a+1) := by
  induction z with
  | zero=>simp [push]
  | succ z ih=>simp [push,ih,pow_succ];ring

theorem double_run {n:ℕ} (d:Point n→Point n→ℝ) (s:Store) (z:ℕ) (one:s.ptrs 11=1) (counter:s.ptrs 12=(z:ℤ)) :
    ∃t,Executes d doubleLoop s t (2+4*z) ∧ t.imem=s.imem ∧
      (∀j,j≠6 → j≠12 → t.ptrs j=s.ptrs j) ∧ t.ptrs 6=(2:ℤ)^z*s.ptrs 6 := by
  induction z generalizing s with
  | zero=>refine ⟨s,.while_false (by change ¬s.ptrs 11 ≤ s.ptrs 12;rw [one,counter];decide),rfl,fun _ _ _=>rfl,?_⟩;simp
  | succ z ih=>
    let q:=perform d s doubleOps
    have reg (j:ℕ) (a:j≠6) (b:j≠12) : q.ptrs j=s.ptrs j:=by simp [q,doubleOps,perform,Op.eval,Function.update_of_ne,a,b]
    have cnt:q.ptrs 12=(z:ℤ):=by simp [q,doubleOps,perform,Op.eval,counter]
    have v:q.ptrs 6=s.ptrs 6+s.ptrs 6:=by simp [q,doubleOps,perform,Op.eval]
    obtain ⟨t,ex,mem,old,r⟩:=ih q ((reg 11 (by decide) (by decide)).trans one) cnt
    have yes:(Cond.pointerLE 11 12).test s:=by change s.ptrs 11 ≤ s.ptrs 12;rw [one,counter];omega
    refine ⟨t,?_,mem,fun j a b=>(old j a b).trans (reg j a b),?_⟩
    · have ex':=Executes.while_true yes (line_exec d s doubleOps) ex
      have same : 2+4*(z+1)=1+doubleOps.length+1+(2+4*z):=by simp [doubleOps];omega
      rw [same];exact ex'
    · rw [r,v,pow_succ];ring

structure Cursor (s:Store) (i rem acc:ℕ) : Prop where
  atIndex : s.ptrs 9=inputCell 7 i
  remaining : s.ptrs 8=(rem:ℤ)
  stride : s.ptrs 10=512
  one : s.ptrs 11=1
  value : s.ptrs 6=(acc:ℤ)

theorem input_stride (i:ℕ) : inputCell 7 (i+1)=inputCell 7 i-512:=by simp [inputCell,cell,word];ring

theorem digit_run {n:ℕ} (d:Point n→Point n→ℝ) (s:Store) (i rem a z:ℕ)
    (st:Cursor s i (rem+1) a) (val:s.imem (inputCell 7 i)=(z:ℤ)) :
    ∃t,Executes d digitCmd s t (7+4*z) ∧ Cursor t (i+1) rem (push a z) ∧
      t.imem=s.imem ∧ ∀j<6,t.ptrs j=s.ptrs j := by
  let b:=perform d s headOps
  have br (j:ℕ) (h:j≠6) (h':j≠12) : b.ptrs j=s.ptrs j:=by
    simp [b,headOps,perform,Op.eval,Function.update_of_ne,h,h']
  have v:b.ptrs 6=(a:ℤ)+(a:ℤ)+1:=by simp [b,headOps,perform,Op.eval,st.value]
  have digit:b.ptrs 12=(z:ℤ):=by simp [b,headOps,perform,Op.eval,st.atIndex,val]
  obtain ⟨q,dbl,mq,rq,va⟩:=double_run d b z ((br 11 (by decide) (by decide)).trans st.one) digit
  have qr (j:ℕ) (h:j≠6) (h':j≠12) : q.ptrs j=s.ptrs j:=(rq j h h').trans (br j h h')
  let t:=perform d q tailOps
  have tr (j:ℕ) (h:j≠9) (h':j≠8) : t.ptrs j=q.ptrs j:=by
    simp [t,tailOps,perform,Op.eval,Function.update_of_ne,h,h']
  have ti:t.ptrs 9=inputCell 7 (i+1):=by
    simp [t,tailOps,perform,Op.eval,qr 9 (by decide) (by decide),qr 10 (by decide) (by decide),st.atIndex,st.stride,input_stride]
  have tc:t.ptrs 8=(rem:ℤ):=by simp [t,tailOps,perform,Op.eval,qr 8 (by decide) (by decide),st.remaining]
  refine ⟨t,?_,⟨ti,tc,?_,?_,?_⟩,mq,fun j hj=>(tr j (by omega) (by omega)).trans (qr j (by omega) (by omega))⟩
  · have ex:=Executes.seq (line_exec d s headOps) (Executes.seq dbl (line_exec d q tailOps))
    have same:7+4*z=headOps.length+(2+4*z+tailOps.length):=by simp [headOps,tailOps];omega
    rw [same];exact ex
  · exact (tr 10 (by decide) (by decide)).trans ((qr 10 (by decide) (by decide)).trans st.stride)
  · exact (tr 11 (by decide) (by decide)).trans ((qr 11 (by decide) (by decide)).trans st.one)
  · rw [tr 6 (by decide) (by decide),va,v,push_eq];push_cast;ring

end StableMSR.Recovery.NativeWriter.Production.Candidates.KeyCode
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.KeyCode
open Compiler OracleQueries Relative.Machine SingleCircuit
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem scan_run {n:ℕ} (d:Point n→Point n→ℝ) (xs:List ℕ) (s:Store) (i a:ℕ)
    (st:Cursor s i xs.length a) (input:∀j (hj:j<xs.length),s.imem (inputCell 7 (i+j))=(xs[j]:ℤ)) :
    ∃t,Executes d scan s t (2+9*xs.length+4*xs.sum) ∧ t.imem=s.imem ∧
      (∀j<6,t.ptrs j=s.ptrs j) ∧ t.ptrs 6=((xs.foldl push a:ℕ):ℤ) := by
  induction xs generalizing s i a with
  | nil=>
    have neg:¬(Cond.pointerLE 11 8).test s:=by change ¬s.ptrs 11 ≤ s.ptrs 8;rw [st.one,st.remaining];decide
    exact ⟨s,.while_false neg,rfl,fun _ _=>rfl,st.value⟩
  | cons z zs ih=>
    have val:s.imem (inputCell 7 i)=(z:ℤ):=by
      have hx:=input 0 (by simp);change s.imem (inputCell 7 (i+0))=(z:ℤ) at hx;simpa using hx
    obtain ⟨q,dx,cursor,mem,low⟩:=digit_run d s i zs.length a z st val
    have input':∀j (hj:j<zs.length),q.imem (inputCell 7 (i+1+j))=(zs[j]:ℤ):=by
      intro j hj;rw [mem];have hx:=input (j+1) (by simpa using hj)
      change s.imem (inputCell 7 (i+(j+1)))=(zs[j]:ℤ) at hx;simpa [Nat.add_assoc,Nat.add_comm 1 j] using hx
    obtain ⟨t,ex,fr,rg,res⟩:=ih q (i+1) (push a z) cursor input'
    have yes:(Cond.pointerLE 11 8).test s:=by change s.ptrs 11 ≤ s.ptrs 8;rw [st.one,st.remaining];simp
    have clock:2+9*(z::zs).length+4*(z::zs).sum=1+(7+4*z)+1+(2+9*zs.length+4*zs.sum):=by
      simp;omega
    refine ⟨t,?_,fr.trans mem,fun j hj=>(rg j hj).trans (low j hj),res⟩
    rw [clock];exact Executes.while_true yes dx ex

theorem encoder : ∃enc:Key→ℕ,Function.Injective enc ∧ ∃(A:ℕ) (cmd:Cmd),∀(x:World) (s:Store) (key:Key),
    let ds:=digits key
    Ready x s → s.imem (inputCell 6 0)=(ds.length:ℤ) →
    (∀j (hj:j<ds.length),s.imem (inputCell 7 j)=(ds[j]:ℤ)) →
    ∃t z,Executes x.dist cmd s t z ∧ z≤A*(1+ds.length+ds.sum) ∧ t.imem=s.imem ∧
      (∀j<6,t.ptrs j=s.ptrs j) ∧ t.ptrs 6=(enc key:ℤ) := by
  refine ⟨name,name_injective,9,command,?_⟩
  intro x s key
  dsimp only
  intro _ count source
  let ds:=digits key
  let b:=perform x.dist s initialOps
  have st:Cursor b 0 ds.length 0:=by
    constructor <;> simp [b,initialOps,perform,Op.eval,ds] <;> exact count
  have lo (j:ℕ) (hj:j<6) : b.ptrs j=s.ptrs j:=by
    simp [b,initialOps,perform,Op.eval,Function.update_of_ne (by omega:j≠6),Function.update_of_ne (by omega:j≠8),
      Function.update_of_ne (by omega:j≠9),Function.update_of_ne (by omega:j≠10),Function.update_of_ne (by omega:j≠11)]
  obtain ⟨t,go,mem,reg,out⟩:=scan_run x.dist ds b 0 0 st (by intro j hj;simpa [b,initialOps,perform,Op.eval] using source j hj)
  refine ⟨t,_,.seq (line_exec x.dist s initialOps) go,?_,mem,fun j hj=>(reg j hj).trans (lo j hj),?_⟩
  · change initialOps.length+(2+9*ds.length+4*ds.sum)≤9*(1+ds.length+ds.sum)
    simp [initialOps];omega
  · rw [out,accumulated];rfl

end StableMSR.Recovery.NativeWriter.Production.Candidates.KeyCode
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates
theorem solution :
  ∃enc:Key→ℕ,Function.Injective enc ∧ ∃(A:ℕ) (cmd:Cmd),∀(x:World) (s:Store) (key:Key),
    let digits:=key.1.map Nat.succ ++ [0] ++ key.2.flatMap (fun q=>[q.1,q.2])
    Ready x s → s.imem (inputCell 6 0)=(digits.length:ℤ) →
    (∀j (hj:j<digits.length),s.imem (inputCell 7 j)=((digits[j]:ℕ):ℤ)) →
    ∃t z,Executes x.dist cmd s t z ∧ z≤A*(1+digits.length+digits.sum) ∧ t.imem=s.imem ∧
      (∀j<6,t.ptrs j=s.ptrs j) ∧ t.ptrs 6=(enc key:ℤ) := StableMSR.Recovery.NativeWriter.Production.Candidates.KeyCode.encoder
