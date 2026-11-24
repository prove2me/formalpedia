-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.menu_word_schedule_and_digits
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T21:00:38.818854+00:00
-- url     : https://prove2.me/submissions/3fc52dea-74b5-48d2-aa51-b7c48d3bb1d9

import Definitions.Def_StableMSR_InitializedSeparatorTraversal
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

section
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option linter.all false
set_option maxRecDepth 35000
set_option maxHeartbeats 4100000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 35000
theorem source_loop {N:ℕ} {input:ℤ → ℤ} (ix last n cap:ℕ) (body:Program) (P:ℕ→State→Prop) (ne:ix≠last)
    (step:∀i<n,∀s:State,P i s → s.reg ix=(i:ℤ) → s.reg last=(n:ℤ)-1 →
      ∃t k,Executes N input body s t k ∧ k≤cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1)))
    (i rem:ℕ) (len:i+rem=n) (s:State) (start:P i s) (idx:s.reg ix=(i:ℤ)) (lim:s.reg last=(n:ℤ)-1) :
    ∃t k,Executes N input (.loop ix last (chain [body,.op (.regular (.inc ix))])) s t k ∧ k≤1+rem*(cap+5) ∧ P n t :=by
  induction rem generalizing i s with
  | zero=>
    have eq:i=n:=by omega
    exact ⟨s,1,.stop (by rw [idx,lim];omega),by omega,eq ▸ start⟩
  | succ r ih=>
    have lt:i<n:=by omega
    obtain ⟨u,k,ex,tim,idx',lim',next⟩:=step i lt s start idx lim
    let v:=u.assign ix (u.reg ix+1)
    have vi:v.reg ix=((i+1:ℕ):ℤ):=by simp [v,State.assign,idx',idx]
    have vl:v.reg last=(n:ℤ)-1:=by simp [v,State.assign,Ne.symm ne,lim',lim]
    obtain ⟨t,z,more,tm,out⟩:=ih (i+1) (by omega) v next vi vl
    have full:Executes N input (chain [body,.op (.regular (.inc ix))]) s v (1+k+(1+1+1)):=.seq ex (.seq (.op rfl) (.skip _))
    exact ⟨t,_,.more (by rw [idx,lim];omega) full more,by rw [Nat.succ_mul];omega,out⟩

def forSetup (ix last len:ℕ) (s:State) := let u:=s.assign ix 0; let v:=u.assign last (u.reg len);v.assign last (v.reg last-1)
theorem source_for {N:ℕ} {input:ℤ → ℤ} (ix last len n cap:ℕ) (body:Program) (P:ℕ→State→Prop)
    (ne:ix≠last) (dis:len≠ix) (s:State) (size:s.reg len=(n:ℤ))
    (start:P 0 (forSetup ix last len s))
    (step:∀i<n,∀s:State,P i s → s.reg ix=(i:ℤ) → s.reg last=(n:ℤ)-1 →
      ∃t k,Executes N input body s t k ∧ k≤cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1))) :
    ∃t k,Executes N input (forCount ix last len body) s t k ∧ k≤9+n*(cap+5) ∧ P n t :=by
  let u:=forSetup ix last len s
  have fi:u.reg ix=0:=by simp [u,forSetup,State.assign,ne]
  have last':u.reg last=(n:ℤ)-1:=by simp [u,forSetup,State.assign,dis,size]
  obtain ⟨t,z,loop,tm,out⟩:=source_loop ix last n cap body P ne step 0 n (by omega) u start fi last'
  refine ⟨t,_,.seq (.op rfl) (.seq (.op rfl) (.seq (.op rfl) (.seq loop (.skip _)))),by omega,out⟩


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
inductive PrefixRun (N:ℕ) (input:ℤ → ℤ) : List Program → State → State → ℕ → Prop where
  | nil (s:State) : PrefixRun N input [] s s 0
  | cons {p ps s u t a z} : Executes N input p s u a → PrefixRun N input ps u t z →
    PrefixRun N input (p::ps) s t (1+a+z)
theorem PrefixRun.continue {N input ps s t z} (h:PrefixRun N input ps s t z)
    (q:Program) {u k} (tail:Executes N input q t u k):
    Executes N input (ps.foldr Program.seq q) s u (z+k):=by
  induction h with
  | nil=>simpa using tail
  | cons run _ ih=>
    simpa [Nat.add_assoc] using Executes.seq run (ih tail)
theorem PrefixRun.finish {N input ps s t z} (h:PrefixRun N input ps s t z):
    Executes N input (chain ps) s t (z+1):=h.continue .skip (.skip t)
end Logical
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
def evalLine (n:ℕ) (m:ℤ → ℤ) : Program → State → Option (State×ℕ)
  | .skip,s=>some (s,1)
  | .op o,s=>o.next n m s
  | .seq p q,s=>do
    let (u,a)←evalLine n m p s
    let (t,b)←evalLine n m q u
    pure (t,1+a+b)
  | .cond i j p q,s=>do
    let (t,b)←if s.reg i ≤ s.reg j then evalLine n m p s else evalLine n m q s
    pure (t,1+b)
  | .loop _ _ _,_=>none
theorem evalLine_sound {n m} (p:Program) (s t:State) (k:ℕ) (ex:evalLine n m p s=some (t,k)):
    Executes n m p s t k:=by
  induction p generalizing s t k with
  | skip=>obtain ⟨rfl,rfl⟩:=Option.some.inj ex;exact .skip _
  | op=>exact .op ex
  | loop=>contradiction
  | seq p q a b=>
    cases h:evalLine n m p s with
    | none=>simp [evalLine,h] at ex
    | some z=>
      obtain ⟨u,au⟩:=z
      cases j:evalLine n m q u with
      | none=>simp [evalLine,h,j] at ex
      | some v=>obtain ⟨v,bu⟩:=v;simp [evalLine,h,j] at ex;obtain ⟨rfl,rfl⟩:=ex
                exact .seq (a _ _ _ h) (b _ _ _ j)
  | cond i j p q a b=>
    by_cases g:s.reg i ≤ s.reg j
    · cases h:evalLine n m p s with
      | none=>simp [evalLine,g,h] at ex
      | some z=>obtain ⟨u,au⟩:=z;simp [evalLine,g,h] at ex;obtain ⟨rfl,rfl⟩:=ex;exact .yes g (a _ _ _ h)
    · cases h:evalLine n m q s with
      | none=>simp [evalLine,g,h] at ex
      | some z=>obtain ⟨u,au⟩:=z;simp [evalLine,g,h] at ex;obtain ⟨rfl,rfl⟩:=ex;exact .no g (b _ _ _ h)

def writesOp (j:ℕ) : Operation → Bool
  | .regular (.store _ _)|.save _ _ _=>false
  | .regular (.set d _)|.regular (.copy d _)|.regular (.add d _ _)|.regular (.sub d _ _)|
    .regular (.inc d)|.regular (.dec d)|.regular (.load d _)|.multiply d _ _|.divide _ d _ _|
    .fetch d _ _|.shift d _ _=>j==d
  | .alloc d _=>j==d || j==8
  | .output=>j==82
def writesReg (j:ℕ) : Program → Bool
  | .skip=>false | .op o=>writesOp j o | .seq p q|.cond _ _ p q=>writesReg j p || writesReg j q
  | .loop _ _ p=>writesReg j p
theorem op_preserves {n input s t k} (o:Operation) (j:ℕ) (frame:writesOp j o=false)
    (ex:o.next n input s=some (t,k)):t.reg j=s.reg j:=by
  cases o with
  | regular o=>
    cases o <;> simp [writesOp] at frame <;> simp only [Operation.next,regularNext] at ex <;>
      (try split at ex) <;> (try contradiction) <;> obtain ⟨rfl,rfl⟩:=Option.some.inj ex <;> simp [State.assign,frame]
  | multiply|divide|shift|fetch|save|alloc|output=>
    simp [writesOp] at frame
    simp only [Operation.next] at ex
    (try split at ex) <;> (try contradiction) <;> obtain ⟨rfl,rfl⟩:=Option.some.inj ex <;>
      simp_all [State.assign,State.clear,State.save]
theorem Executes.preserves {n input p s t k} (ex:Executes n input p s t k) (j:ℕ) (off:writesReg j p=false):
    t.reg j=s.reg j:=by
  induction ex with
  | skip|stop=>rfl
  | op h=>exact op_preserves _ _ off h
  | seq _ _ ih jh=>obtain ⟨a,b⟩:=Bool.or_eq_false_iff.mp off;exact (jh b).trans (ih a)
  | yes _ _ ih=>exact ih (Bool.or_eq_false_iff.mp off).1
  | no _ _ ih=>exact ih (Bool.or_eq_false_iff.mp off).2
  | more _ _ _ ih jh=>exact (jh off).trans (ih off)
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
open scoped Classical
theorem splitChain {N input} (ps:List Program) {s t:State} {k:ℕ} (ex:Executes N input (chain ps) s t k) :
    ∃z,PrefixRun N input ps s t z ∧ k=z+1:=by
  induction ps generalizing s t k with
  | nil=>cases ex;exact ⟨0,.nil _,rfl⟩
  | cons p ps ih=>
    change Executes N input (.seq p (chain ps)) s t k at ex
    cases ex with
    | seq left right=>
      obtain ⟨z,e,h⟩:=ih right
      exact ⟨_,.cons left e,by omega⟩
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM



end
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option linter.all false
set_option maxRecDepth 35000
set_option maxHeartbeats 4100000
set_option autoImplicit false

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
/-- Registers outside the write set retain the values with which the loop started. -/
lemma outside_for {ix last len r : ℕ} {body : Program}
    (off : writesReg r (forCount ix last len body) = false) :
    r ≠ ix ∧ r ≠ last ∧ writesReg r body = false := by
  simpa [forCount,chain,writesReg,writesOp,and_assoc,and_left_comm,and_comm] using off

lemma counted {n : ℕ} {m : ℤ → ℤ} (ix last len count cap : ℕ) (body : Program)
    (s : State) (P : ℕ → State → Prop) (ne : ix ≠ last) (dis : len ≠ ix)
    (ixSafe : writesReg ix body = false) (lastSafe : writesReg last body = false)
    (size : s.reg len = (count : ℤ)) (init : P 0 s)
    (ignores : ∀ j u a v, a = ix ∨ a = last → P j u → P j (u.assign a v))
    (step : ∀ i < count, ∀ u, P i u →
      (∀ r, writesReg r (forCount ix last len body) = false → u.reg r = s.reg r) →
      u.reg ix = (i : ℤ) → ∃ t k, Executes n m body u t k ∧ k ≤ cap ∧ P (i+1) t) :
    ∃ t k, Executes n m (forCount ix last len body) s t k ∧
      k ≤ 9+count*(cap+5) ∧ P count t := by
  let Q := fun j u => P j u ∧ ∀ r, writesReg r (forCount ix last len body) = false → u.reg r = s.reg r
  have start : Q 0 (forSetup ix last len s) := by
    refine ⟨ignores _ _ _ _ (.inr rfl) (ignores _ _ _ _ (.inr rfl) (ignores _ _ _ _ (.inl rfl) init)),?_⟩
    intro r off
    obtain ⟨a,b,_⟩ := outside_for off
    simp [forSetup,State.assign,a,b]
  obtain ⟨t,k,run,tm,res,_⟩ := source_for (N:=n) (input:=m) ix last len count cap body Q ne dis s size start (by
    intro i hi u good idx _
    obtain ⟨t,k,ex,tm,next⟩ := step i hi u good.1 good.2 idx
    refine ⟨t,k,ex,tm,ex.preserves _ ixSafe,ex.preserves _ lastSafe,ignores _ _ _ _ (.inl rfl) next,?_⟩
    intro r off
    obtain ⟨a,_,b⟩ := outside_for off
    simpa [State.assign,a] using (ex.preserves r b).trans (good.2 r off))
  exact ⟨t,k,run,tm,res⟩


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.MenuWordProof
private lemma wordList_length (H R : ℕ) (f : ℕ → ℕ → ℕ) :
    ((List.range H).flatMap (fun g=>(List.range R).map (f g))).length=H*R := by
  induction H with
  | zero => simp
  | succ H ih => simp [List.range_succ,List.flatMap_append,ih,Nat.succ_mul]

private lemma wordList_cell (H R g u : ℕ) (f : ℕ → ℕ → ℕ) (hg:g<H) (hu:u<R) :
    ((List.range H).flatMap (fun q=>(List.range R).map (f q)))[g*R+u]?=some (f g u) := by
  induction H with
  | zero => omega
  | succ H ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton]
    by_cases inside:g<H
    · rw [List.getElem?_append_left]
      · exact ih inside
      · rw [wordList_length]
        calc g*R+u < g*R+R := Nat.add_lt_add_left hu _
             _ = (g+1)*R := by ring
             _ ≤ H*R := Nat.mul_le_mul_right _ inside
    · have eq:g=H := by omega
      subst g
      rw [List.getElem?_append_right (by rw [wordList_length]; omega),wordList_length,Nat.add_sub_cancel_left,
        List.getElem?_map,List.getElem?_range hu]
      rfl

private def dispatchLine : Logical.Program := Logical.chain [
  .op (.divide false 762 196 69),.op (.multiply 761 762 68),
  .op (.divide true 766 196 69),.op (.regular (.add 760 761 766)),
  .op (.regular (.copy 199 760)),.op (.save 76 196 199)]


theorem dispatch_sound
    (n h g u base : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (hn : 0<n) (hg : g<h+1) (hu : u<CartesianBallRows.rows n (h+1))
    (one : s.reg 6=1) (height : s.reg 68=((h+1:ℕ):ℤ))
    (rowCount : s.reg 69=(CartesianBallRows.rows n (h+1):ℤ))
    (ptr : s.reg 76=(base:ℤ)) (ix : s.reg 196=((g*CartesianBallRows.rows n (h+1)+u:ℕ):ℤ)) :
    let R:=CartesianBallRows.rows n (h+1)
    let i:=g*R+u
    let c:=SingleCodes.encode h g u
    let dispatch:=match (Logical.listOf ((Logical.listOf Logical.src_build_geometry)[24]?.getD .skip))[3]? with
      | some (Logical.Program.loop _ _ body) => Logical.chain ((Logical.listOf ((Logical.listOf body)[0]?.getD .skip)).take 6)
      | _ => Logical.Program.skip
    (SingleCodes.words n h)[i]?=some c ∧
      ∃t k, Logical.Executes n m dispatch s t k ∧ k≤180+22*(h+1) ∧
        t.reg 199=(c:ℤ) ∧ t.heap=Function.update s.heap (base+i) (c:ℤ) ∧ t.output=s.output ∧ t.closed=s.closed := by
  let R := CartesianBallRows.rows n (h+1)
  let i := g*R+u
  let c := SingleCodes.encode h g u
  have positive : 0<R := by omega
  have div : i/R=g := by
    dsimp [i]; rw [Nat.add_comm,Nat.add_mul_div_right _ _ positive,Nat.div_eq_of_lt hu,zero_add]
  have rem : i%R=u := by dsimp [i]; rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hu]
  constructor
  · exact wordList_cell (h+1) R g u (SingleCodes.encode h) hg hu
  change ∃ t k,Executes n m dispatchLine s t k ∧ k≤180+22*(h+1) ∧
    t.reg 199=(c:ℤ) ∧ t.heap=Function.update s.heap (base+i) (c:ℤ) ∧ t.output=s.output ∧ t.closed=s.closed
  change s.reg 69=(R:ℤ) at rowCount
  change s.reg 196=(i:ℤ) at ix
  have h : ∃t k,evalLine n m dispatchLine s=some (t,k) ∧ k≤180+22*(h+1) ∧
      t.reg 199=(c:ℤ) ∧ t.heap=Function.update s.heap (base+i) (c:ℤ) ∧ t.output=s.output ∧ t.closed=s.closed := by
    have posZ : 0<(R:ℤ) := by exact_mod_cast positive
    have di : (i:ℤ)/(R:ℤ)=(g:ℤ) := by exact_mod_cast div
    have md : (i:ℤ)%(R:ℤ)=(u:ℤ) := by exact_mod_cast rem
    simp [dispatchLine,chain,evalLine,Operation.next,regularNext,State.assign,State.save,one,height,rowCount,ix,ptr,
      posZ,positive,show 0 ≤ (h:ℤ)+1 by omega,di,md,div,rem,c,SingleCodes.encode,show 0 ≤ (base:ℤ)+i by omega,show ((base:ℤ)+i).toNat=base+i by omega] <;> omega
  obtain ⟨t,k,ev,tm,facts⟩ := h
  exact ⟨t,k,evalLine_sound _ _ _ _ ev,tm,facts⟩

private def digitLine : Program := chain [.op (.divide false 434 167 64), .op (.save 166 168 434),
  .op (.divide true 437 167 64),.op (.regular (.copy 167 437))]

private def digitSetup : List Program := [.op (.divide true 425 163 68),.op (.regular (.copy 167 425)),.op (.shift 428 68 1)]

private lemma step_digit (n q base j : ℕ) (m:ℤ→ℤ) (s:State) (hn:0<n) (one:s.reg 6=1) (size:s.reg 64=(n:ℤ))
    (pointer:s.reg 166=(base:ℤ)) (quot:s.reg 167=(q:ℤ)) (index:s.reg 168=(j:ℤ)) :
    ∃t k,Executes n m digitLine s t k ∧ k≤150+16*q ∧ t.reg 167=((q/n:ℕ):ℤ) ∧
      t.heap=Function.update s.heap (base+j) ((q%n:ℕ):ℤ) ∧ t.output=s.output ∧ t.closed=s.closed := by
  have ev : ∃t k,evalLine n m digitLine s=some (t,k) ∧ k≤150+16*q ∧ t.reg 167=((q/n:ℕ):ℤ) ∧
      t.heap=Function.update s.heap (base+j) ((q%n:ℕ):ℤ) ∧ t.output=s.output ∧ t.closed=s.closed := by
    have small := Nat.div_le_self q n
    have eqd : (q:ℤ)/(n:ℤ)=((q/n:ℕ):ℤ) := by exact_mod_cast (rfl : q/n=q/n)
    have eqm : (q:ℤ)%(n:ℤ)=((q%n:ℕ):ℤ) := by exact_mod_cast (rfl : q%n=q%n)
    simp [digitLine,chain,evalLine,Operation.next,regularNext,State.assign,State.save,hn,one,size,pointer,quot,index,
      show 0 ≤ (base:ℤ)+j by omega,show ((base:ℤ)+j).toNat=base+j by omega] <;> omega
  obtain ⟨t,k,e,tm,p⟩ := ev
  exact ⟨t,k,evalLine_sound _ _ _ _ e,tm,p⟩

private lemma start_digits (n h g u : ℕ) (m:ℤ→ℤ) (s:State) (hg:g<h+1) (one:s.reg 6=1)
    (height:s.reg 68=((h+1:ℕ):ℤ)) (code:s.reg 163=(SingleCodes.encode h g u:ℤ)) :
    ∃t k,Executes n m (chain digitSetup) s t k ∧ k≤46+8*u ∧ t.reg 167=(u:ℤ) ∧
      t.reg 428=((2*(h+1):ℕ):ℤ) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  let c := SingleCodes.encode h g u
  have div : c/(h+1)=u := by
    dsimp [c,SingleCodes.encode]; rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt hg,zero_add]
  have di : (c:ℤ)/((h+1:ℕ):ℤ)=(u:ℤ) := by exact_mod_cast div
  change s.reg 163=(c:ℤ) at code
  have ev : ∃t k,evalLine n m (chain digitSetup) s=some (t,k) ∧ k≤46+8*u ∧ t.reg 167=(u:ℤ) ∧
      t.reg 428=((2*(h+1):ℕ):ℤ) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
    have H : 0<(h:ℤ)+1 := by omega
    simp [digitSetup,chain,evalLine,Operation.next,regularNext,State.assign,one,height,code,
      H,div,show (c:ℤ)/((h:ℤ)+1)=(u:ℤ) by simpa using di] <;> omega
  obtain ⟨t,k,e,tm,p⟩ := ev
  exact ⟨t,k,evalLine_sound _ _ _ _ e,tm,p⟩


theorem decode_digits
    (n h g u base : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (hn : 0<n) (hg : g<h+1) (hu : u<CartesianBallRows.rows n (h+1))
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (height : s.reg 68=((h+1:ℕ):ℤ))
    (code : s.reg 163=(SingleCodes.encode h g u:ℤ)) (ptr : s.reg 166=(base:ℤ)) :
    let L:=2*(h+1)
    ∃ t k, Logical.Executes n m (Logical.chain (((Logical.listOf Logical.src_data_for_vertex).drop 7).take 4)) s t k ∧
      k ≤ 65+8*u+L*(155+16*u) ∧ t.reg 167=0 ∧
      (∀j<L,t.heap (base+j)=(CartesianBallRows.digit n u j:ℤ)) ∧
      (∀z,z<base ∨ base+L≤z → t.heap z=s.heap z) ∧ t.output=s.output ∧ t.closed=s.closed := by
  let L := 2*(h+1)
  obtain ⟨v,k,setup,kt,uq,sizeL,vh,vo,vc⟩ := start_digits n h g u m s hg one height code
  let P := fun j (t:State) => t.reg 167=((u/n^j:ℕ):ℤ) ∧
    (∀i<j,t.heap (base+i)=(CartesianBallRows.digit n u i:ℤ)) ∧
    (∀z,z<base ∨ base+j≤z → t.heap z=s.heap z) ∧ t.output=s.output ∧ t.closed=s.closed
  obtain ⟨t,l,loop,lt,ans⟩ := GeometryTables.counted (n:=n) (m:=m) 168 430 428 L (150+16*u)
    digitLine v P (by decide) (by decide) (by decide) (by decide) sizeL
    ⟨by simpa using uq,by simp,by intro z _; rw [vh],vo,vc⟩ (by
      intro i t r y hr ok
      obtain ⟨q,c,f,o,b⟩ := ok
      exact ⟨by rcases hr with rfl|rfl <;> simpa [State.assign] using q,c,f,o,b⟩) (by
      intro j hj t ok frame idx
      obtain ⟨quot,history,off,out,cl⟩ := ok
      obtain ⟨t',l,run,tm,next,mem,to',tc⟩ := step_digit n (u/n^j) base j m t hn
        ((frame 6 (by decide)).trans ((setup.preserves 6 (by decide)).trans one))
        ((frame 64 (by decide)).trans ((setup.preserves 64 (by decide)).trans size))
        ((frame 166 (by decide)).trans ((setup.preserves 166 (by decide)).trans ptr)) quot idx
      refine ⟨t',l,run,tm.trans ?_,?_,?_,?_,to'.trans out,tc.trans cl⟩
      · have bound := Nat.div_le_self u (n^j); omega
      · simpa only [Nat.div_div_eq_div_mul,pow_succ] using next
      · intro i hi
        by_cases same:i=j
        · subst i; rw [mem,Function.update_self]; rfl
        · rw [mem,Function.update_of_ne (by omega)]; exact history i (by omega)
      · intro z hz; rw [mem,Function.update_of_ne (by omega)]; exact off z (by omega))
  obtain ⟨q,pr,charge⟩ := splitChain digitSetup setup
  have together : Executes n m (chain (((listOf src_data_for_vertex).drop 7).take 4)) s t _ :=
    pr.continue (.seq (forCount 168 430 428 digitLine) .skip) (.seq loop (.skip t))
  obtain ⟨finalReg,words,frame,out,cl⟩ := ans
  have below : u<n^L := hu
  refine ⟨t,_,together,?_,?_,words,frame,out,cl⟩
  · simp only [L] at lt ⊢; ring_nf at lt ⊢ <;> omega
  · simpa only [Nat.div_eq_of_lt below,Nat.cast_zero] using finalReg

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.MenuWordProof

theorem solution (n h g u : ℕ) (m : ℤ → ℤ)
    (hn : 0<n) (hg : g<h+1) (hu : u<CartesianBallRows.rows n (h+1)) :
  (∀ (base : ℕ) (s : Logical.State), s.reg 6=1 → s.reg 68=((h+1:ℕ):ℤ) →
    s.reg 69=(CartesianBallRows.rows n (h+1):ℤ) → s.reg 76=(base:ℤ) →
    s.reg 196=((g*CartesianBallRows.rows n (h+1)+u:ℕ):ℤ) →
    let R:=CartesianBallRows.rows n (h+1)
    let i:=g*R+u
    let c:=SingleCodes.encode h g u
    let dispatch:=match (Logical.listOf ((Logical.listOf Logical.src_build_geometry)[24]?.getD .skip))[3]? with
      | some (Logical.Program.loop _ _ body) => Logical.chain ((Logical.listOf ((Logical.listOf body)[0]?.getD .skip)).take 6)
      | _ => Logical.Program.skip
    (SingleCodes.words n h)[i]?=some c ∧
      ∃t k, Logical.Executes n m dispatch s t k ∧ k≤180+22*(h+1) ∧
        t.reg 199=(c:ℤ) ∧ t.heap=Function.update s.heap (base+i) (c:ℤ) ∧ t.output=s.output ∧ t.closed=s.closed) ∧
  (∀ (base : ℕ) (s : Logical.State), s.reg 6=1 → s.reg 64=(n:ℤ) → s.reg 68=((h+1:ℕ):ℤ) →
    s.reg 163=(SingleCodes.encode h g u:ℤ) → s.reg 166=(base:ℤ) →
    let L:=2*(h+1)
    ∃ t k, Logical.Executes n m (Logical.chain (((Logical.listOf Logical.src_data_for_vertex).drop 7).take 4)) s t k ∧
      k ≤ 65+8*u+L*(155+16*u) ∧ t.reg 167=0 ∧
      (∀j<L,t.heap (base+j)=(CartesianBallRows.digit n u j:ℤ)) ∧
      (∀z,z<base ∨ base+L≤z → t.heap z=s.heap z) ∧ t.output=s.output ∧ t.closed=s.closed) := by
  constructor
  · intro base s one height count ptr ix
    exact Scene.MenuWordProof.dispatch_sound n h g u base m s hn hg hu one height count ptr ix
  · intro base s one size height code ptr
    exact Scene.MenuWordProof.decode_digits n h g u base m s hn hg hu one size height code ptr
