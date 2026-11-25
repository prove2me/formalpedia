-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.fill_membership_row
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T04:53:24.630006+00:00
-- url     : https://prove2.me/submissions/7b480d71-8930-4f66-b835-af7a82005d7e

import Definitions.Def_StableMSR_VertexBlockRows
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option maxHeartbeats 4100000
set_option maxRecDepth 35000
set_option autoImplicit false
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
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option maxHeartbeats 4100000
set_option maxRecDepth 35000
set_option autoImplicit false
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows
private def bReads : List Program := [
  .op (.regular (.set 478 1)),
  .op (.regular (.add 476 183 478)),
  .op (.shift 475 476 1),
  .op (.fetch 473 166 475),
  .op (.regular (.copy 178 473)),
  .op (.regular (.set 485 1)),
  .op (.regular (.add 483 183 485)),
  .op (.shift 482 483 1),
  .op (.regular (.set 486 1)),
  .op (.regular (.add 481 482 486)),
  .op (.fetch 479 166 481),
  .op (.regular (.copy 184 479))
]
private def bTests : List Program := [
  .op (.regular (.copy 159 178)),
  .op (.regular (.copy 160 184)),
  src_imat,
  .op (.regular (.copy 487 161)),
  .op (.regular (.copy 185 487)),
  .op (.regular (.copy 159 178)),
  .op (.regular (.copy 160 173)),
  src_imat,
  .op (.regular (.copy 491 161)),
  .cond 491 185 (.op (.regular (.set 490 1))) (.op (.regular (.set 490 0))),
  .op (.regular (.copy 186 490)),
  .op (.regular (.copy 159 178)),
  .op (.regular (.copy 160 174)),
  src_imat,
  .op (.regular (.copy 496 161)),
  .cond 496 185 (.op (.regular (.set 495 1))) (.op (.regular (.set 495 0))),
  .op (.regular (.copy 187 495))
]
private def bFlags : List Program := [
  .cond 6 186 (chain [.op (.regular (.set 501 1)),
                    .op (.regular (.copy 181 501))]) (.skip),
  .cond 6 187 (chain [.op (.regular (.set 503 1)),
                    .op (.regular (.copy 182 503))]) (.skip),
  .op (.regular (.copy 504 186)),
  .cond 6 504 (.op (.regular (.copy 504 187))) (.skip),
  .cond 6 504 (chain [.op (.regular (.set 507 1)),
                    .op (.regular (.copy 180 507))]) (.skip)
]
private def qInit : List Program := [
  .op (.regular (.set 468 0)),
  .op (.regular (.copy 180 468)),
  .op (.regular (.set 469 0)),
  .op (.regular (.copy 181 469)),
  .op (.regular (.set 470 0)),
  .op (.regular (.copy 182 470))
]
private def qFinish : List Program := [
  .cond 6 181 (.op (.regular (.set 509 0))) (.op (.regular (.set 509 1))),
  .op (.regular (.copy 508 509)),
  .cond 6 508 (chain [.cond 6 182 (.op (.regular (.set 511 0))) (.op (.regular (.set 511 1))),
                    .op (.regular (.copy 508 511))]) (.skip),
  .cond 6 508 (chain [.op (.regular (.copy 159 173)),
                    .op (.regular (.copy 160 174)),
                    src_imat,
                    .op (.regular (.copy 514 161)),
                    .op (.regular (.set 520 0)),
                    .op (.fetch 518 166 520),
                    .op (.regular (.set 523 1)),
                    .op (.fetch 521 166 523),
                    .op (.regular (.copy 159 518)),
                    .op (.regular (.copy 160 521)),
                    src_imat,
                    .op (.regular (.copy 517 161)),
                    .cond 514 517 (.op (.regular (.set 513 1))) (.op (.regular (.set 513 0))),
                    .cond 6 513 (chain [.op (.regular (.set 524 1)),
                    .op (.regular (.copy 180 524))]) (.skip)]) (.skip),
  .op (.save 176 174 180)
]
private def qRead : List Program := [
  .op (.fetch 465 170 174)
]
private def bStep := chain (bReads ++ bTests ++ bFlags)
private def qWork := chain (qInit ++ [forCount 183 472 169 bStep] ++ qFinish)
private def qStep := chain (qRead ++ [.cond 6 465 qWork .skip])
private lemma qIdentify : fillBlock = forCount 174 464 64 qStep := by rfl

private lemma concat_run {n m} {l r : List Program} {s t u : State} {k j}
    (a : Executes n m (chain l) s t k) (b : Executes n m (chain r) t u j) :
    ∃ c, Executes n m (chain (l++r)) s u c ∧ c+1=k+j := by
  obtain ⟨c,run,eq⟩ := splitChain l a
  refine ⟨c+j,?_,by omega⟩
  simpa only [chain,List.foldr_append] using run.continue (chain r) b

private lemma matrix_address (n i j : ℕ) : cell 6 (i*n+j) = -87-64*((i:ℤ)*n+j) := by
  simp [cell,word]; ring
private lemma matrix_raw (n i j : ℕ) : rawInput (cell 6 (i*n+j)) = true := by
  have nn : 0 ≤ (i:ℤ)*n := by positivity
  simp [cell,word,rawInput]; omega

private def distWord (n : ℕ) (m : ℤ → ℤ) (x y : ℕ) := m (cell 6 (x*n+y))
private def center (n u v : ℕ) := CartesianBallRows.digit n u (2*v)
private def witness (n u v : ℕ) := CartesianBallRows.digit n u (2*v+1)
private def hitBall (n : ℕ) (m : ℤ → ℤ) (u v p : ℕ) :=
  distWord n m (center n u v) p ≤ distWord n m (center n u v) (witness n u v)
private def seenBall (F : ℕ → Prop) (j : ℕ) := ∃ v, 0 < v ∧ v ≤ j ∧ F v

private lemma seen_next (F : ℕ → Prop) (i : ℕ) : seenBall F (i+1) ↔ F (i+1) ∨ seenBall F i := by
  constructor
  · rintro ⟨v,lt,le,h⟩
    by_cases e : v=i+1
    · exact .inl (e ▸ h)
    · exact .inr ⟨v,lt,by omega,h⟩
  · rintro (a|⟨v,lt,le,h⟩)
    · exact ⟨i+1,by omega,by omega,a⟩
    · exact ⟨v,lt,by omega,h⟩

private lemma atPair_in {n : ℕ} (m : ℤ → ℤ) (i j : ℕ) (hi : i<n) (hj : j<n) :
    Bits.atPair n m (i:ℤ) (j:ℤ) = distWord n m i j := by
  simp [Bits.atPair,MinSumFPT.toPoint,hi,hj,distWord,address]

private lemma range_any (h g : ℕ) (hg : g<h+1) (f : ℕ → Bool) :
    (((List.range (h+1)).filter (fun v => decide (0<v) && decide (v≤g))).any f = true) ↔
      seenBall (fun v => f v = true) g := by
  simp only [List.any_eq_true,List.mem_filter,List.mem_range,Bool.and_eq_true,decide_eq_true_eq,seenBall]
  constructor
  · rintro ⟨v,⟨_,lt,le⟩,a⟩; exact ⟨v,lt,le,a⟩
  · rintro ⟨v,lt,le,a⟩; exact ⟨v,⟨by omega,lt,le⟩,a⟩

private lemma joins_iff (n h g u : ℕ) (m : ℤ → ℤ) (p q : Fin n) (hg : g<h+1) :
    Bits.joins n m h (SingleCodes.encode h g u) p q = true ↔
      seenBall (fun v=>hitBall n m u v p.val ∧ hitBall n m u v q.val) g ∨
      (¬seenBall (fun v=>hitBall n m u v p.val) g ∧ ¬seenBall (fun v=>hitBall n m u v q.val) g ∧
        distWord n m p.val q.val ≤ distWord n m (center n u 0) (witness n u 0)) := by
  have hn : 0<n := Nat.zero_lt_of_lt p.isLt
  have dc (v : ℕ) : center n u v < n := Nat.mod_lt _ hn
  have dw (v : ℕ) : witness n u v < n := Nat.mod_lt _ hn
  have div : SingleCodes.encode h g u/(h+1)=u := by
    unfold SingleCodes.encode
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt hg,zero_add]
  have rem : SingleCodes.encode h g u%(h+1)=g := by
    simp [SingleCodes.encode,Nat.add_mod,Nat.mod_eq_of_lt hg]
  have inner (v : ℕ) (a : Fin n) :
      (Bits.atPair n m (CartesianBallRows.digit n u (2*v):ℤ) (a.val:ℤ) ≤
       Bits.atPair n m (CartesianBallRows.digit n u (2*v):ℤ) (CartesianBallRows.digit n u (2*v+1):ℤ)) ↔
       hitBall n m u v a.val := by
    change Bits.atPair n m (center n u v:ℤ) (a.val:ℤ) ≤ Bits.atPair n m (center n u v:ℤ) (witness n u v:ℤ) ↔ _
    rw [atPair_in m _ _ (dc v) a.isLt,atPair_in m _ _ (dc v) (dw v)]
    rfl
  unfold Bits.joins
  simp only [div,rem]
  change (_ || (_ && _ && decide (Bits.atPair n m (p.val:ℤ) (q.val:ℤ) ≤
    Bits.atPair n m (center n u 0:ℤ) (witness n u 0:ℤ)))) = true ↔ _
  simp only [Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,
    range_any h g hg,decide_eq_true_eq,seenBall,inner,atPair_in m _ _ p.isLt q.isLt,
    atPair_in m _ _ (dc 0) (dw 0),and_assoc]

private lemma ball_reads (n buf i x y : ℕ) (m : ℤ → ℤ) (s : State)
    (atBuf : s.reg 166=(buf:ℤ)) (index : s.reg 183=(i:ℤ))
    (dx : s.heap (buf+2*(i+1))=(x:ℤ)) (dy : s.heap (buf+(2*(i+1)+1))=(y:ℤ)) :
    ∃ t k, Executes n m (chain bReads) s t k ∧ k ≤ 180 ∧ t.reg 178=(x:ℤ) ∧ t.reg 184=(y:ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  have ev : ∃ t k, evalLine n m (chain bReads) s=some (t,k) ∧ k ≤ 180 ∧
      t.reg 178=(x:ℤ) ∧ t.reg 184=(y:ℤ) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
    simp [bReads,chain,evalLine,Operation.next,regularNext,State.assign,atBuf,index,
      show 0 ≤ (buf:ℤ)+2*((i:ℤ)+1) by omega,show 0 ≤ (buf:ℤ)+(2*((i:ℤ)+1)+1) by omega,
      show ((buf:ℤ)+2*((i:ℤ)+1)).toNat=buf+2*(i+1) by omega,
      show ((buf:ℤ)+(2*((i:ℤ)+1)+1)).toNat=buf+(2*(i+1)+1) by omega,dx,dy]
  obtain ⟨t,k,e,tm,v⟩ := ev
  exact ⟨t,k,evalLine_sound _ _ _ _ e,tm,v⟩

private lemma ball_tests (n x y p q : ℕ) (m : ℤ → ℤ) (s : State)
    (one : s.reg 6=1) (sz : s.reg 64=(n:ℤ)) (cx : s.reg 178=(x:ℤ)) (cy : s.reg 184=(y:ℤ))
    (pi : s.reg 173=(p:ℤ)) (qi : s.reg 174=(q:ℤ)) :
    let P := distWord n m x p ≤ distWord n m x y
    let Q := distWord n m x q ≤ distWord n m x y
    ∃ t k, Executes n m (chain (bTests++bFlags)) s t k ∧ k ≤ 370+18*n ∧
      t.reg 180=(if P ∧ Q then 1 else s.reg 180) ∧ t.reg 181=(if P then 1 else s.reg 181) ∧
      t.reg 182=(if Q then 1 else s.reg 182) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  dsimp only
  have ev : ∃ t k, evalLine n m (chain (bTests++bFlags)) s=some (t,k) ∧ k ≤ 370+18*n ∧
      t.reg 180=(if distWord n m x p ≤ distWord n m x y ∧ distWord n m x q ≤ distWord n m x y then 1 else s.reg 180) ∧
      t.reg 181=(if distWord n m x p ≤ distWord n m x y then 1 else s.reg 181) ∧
      t.reg 182=(if distWord n m x q ≤ distWord n m x y then 1 else s.reg 182) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
    by_cases hp : m (cell 6 (x*n+p)) ≤ m (cell 6 (x*n+y)) <;>
      by_cases hq : m (cell 6 (x*n+q)) ≤ m (cell 6 (x*n+y)) <;>
      simp [distWord,bTests,bFlags,chain,evalLine,Operation.next,regularNext,State.assign,src_imat,one,sz,cx,cy,pi,qi,
        ←matrix_address n x y,←matrix_address n x p,←matrix_address n x q,matrix_raw,hp,hq] <;> omega
  obtain ⟨t,k,e,tm,v⟩ := ev
  exact ⟨t,k,evalLine_sound _ _ _ _ e,tm,v⟩

private lemma ball_loop (n h g u buf p q : ℕ) (m : ℤ → ℤ) (s : State)
    (hg : g<h+1) (one : s.reg 6=1) (sz : s.reg 64=(n:ℤ)) (pi : s.reg 173=(p:ℤ))
    (qi : s.reg 174=(q:ℤ)) (atBuf : s.reg 166=(buf:ℤ)) (lim : s.reg 169=(g:ℤ))
    (digits : ∀ j < 2*(h+1),s.heap (buf+j)=(CartesianBallRows.digit n u j:ℤ))
    (zeroA : s.reg 180=0) (zeroP : s.reg 181=0) (zeroQ : s.reg 182=0) :
    ∃ t k, Executes n m (forCount 183 472 169 bStep) s t k ∧ k ≤ 9+g*(555+18*n) ∧
      t.reg 180=(if seenBall (fun v => hitBall n m u v p ∧ hitBall n m u v q) g then 1 else 0) ∧
      t.reg 181=(if seenBall (fun v => hitBall n m u v p) g then 1 else 0) ∧
      t.reg 182=(if seenBall (fun v => hitBall n m u v q) g then 1 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  classical
  let A := fun v => hitBall n m u v p ∧ hitBall n m u v q
  let B := fun v => hitBall n m u v p
  let D := fun v => hitBall n m u v q
  let P (j : ℕ) (t : State) := t.reg 180=(if seenBall A j then 1 else 0) ∧
    t.reg 181=(if seenBall B j then 1 else 0) ∧ t.reg 182=(if seenBall D j then 1 else 0) ∧
    t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed
  have stepBit (F : ℕ → Prop) (i : ℕ) {now : Prop} [Decidable now] (w : ℤ) (matched : now ↔ F (i+1)) (hw : w=(if seenBall F i then 1 else 0)) :
      (if now then 1 else w)=(if seenBall F (i+1) then 1 else 0) := by
    by_cases yes : now
    · simp [seen_next,yes,matched.mp yes]
    · simp [seen_next,yes,mt matched.mpr yes,hw]
  obtain ⟨t,k,ex,tm,inv⟩ := GeometryTables.counted (n:=n) (m:=m) 183 472 169 g (550+18*n) bStep s P
    (by decide) (by decide) (by decide) (by decide) lim (by simp [P,seenBall,zeroA,zeroP,zeroQ])
    (by intro j z a v cases prev; rcases cases with rfl|rfl <;> simpa [P,State.assign] using prev) (by
      intro i lt z good fr ix
      obtain ⟨za,zb,zd,zh,zo,zc⟩ := good
      obtain ⟨r,j,reads,jt,cx,cy,rh,ro,rc⟩ := ball_reads n buf i (center n u (i+1)) (witness n u (i+1)) m z
        ((fr 166 (by decide)).trans atBuf) ix (by rw [zh]; exact digits _ (by omega))
        (by rw [zh]; exact digits _ (by omega))
      obtain ⟨v,l,tests,lt',fa,fb,fd,vh,vo,vc⟩ := ball_tests n (center n u (i+1)) (witness n u (i+1)) p q m r
        ((reads.preserves 6 (by decide)).trans ((fr 6 (by decide)).trans one))
        ((reads.preserves 64 (by decide)).trans ((fr 64 (by decide)).trans sz)) cx cy
        ((reads.preserves 173 (by decide)).trans ((fr 173 (by decide)).trans pi))
        ((reads.preserves 174 (by decide)).trans ((fr 174 (by decide)).trans qi))
      obtain ⟨cost,run,hc⟩ := concat_run reads tests
      have exe : Executes n m bStep z v cost := by simpa only [bStep,List.append_assoc] using run
      refine ⟨v,cost,exe,by omega,fa.trans ?_,fb.trans ?_,fd.trans ?_,
        vh.trans (rh.trans zh),vo.trans (ro.trans zo),vc.trans (rc.trans zc)⟩
      · exact @stepBit A i _ instDecidableAnd _ Iff.rfl ((reads.preserves 180 (by decide)).trans za)
      · exact @stepBit B i _ (Int.decLe _ _) _ Iff.rfl ((reads.preserves 181 (by decide)).trans zb)
      · exact @stepBit D i _ (Int.decLe _ _) _ Iff.rfl ((reads.preserves 182 (by decide)).trans zd))
  exact ⟨t,k,ex,by ring_nf at tm ⊢; exact tm,inv⟩

private lemma write_bit (n buf dest p q x y : ℕ) (m : ℤ → ℤ) (s : State) (A B D : Prop)
    (one : s.reg 6=1) (sz : s.reg 64=(n:ℤ)) (pi : s.reg 173=(p:ℤ)) (qi : s.reg 174=(q:ℤ))
    (atBuf : s.reg 166=(buf:ℤ)) (ptr : s.reg 176=(dest:ℤ))
    (dx : s.heap buf=(x:ℤ)) (dy : s.heap (buf+1)=(y:ℤ))
    (a : s.reg 180=(if A then 1 else 0)) (b : s.reg 181=(if B then 1 else 0))
    (d : s.reg 182=(if D then 1 else 0)) :
    ∃ t k, Executes n m (chain qFinish) s t k ∧ k ≤ 430+12*n ∧
      t.heap=Function.update s.heap (dest+q)
        (if A ∨ (¬B ∧ ¬D ∧ distWord n m p q ≤ distWord n m x y) then 1 else 0) ∧
      t.output=s.output ∧ t.closed=s.closed := by
  classical
  have ev : ∃ t k, evalLine n m (chain qFinish) s=some (t,k) ∧ k ≤ 430+12*n ∧
      t.heap=Function.update s.heap (dest+q)
        (if A ∨ (¬B ∧ ¬D ∧ distWord n m p q ≤ distWord n m x y) then 1 else 0) ∧
      t.output=s.output ∧ t.closed=s.closed := by
    by_cases hB : B <;> by_cases hD : D <;> by_cases hA : A <;>
      by_cases near : m (cell 6 (p*n+q)) ≤ m (cell 6 (x*n+y)) <;>
      simp [qFinish,distWord,chain,evalLine,Operation.next,regularNext,State.assign,State.save,src_imat,
        one,sz,pi,qi,atBuf,ptr,dx,dy,a,b,d,hA,hB,hD,near,←matrix_address n p q,←matrix_address n x y,matrix_raw,
        show 0 ≤ (buf:ℤ)+1 by omega,show ((buf:ℤ)+1).toNat=buf+1 by omega,
        show 0 ≤ (dest:ℤ)+q by omega,show ((dest:ℤ)+q).toNat=dest+q by omega] <;> omega
  obtain ⟨t,k,e,tm,v⟩ := ev
  exact ⟨t,k,evalLine_sound _ _ _ _ e,tm,v⟩

private lemma qWork_run (n h g u buf dest : ℕ) (m : ℤ → ℤ) (p q : Fin n) (s : State)
    (hg : g<h+1) (one : s.reg 6=1) (sz : s.reg 64=(n:ℤ)) (pi : s.reg 173=(p.val:ℤ))
    (qi : s.reg 174=(q.val:ℤ)) (atBuf : s.reg 166=(buf:ℤ)) (lim : s.reg 169=(g:ℤ))
    (ptr : s.reg 176=(dest:ℤ)) (digits : ∀ j < 2*(h+1), s.heap (buf+j)=(CartesianBallRows.digit n u j:ℤ)) :
    ∃ t k, Executes n m qWork s t k ∧ k ≤ 470+12*n+g*(555+18*n) ∧
      t.heap=Function.update s.heap (dest+q.val) (if Bits.joins n m h (SingleCodes.encode h g u) p q then 1 else 0) ∧
      t.output=s.output ∧ t.closed=s.closed := by
  classical
  have init : ∃ z k, evalLine n m (chain qInit) s=some (z,k) ∧ k ≤ 14 ∧
      z.reg 180=0 ∧ z.reg 181=0 ∧ z.reg 182=0 ∧ z.heap=s.heap ∧ z.output=s.output ∧ z.closed=s.closed := by
    simp [qInit,chain,evalLine,Operation.next,regularNext,State.assign]
  obtain ⟨a,i,ev,it,za,zb,zd,ah,ao,ac⟩ := init
  have start := evalLine_sound _ _ _ _ ev
  obtain ⟨v,j,ex,jt,va,vb,vd,vh,vo,vc⟩ := ball_loop n h g u buf p.val q.val m a hg
    ((start.preserves 6 (by decide)).trans one) ((start.preserves 64 (by decide)).trans sz)
    ((start.preserves 173 (by decide)).trans pi) ((start.preserves 174 (by decide)).trans qi)
    ((start.preserves 166 (by decide)).trans atBuf) ((start.preserves 169 (by decide)).trans lim)
    (by rw [ah]; exact digits) za zb zd
  have hx : v.heap buf=(center n u 0:ℤ) := by simpa [vh,ah,center] using digits 0 (by omega)
  have hy : v.heap (buf+1)=(witness n u 0:ℤ) := by simpa [vh,ah,witness] using digits 1 (by omega)
  obtain ⟨t,l,fin,lt,th,tout,tc⟩ := write_bit n buf dest p.val q.val (center n u 0) (witness n u 0) m v _ _ _
    ((ex.preserves 6 (by decide)).trans ((start.preserves 6 (by decide)).trans one))
    ((ex.preserves 64 (by decide)).trans ((start.preserves 64 (by decide)).trans sz))
    ((ex.preserves 173 (by decide)).trans ((start.preserves 173 (by decide)).trans pi))
    ((ex.preserves 174 (by decide)).trans ((start.preserves 174 (by decide)).trans qi))
    ((ex.preserves 166 (by decide)).trans ((start.preserves 166 (by decide)).trans atBuf))
    ((ex.preserves 176 (by decide)).trans ((start.preserves 176 (by decide)).trans ptr)) hx hy va vb vd
  obtain ⟨z,pr,eq⟩ := splitChain qInit start
  have run := pr.continue _ (Executes.seq ex fin)
  refine ⟨t,_,run,by omega,?_,tout.trans (vo.trans ao),tc.trans (vc.trans ac)⟩
  simpa only [vh,ah,joins_iff n h g u m p q hg] using th

private lemma column_step (n h g u buf win dest : ℕ) (m : ℤ → ℤ) (p q : Fin n) (s : State)
    (W : Cluster n) (hg : g<h+1) (one : s.reg 6=1) (sz : s.reg 64=(n:ℤ))
    (pi : s.reg 173=(p.val:ℤ)) (qi : s.reg 174=(q.val:ℤ)) (atBuf : s.reg 166=(buf:ℤ))
    (lim : s.reg 169=(g:ℤ)) (window : s.reg 170=(win:ℤ)) (ptr : s.reg 176=(dest:ℤ))
    (digits : ∀ j < 2*(h+1), s.heap (buf+j)=(CartesianBallRows.digit n u j:ℤ))
    (inside : 1 ≤ s.heap (win+q.val) ↔ q∈W) (init : q∉W → s.heap (dest+q.val)=0) :
    ∃ t k, Executes n m qStep s t k ∧ k ≤ 550+12*n+g*(555+18*n) ∧
      t.heap=Function.update s.heap (dest+q.val) (if q∈Bits.block m W h (SingleCodes.encode h g u) p then 1 else 0) ∧
      t.output=s.output ∧ t.closed=s.closed := by
  classical
  let a := s.assign 465 (s.heap (win+q.val))
  have read : Executes n m (chain qRead) s a 66 := by
    apply evalLine_sound
    simp [qRead,chain,evalLine,Operation.next,State.assign,window,qi,a,
      show 0 ≤ (win:ℤ)+q.val by omega,show ((win:ℤ)+q.val).toNat=win+q.val by omega]
  have control : a.reg 6 ≤ a.reg 465 ↔ q∈W := by simpa [a,State.assign,one] using inside
  obtain ⟨i,pr,eq⟩ := splitChain qRead read
  by_cases hq : q∈W
  · obtain ⟨t,k,ex,tim,hm,om,cm⟩ := qWork_run n h g u buf dest m p q a hg
      ((read.preserves 6 (by decide)).trans one) ((read.preserves 64 (by decide)).trans sz)
      ((read.preserves 173 (by decide)).trans pi) ((read.preserves 174 (by decide)).trans qi)
      ((read.preserves 166 (by decide)).trans atBuf) ((read.preserves 169 (by decide)).trans lim)
      ((read.preserves 176 (by decide)).trans ptr) digits
    refine ⟨t,_,pr.continue _ (.seq (.yes (control.mpr hq) ex) (.skip _)),by omega,?_,om,cm⟩
    by_cases hit : Bits.joins n m h (SingleCodes.encode h g u) p q = true <;>
      simpa [a,State.assign,Bits.block,hq,hit] using hm
  · refine ⟨a,_,pr.continue _ (.seq (.no (mt control.mp hq) (.skip _)) (.skip _)),by omega,?_,rfl,rfl⟩
    change s.heap=_
    symm
    apply Function.update_eq_self_iff.mpr
    simp [Bits.block,hq,init hq]

lemma fill_row
    (n h g u buf win dest : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (W : Cluster n) (p : Fin n) (hg : g < h+1)
    (one : s.reg 6 = 1) (size : s.reg 64 = (n : ℤ)) (seed : s.reg 173 = (p.val : ℤ))
    (digitsAt : s.reg 166 = (buf : ℤ)) (balls : s.reg 169 = (g : ℤ))
    (window : s.reg 170 = (win : ℤ)) (row : s.reg 176 = (dest : ℤ))
    (digits : ∀ j < 2*(h+1), s.heap (buf+j) = (CartesianBallRows.digit n u j : ℤ))
    (inside : ∀ q : Fin n, 1 ≤ s.heap (win+q.val) ↔ q ∈ W)
    (zeroOutside : ∀ q : Fin n, q ∉ W → s.heap (dest+q.val) = 0)
    (digitDisjoint : ∀ i < n, ∀ j < 2*(h+1), dest+i ≠ buf+j)
    (winDisjoint : ∀ i < n, ∀ j < n, dest+i ≠ win+j) :
    ∃ t k, Logical.Executes n m fillBlock s t k ∧ k ≤ 4000*(n+1)^2*(h+1) ∧
      (∀ q : Fin n, t.heap (dest+q.val) = if q ∈ Bits.block m W h (SingleCodes.encode h g u) p then 1 else 0) ∧
      (∀ z, z < dest ∨ dest+n ≤ z → t.heap z = s.heap z) ∧
      t.output = s.output ∧ t.closed = s.closed
    := by
  classical
  let C := Bits.block m W h (SingleCodes.encode h g u) p
  let bit (q : Fin n) : ℤ := if q ∈ C then 1 else 0
  let P (j : ℕ) (z : State) :=
    (∀ q : Fin n, q.val < j → z.heap (dest+q.val)=bit q) ∧
    (∀ a, (∀ i < j, dest+i ≠ a) → z.heap a=s.heap a) ∧ z.output=s.output ∧ z.closed=s.closed
  let cap := 550+12*n+g*(555+18*n)
  obtain ⟨t,k,run,tm,res⟩ := GeometryTables.counted (n:=n) (m:=m) 174 464 64 n cap qStep s P
    (by decide) (by decide) (by decide) (by decide) size (by simp [P])
    (by intro j z a v cases prev; rcases cases with rfl|rfl <;> simpa [P,State.assign] using prev) (by
      intro i lt z good fr idx
      let q : Fin n := ⟨i,lt⟩
      obtain ⟨before,unchanged,out,cl⟩ := good
      have buffer (j : ℕ) (hj : j < 2*(h+1)) :
          z.heap (buf+j)=(CartesianBallRows.digit n u j:ℤ) :=
        (unchanged _ (fun v hv => digitDisjoint v (by omega) j hj)).trans (digits j hj)
      have wincell : z.heap (win+i)=s.heap (win+i) := unchanged _ (fun v hv => winDisjoint v (by omega) i lt)
      have fresh : z.heap (dest+i)=s.heap (dest+i) := unchanged _ (fun v hv => by omega)
      obtain ⟨u',l,ex,tl,heap,o',c'⟩ := column_step n h g u buf win dest m p q z W hg
        ((fr 6 (by decide)).trans one) ((fr 64 (by decide)).trans size)
        ((fr 173 (by decide)).trans seed) idx ((fr 166 (by decide)).trans digitsAt)
        ((fr 169 (by decide)).trans balls) ((fr 170 (by decide)).trans window)
        ((fr 176 (by decide)).trans row) buffer (by rw [show q.val=i from rfl,wincell];exact inside q)
        (fun outside => fresh.trans (zeroOutside q outside))
      change u'.heap=Function.update z.heap (dest+i) (bit q) at heap
      refine ⟨u',l,ex,tl,?_,?_,o'.trans out,c'.trans cl⟩
      · intro a ha
        rw [heap]
        by_cases isnew : a.val=i
        · have eq : a=q := Fin.ext isnew
          subst a
          exact Function.update_self _ _ _
        · rw [Function.update_of_ne (show dest+a.val ≠ dest+i by omega)]
          exact before a (by omega)
      · intro a avoid
        rw [heap,Function.update_of_ne (Ne.symm (avoid i (by omega)))]
        exact unchanged _ (fun v hv => avoid v (by omega)))
  obtain ⟨values,untouched,out,cl⟩ := res
  rw [qIdentify]
  have gh : g ≤ h := by omega
  have bound : g*(555+18*n) ≤ h*(555+18*n) := Nat.mul_le_mul_right _ gh
  have outer : n*(cap+5) ≤ n*((550+12*n+h*(555+18*n))+5) :=
    Nat.mul_le_mul_left _ (by dsimp [cap]; omega)
  exact ⟨t,k,run,by dsimp [cap] at tm outer; ring_nf at tm outer ⊢; omega,
    fun q => values q q.isLt,fun a away => untouched a (fun v hv => by omega),out,cl⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows
theorem solution
    (n h g u buf win dest : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (W : Cluster n) (p : Fin n) (hg : g < h+1)
    (one : s.reg 6 = 1) (size : s.reg 64 = (n : ℤ)) (seed : s.reg 173 = (p.val : ℤ))
    (digitsAt : s.reg 166 = (buf : ℤ)) (balls : s.reg 169 = (g : ℤ))
    (window : s.reg 170 = (win : ℤ)) (row : s.reg 176 = (dest : ℤ))
    (digits : ∀ j < 2*(h+1), s.heap (buf+j) = (CartesianBallRows.digit n u j : ℤ))
    (inside : ∀ q : Fin n, 1 ≤ s.heap (win+q.val) ↔ q ∈ W)
    (zeroOutside : ∀ q : Fin n, q ∉ W → s.heap (dest+q.val) = 0)
    (digitDisjoint : ∀ i < n, ∀ j < 2*(h+1), dest+i ≠ buf+j)
    (winDisjoint : ∀ i < n, ∀ j < n, dest+i ≠ win+j) :
    ∃ t k, Logical.Executes n m fillBlock s t k ∧ k ≤ 4000*(n+1)^2*(h+1) ∧
      (∀ q : Fin n, t.heap (dest+q.val) = if q ∈ Bits.block m W h (SingleCodes.encode h g u) p then 1 else 0) ∧
      (∀ z, z < dest ∨ dest+n ≤ z → t.heap z = s.heap z) ∧
      t.output = s.output ∧ t.closed = s.closed
 := StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.fill_row n h g u buf win dest m s W p hg one size seed digitsAt balls window row digits inside zeroOutside digitDisjoint winDisjoint
