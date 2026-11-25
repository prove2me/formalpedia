-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep.complete_vertex_menu
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T05:37:47.518207+00:00
-- url     : https://prove2.me/submissions/2efdad01-85a2-45c3-bbb9-e247e7918564

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_WindowSweep_complete_seed_sweep
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_BlockRows_distinct_block_representatives
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_menu_word_schedule_and_digits
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_window_partition_feasibility
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
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep
private def vStart : List Program := [
  .op (.multiply 417 162 70),
  .op (.regular (.add 416 417 164)),
  .op (.multiply 415 416 64),
  .op (.regular (.copy 165 415)),
  .op (.shift 423 68 1),
  .op (.alloc 422 423),
  .op (.regular (.copy 166 422))
]
private def vMask : List Program := [
  .op (.divide false 440 163 68),
  .op (.regular (.copy 169 440)),
  .op (.multiply 445 162 64),
  .op (.regular (.add 443 74 445)),
  .op (.regular (.copy 170 443)),
  .op (.alloc 448 64),
  .op (.regular (.copy 171 448)),
  .op (.regular (.set 450 1)),
  .op (.regular (.copy 172 450))
]
private def vDecode := ((listOf src_data_for_vertex).drop 7).take 4
private def vEnd := (listOf src_data_for_vertex).drop ((listOf src_data_for_vertex).length-4)
private lemma vShape : src_data_for_vertex=chain (vStart++vDecode++vMask++[seedLoop]++vEnd) := by rfl

private lemma start_slot (n h a M pos cursor : ℕ) (m : ℤ → ℤ) (s : State)
    (one : s.reg 6=1) (zero : s.reg 7=0) (alloc : s.reg 8=(cursor:ℤ))
    (point : s.reg 162=(a:ℤ)) (size : s.reg 64=(n:ℤ)) (length : s.reg 70=(M:ℤ))
    (index : s.reg 164=(pos:ℤ)) (height : s.reg 68=((h+1:ℕ):ℤ)) :
    ∃ t k, Executes n m (chain vStart) s t k ∧ k ≤ 140+6*(M+n)+128*(h+1) ∧
      t.reg 165=(((a*M+pos)*n:ℕ):ℤ) ∧ t.reg 166=(cursor:ℤ) ∧ t.reg 8=((cursor+2*(h+1):ℕ):ℤ) ∧
      (∀ x < cursor,t.heap x=s.heap x) ∧ t.output=s.output ∧ t.closed=s.closed := by
  have ev : ∃ t k,evalLine n m (chain vStart) s=some (t,k) ∧ k ≤ 140+6*(M+n)+128*(h+1) ∧
      t.reg 165=(((a*M+pos)*n:ℕ):ℤ) ∧ t.reg 166=(cursor:ℤ) ∧ t.reg 8=((cursor+2*(h+1):ℕ):ℤ) ∧
      (∀ x < cursor,t.heap x=s.heap x) ∧ t.output=s.output ∧ t.closed=s.closed := by
    have positive : 0 ≤ (a:ℤ)*M+pos := by positivity
    have lengthNat : (2*((h:ℤ)+1)).toNat=2*(h+1) := by omega
    simp [vStart,chain,evalLine,Operation.next,regularNext,State.assign,State.clear,one,zero,alloc,point,
      size,length,index,height,positive,show 0 ≤ (h:ℤ)+1 by omega,show 0 ≤ 2*((h:ℤ)+1) by omega,lengthNat] <;>
      (repeat' apply And.intro) <;> intros <;> omega
  obtain ⟨t,k,e,tm,r⟩ := ev
  exact ⟨t,k,evalLine_sound _ _ _ _ e,tm,r⟩

private lemma start_mask (n h g u a wins mask : ℕ) (m : ℤ → ℤ) (s : State) (hg : g<h+1)
    (one : s.reg 6=1) (zero : s.reg 7=0) (alloc : s.reg 8=(mask:ℤ))
    (size : s.reg 64=(n:ℤ)) (point : s.reg 162=(a:ℤ)) (height : s.reg 68=((h+1:ℕ):ℤ))
    (word : s.reg 163=(SingleCodes.encode h g u:ℤ)) (ptr : s.reg 74=(wins:ℤ)) :
    ∃ t k, Executes n m (chain vMask) s t k ∧ k ≤ 160+8*u+70*n ∧ t.reg 169=(g:ℤ) ∧
      t.reg 170=((wins+a*n:ℕ):ℤ) ∧ t.reg 171=(mask:ℤ) ∧ t.reg 172=1 ∧ t.reg 8=((mask+n:ℕ):ℤ) ∧
      (∀ x < mask,t.heap x=s.heap x) ∧ (∀ j<n,t.heap (mask+j)=0) ∧ t.output=s.output ∧ t.closed=s.closed := by
  have div : SingleCodes.encode h g u/(h+1)=u := by
    unfold SingleCodes.encode
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt hg,zero_add]
  have rem : SingleCodes.encode h g u%(h+1)=g := by simp [SingleCodes.encode,Nat.add_mod,Nat.mod_eq_of_lt hg]
  have ev : ∃ t k, evalLine n m (chain vMask) s=some (t,k) ∧ k ≤ 160+8*u+70*n ∧ t.reg 169=(g:ℤ) ∧
      t.reg 170=((wins+a*n:ℕ):ℤ) ∧ t.reg 171=(mask:ℤ) ∧ t.reg 172=1 ∧ t.reg 8=((mask+n:ℕ):ℤ) ∧
      (∀ x < mask,t.heap x=s.heap x) ∧ (∀ j<n,t.heap (mask+j)=0) ∧ t.output=s.output ∧ t.closed=s.closed := by
    simp [vMask,chain,evalLine,Operation.next,regularNext,State.assign,State.clear,one,zero,alloc,size,point,height,
      word,ptr,show 0 < (h:ℤ)+1 by omega,div,rem] <;>
      (repeat' apply And.intro) <;> intros <;> omega
  obtain ⟨t,k,e,tm,r⟩ := ev
  exact ⟨t,k,evalLine_sound _ _ _ _ e,tm,r⟩

lemma run_vertex
    (n h g u a M pos cursor wins own menus : ℕ) (m : ℤ → ℤ) (s : Logical.State) (L : Layout)
    (W : Cluster n) (owner : Fin n → Fin n) (hn : 0<n) (hg : g<h+1) (hu : u<CartesianBallRows.rows n (h+1))
    (base : L.base=(a*M+pos)*n) (mask : L.mask=cursor+2*(h+1))
    (one : s.reg 6=1) (zero : s.reg 7=0) (atCursor : s.reg 8=(cursor:ℤ))
    (size : s.reg 64=(n:ℤ)) (height : s.reg 68=((h+1:ℕ):ℤ)) (length : s.reg 70=(M:ℤ))
    (atOwner : s.reg 72=(own:ℤ)) (atWins : s.reg 74=(wins:ℤ))
    (rep : s.reg 77=(L.rep:ℤ)) (minAt : s.reg 78=(L.first:ℤ)) (touch : s.reg 79=(L.touch:ℤ))
    (matrixAt : s.reg 80=(L.matrix:ℤ)) (menuAt : s.reg 81=(menus:ℤ))
    (vr : s.reg 162=(a:ℤ)) (word : s.reg 163=(SingleCodes.encode h g u:ℤ)) (slot : s.reg 164=(pos:ℤ))
    (inside : ∀ q : Fin n, s.heap (wins+a*n+q.val)=if q∈W then 1 else 0)
    (owners : ∀ q : Fin n, s.heap (own+q.val)=((owner q).val:ℤ))
    (fresh : ∀ z : Cell n, (∀ p, z≠.mask p) → s.heap (L.addr z)=0)
    (below : ∀ z : Cell n, (∀ p, z≠.mask p) → L.addr z<cursor)
    (inputsBelow : ∀ q : Fin n, wins+a*n+q.val<cursor ∧ own+q.val<cursor)
    (menuDisjoint : ∀ z : Cell n, L.addr z≠menus+(a*M+pos))
    (sep : Separated n h cursor (wins+a*n) own L) :
    ∃ t k, Logical.Executes n m Logical.src_data_for_vertex s t k ∧
      k ≤ 20000*(n+1)^3*(h+1)*(M+u+1) ∧
      VertexImage L W m h (SingleCodes.encode h g u) owner a (menus+(a*M+pos)) cursor s t
    := by
  classical
  let code := SingleCodes.encode h g u
  let C := rowBlock m W h code
  let R := representatives W C
  let P := Bits.blocks m W h code
  obtain ⟨x,i,st,it,bx,buff,xc,keepX,ox,cx⟩ := start_slot n h a M pos cursor m s one zero atCursor vr size length slot height
  obtain ⟨y,j,decode,jt,_,words,keepY,oy,cy⟩ := (Scene.menu_word_schedule_and_digits n h g u m hn hg hu).2 cursor x
    ((st.preserves 6 (by decide)).trans one) ((st.preserves 64 (by decide)).trans size)
    ((st.preserves 68 (by decide)).trans height) ((st.preserves 163 (by decide)).trans word) buff
  change Executes n m (chain vDecode) x y j at decode
  have frY (r : ℕ) (f : writesReg r (chain vStart)=false) (d : writesReg r (chain vDecode)=false) : y.reg r=s.reg r :=
    (decode.preserves _ d).trans (st.preserves _ f)
  have y8 : y.reg 8=(L.mask:ℤ) := by rw [mask];exact (decode.preserves 8 (by decide)).trans xc
  obtain ⟨z,d,setup,dt,count,win,mark,flag,z8,keepZ,clean,oz,cz⟩ := start_mask n h g u a wins L.mask m y hg
    ((frY 6 (by decide) (by decide)).trans one) ((frY 7 (by decide) (by decide)).trans zero) y8
    ((frY 64 (by decide) (by decide)).trans size) ((frY 162 (by decide) (by decide)).trans vr)
    ((frY 68 (by decide) (by decide)).trans height) ((frY 163 (by decide) (by decide)).trans word)
    ((frY 74 (by decide) (by decide)).trans atWins)
  have frZ (r : ℕ) (stOff : writesReg r (chain vStart)=false) (decOff : writesReg r (chain vDecode)=false)
      (setOff : writesReg r (chain vMask)=false) : z.reg r=s.reg r :=
    (setup.preserves _ setOff).trans (frY r stOff decOff)
  have under (q : ℕ) (hq : q<cursor) : z.heap q=s.heap q :=
    (keepZ q (by omega)).trans ((keepY q (.inl hq)).trans (keepX q hq))
  have zr : z.reg 165=(L.base:ℤ) := by rw [base];exact (setup.preserves 165 (by decide)).trans ((decode.preserves 165 (by decide)).trans bx)
  have z166 := (setup.preserves 166 (by decide)).trans ((decode.preserves 166 (by decide)).trans buff)
  have empty (k : Cell n) : z.heap (L.addr k)=0 := by
    by_cases yes : ∃ p : Fin n, k=.mask p
    · obtain ⟨p,rfl⟩ := yes
      exact clean p.val p.isLt
    · have perm : ∀ p : Fin n, k ≠ .mask p := fun p e => yes ⟨p,e⟩
      exact (under _ (below k perm)).trans (fresh k perm)
  obtain ⟨v,l,sweep,lt,rows⟩ := complete_seed_sweep n h g u cursor (wins+a*n) own a m z L W owner hg
    ((frZ 6 (by decide) (by decide) (by decide)).trans one)
    ((frZ 64 (by decide) (by decide) (by decide)).trans size) z166 count win zr
    ((frZ 80 (by decide) (by decide) (by decide)).trans matrixAt) mark
    ((frZ 77 (by decide) (by decide) (by decide)).trans rep)
    ((frZ 78 (by decide) (by decide) (by decide)).trans minAt)
    ((frZ 79 (by decide) (by decide) (by decide)).trans touch)
    ((frZ 72 (by decide) (by decide) (by decide)).trans atOwner)
    ((frZ 162 (by decide) (by decide) (by decide)).trans vr)
    (fun b hb => (keepZ _ (by omega)).trans (words b hb))
    (by intro q;rw [under _ (inputsBelow q).1,inside];by_cases hq : q∈W <;> simp [hq])
    (fun q => (under _ (inputsBelow q).2).trans (owners q)) empty flag sep
  have allCells (k : Cell n) : v.heap (L.addr k)=value W C owner a k := by
    simpa only [if_pos k.seed.isLt] using rows.cells k
  obtain ⟨ranged,represented,distinct,_⟩ := BlockRows.distinct_block_representatives m W h code
  have equivalent : (∀ b∈R,b<n → (C b).Nonempty) ↔ ∀ b∈R,(C b).Nonempty :=
    ⟨fun h b hb => h b hb (ranged b hb),fun h b hb _ => h b hb⟩
  have non : v.reg 172=(if ∀ b∈R,(C b).Nonempty then 1 else 0) := by
    by_cases yes : ∀ b∈R,(C b).Nonempty
    · exact (rows.flag.trans (if_pos (equivalent.mpr yes))).trans (if_pos yes).symm
    · exact (rows.flag.trans (if_neg (mt equivalent.mp yes))).trans (if_neg yes).symm
  have frV (r : ℕ) (f : writesReg r (chain vStart)=false) (d : writesReg r (chain vDecode)=false)
      (u : writesReg r (chain vMask)=false) (sw : writesReg r seedLoop=false) : v.reg r=s.reg r :=
    (sweep.preserves _ sw).trans (frZ r f d u)
  obtain ⟨t,k,finish,kt,heap,tout,tc⟩ := Scene.window_partition_feasibility n L.base L.mask L.matrix (wins+a*n)
    menus a M pos m v W P R C ranged represented distinct
    ((frV 6 (by decide) (by decide) (by decide) (by decide)).trans one)
    ((frV 64 (by decide) (by decide) (by decide) (by decide)).trans size)
    ((sweep.preserves 165 (by decide)).trans zr) ((sweep.preserves 171 (by decide)).trans mark)
    ((frV 80 (by decide) (by decide) (by decide) (by decide)).trans matrixAt)
    ((sweep.preserves 170 (by decide)).trans win)
    ((frV 81 (by decide) (by decide) (by decide) (by decide)).trans menuAt)
    ((frV 162 (by decide) (by decide) (by decide) (by decide)).trans vr)
    ((frV 70 (by decide) (by decide) (by decide) (by decide)).trans length)
    ((frV 164 (by decide) (by decide) (by decide) (by decide)).trans slot) non
    (by intro b hb
        have bit := allCells (.mask ⟨b,hb⟩)
        change v.heap (L.mask+b)=_ at bit
        rw [bit]
        change (1 ≤ (if b∈R then (1:ℤ) else 0)) ↔ b∈R
        by_cases on : b∈R <;> simp [on])
    (by intro q i hi
        let p : Fin n := ⟨i,ranged i hi⟩
        have point : p∈W := by
          obtain ⟨q,hq,e⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hi).1
          exact (show q=p from Fin.ext e) ▸ hq
        have bit := allCells (.member p q)
        rw [show L.matrix+((L.base+i)*n+q.val)=L.addr (.member p q) by simp [Layout.addr,p,Nat.add_assoc],bit]
        change (1 ≤ (if p∈W ∧ q∈C i then (1:ℤ) else 0)) ↔ q∈C i
        by_cases yes : q∈C i <;> simp [point,yes])
    (by intro q
        rw [rows.frame _ (fun c=>sep.window c q),under _ (inputsBelow q).1,inside]
        split <;> simp)
  change Executes n m (chain vEnd) v t k at finish
  obtain ⟨si,startRun,siEq⟩ := splitChain vStart st
  obtain ⟨dj,digitRun,djEq⟩ := splitChain vDecode decode
  obtain ⟨ms,maskRun,msEq⟩ := splitChain vMask setup
  rw [vShape]
  refine ⟨t,_,startRun.continue _ (digitRun.continue _ (maskRun.continue _ (.seq sweep finish))),?_,?_⟩
  · ring_nf at it jt dt lt kt ⊢ <;> omega
  · refine ⟨?_,?_,?_,?_,tout.trans (rows.output.trans (oz.trans (oy.trans ox))),
      tc.trans (rows.closed.trans (cz.trans (cy.trans cx)))⟩
    · intro z
      rw [heap,Function.update_of_ne (menuDisjoint z)]
      exact allCells z
    · rw [heap,Function.update_self]
    · intro q hq ne outside
      rw [heap,Function.update_of_ne ne,rows.frame _ outside,under _ hq]
    · have h8 := (finish.preserves 8 (by decide)).trans ((sweep.preserves 8 (by decide)).trans z8)
      simpa [mask] using h8

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep

theorem solution
    (n h g u a M pos cursor wins own menus : ℕ) (m : ℤ → ℤ) (s : Logical.State) (L : Layout)
    (W : Cluster n) (owner : Fin n → Fin n) (hn : 0<n) (hg : g<h+1) (hu : u<CartesianBallRows.rows n (h+1))
    (base : L.base=(a*M+pos)*n) (mask : L.mask=cursor+2*(h+1))
    (one : s.reg 6=1) (zero : s.reg 7=0) (atCursor : s.reg 8=(cursor:ℤ))
    (size : s.reg 64=(n:ℤ)) (height : s.reg 68=((h+1:ℕ):ℤ)) (length : s.reg 70=(M:ℤ))
    (atOwner : s.reg 72=(own:ℤ)) (atWins : s.reg 74=(wins:ℤ))
    (rep : s.reg 77=(L.rep:ℤ)) (minAt : s.reg 78=(L.first:ℤ)) (touch : s.reg 79=(L.touch:ℤ))
    (matrixAt : s.reg 80=(L.matrix:ℤ)) (menuAt : s.reg 81=(menus:ℤ))
    (vr : s.reg 162=(a:ℤ)) (word : s.reg 163=(SingleCodes.encode h g u:ℤ)) (slot : s.reg 164=(pos:ℤ))
    (inside : ∀ q : Fin n, s.heap (wins+a*n+q.val)=if q∈W then 1 else 0)
    (owners : ∀ q : Fin n, s.heap (own+q.val)=((owner q).val:ℤ))
    (fresh : ∀ z : Cell n, (∀ p, z≠.mask p) → s.heap (L.addr z)=0)
    (below : ∀ z : Cell n, (∀ p, z≠.mask p) → L.addr z<cursor)
    (inputsBelow : ∀ q : Fin n, wins+a*n+q.val<cursor ∧ own+q.val<cursor)
    (menuDisjoint : ∀ z : Cell n, L.addr z≠menus+(a*M+pos))
    (sep : Separated n h cursor (wins+a*n) own L) :
    ∃ t k, Logical.Executes n m Logical.src_data_for_vertex s t k ∧
      k ≤ 20000*(n+1)^3*(h+1)*(M+u+1) ∧
      VertexImage L W m h (SingleCodes.encode h g u) owner a (menus+(a*M+pos)) cursor s t
 := StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep.run_vertex n h g u a M pos cursor wins own menus m s L W owner hn hg hu base mask one zero atCursor size height length atOwner atWins rep minAt touch matrixAt menuAt vr word slot inside owners fresh below inputsBelow menuDisjoint sep
