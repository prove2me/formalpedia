-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep.complete_seed_sweep
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T05:32:10.47845+00:00
-- url     : https://prove2.me/submissions/9ab82176-79a6-47b2-b456-c7e1bbf2e8a7

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_BlockRows_process_window_seed
import Definitions.Def_StableMSR_WindowSweep
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
private noncomputable def writeMeta {n : ℕ} (L : Layout) (C : ℕ → Cluster n) (R : Finset ℕ)
    (own : Fin n → Fin n) (v : ℕ) (p : Fin n) (H : ℕ → ℤ) : ℕ → ℤ :=
  if p.val ∈ R then
    let B := Function.update (Function.update H (L.addr (.mask p)) 1) (L.addr (.representative p)) 1
    let M := if ne : (C p.val).Nonempty then Function.update B (L.addr (.minimum p)) (((C p.val).min' ne).val:ℤ) else B
    if ∃ q∈C p.val, (own q).val=v then Function.update M (L.addr (.touch p)) 1 else M
  else H

private lemma meta_frame {n : ℕ} (L : Layout) (C : ℕ → Cluster n) (R : Finset ℕ) (own : Fin n → Fin n)
    (v : ℕ) (p : Fin n) (H : ℕ → ℤ) (a : ℕ) (hm : a ≠ L.addr (.mask p))
    (hr : a ≠ L.addr (.representative p)) (hf : a ≠ L.addr (.minimum p)) (ht : a ≠ L.addr (.touch p)) :
    writeMeta L C R own v p H a=H a := by
  classical
  by_cases r : p.val∈R <;> by_cases ne : (C p.val).Nonempty <;> by_cases touched : ∃ q∈C p.val,(own q).val=v <;>
    simp [writeMeta,r,ne,touched,hm,hr,hf,ht]

private lemma outside_row {n : ℕ} (L : Layout) (p : Fin n) (a : ℕ)
    (off : ∀ q : Fin n, L.addr (.member p q) ≠ a) :
    a < L.matrix+(L.base+p.val)*n ∨ L.matrix+(L.base+p.val)*n+n ≤ a := by
  let d := L.matrix+(L.base+p.val)*n
  by_contra no
  change ¬(a<d ∨ d+n ≤ a) at no
  let q : Fin n := ⟨a-d,by omega⟩
  apply off q
  change d+(a-d)=a
  omega

private lemma flag_succ {n : ℕ} (C : ℕ → Cluster n) (R : Finset ℕ) (p : ℕ) :
    (∀ i∈R,i<p+1 → (C i).Nonempty) ↔ (∀ i∈R,i<p → (C i).Nonempty) ∧ ¬(p∈R ∧ ¬(C p).Nonempty) := by
  constructor
  · intro h
    exact ⟨fun i hi lt => h i hi (by omega),fun ⟨hp,ne⟩ => ne (h p hp (by omega))⟩
  · rintro ⟨h,keep⟩ i hi le
    by_cases eq : i=p
    · subst i; by_contra hn; exact keep ⟨hi,hn⟩
    · exact h i hi (by omega)

private lemma extend_seed {n : ℕ} (L : Layout) (W : Cluster n) (C : ℕ → Cluster n) (own : Fin n → Fin n)
    (v : ℕ) (p : Fin n) (hp : p∈W) (s a t : State) (H : ℕ → ℤ)
    (inj : Function.Injective (L.addr (n:=n))) (prev : Image L W C own v p.val s a)
    (row : ∀ q : Fin n,H (L.addr (.member p q))=if q∈C p.val then 1 else 0)
    (frame : ∀ z, z<L.matrix+(L.base+p.val)*n ∨ L.matrix+(L.base+p.val)*n+n ≤ z → H z=a.heap z)
    (heap : t.heap=writeMeta L C (representatives W C) own v p H)
    (flag : t.reg 172=(if p.val∈representatives W C ∧ ¬(C p.val).Nonempty then 0 else a.reg 172))
    (out : t.output=a.output) (cl : t.closed=a.closed) : Image L W C own v (p.val+1) s t := by
  classical
  let R := representatives W C
  have zero (k : Cell n) (same : k.seed=p) (other : ∀ q : Fin n, Cell.member p q ≠ k) : H (L.addr k)=0 := by
    rw [frame _ (outside_row L p _ (fun q eq => other q (inj eq))),prev.cells,same]
    simp
  have m0 := zero (.mask p) rfl (by intro q; simp)
  have r0 := zero (.representative p) rfl (by intro q; simp)
  have f0 := zero (.minimum p) rfl (by intro q; simp)
  have t0 := zero (.touch p) rfl (by intro q; simp)
  refine ⟨?_,?_,?_,out.trans prev.output,cl.trans prev.closed⟩
  · intro k
    by_cases same : k.seed=p
    · simp only [same,Nat.lt_succ_self,if_true]
      rw [heap]
      cases k with
      | mask x | representative x | minimum x | touch x =>
        change x=p at same
        subst x
        by_cases hr : p.val∈representatives W C <;> by_cases ne : (C p.val).Nonempty <;>
          by_cases toOwner : ∃ q∈C p.val,(own q).val=v <;>
          simp [writeMeta,value,hr,ne,toOwner,Function.update_apply,inj.eq_iff,m0,r0,f0,t0]
      | member x q =>
        change x=p at same
        subst x
        rw [meta_frame L C (representatives W C) own v p H _ (by simp [inj.eq_iff]) (by simp [inj.eq_iff])
          (by simp [inj.eq_iff]) (by simp [inj.eq_iff]),row]
        simp [value,hp]
    · have off (l : Cell n) (seed : l.seed=p) : L.addr k ≠ L.addr l :=
        fun e => same ((congrArg Cell.seed (inj e)).trans seed)
      have num : k.seed.val ≠ p.val := fun e => same (Fin.ext e)
      rw [heap,meta_frame L C R own v p H _ (off _ rfl) (off _ rfl) (off _ rfl) (off _ rfl),
        frame _ (outside_row L p _ (fun q => Ne.symm (off (.member p q) rfl))),prev.cells]
      by_cases less : k.seed.val<p.val <;> simp [less,show (k.seed.val<p.val+1) ↔ (k.seed.val<p.val) by omega]
  · intro i away
    rw [heap,meta_frame L C R own v p H _ (Ne.symm (away _)) (Ne.symm (away _)) (Ne.symm (away _)) (Ne.symm (away _)),
        frame _ (outside_row L p _ (fun _ => away _)),prev.frame i away]
  · by_cases allNew : ∀ i∈representatives W C,i<p.val+1 → (C i).Nonempty
    · obtain ⟨old,no⟩ := (flag_succ C (representatives W C) p.val).mp allNew
      rw [if_pos allNew,flag,if_neg no,prev.flag,if_pos old]
    · rw [if_neg allNew,flag]
      by_cases bad : p.val∈representatives W C ∧ ¬(C p.val).Nonempty
      · rw [if_pos bad]
      · have fail : ¬∀ i∈representatives W C,i<p.val → (C i).Nonempty :=
          fun old => allNew ((flag_succ C (representatives W C) p.val).mpr ⟨old,bad⟩)
        rw [if_neg bad,prev.flag,if_neg fail]

private lemma missing_seed {n : ℕ} (L : Layout) (W : Cluster n) (C : ℕ → Cluster n) (own : Fin n → Fin n)
    (v : ℕ) (p : Fin n) (hp : p∉W) (s a : State) (before : Image L W C own v p.val s a) :
    Image L W C own v (p.val+1) s a := by
  classical
  have absent : p.val∉representatives W C := by
    intro h
    obtain ⟨q,hq,e⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
    exact hp (Fin.ext e ▸ hq)
  refine ⟨?_,before.frame,?_,before.output,before.closed⟩
  · intro k
    rw [before.cells]
    by_cases eq : k.seed=p
    · simp only [eq,lt_self_iff_false,if_false,Nat.lt_succ_self,if_true]
      cases k with
      | mask q | representative q | minimum q | touch q | member q _ =>
        change q=p at eq
        subst q
        simp [value,absent,hp]
    · have diff : k.seed.val≠p.val := fun e=>eq (Fin.ext e)
      have iff : (k.seed.val<p.val+1) ↔ k.seed.val<p.val := by omega
      simp only [iff]
  · simpa only [flag_succ C (representatives W C) p.val,absent,false_and,not_false_eq_true,and_true] using before.flag

private lemma seed_in_window {n : ℕ} {W : Cluster n} {C : ℕ → Cluster n} {p : Fin n}
    (mem : p.val∈representatives W C) : p∈W := by
  obtain ⟨q,hq,e⟩ := Finset.mem_image.mp (Finset.mem_filter.mp mem).1
  exact Fin.ext e ▸ hq

private lemma metadata_disjoint {n h buf win own : ℕ} (L : Layout) (sep : Separated n h buf win own L)
    (p : Fin n) : ∀ a ∈ [L.mask+p.val,L.rep+(L.base+p.val),L.first+(L.base+p.val),L.touch+(L.base+p.val)],
      ∀ q : Fin n, a≠L.matrix+(L.base+p.val)*n+q.val ∧ a≠own+q.val := by
  intro a ha q
  change a ∈ [L.addr (.mask p),L.addr (.representative p),L.addr (.minimum p),L.addr (.touch p)] at ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with e|e|e|e <;> subst a
  all_goals constructor
  all_goals first | exact sep.owners _ q | exact fun bad => by cases sep.inj (show L.addr _=L.addr (.member p q) from bad)

private def loopStep := countedBody seedLoop
private lemma loop_shape : seedLoop=forCount 173 452 64 loopStep := by rfl

lemma run_sweep
    (n h g u buf win own vertex : ℕ) (m : ℤ → ℤ) (s : Logical.State) (L : Layout)
    (W : Cluster n) (owner : Fin n → Fin n) (hg : g < h+1)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (digitsAt : s.reg 166=(buf:ℤ))
    (balls : s.reg 169=(g:ℤ)) (window : s.reg 170=(win:ℤ)) (b : s.reg 165=(L.base:ℤ))
    (matrixAt : s.reg 80=(L.matrix:ℤ)) (mask : s.reg 171=(L.mask:ℤ)) (rep : s.reg 77=(L.rep:ℤ))
    (minAt : s.reg 78=(L.first:ℤ)) (touch : s.reg 79=(L.touch:ℤ))
    (ownerAt : s.reg 72=(own:ℤ)) (vertexAt : s.reg 162=(vertex:ℤ))
    (digits : ∀ j < 2*(h+1), s.heap (buf+j)=(CartesianBallRows.digit n u j:ℤ))
    (inside : ∀ q : Fin n, 1 ≤ s.heap (win+q.val) ↔ q∈W)
    (owners : ∀ q : Fin n, s.heap (own+q.val)=((owner q).val:ℤ))
    (empty : ∀ z : Cell n, s.heap (L.addr z)=0) (initialFlag : s.reg 172=1)
    (sep : Separated n h buf win own L) :
    ∃ t k, Logical.Executes n m seedLoop s t k ∧ k ≤ 6200*(n+1)^3*(h+1) ∧
      Image L W (rowBlock m W h (SingleCodes.encode h g u)) owner vertex n s t
    := by
  classical
  let C := rowBlock m W h (SingleCodes.encode h g u)
  let R := representatives W C
  let P := fun j (z : State) => Image L W C owner vertex j s z
  have start : P 0 s := ⟨fun z => by simpa using empty z,fun _ _=>rfl,by simpa using initialFlag,rfl,rfl⟩
  obtain ⟨t,k,ex,tm,ans⟩ := GeometryTables.counted (n:=n) (m:=m)
    173 452 64 n (6075*(n+1)^2*(h+1)) loopStep s P (by decide) (by decide) (by decide) (by decide)
    size start (by
      intro j z r w changes ok
      refine ⟨ok.cells,ok.frame,?_,ok.output,ok.closed⟩
      rcases changes with rfl|rfl <;> simpa [State.assign] using ok.flag) (by
      intro i hi z prev fr atI
      let p : Fin n := ⟨i,hi⟩
      let a := z.assign 453 (z.heap (win+i))
      have read : Executes n m (.op (.fetch 453 170 173)) z a 64 := by
        apply Executes.op
        simp [Operation.next,a,(fr 170 (by decide)).trans window,atI,
          show 0 ≤ (win:ℤ)+i by omega,show ((win:ℤ)+i).toNat=win+i by omega]
      have regA (r : ℕ) (off : writesReg r (forCount 173 452 64 loopStep)=false) (ne : r≠453) :
          a.reg r=s.reg r := by simpa [a,State.assign,ne] using fr r off
      have prevA : Image L W C owner vertex p.val s a :=
        ⟨prev.cells,prev.frame,by simpa [a,State.assign] using prev.flag,prev.output,prev.closed⟩
      have originalWin (q : Fin n) := prevA.frame (win+q.val) (fun j => sep.window j q)
      have readBit : a.reg 453=a.heap (win+p.val) := by simp [a,State.assign,p]
      have oneA := (regA 6 (by decide) (by decide)).trans one
      have guard : a.reg 6 ≤ a.reg 453 ↔ p∈W := by rw [oneA,readBit,originalWin];exact inside p
      by_cases hp : p∈W
      · obtain ⟨v,l,H,seedRun,lt,row,frame,storeEq,flag,out,cl⟩ := BlockRows.process_window_seed
          n h g u buf win L.base L.matrix L.mask L.rep L.first L.touch own vertex m a W p owner hp hg
          oneA ((regA 64 (by decide) (by decide)).trans size) (by simpa [a,State.assign,p] using atI)
          ((regA 166 (by decide) (by decide)).trans digitsAt) ((regA 169 (by decide) (by decide)).trans balls)
          ((regA 170 (by decide) (by decide)).trans window) ((regA 165 (by decide) (by decide)).trans b)
          ((regA 80 (by decide) (by decide)).trans matrixAt) ((regA 171 (by decide) (by decide)).trans mask)
          ((regA 77 (by decide) (by decide)).trans rep) ((regA 78 (by decide) (by decide)).trans minAt)
          ((regA 79 (by decide) (by decide)).trans touch) ((regA 72 (by decide) (by decide)).trans ownerAt)
          ((regA 162 (by decide) (by decide)).trans vertexAt)
          (fun j hj => (prevA.frame _ (fun z=>sep.digits z j hj)).trans (digits j hj))
          (by intro q;rw [originalWin];exact inside q)
          (fun q => (prevA.frame _ (fun z=>sep.owners z q)).trans (owners q))
          (by intro q _;simpa [Layout.addr,Cell.seed] using prevA.cells (.member p q))
          (by intro j hj
              let q : Fin n := ⟨j,by omega⟩
              have bit := prevA.cells (.mask q)
              change a.heap (L.mask+j)=_ at bit
              rw [bit]
              by_cases mem : j∈R <;> simp [value,Cell.seed,hj,mem,q,R,C] at mem ⊢)
          (by intro j hj mR q
              let x : Fin n := ⟨j,by omega⟩
              have wx : x∈W := seed_in_window (C:=C) mR
              simpa [Layout.addr,Cell.seed,value,x,hj,wx,C] using prevA.cells (.member x q))
          (fun j hj d hd => sep.digits (.member p ⟨j,hj⟩) d hd)
          (by intro j hj d hd
              exact ⟨sep.window (.member p ⟨j,hj⟩) ⟨d,hd⟩,sep.owners (.member p ⟨j,hj⟩) ⟨d,hd⟩,
                fun eq => by cases sep.inj (show L.addr (.member p ⟨j,hj⟩)=L.addr (.mask ⟨d,hd⟩) from eq)⟩)
          (metadata_disjoint L sep p)
        have done := extend_seed L W C owner vertex p hp s a v H sep.inj prevA row frame storeEq flag out cl
        refine ⟨v,_,Executes.seq read (.seq (.yes (guard.mpr hp) seedRun) (.skip _)),?_,done⟩
        ring_nf at lt ⊢ <;> omega
      · exact ⟨a,_,Executes.seq read (.seq (.no (mt guard.mp hp) (.skip _)) (.skip _)),by ring_nf <;> omega,
          missing_seed L W C owner vertex p hp s a prevA⟩)
  rw [loop_shape]
  exact ⟨t,k,ex,by ring_nf at tm ⊢ <;> omega,ans⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep

theorem solution
    (n h g u buf win own vertex : ℕ) (m : ℤ → ℤ) (s : Logical.State) (L : Layout)
    (W : Cluster n) (owner : Fin n → Fin n) (hg : g < h+1)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (digitsAt : s.reg 166=(buf:ℤ))
    (balls : s.reg 169=(g:ℤ)) (window : s.reg 170=(win:ℤ)) (b : s.reg 165=(L.base:ℤ))
    (matrixAt : s.reg 80=(L.matrix:ℤ)) (mask : s.reg 171=(L.mask:ℤ)) (rep : s.reg 77=(L.rep:ℤ))
    (minAt : s.reg 78=(L.first:ℤ)) (touch : s.reg 79=(L.touch:ℤ))
    (ownerAt : s.reg 72=(own:ℤ)) (vertexAt : s.reg 162=(vertex:ℤ))
    (digits : ∀ j < 2*(h+1), s.heap (buf+j)=(CartesianBallRows.digit n u j:ℤ))
    (inside : ∀ q : Fin n, 1 ≤ s.heap (win+q.val) ↔ q∈W)
    (owners : ∀ q : Fin n, s.heap (own+q.val)=((owner q).val:ℤ))
    (empty : ∀ z : Cell n, s.heap (L.addr z)=0) (initialFlag : s.reg 172=1)
    (sep : Separated n h buf win own L) :
    ∃ t k, Logical.Executes n m seedLoop s t k ∧ k ≤ 6200*(n+1)^3*(h+1) ∧
      Image L W (rowBlock m W h (SingleCodes.encode h g u)) owner vertex n s t
 := StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep.run_sweep n h g u buf win own vertex m s L W owner hg one size digitsAt balls window b matrixAt mask rep minAt touch ownerAt vertexAt digits inside owners empty initialFlag sep
