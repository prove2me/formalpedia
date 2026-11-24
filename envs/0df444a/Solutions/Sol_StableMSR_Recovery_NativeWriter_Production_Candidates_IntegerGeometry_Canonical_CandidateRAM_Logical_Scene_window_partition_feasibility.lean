-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.window_partition_feasibility
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T21:16:06.868379+00:00
-- url     : https://prove2.me/submissions/47a04217-3514-4093-8ca7-ed1d44472cdc

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


private lemma feasible_conditions {n : ℕ} (W : Cluster n) (P : List (Cluster n)) :
    Bits.feasible W P=true ↔
      (∀C∈P,C.Nonempty) ∧ (∀C∈P,∀D∈P,C=D ∨ Disjoint C D) ∧
      P.toFinset.biUnion id=W := by
  simp only [Bits.feasible,Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,decide_eq_true_eq,and_assoc]

/-- The incidence count used by the machine characterizes a feasible list of
blocks once duplicate rows have a single representative. -/
lemma feasible_iff_counts {n : ℕ} (W:Cluster n) (P:List (Cluster n)) (R:Finset ℕ) (C:ℕ→Cluster n)
    (rep:P.toFinset=R.image C) (inj:∀a∈R,∀b∈R,C a=C b → a=b) :
    Bits.feasible W P=true ↔
      (∀a∈R,(C a).Nonempty) ∧
      ∀p:Fin n,(R.filter (fun a=>p∈C a)).card=(if p∈W then 1 else 0) := by
  have member (D:Cluster n) : D∈P ↔ ∃a∈R,C a=D := by
    change D∈P ↔ _
    rw [←List.mem_toFinset,rep,Finset.mem_image]
  have union (p:Fin n) : p∈P.toFinset.biUnion id ↔ ∃a∈R,p∈C a := by
    rw [rep,Finset.mem_biUnion]
    constructor
    · rintro ⟨D,h,hd⟩; obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp h; exact ⟨a,ha,hd⟩
    · rintro ⟨a,ha,hp⟩; exact ⟨_,Finset.mem_image.mpr ⟨a,ha,rfl⟩,hp⟩
  rw [feasible_conditions]
  constructor
  · rintro ⟨ne,dis,cover⟩
    refine ⟨fun a ha=>ne _ ((member _).mpr ⟨a,ha,rfl⟩),?_⟩
    intro p; by_cases inside:p∈W
    · rw [if_pos inside,Finset.card_eq_one]
      obtain ⟨a,ha,hp⟩ := (union p).mp (cover ▸ inside)
      refine ⟨a,Finset.ext (fun b=>?_)⟩
      rw [Finset.mem_filter,Finset.mem_singleton]
      constructor
      · rintro ⟨hb,hb'⟩
        obtain eq|apart := dis _ ((member _).mpr ⟨b,hb,rfl⟩) _ ((member _).mpr ⟨a,ha,rfl⟩)
        · exact inj b hb a ha eq
        · exact (Finset.disjoint_left.mp apart hb' hp).elim
      · rintro rfl; exact ⟨ha,hp⟩
    · rw [if_neg inside,Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem]
      intro a ha; obtain ⟨ha,hp⟩ := Finset.mem_filter.mp ha; exact inside (cover ▸ (union p).mpr ⟨a,ha,hp⟩)
  · rintro ⟨ne,count⟩
    have covered {p:Fin n} {a} (ha:a∈R) (hp:p∈C a) : p∈W := by
      by_contra bad
      have zero := count p; rw [if_neg bad,Finset.card_eq_zero] at zero
      have h : a∈R.filter (fun j=>p∈C j) := Finset.mem_filter.mpr ⟨ha,hp⟩
      rw [zero] at h; exact Finset.notMem_empty _ h
    refine ⟨?_,?_,Finset.ext (fun p=>?_)⟩
    · intro D h; obtain ⟨a,ha,rfl⟩ := (member _).mp h; exact ne a ha
    · intro D d E e
      obtain ⟨a,ha,rfl⟩ := (member _).mp d
      obtain ⟨b,hb,rfl⟩ := (member _).mp e
      by_cases eq:a=b
      · exact .inl (congrArg C eq)
      · right
        apply Finset.disjoint_left.mpr
        intro p hp hq
        have one := count p; rw [if_pos (covered ha hp),Finset.card_eq_one] at one
        obtain ⟨z,onlyZ⟩ := one
        have unique (j) (hj:j∈R) (hjp:p∈C j) : j=z := by
          have h : j∈R.filter (fun l=>p∈C l) := Finset.mem_filter.mpr ⟨hj,hjp⟩
          simpa only [onlyZ,Finset.mem_singleton] using h
        exact eq ((unique a ha hp).trans (unique b hb hq).symm)
    · rw [union]; constructor
      · rintro ⟨a,ha,hp⟩; exact covered ha hp
      · intro hp
        have one:=count p; rw [if_pos hp,Finset.card_eq_one] at one
        obtain ⟨a,single⟩:=one
        have h:a∈R.filter (fun j=>p∈C j) := by rw [single]; exact Finset.mem_singleton_self _
        exact ⟨a,Finset.mem_filter.mp h⟩

private def countStep : Program := chain [.op (.fetch 592 171 173),
          .op (.regular (.copy 591 592)),
          .cond 6 591 (chain [.op (.regular (.add 599 165 173)),
              .op (.multiply 598 599 64),
              .op (.regular (.add 597 598 174)),
              .op (.fetch 595 80 597),
              .op (.regular (.copy 591 595))]) (.skip),
          .cond 6 591 (chain [.op (.regular (.set 606 1)),
              .op (.regular (.add 604 175 606)),
              .op (.regular (.copy 175 604))]) (.skip)]

private def finishCol : List Program := [
      .op (.fetch 609 170 174),
      .cond 175 609 (.cond 609 175 (.op (.regular (.set 607 0))) (.op (.regular (.set 607 1)))) (.op (.regular (.set 607 1))),
      .cond 6 607 (chain [.op (.regular (.set 612 0)),
          .op (.regular (.copy 172 612))]) (.skip)]
private def checkCol : Program := chain ([.op (.regular (.set 588 0)),.op (.regular (.copy 175 588)),forCount 173 590 64 countStep] ++ finishCol)
private def finishFeas : List Program := [.op (.multiply 616 162 70),.op (.regular (.add 615 616 164)),.op (.save 81 615 172)]
private structure Layout (n b mark mat win : ℕ) (s : State) : Prop where
  one : s.reg 6=1
  size : s.reg 64=(n:ℤ)
  base : s.reg 165=(b:ℤ)
  mark : s.reg 171=(mark:ℤ)
  mat : s.reg 80=(mat:ℤ)
  win : s.reg 170=(win:ℤ)

private lemma Layout.lift {n b mark mat win s t} (c:Layout n b mark mat win s)
    (fr:∀j∈[6,64,165,171,80,170],t.reg j=s.reg j) : Layout n b mark mat win t :=
  ⟨(fr _ (by decide)).trans c.one,(fr _ (by decide)).trans c.size,(fr _ (by decide)).trans c.base,
   (fr _ (by decide)).trans c.mark,(fr _ (by decide)).trans c.mat,(fr _ (by decide)).trans c.win⟩

private def incidence {n : ℕ} (R:Finset ℕ) (C:ℕ→Cluster n) (p:Fin n) (i:ℕ) :=
  ((Finset.range i).filter (fun j=> j∈R ∧ p∈C j)).card

private lemma inc_succ {n} (R:Finset ℕ) (C:ℕ→Cluster n) (p:Fin n) (i:ℕ) :
    incidence R C p (i+1)=incidence R C p i+(if i∈R ∧ p∈C i then 1 else 0) := by
  have out : i ∉ (Finset.range i).filter (fun j=>j∈R ∧ p∈C j) := by simp
  by_cases hi:i∈R ∧ p∈C i <;> simp [incidence,Finset.range_add_one,Finset.filter_insert,hi,out]

private lemma inc_end {n} (R:Finset ℕ) (C:ℕ→Cluster n) (p:Fin n) (lim:∀r∈R,r < n) :
    incidence R C p n=(R.filter (fun j=>p∈C j)).card := by
  unfold incidence
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_range]; exact ⟨fun z=>z.2,fun z=>⟨lim _ z.1,z⟩⟩

private lemma count_one {n b mark mat win : ℕ} (i j v : ℕ) (m:ℤ→ℤ) (s:State) (layout:Layout n b mark mat win s)
    (row:s.reg 173=(i:ℤ)) (col:s.reg 174=(j:ℤ)) (old:s.reg 175=(v:ℤ)) :
    ∃t k,Executes n m countStep s t k ∧ k ≤ 220+6*n ∧
      t.reg 175=((v+(if 1 ≤ s.heap (mark+i) ∧ 1 ≤ s.heap (mat+((b+i)*n+j)) then 1 else 0):ℕ):ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  have ipos : 0 ≤ (mat:ℤ)+(((b:ℤ)+i)*n+j) := by positivity
  have iaddr : ((mat:ℤ)+(((b:ℤ)+i)*n+j)).toNat=mat+((b+i)*n+j) := by
    exact_mod_cast (Int.toNat_natCast (mat+((b+i)*n+j)))
  have ev : ∃t k,evalLine n m countStep s=some (t,k) ∧ k ≤ 220+6*n ∧
      t.reg 175=((v+(if 1 ≤ s.heap (mark+i) ∧ 1 ≤ s.heap (mat+((b+i)*n+j)) then 1 else 0):ℕ):ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
    by_cases a:1 ≤ s.heap (mark+i) <;> by_cases bit:1 ≤ s.heap (mat+((b+i)*n+j)) <;>
      simp [countStep,chain,evalLine,Operation.next,regularNext,State.assign,layout.one,layout.size,layout.mark,layout.mat,
        layout.base,row,col,old,a,bit,ipos,iaddr,show 0 ≤ (mark:ℤ)+i by omega,show ((mark:ℤ)+i).toNat=mark+i by omega,
        show 0 ≤ (b:ℤ)+i by omega] <;> omega
  obtain ⟨t,k,eq,tm,p⟩ := ev
  exact ⟨t,k,evalLine_sound _ _ _ _ eq,tm,p⟩

private lemma count_col {n b mark mat win} (m:ℤ→ℤ) (s:State) (layout:Layout n b mark mat win s)
    (R:Finset ℕ) (C:ℕ→Cluster n) (p:Fin n) (col:s.reg 174=(p.val:ℤ)) (zero:s.reg 175=0)
    (sel:∀i < n,1 ≤ s.heap (mark+i) ↔ i∈R)
    (has:∀i∈R,1 ≤ s.heap (mat+((b+i)*n+p.val)) ↔ p∈C i) :
    ∃t k, Executes n m (forCount 173 590 64 countStep) s t k ∧ k ≤ 9+n*(225+6*n) ∧
      t.reg 175=(incidence R C p n:ℤ) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  let P:=fun i (t:State)=>t.reg 175=(incidence R C p i:ℤ) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed
  obtain ⟨t,k,run,tm,ans⟩ := counted (n:=n) (m:=m) 173 590 64 n (220+6*n) countStep s P
    (by decide) (by decide) (by decide) (by decide) layout.size
    ⟨by simpa [incidence] using zero,rfl,rfl,rfl⟩ (by
      intro j t i v result h; obtain ⟨old,heap,o,c⟩:=h
      exact ⟨by rcases result with rfl|rfl <;> simpa [State.assign] using old,heap,o,c⟩) (by
      intro i hi t ok fr pos
      obtain ⟨old,mem,o,c⟩:=ok
      have ct:Layout n b mark mat win t := layout.lift (by
        intro j hj; simp at hj; rcases hj with h|h|h|h|h|h <;> subst j <;> exact fr _ (by decide))
      obtain ⟨y,l,act,cost,num,hm,yo,yc⟩:=count_one i p.val _ m t ct pos ((fr 174 (by decide)).trans col) old
      have test:(1 ≤ s.heap (mark+i) ∧ 1 ≤ s.heap (mat+((b+i)*n+p.val))) ↔ i∈R ∧ p∈C i := by
        constructor
        · rintro ⟨a,h⟩; have rep:=(sel i hi).mp a; exact ⟨rep,(has i rep).mp h⟩
        · rintro ⟨rep,h⟩; exact ⟨(sel i hi).mpr rep,(has i rep).mpr h⟩
      exact ⟨y,l,act,cost,by rw [inc_succ]; simpa only [mem, test] using num,hm.trans mem,yo.trans o,yc.trans c⟩)
  exact ⟨t,k,run,by ring_nf at tm ⊢; omega,ans⟩
private def resetCol : List Program := [.op (.regular (.set 588 0)),.op (.regular (.copy 175 588))]

private lemma reset_col (n:ℕ) (m:ℤ→ℤ) (s:State) :
    ∃t k,Executes n m (chain resetCol) s t k ∧ k ≤ 10 ∧ t.reg 175=0 ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  have ev : ∃t k,evalLine n m (chain resetCol) s=some (t,k) ∧ k ≤ 10 ∧ t.reg 175=0 ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by simp [resetCol,chain,evalLine,Operation.next,regularNext,State.assign]
  obtain ⟨t,k,eq,tm,p⟩:=ev; exact ⟨t,k,evalLine_sound _ _ _ _ eq,tm,p⟩

private lemma finish_col (n win j v want:ℕ) (m:ℤ→ℤ) (s:State) (one:s.reg 6=1)
    (window:s.reg 170=(win:ℤ)) (col:s.reg 174=(j:ℤ)) (cnt:s.reg 175=(v:ℤ))
    (wantV:s.heap (win+j)=(want:ℤ)) :
    ∃t k,Executes n m (chain finishCol) s t k ∧ k ≤ 100 ∧
      t.reg 172=(if v=want then s.reg 172 else 0) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  have ev : ∃t k,evalLine n m (chain finishCol) s=some (t,k) ∧ k ≤ 100 ∧
      t.reg 172=(if v=want then s.reg 172 else 0) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
    by_cases le:v ≤ want <;> by_cases ge:want ≤ v <;>
      simp [finishCol,chain,evalLine,Operation.next,regularNext,State.assign,one,window,col,cnt,wantV,
        show 0 ≤ (win:ℤ)+j by omega,show ((win:ℤ)+j).toNat=win+j by omega,le,ge] <;> omega
  obtain ⟨t,k,eq,tm,p⟩:=ev; exact ⟨t,k,evalLine_sound _ _ _ _ eq,tm,p⟩

private lemma check_column {n b mark mat win} (m:ℤ→ℤ) (s:State) (layout:Layout n b mark mat win s)
    (W:Cluster n) (R:Finset ℕ) (C:ℕ→Cluster n) (p:Fin n) (col:s.reg 174=(p.val:ℤ))
    (sel:∀i < n,1 ≤ s.heap (mark+i) ↔ i∈R)
    (has:∀i∈R,1 ≤ s.heap (mat+((b+i)*n+p.val)) ↔ p∈C i)
    (window:s.heap (win+p.val)=((if p∈W then 1 else 0:ℕ):ℤ)) :
    ∃t k,Executes n m checkCol s t k ∧ k ≤ 125+n*(225+6*n) ∧
      t.reg 172=(if incidence R C p n=(if p∈W then 1 else 0) then s.reg 172 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  obtain ⟨v,k,start,kt,zero,vh,vo,vc⟩:=reset_col n m s
  have lv:Layout n b mark mat win v := layout.lift (by
    intro j hj; simp at hj; rcases hj with h|h|h|h|h|h <;> subst j <;> exact start.preserves _ (by decide))
  obtain ⟨y,l,loop,lt,count,yh,yo,yc⟩:=count_col m v lv R C p ((start.preserves 174 (by decide)).trans col) zero
    (by intro i hi; rw [vh]; exact sel i hi) (by intro i hi; rw [vh]; exact has i hi)
  obtain ⟨t,j,fin,jt,flag,th,to',tc⟩:=finish_col n win p.val _ _ m y
    ((loop.preserves 6 (by decide)).trans lv.one) ((loop.preserves 170 (by decide)).trans lv.win)
    ((loop.preserves 174 (by decide)).trans ((start.preserves 174 (by decide)).trans col)) count (by rw [yh,vh]; exact window)
  obtain ⟨z,pr,tim⟩:=splitChain resetCol start
  have run : Executes n m checkCol s t _ := pr.continue _ (.seq loop fin)
  have closedFlag := (loop.preserves 172 (by decide)).trans (start.preserves 172 (by decide))
  exact ⟨t,_,run,by omega,by simpa only [closedFlag] using flag,th.trans (yh.trans vh),
    to'.trans (yo.trans vo),tc.trans (yc.trans vc)⟩

private def passed {n} (W:Cluster n) (R:Finset ℕ) (C:ℕ→Cluster n) (i:ℕ) : Prop :=
  (∀a∈R,(C a).Nonempty) ∧ ∀p:Fin n,p.val < i → incidence R C p n=(if p∈W then 1 else 0)

private lemma check_all {n b mark mat win} (m:ℤ→ℤ) (s:State) (layout:Layout n b mark mat win s)
    (W:Cluster n) (R:Finset ℕ) (C:ℕ→Cluster n)
    (flag:s.reg 172=if ∀a∈R,(C a).Nonempty then 1 else 0)
    (sel:∀i < n,1 ≤ s.heap (mark+i) ↔ i∈R)
    (has:∀p:Fin n,∀i∈R,1 ≤ s.heap (mat+((b+i)*n+p.val)) ↔ p∈C i)
    (window:∀p:Fin n,s.heap (win+p.val)=((if p∈W then 1 else 0:ℕ):ℤ)) :
    ∃t k,Executes n m (forCount 174 587 64 checkCol) s t k ∧ k ≤ 9+n*(130+n*(225+6*n)) ∧
      t.reg 172=(if passed W R C n then 1 else 0) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  let P:=fun i (t:State)=>t.reg 172=(if passed W R C i then 1 else 0) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed
  obtain ⟨t,k,outer,tm,ans⟩:=counted (n:=n) (m:=m) 174 587 64 n (125+n*(225+6*n)) checkCol s P
    (by decide) (by decide) (by decide) (by decide) layout.size
    ⟨by simpa [passed] using flag,rfl,rfl,rfl⟩ (by
      intro j u a v off ok
      obtain ⟨fl,h,o,c⟩:=ok
      exact ⟨by rcases off with rfl|rfl <;> simpa [State.assign] using fl,h,o,c⟩) (by
      intro i hi u ok fr pos
      obtain ⟨fl,mem,o,c⟩:=ok
      let p:Fin n:=⟨i,hi⟩
      have lv:Layout n b mark mat win u := layout.lift (by
        intro j hj; simp at hj; rcases hj with h|h|h|h|h|h <;> subst j <;> exact fr _ (by decide))
      obtain ⟨v,k,run,kt,flag',vh,vo,vc⟩:=check_column m u lv W R C p pos
        (by intro a ha; rw [mem]; exact sel a ha) (by intro a ha; rw [mem]; exact has p a ha)
        (by rw [mem]; exact window p)
      let good := incidence R C p n=(if p∈W then 1 else 0)
      have step : passed W R C (i+1) ↔ passed W R C i ∧ good := by
        constructor
        · rintro ⟨non,all⟩; exact ⟨⟨non,fun a ha=>all a (by omega)⟩,all p (by change i < i+1; omega)⟩
        · rintro ⟨⟨non,earlier⟩,now⟩; refine ⟨non,?_⟩
          intro a ha; by_cases eq:a.val=i
          · have same:a=p := Fin.ext eq; simpa only [same] using now
          · exact earlier a (by omega)
      refine ⟨v,k,run,kt,?_,vh.trans mem,vo.trans o,vc.trans c⟩
      rw [flag',fl,step]
      by_cases hp:p∈W
      · by_cases matchBit:incidence R C p n=1 <;> by_cases prev:passed W R C i <;> simp [good,hp,matchBit,prev]
      · by_cases matchBit:incidence R C p n=0 <;> by_cases prev:passed W R C i <;> simp [good,hp,matchBit,prev])
  exact ⟨t,k,outer,by ring_nf at tm ⊢; omega,ans⟩
private lemma store_result (n vertex M pos menu:ℕ) (m:ℤ→ℤ) (s:State)
    (one:s.reg 6=1) (vr:s.reg 162=(vertex:ℤ)) (len:s.reg 70=(M:ℤ)) (slot:s.reg 164=(pos:ℤ)) (dst:s.reg 81=(menu:ℤ)) :
    ∃t k,Executes n m (chain finishFeas) s t k ∧ k ≤ 90+6*M ∧
      t.heap=Function.update s.heap (menu+(vertex*M+pos)) (s.reg 172) ∧ t.output=s.output ∧ t.closed=s.closed := by
  have ev : ∃t k,evalLine n m (chain finishFeas) s=some (t,k) ∧ k ≤ 90+6*M ∧
      t.heap=Function.update s.heap (menu+(vertex*M+pos)) (s.reg 172) ∧ t.output=s.output ∧ t.closed=s.closed := by
    have eq : ((menu:ℤ)+((vertex:ℤ)*M+pos)).toNat=menu+(vertex*M+pos) := by exact_mod_cast (Int.toNat_natCast (menu+(vertex*M+pos)))
    simp [finishFeas,chain,evalLine,Operation.next,regularNext,State.assign,State.save,one,vr,len,slot,dst,
      show 0 ≤ (menu:ℤ)+((vertex:ℤ)*M+pos) by positivity,eq] <;> omega
  obtain ⟨t,k,h,tmp,p⟩:=ev; exact ⟨t,k,evalLine_sound _ _ _ _ h,tmp,p⟩


theorem check_window
    (n b mark matrix win menu vertex M pos : ℕ) (m:ℤ→ℤ) (s:Logical.State)
    (W:Cluster n) (P:List (Cluster n)) (R:Finset ℕ) (C:ℕ→Cluster n)
    (rangeR:∀a∈R,a < n) (represented:P.toFinset=R.image C)
    (distinct:∀a∈R,∀z∈R,C a=C z → a=z)
    (one:s.reg 6=1) (size:s.reg 64=(n:ℤ)) (base:s.reg 165=(b:ℤ)) (mask:s.reg 171=(mark:ℤ))
    (mat:s.reg 80=(matrix:ℤ)) (window:s.reg 170=(win:ℤ)) (dst:s.reg 81=(menu:ℤ))
    (vr:s.reg 162=(vertex:ℤ)) (len:s.reg 70=(M:ℤ)) (slot:s.reg 164=(pos:ℤ))
    (flag:s.reg 172=if ∀a∈R,(C a).Nonempty then 1 else 0)
    (sel:∀i < n,1 ≤ s.heap (mark+i) ↔ i∈R)
    (has:∀p:Fin n,∀i∈R,1 ≤ s.heap (matrix+((b+i)*n+p.val)) ↔ p∈C i)
    (inside:∀p:Fin n,s.heap (win+p.val)=((if p∈W then 1 else 0:ℕ):ℤ)) :
    let ops:=Logical.listOf Logical.src_data_for_vertex
    ∃t k, Logical.Executes n m (Logical.chain (ops.drop (ops.length-4))) s t k ∧
      k ≤ 1000*(n+1)^3+10*(M+1) ∧
      t.heap=Function.update s.heap (menu+(vertex*M+pos)) (if Bits.feasible W P then 1 else 0) ∧
      t.output=s.output ∧ t.closed=s.closed := by
  have lay:Layout n b mark matrix win s:=⟨one,size,base,mask,mat,window⟩
  obtain ⟨v,k,loop,kt,fl,mem,vo,vc⟩:=check_all m s lay W R C flag sel has inside
  obtain ⟨t,l,fin,lt,heap,out,cl⟩:=store_result n vertex M pos menu m v
    ((loop.preserves 6 (by decide)).trans one) ((loop.preserves 162 (by decide)).trans vr)
    ((loop.preserves 70 (by decide)).trans len) ((loop.preserves 164 (by decide)).trans slot)
    ((loop.preserves 81 (by decide)).trans dst)
  have result:passed W R C n ↔ Bits.feasible W P=true := by
    rw [feasible_iff_counts W P R C represented distinct]
    constructor
    · rintro ⟨non,count⟩; exact ⟨non,fun p=>by simpa only [inc_end _ _ _ rangeR] using count p p.isLt⟩
    · rintro ⟨non,count⟩; exact ⟨non,fun p _=>by rw [inc_end _ _ _ rangeR]; exact count p⟩
  refine ⟨t,_,Executes.seq loop fin,?_,?_,out.trans vo,cl.trans vc⟩
  · ring_nf at kt lt ⊢ <;> omega
  · simpa only [mem,fl,result] using heap

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables

theorem solution
    (n b mark matrix win menu vertex M pos : ℕ) (m:ℤ→ℤ) (s:Logical.State)
    (W:Cluster n) (P:List (Cluster n)) (R:Finset ℕ) (C:ℕ→Cluster n)
    (rangeR:∀a∈R,a < n) (represented:P.toFinset=R.image C)
    (distinct:∀a∈R,∀z∈R,C a=C z → a=z)
    (one:s.reg 6=1) (size:s.reg 64=(n:ℤ)) (base:s.reg 165=(b:ℤ)) (mask:s.reg 171=(mark:ℤ))
    (mat:s.reg 80=(matrix:ℤ)) (window:s.reg 170=(win:ℤ)) (dst:s.reg 81=(menu:ℤ))
    (vr:s.reg 162=(vertex:ℤ)) (len:s.reg 70=(M:ℤ)) (slot:s.reg 164=(pos:ℤ))
    (flag:s.reg 172=if ∀a∈R,(C a).Nonempty then 1 else 0)
    (sel:∀i < n,1 ≤ s.heap (mark+i) ↔ i∈R)
    (has:∀p:Fin n,∀i∈R,1 ≤ s.heap (matrix+((b+i)*n+p.val)) ↔ p∈C i)
    (inside:∀p:Fin n,s.heap (win+p.val)=((if p∈W then 1 else 0:ℕ):ℤ)) :
    let ops:=Logical.listOf Logical.src_data_for_vertex
    ∃t k, Logical.Executes n m (Logical.chain (ops.drop (ops.length-4))) s t k ∧
      k ≤ 1000*(n+1)^3+10*(M+1) ∧
      t.heap=Function.update s.heap (menu+(vertex*M+pos)) (if Bits.feasible W P then 1 else 0) ∧
      t.output=s.output ∧ t.closed=s.closed := Scene.GeometryTables.check_window n b mark matrix win menu vertex M pos m s W P R C rangeR represented distinct one size base mask mat window dst vr len slot flag sel has inside
