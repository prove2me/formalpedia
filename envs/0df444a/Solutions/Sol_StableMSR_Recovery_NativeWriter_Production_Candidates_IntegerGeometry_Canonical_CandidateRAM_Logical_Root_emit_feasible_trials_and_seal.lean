-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.emit_feasible_trials_and_seal
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T03:04:09.254121+00:00
-- url     : https://prove2.me/submissions/62a241bc-a9c3-474c-b51e-f0624a9066d5

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Root_execute_one_vertex_trial
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_emit_canonical_component_seal
import Definitions.Def_StableMSR_OneVertexTrial
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


namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 35000
private theorem source_loop {N:ℕ} {input:ℤ → ℤ} (ix last n cap:ℕ) (body:Program) (P:ℕ→State→Prop) (ne:ix≠last)
    (step:∀i < n,∀s:State,P i s → s.reg ix=(i:ℤ) → s.reg last=(n:ℤ)-1 →
      ∃t k,Executes N input body s t k ∧ k≤cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1)))
    (i rem:ℕ) (len:i+rem=n) (s:State) (start:P i s) (idx:s.reg ix=(i:ℤ)) (lim:s.reg last=(n:ℤ)-1) :
    ∃t k,Executes N input (.loop ix last (chain [body,.op (.regular (.inc ix))])) s t k ∧ k≤1+rem*(cap+5) ∧ P n t :=by
  induction rem generalizing i s with
  | zero=>
    have eq:i=n:=by omega
    exact ⟨s,1,.stop (by rw [idx,lim];omega),by omega,eq ▸ start⟩
  | succ r ih=>
    have lt:i < n:=by omega
    obtain ⟨u,k,ex,tim,idx',lim',next⟩:=step i lt s start idx lim
    let v:=u.assign ix (u.reg ix+1)
    have vi:v.reg ix=((i+1:ℕ):ℤ):=by simp [v,State.assign,idx',idx]
    have vl:v.reg last=(n:ℤ)-1:=by simp [v,State.assign,Ne.symm ne,lim',lim]
    obtain ⟨t,z,more,tm,out⟩:=ih (i+1) (by omega) v next vi vl
    have full:Executes N input (chain [body,.op (.regular (.inc ix))]) s v (1+k+(1+1+1)):=.seq ex (.seq (.op rfl) (.skip _))
    exact ⟨t,_,.more (by rw [idx,lim];omega) full more,by rw [Nat.succ_mul];omega,out⟩

private def forSetup (ix last len:ℕ) (s:State) := let u:=s.assign ix 0; let v:=u.assign last (u.reg len);v.assign last (v.reg last-1)
private theorem source_for {N:ℕ} {input:ℤ → ℤ} (ix last len n cap:ℕ) (body:Program) (P:ℕ→State→Prop)
    (ne:ix≠last) (dis:len≠ix) (s:State) (size:s.reg len=(n:ℤ))
    (start:P 0 (forSetup ix last len s))
    (step:∀i < n,∀s:State,P i s → s.reg ix=(i:ℤ) → s.reg last=(n:ℤ)-1 →
      ∃t k,Executes N input body s t k ∧ k≤cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1))) :
    ∃t k,Executes N input (forCount ix last len body) s t k ∧ k≤9+n*(cap+5) ∧ P n t :=by
  let u:=forSetup ix last len s
  have fi:u.reg ix=0:=by simp [u,forSetup,State.assign,ne]
  have last':u.reg last=(n:ℤ)-1:=by simp [u,forSetup,State.assign,dis,size]
  obtain ⟨t,z,loop,tm,out⟩:=source_loop ix last n cap body P ne step 0 n (by omega) u start fi last'
  refine ⟨t,_,.seq (.op rfl) (.seq (.op rfl) (.seq (.op rfl) (.seq loop (.skip _)))),by omega,out⟩


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
private def writesOp (j:ℕ) : Operation → Bool
  | .regular (.store _ _)|.save _ _ _=>false
  | .regular (.set d _)|.regular (.copy d _)|.regular (.add d _ _)|.regular (.sub d _ _)|
    .regular (.inc d)|.regular (.dec d)|.regular (.load d _)|.multiply d _ _|.divide _ d _ _|
    .fetch d _ _|.shift d _ _=>j==d
  | .alloc d _=>j==d || j==8
  | .output=>j==82
private def writesReg (j:ℕ) : Program → Bool
  | .skip=>false | .op o=>writesOp j o | .seq p q|.cond _ _ p q=>writesReg j p || writesReg j q
  | .loop _ _ p=>writesReg j p
private theorem op_preserves {n input s t k} (o:Operation) (j:ℕ) (frame:writesOp j o=false)
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
private theorem Executes.preserves {n input p s t k} (ex:Executes n input p s t k) (j:ℕ) (off:writesReg j p=false):
    t.reg j=s.reg j:=by
  induction ex with
  | skip|stop=>rfl
  | op h=>exact op_preserves _ _ off h
  | seq _ _ ih jh=>obtain ⟨a,b⟩:=Bool.or_eq_false_iff.mp off;exact (jh b).trans (ih a)
  | yes _ _ ih=>exact ih (Bool.or_eq_false_iff.mp off).1
  | no _ _ ih=>exact ih (Bool.or_eq_false_iff.mp off).2
  | more _ _ _ ih jh=>exact (jh off).trans (ih off)
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
private lemma outside_for {ix last len r : ℕ} {body : Program}
    (off : writesReg r (forCount ix last len body) = false) :
    r ≠ ix ∧ r ≠ last ∧ writesReg r body = false := by
  simpa [forCount,chain,writesReg,writesOp,and_assoc,and_left_comm,and_comm] using off

private lemma counted {n : ℕ} {m : ℤ → ℤ} (ix last len count cap : ℕ) (body : Program)
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

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open SingleCircuit TightLanguage Scene.SeparatorLevels
set_option maxHeartbeats 8000000
set_option maxRecDepth 50000
private structure Tables (d : Instance) (a : State) (M bits words : ℕ) : Prop where
  one : a.reg 6=1
  size : a.reg 64=(d.n:ℤ)
  base : a.reg 70=(M:ℤ)
  bitsAt : a.reg 81=(bits:ℤ)
  wordsAt : a.reg 76=(words:ℤ)
  positive : 0<M
  wordEnd : words+M ≤ (a.reg 8).toNat
  bitsEnd : bits+d.n*M ≤ (a.reg 8).toNat
  values : ∀ j<M, 0 ≤ a.heap (words+j) ∧ (a.heap (words+j)).toNat ≤ M
  menu : ∀ p<d.n, d.menu p = (List.range M).filterMap (fun j =>
    if 1 ≤ a.heap (bits+(p*M+j)) then some ((a.heap (words+j)).toNat) else none)

private abbrev protectedReg (j : ℕ) := j=6 ∨ j=7 ∨ j=8 ∨ (64≤j ∧ j≤82) ∨ j∈[241,242,243,247,250]

private lemma updateFrame {n a t cut q} (F : TrialFrame n cut q a t) (r : ℕ) (val : ℤ)
    (free : ¬ protectedReg r) : TrialFrame n cut q a (t.assign r val) := by
  have keep (j : ℕ) (hj : protectedReg j) : (t.assign r val).reg j=t.reg j := by
    have ne : j ≠ r := by rintro rfl;exact free hj
    simp [State.assign,ne]
  refine ⟨⟨⟨?_,?_,F.preserved.tables,?_,F.preserved.available⟩,?_,?_,?_,?_,?_,?_⟩,F.digits⟩
  · intro j hj; rw [keep j (by unfold protectedReg;rcases hj with h|h|h <;> omega)];exact F.preserved.control j hj
  · rw [keep 8 (by decide)];exact F.preserved.cursor
  · rw [keep 82 (by decide)];exact F.preserved.count
  · rw [keep 241 (by decide)];exact F.bitmap
  · rw [keep 242 (by decide)];exact F.vector
  · rw [keep 243 (by decide)];exact F.lengthReg
  · rw [keep 247 (by decide)];exact F.component
  · rw [keep 250 (by decide)];exact F.scratch
  · rw [keep 8 (by decide)];exact F.reserved

private def prepareCall (t : State) :=
  ((((t.assign 223 (t.reg 247)).assign 224 (t.reg 241)).assign 225 (t.reg 250)).assign 226 (t.reg 256)).assign 227 (t.reg 255)

private def callProgram := chain [.op (.regular (.copy 223 247)),.op (.regular (.copy 224 241)),
  .op (.regular (.copy 225 250)),.op (.regular (.copy 226 256)),.op (.regular (.copy 227 255)),
  src_trial,.op (.regular (.copy 1131 239))]
private def slotBody := chain [.op (.multiply 1127 256 70),.op (.regular (.add 1126 1127 255)),
  .op (.fetch 1124 81 1126),.cond 6 1124 callProgram .skip]
private def vertexBody := chain [.op (.fetch 1119 247 256),.cond 6 1119 (forCount 255 1123 70 slotBody) .skip]
private def scan := forCount 256 1118 64 vertexBody

private def LiveCall (d : Instance) (m : ℤ→ℤ) (a : State) (c cut : List ℕ) (row : Assignment)
    (q M words bits V : ℕ) : Prop :=
  ∀v∈c, ∀j<M, 1 ≤ a.heap (bits+(v*M+j)) → ∀s : State, TrialFrame d.n cut q a s →
    s.reg 223=s.reg 247 → s.reg 224=s.reg 241 → s.reg 225=s.reg 250 → s.reg 226=(v:ℤ) → s.reg 227=(j:ℤ) →
    ∃y k, Executes d.n m src_trial s y k ∧ k≤V ∧ TrialFrame d.n cut q a y ∧
      y.output=s.output++trial Naming.name d c row v (a.heap (words+j)).toNat

private lemma runSlot (d : Instance) (m : ℤ→ℤ) (a t : State) (c cut : List ℕ) (row : Assignment)
    (q M words bits V v j : ℕ) (data : Tables d a M bits words)
    (call : LiveCall d m a c cut row q M words bits V) (hv : v∈c) (vn : v<d.n)
    (hj : j<M) (F : TrialFrame d.n cut q a t) (rv : t.reg 256=(v:ℤ)) (rj : t.reg 255=(j:ℤ)) :
    ∃ y k, Executes d.n m slotBody t y k ∧ k≤V+100+6*M ∧ TrialFrame d.n cut q a y ∧
      y.output=t.output++(if 1 ≤ a.heap (bits+(v*M+j)) then trial Naming.name d c row v (a.heap (words+j)).toNat else []) := by
  let off:=v*M+j
  let cell:=a.heap (bits+off)
  let t₁:=t.assign 1127 ((v*M:ℕ):ℤ)
  let t₂:=t₁.assign 1126 (off:ℤ)
  let t₃:=t₂.assign 1124 cell
  have h1 := (F.preserved.control 6 (by decide)).trans data.one
  have bm := (F.preserved.control 70 (by decide)).trans data.base
  have ptr := (F.preserved.control 81 (by decide)).trans data.bitsAt
  have lt : off < d.n*M := by
    calc v*M+j < v*M+M := by omega
         _ = (v+1)*M := (Nat.succ_mul ..).symm
         _ ≤ _ := Nat.mul_le_mul_right _ vn
  have same := F.preserved.tables (bits+off) (by have := data.bitsEnd;omega)
  have e1 : Executes d.n m (.op (.multiply 1127 256 70)) t t₁ (8+6*M) :=
    .op (by simp [Operation.next,t₁,h1,rv,bm])
  have e2 : Executes d.n m (.op (.regular (.add 1126 1127 255))) t₁ t₂ 1 :=
    .op (by simp [Operation.next,regularNext,t₁,t₂,off,State.assign,rj])
  have e3 : Executes d.n m (.op (.fetch 1124 81 1126)) t₂ t₃ 64 := by
    apply Executes.op
    have addr : t₂.reg 81+t₂.reg 1126=((bits+off:ℕ):ℤ) := by simp [t₂,t₁,State.assign,ptr]
    simp only [Operation.next,addr,Int.natCast_nonneg,if_true,Int.toNat_natCast]
    change some (t₂.assign 1124 (t.heap (bits+off)),64)=_;rw [same]
  have fr : TrialFrame d.n cut q a t₃ := updateFrame (updateFrame (updateFrame F 1127 _ (by decide)) 1126 _ (by decide)) 1124 cell (by decide)
  have test : t₃.reg 1124=cell := by simp [t₃,State.assign]
  have testOne : t₃.reg 6=1 := by simp [t₃,t₂,t₁,State.assign,h1]
  by_cases ok : 1≤cell
  · let s:=prepareCall t₃
    have sc : TrialFrame d.n cut q a s := updateFrame (updateFrame (updateFrame (updateFrame (updateFrame fr 223 _ (by decide)) 224 _ (by decide)) 225 _ (by decide)) 226 _ (by decide)) 227 _ (by decide)
    obtain ⟨y,k,run,bt,fy,oy⟩:=call v hv j hj ok s sc
      (by simp [s,prepareCall,State.assign]) (by simp [s,prepareCall,State.assign]) (by simp [s,prepareCall,State.assign])
      (by simp [s,prepareCall,t₃,t₂,t₁,State.assign,rv]) (by simp [s,prepareCall,t₃,t₂,t₁,State.assign,rj])
    let z := y.assign 1131 (y.reg 239)
    have body : Executes d.n m callProgram t₃ z (1+1+(1+1+(1+1+(1+1+(1+1+(1+k+(1+1+1))))))) :=
      .seq (.op rfl) (.seq (.op rfl) (.seq (.op rfl) (.seq (.op rfl) (.seq (.op rfl) (.seq run (.seq (.op rfl) (.skip _)))))))
    refine ⟨z,_,.seq e1 (.seq e2 (.seq e3 (.seq (.yes (by rw [testOne,test];exact ok) body) (.skip _)))),by omega,
      updateFrame fy 1131 _ (by decide),?_⟩
    change y.output=t.output++_;rw [if_pos ok];exact oy
  · refine ⟨t₃,_,.seq e1 (.seq e2 (.seq e3 (.seq (.no (by rw [testOne,test];exact ok) (.skip _)) (.skip _)))),by omega,fr,?_⟩
    rw [if_neg ok,List.append_nil];rfl

private def slotTape (d : Instance) (a : State) (c : List ℕ) (row : Assignment)
    (M words bits v j : ℕ) : List Instr :=
  if 1≤a.heap (bits+(v*M+j)) then trial Naming.name d c row v (a.heap (words+j)).toNat else []

private lemma menuTape {α β γ : Type*} (xs : List α) (p : α→Prop) [DecidablePred p] (f : α→β) (g : β→List γ) :
    (xs.filterMap (fun j => if p j then some (f j) else none)).flatMap g =
      xs.flatMap (fun j=>if p j then g (f j) else []) := by
  induction xs with
  | nil => rfl
  | cons j js ih => by_cases h : p j <;> simp [h,ih]

private lemma runVertex (d : Instance) (m : ℤ→ℤ) (a t : State) (c cut : List ℕ) (row : Assignment)
    (q M words bits V v comp : ℕ) (data : Tables d a M bits words)
    (call : LiveCall d m a c cut row q M words bits V) (vn : v<d.n)
    (F : TrialFrame d.n cut q a t) (rv : t.reg 256=(v:ℤ)) (cptr : a.reg 247=(comp:ℤ))
    (endC : comp+d.n ≤ (a.reg 8).toNat) (cmask : ∀j<d.n,a.heap (comp+j)=if j∈c then 1 else 0) :
    ∃ y k, Executes d.n m vertexBody t y k ∧ k≤100+M*(V+105+6*M) ∧ TrialFrame d.n cut q a y ∧
      y.output=t.output++(if v∈c then (d.menu v).flatMap (trial Naming.name d c row v) else []) := by
  let bit : ℤ := if v∈c then 1 else 0
  let s:=t.assign 1119 bit
  have atC := F.component.trans cptr
  have old := (F.preserved.tables (comp+v) (by omega)).trans (cmask v vn)
  have tag : Executes d.n m (.op (.fetch 1119 247 256)) t s 64 := by
    apply Executes.op
    have addr : t.reg 247+t.reg 256=((comp+v:ℕ):ℤ) := by simp [atC,rv]
    simp only [Operation.next,addr,Int.natCast_nonneg,if_true,Int.toNat_natCast,old];rfl
  have sf : TrialFrame d.n cut q a s := updateFrame F 1119 _ (by decide)
  have so := (sf.preserved.control 6 (by decide)).trans data.one
  have val : s.reg 1119=bit := by simp [s,State.assign]
  by_cases hv : v∈c
  · let P := fun i (u:State) => TrialFrame d.n cut q a u ∧
          u.output=s.output++(List.range i).flatMap (slotTape d a c row M words bits v)
    obtain ⟨y,k,ex,bt,res⟩ := GeometryTables.counted (n:=d.n) (m:=m) 255 1123 70 M (V+100+6*M) slotBody s P
      (by decide) (by decide) (by decide) (by decide) ((sf.preserved.control 70 (by decide)).trans data.base)
      ⟨sf,by simp⟩ (by
        intro i u r z hr h;rcases hr with rfl|rfl <;> exact ⟨updateFrame h.1 _ _ (by decide),h.2⟩) (by
        intro i hi u h frame idx
        have fixed := (frame 256 (by decide)).trans (show s.reg 256=(v:ℤ) by simpa [s,State.assign] using rv)
        obtain ⟨z,k,e,tm,f,out⟩ := runSlot d m a u c cut row q M words bits V v i data call hv vn hi h.1 fixed idx
        exact ⟨z,k,e,tm,f,by rw [out,h.2];simp [List.range_succ,List.flatMap_append,slotTape,List.append_assoc]⟩)
    refine ⟨y,_,.seq tag (.seq (.yes (by rw [so,val];simp [bit,hv]) ex) (.skip _)),?_,res.1,?_⟩
    · have eq : V+100+6*M+5=V+105+6*M := by omega
      rw [eq] at bt;omega
    · rw [if_pos hv,data.menu v vn,menuTape];exact res.2
  · exact ⟨s,_,.seq tag (.seq (.no (by rw [so,val];simp [bit,hv]) (.skip _)) (.skip _)),by omega,sf,by simp [hv,s,State.assign]⟩

private lemma scanRows (d : Instance) (m : ℤ→ℤ) (a t : State) (c cut : List ℕ) (row : Assignment)
    (q M words bits V comp : ℕ) (data : Tables d a M bits words)
    (call : LiveCall d m a c cut row q M words bits V) (F : TrialFrame d.n cut q a t)
    (cptr : a.reg 247=(comp:ℤ)) (endC : comp+d.n ≤ (a.reg 8).toNat)
    (cmask : ∀j<d.n,a.heap (comp+j)=if j∈c then 1 else 0)
    (ordered : (List.range d.n).filter (fun j=>decide (j∈c))=c) :
    ∃ y k, Executes d.n m scan t y k ∧ k≤9+d.n*(105+M*(V+105+6*M)) ∧ TrialFrame d.n cut q a y ∧
      y.output=t.output++c.flatMap (fun v=>(d.menu v).flatMap (trial Naming.name d c row v)) := by
  let emitV := fun v => if v∈c then (d.menu v).flatMap (trial Naming.name d c row v) else []
  let P := fun i (u:State) => TrialFrame d.n cut q a u ∧ u.output=t.output++(List.range i).flatMap emitV
  obtain ⟨z,k,ex,tm,res⟩ := GeometryTables.counted (n:=d.n) (m:=m) 256 1118 64 d.n (100+M*(V+105+6*M)) vertexBody t P
    (by decide) (by decide) (by decide) (by decide) ((F.preserved.control 64 (by decide)).trans data.size) ⟨F,by simp⟩ (by
      intro i u r y hr h;rcases hr with rfl|rfl <;> exact ⟨updateFrame h.1 _ _ (by decide),h.2⟩) (by
      intro i hi u h frame idx
      obtain ⟨y,k,e,tm,f,out⟩ := runVertex d m a u c cut row q M words bits V i comp data call hi h.1 idx cptr endC cmask
      exact ⟨y,k,e,tm,f,by rw [out,h.2];simp [List.range_succ,List.flatMap_append,emitV,List.append_assoc]⟩)
  refine ⟨z,k,ex,?_,res.1,?_⟩
  · simpa only [show 100+M*(V+105+6*M)+5=105+M*(V+105+6*M) by omega] using tm
  · rw [res.2];congr 1
    have filt (xs : List ℕ) : xs.flatMap emitV =
        (xs.filter (fun j=>decide (j∈c))).flatMap (fun v=>(d.menu v).flatMap (trial Naming.name d c row v)) := by
      induction xs with
      | nil => rfl
      | cons x xs ih => by_cases good : x∈c <;> simp [emitV,good,ih]
    simpa only [ordered] using filt (List.range d.n)
private lemma wordCount (n h : ℕ) : (SingleCodes.words n h).length = sizes n h := by
  have rect (H R : ℕ) (f : ℕ → ℕ → ℕ) :
      ((List.range H).flatMap fun i => (List.range R).map (f i)).length = H*R := by
    induction H with
    | zero => simp
    | succ H ih => simp [List.range_succ, List.flatMap_append, ih, Nat.succ_mul]
  exact rect (h+1) (n^(2*(h+1))) (SingleCodes.encode h)

private lemma listFromSlots (xs : List ℕ) :
    (List.range xs.length).map (fun i => xs[i]?.getD 0) = xs := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂; simp [List.getElem?_eq_getElem h₂]

private lemma representedTables (x : World) (s : Store) (r h w : ℕ) (u v z a : State)
    (hn : 0<x.n) (prep : Logical.Prepared x.n r h w u)
    (geometry : Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h u v)
    (menus : Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h v z)
    (preserved : Between z a) :
    let M := sizes x.n h
    let layout := offsets x.n M
    Tables (integerData x.n x.mem s.imem r h) a M (cursorAt layout 10) (cursorAt layout 5) := by
  let M := sizes x.n h
  let layout := offsets x.n M
  let W := WindowProfiles.piece x (r/x.n) (r%x.n)
  obtain ⟨u1,_,un,_,_,_,_,_,baseReg,_,_,ptrs,_,_,_⟩ := prep
  have ctrl (j : ℕ) (hj : j=6 ∨ (64 ≤ j ∧ j ≤ 81)) : a.reg j=u.reg j :=
    (preserved.control j (by rcases hj with h|h <;> omega)).trans
      ((menus.controls j (by rcases hj with h|h <;> omega)).trans (geometry.controls j (by rcases hj with h|h <;> omega)))
  have endWords : cursorAt layout 5+M ≤ cursorAt layout 11 := by simp [layout,cursorAt,offsets];omega
  have endBits : cursorAt layout 10+x.n*M ≤ cursorAt layout 11 := by simp [layout,cursorAt,offsets];omega
  have safe : cursorAt layout 11 ≤ (z.reg 8).toNat := by have := menus.cursor; dsimp [layout,M]; omega
  have cur := preserved.cursor
  refine ⟨(ctrl 6 (by decide)).trans u1,(ctrl 64 (by decide)).trans un,(ctrl 70 (by decide)).trans baseReg,
    (ctrl 81 (by decide)).trans (ptrs ⟨10,by decide⟩),(ctrl 76 (by decide)).trans (ptrs ⟨5,by decide⟩),
    by dsimp [M,sizes]; positivity,by change cursorAt layout 5+M≤_;omega,by change cursorAt layout 10+x.n*M≤_;omega,?_,?_⟩
  · intro j hj
    have wc := (preserved.tables (cursorAt layout 5+j) (by omega)).trans (menus.words j hj)
    change a.heap (cursorAt layout 5+j)=(((SingleCodes.words x.n h)[j]?.getD 0 : ℕ):ℤ) at wc
    rw [wc];simp only [Int.natCast_nonneg,Int.toNat_natCast,true_and]
    have hh : j<(SingleCodes.words x.n h).length := by rw [wordCount];exact hj
    rw [List.getElem?_eq_getElem hh,Option.getD_some]
    generalize heq : (SingleCodes.words x.n h)[j] = value
    have mem : value ∈ SingleCodes.words x.n h := heq ▸ List.getElem_mem hh
    change value ∈ (List.range (h+1)).flatMap (fun g=>(List.range (x.n^(2*(h+1)))).map (fun v=>SingleCodes.encode h g v)) at mem
    obtain ⟨g,hg,hits⟩ := List.mem_flatMap.mp mem
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hits
    have small := List.mem_range.mp hg
    have small' := List.mem_range.mp hv
    change v*(h+1)+g ≤ (h+1)*x.n^(2*(h+1))
    calc v*(h+1)+g ≤ (v+1)*(h+1) := by rw [Nat.succ_mul];omega
         _ ≤ _ := by rw [Nat.mul_comm (h+1)];exact Nat.mul_le_mul_right _ small'
  · intro p small
    change p<x.n at small
    let vertex : Fin x.n := ⟨p, small⟩
    let words := SingleCodes.words x.n h
    let valid := fun c => Bits.feasible (Bits.win s.imem W vertex)
      (Bits.blocks s.imem (Bits.win s.imem W vertex) h c)
    have len : words.length = M := wordCount _ _
    have menuEq : (integerData x.n x.mem s.imem r h).menu p = words.filter valid := by
      simp [integerData, arrange, Bits.normalized, Bits.lookup, small, Bits.menus, words, valid, vertex, W]
      rfl
    rw [menuEq]
    have listed : (List.range M).map (fun j => words[j]?.getD 0) = words := by
      rw [← len]; exact listFromSlots _
    calc
      words.filter valid = (List.range M).filterMap
          (fun j => if valid (words[j]?.getD 0) then some (words[j]?.getD 0) else none) := by
        conv_lhs => rw [← listed]
        rw [← List.filterMap_eq_filter, List.filterMap_map]
        rfl
      _ = _ := by
        apply List.filterMap_congr
        intro j hj
        have hj := List.mem_range.mp hj
        have slot : p*M+j < x.n*M := by
          calc p*M+j < p*M+M := Nat.add_lt_add_left hj _
               _ = (p+1)*M := (Nat.succ_mul _ _).symm
               _ ≤ _ := Nat.mul_le_mul_right _ small
        have endWords : cursorAt layout 5+M ≤ cursorAt layout 11 := by
          simp [layout,cursorAt,offsets]; omega
        have endBits : cursorAt layout 10+x.n*M ≤ cursorAt layout 11 := by
          simp [layout,cursorAt,offsets]; omega
        have safe : cursorAt layout 11 ≤ (z.reg 8).toNat := by have := menus.cursor; dsimp [layout,M]; omega
        have wc := (preserved.tables (cursorAt layout 5+j) (by omega)).trans (menus.words j hj)
        have fe := (preserved.tables (cursorAt layout 10+(p*M+j)) (by omega)).trans
          (menus.tables vertex j hj).2.2.2.2
        change a.heap (cursorAt layout 5+j) = ((words[j]?.getD 0 : ℕ):ℤ) at wc
        change a.heap (cursorAt layout 10+(p*M+j)) = (if valid (words[j]?.getD 0) then 1 else 0) at fe
        rw [wc, fe]
        cases valid (words[j]?.getD 0) <;> simp
private def enabled (d : Instance) (cut : List ℕ) (p : ℕ) := d.active p && !cut.contains p
private lemma allowed_eq (d : Instance) (cut : List ℕ) :
    allowed d cut=(List.range d.n).filter (enabled d cut) := by
  unfold allowed vertices
  rw [List.filter_filter]
  apply List.filter_congr;intro q _
  simp [enabled,Bool.and_comm]

private lemma form_piece (d : Instance) (cut : List ℕ) (seed : ℕ) (pos : 0 < d.n) :
    ∃f:ℕ→Bool, pieceAt d (allowed d cut) seed=(List.range d.n).filter f := by
  have hs : List.range d.n=List.range (d.n-1)++[d.n-1] := by rw [←List.range_succ];congr 1;omega
  unfold pieceAt
  rw [hs,List.foldl_append,List.foldl_cons,List.foldl_nil,allowed_eq,List.filter_filter,←hs]
  exact ⟨_,rfl⟩

private def decRow (M : ℕ) (val : ℕ→ℕ) (ok : ℕ→ℕ→Bool) (vs : List ℕ) :
    ℕ→Option Assignment := vs.foldr (fun v (k : ℕ→Option Assignment) q =>
      if ok v (q%M) then (k (q/M)).map (fun t=>t++[(v,val (q%M))]) else none) (fun _=>some [])

private lemma rowLabels (M : ℕ) (val lab : ℕ→ℕ) (ok : ℕ→ℕ→Bool) (vs : List ℕ) (q : ℕ) (a : Assignment)
    (accepted : decRow M val ok vs q=some a)
    (labels : ∀i (hi : i<vs.length),lab vs[i]=val ((q/M^i)%M)) :
    a=(vs.map (fun j=>(j,lab j))).reverse := by
  induction vs generalizing q a with
  | nil => simpa [decRow] using accepted.symm
  | cons v vs ih =>
    change (if ok v (q%M) then (decRow M val ok vs (q/M)).map (fun t=>t++[(v,val (q%M))]) else none)=_ at accepted
    split at accepted <;> try contradiction
    cases e : decRow M val ok vs (q/M) with
    | none => simp [e] at accepted
    | some tail =>
      have hd := labels 0 (by simp)
      have eq := ih (q/M) tail e (by
        intro i hi; have h := labels (i+1) (by simpa using hi)
        simpa [pow_succ,Nat.div_div_eq_div_mul,Nat.mul_comm M] using h)
      simpa [e,eq,List.reverse_cons,show lab v=val (q%M) by simpa using hd] using accepted.symm

private lemma canonicalFilter {xs : List ℕ} {n : ℕ} (ex : ∃p : ℕ→Bool,xs=(List.range n).filter p) :
    (List.range n).filter (fun j=>decide (j∈xs))=xs := by
  obtain ⟨p,rfl⟩:=ex
  apply List.filter_congr;intro j hj;cases h:p j <;> simp [List.mem_filter,h,hj]

private lemma scanThenSeal (d : Instance) (w level M words bits V : ℕ) (m : ℤ→ℤ) (z a : State)
    (cut : List ℕ) (seed : ℕ) (input : CutInput d.n level cut a) (c : List ℕ)
    (pos : 0<d.n) (eqc : c=pieceAt d (allowed d cut) seed) (rim : rimOf d c=cut)
    (member : ComponentArg d.n c a) (data : Tables d a M bits words)
    (q : ℕ) (row : Assignment) (accepted : ordinalAssignment a cut q=some row)
    (call : LiveCall d m a c cut row q M words bits V) (t : State) (F : TrialFrame d.n cut q a t) :
    ∃y k, Executes d.n m emitFeasible t y k ∧
      k≤ 12+d.n*(105+M*(V+105+6*M)) + 700*(d.n+1)*(d.n+M+1)+300+d.n*(165+6*d.n) ∧
      OrdinalFrame d.n a y ∧ y.reg 251=t.reg 251 ∧ y.reg 1085=t.reg 1085 ∧
      y.output=t.output++entry Naming.name d c row := by
  obtain ⟨cp,cptr,ce,cm⟩ := member.row
  obtain ⟨bp,bv,bptr,_,be,_,bm,_⟩ := input.rows
  have orderedC := canonicalFilter (eqc ▸ form_piece d cut seed pos)
  have orderedB : (List.range d.n).filter (fun j=>decide (j∈cut))=cut := by
    apply canonicalFilter
    rw [←rim];unfold rimOf vertices;rw [List.filter_filter];exact ⟨_,rfl⟩
  have nodup : cut.reverse.Nodup := List.nodup_reverse.mpr (by
    have hh : ((List.range d.n).filter (fun j=>decide (j∈cut))).Nodup := List.nodup_range.filter _
    simpa only [orderedB] using hh)
  obtain ⟨u,k,run,bt,fu,ou⟩ := scanRows d m a t c cut row q M words bits V cp data call F cptr ce cm orderedC
  let slot := fun j : ℕ => q / M^(cut.reverse.idxOf j) % M
  let word := fun j : ℕ => (a.heap (words+j)).toNat
  let label := fun j => word (slot j)
  have right (i : ℕ) (hi : i<cut.reverse.length) : slot cut.reverse[i] = q/M^i%M := by simp only [slot,nodup.idxOf_getElem i hi]
  have rowEq : row = cut.map (fun j=>(j,label j)) := by
    have acc : decRow M word (fun v j => decide (1 ≤ a.heap (bits+(v*M+j)))) cut.reverse q=some row := by
      simpa [ordinalAssignment,decRow,word,data.base,data.bitsAt,data.wordsAt] using accepted
    have re := rowLabels M word label _ cut.reverse q row acc (by intro i hi;exact congrArg word (right i hi))
    simpa using re
  have up (j : ℕ) (hj:j∈cut) : u.heap ((a.reg 8).toNat+j)=(slot j:ℤ) := by
    have mem := List.mem_reverse.mpr hj
    have hidx : cut.reverse.idxOf j<cut.reverse.length := List.idxOf_lt_length_iff.mpr mem
    have rv : reverseVertex cut (cut.reverse.idxOf j)=j := by
      simp [reverseVertex,List.getElem?_eq_getElem hidx,List.getElem_idxOf hidx]
    have h:=fu.digits (cut.reverse.idxOf j) (by simpa using hidx)
    simpa [rv,slot,data.base] using h
  have wordLim (j : ℕ) : slot j < M := Nat.mod_lt _ data.positive
  have upWords (j : ℕ) : u.heap (words+slot j)=(label j:ℤ) := by
    have v := data.values _ (wordLim j)
    rw [fu.preserved.tables _ (by have := data.wordEnd; have := wordLim j;omega)]
    exact (Int.toNat_of_nonneg v.1).symm
  have nonneg : 0≤a.reg 8 := by have := data.bitsEnd;have := data.wordEnd;have := data.positive;omega
  obtain ⟨y,l,se,tm,hy,cl,oy,count,reg⟩ := emit_canonical_component_seal d.n cp bp (a.reg 8).toNat words M m u
    (fun j=>decide (j∈c)) (fun j=>decide (j∈cut)) slot label
    ((fu.preserved.control 6 (by decide)).trans data.one) ((fu.preserved.control 64 (by decide)).trans data.size)
    fu.preserved.count fu.preserved.available (fu.component.trans cptr) (fu.bitmap.trans bptr)
    (fu.scratch.trans (Int.toNat_of_nonneg nonneg).symm) ((fu.preserved.control 76 (by decide)).trans data.wordsAt)
    (by intro j hj;rw [fu.preserved.tables _ (by omega),cm _ hj];split <;> simp_all)
    (by intro j hj;rw [fu.preserved.tables _ (by omega),bm _ hj];split <;> simp_all)
    (by intro j hj hb;exact up j (by simpa using hb)) (by intro j _ _;exact upWords j)
    (by intro j _ _;exact (data.values _ (wordLim j)).2)
  have fy : OrdinalFrame d.n a y := by
    refine ⟨⟨?_,?_,?_,count,cl⟩,?_,?_,?_,?_,?_,?_⟩
    · intro j hj;exact (reg j (.inl (by rcases hj with h|h|h <;> omega))).trans (fu.preserved.control j hj)
    · rw [reg 8 (by decide)];exact fu.preserved.cursor
    · intro j hj;rw [hy];exact fu.preserved.tables _ hj
    · exact (reg 241 (by decide)).trans fu.bitmap
    · exact (reg 242 (by decide)).trans fu.vector
    · exact (reg 243 (by decide)).trans fu.lengthReg
    · exact (reg 247 (by decide)).trans fu.component
    · exact (reg 250 (by decide)).trans fu.scratch
    · rw [reg 8 (by decide)];exact fu.reserved
  have glue : emitFeasible=.seq scan (chain ((listOf emitFeasible).drop 1)) := rfl
  rw [glue]
  exact ⟨y,_,.seq run se,by omega,fy,(reg 251 (by decide)).trans (run.preserves _ (by decide)),
    (reg 1085 (by decide)).trans (run.preserves _ (by decide)),by
      rw [oy,ou,orderedC,orderedB,←rowEq];simp [entry,List.append_assoc]⟩
private lemma totalCost (n cap c D b : ℕ) (e : ℚ) (hn : 2≤n) (hc : n+1≤cap) (he : 0<e) (he' : e<1) :
    let M := sizes n (budget (e:ℝ))
    let E := parameterEnvelope (e:ℝ)
    let V := c*cap^D*n^(b*E)
    12+n*(105+M*(V+105+6*M))+700*(n+1)*(n+M+1)+300+n*(165+6*n)
      ≤ (3000+c)*cap^(D+3)*n^((b+30)*E) := by
  let O := ownerBound (e:ℝ)
  let E := parameterEnvelope (e:ℝ)
  let W := widthBound (e:ℝ)
  let H := budget (e:ℝ)+1
  let M := sizes n (budget (e:ℝ))
  let F := n^(15*E)
  let P := cap^D*n^(b*E)
  have er : (0:ℝ)<e := by exact_mod_cast he
  have er' : (e:ℝ)<1 := by exact_mod_cast he'
  have op : 1 ≤ O := by
    unfold O ownerBound; apply Nat.le_floor; rw [le_div_iff₀ er]; norm_num; linarith
  have hH : H ≤ 5*O := by dsimp [H,budget,O] at *; omega
  have OW : O*(W+1) ≤ E := by dsimp [O,W,E,parameterEnvelope]; omega
  have O1 : O ≤ E := (by simpa using Nat.mul_le_mul_left O (show 1≤W+1 by omega) : O ≤ O*(W+1)).trans OW
  have Hn : H ≤ n^H := (Nat.le_of_lt (Nat.lt_two_pow_self)).trans (Nat.pow_le_pow_left hn _)
  have M0 : M ≤ n^(3*H) := by
    change H*n^(2*H) ≤ _
    calc H*n^(2*H) ≤ n^H*n^(2*H) := Nat.mul_le_mul_right _ Hn
         _ = _ := by rw [← pow_add]; congr 1; omega
  have MF : M ≤ F := M0.trans (Nat.pow_le_pow_right (by omega) (by omega))
  let P := cap^D*n^(b*E)
  let B := cap^3*P*F^2
  have cpos : 1≤cap := by omega
  have ppos : 1≤P := Nat.mul_pos (Nat.pow_pos cpos) (Nat.pow_pos (by omega))
  have fpos : 1≤F := Nat.pow_pos (by omega)
  have cc : cap ≤ cap^3 := by simpa using (Nat.pow_le_pow_right cpos (by decide : 1≤3))
  have ca : cap*cap ≤ cap^3 := by simpa [pow_two] using (Nat.pow_le_pow_right cpos (by decide : 2≤3))
  have ff : F≤F^2 := by simpa using (Nat.pow_le_pow_right fpos (by decide : 1≤2))
  have unit : 1≤B := Nat.mul_pos (Nat.mul_pos (Nat.pow_pos cpos) ppos) (Nat.pow_pos fpos)
  have bcap : cap≤B := by
    calc cap = cap*1*1 := by simp
         _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul cc ppos) (Nat.pow_pos fpos)
  have nM : n*M ≤ B := by
    calc n*M = n*1*M := by simp
         _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (by omega) ppos) (MF.trans ff)
  have capM : cap*M ≤ B := by
    calc cap*M = cap*1*M := by simp
         _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul cc ppos) (MF.trans ff)
  have cap2 : cap*cap≤B := by
    calc cap*cap = (cap*cap)*1*1 := by simp
         _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul ca ppos) (Nat.pow_pos fpos)
  have n2 : n*n ≤ B := (Nat.mul_le_mul (by omega : n ≤ cap) (by omega : n ≤ cap)).trans cap2
  have nM2 : n*M*M ≤ B := by
    calc n*M*M = n*1*(M^2) := by ring
         _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (by omega) ppos) (Nat.pow_le_pow_left MF 2)
  have nMP : n*M*P ≤ B := by
    calc n*M*P = n*P*M := by ring
         _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (by omega) (le_refl P)) (MF.trans ff)
  have mix : n*(M*(c*P)) ≤ c*B := by calc
    n*(M*(c*P)) = c*(n*M*P) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ nMP
  have key : (n+1)*(n+M+1) ≤ 2*B := by
    calc (n+1)*(n+M+1) ≤ cap*(cap+M) := Nat.mul_le_mul hc (by omega)
         _ = cap*cap+cap*M := Nat.mul_add .. 
         _ ≤ _ := by omega
  change 12+n*(105+M*(c*cap^D*n^(b*E)+105+6*M))+700*(n+1)*(n+M+1)+300+n*(165+6*n) ≤ _
  rw [Nat.mul_assoc c]
  calc _ = 312+270*n+n*(M*(c*P))+105*(n*M)+6*(n*M*M)+700*((n+1)*(n+M+1))+6*(n*n) := by dsimp [P];ring
       _ ≤ 3000*B+c*B := by omega
       _ = _ := by dsimp [B,P,F];rw [show (b+30)*E=b*E+30*E by ring,pow_add n,pow_add cap D 3,
                                      show 30*E=15*E*2 by ring,pow_mul];ring

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal

open Scene.CutTraversal Scene.SeparatorLevels TightLanguage
theorem solution :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    ∀z:Logical.State, Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) v z →
    ∀level<x.n, let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
      Scene.CutTraversal.FeasibleEmissions d (widthBound (e:ℝ)) level s.imem z (c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ))) := by
  obtain ⟨c,D,b,calls⟩ := Root.execute_one_vertex_trial
  refine ⟨3000+c,D+3,b+30,?_⟩
  intro e he he' x s hk hkn ready bounded r p pr pp rr key u prep v geo z menus level hl
  let h := budget (e:ℝ)
  let w := widthBound (e:ℝ)
  let E := parameterEnvelope (e:ℝ)
  let d := integerData x.n x.mem s.imem r h
  let M := sizes x.n h
  let bits := cursorAt (offsets x.n M) 10
  let words := cursorAt (offsets x.n M) 5
  let V := c*x.cap^D*x.n^(b*E)
  have steps := calls e he he' x s hk hkn ready bounded r p pr pp rr key u prep v geo z menus level hl
  change FeasibleEmissions d w level s.imem z ((3000+c)*x.cap^(D+3)*x.n^((b+30)*E))
  intro a cut seed az hc inp hs rs
  dsimp only
  intro ch rowArg len rim q hq row ok t ft tq slots
  let C := pieceAt d (allowed d cut) seed
  have data : Tables d a M bits words := representedTables x s r h w u v z a (by omega) prep geo menus az
  have f : TrialFrame d.n cut q a t := ⟨ft,slots⟩
  have each : LiveCall d s.imem a C cut row q M words bits V := by
    intro v hv j hj permitted t fr a1 a2 a3 a4 a5
    have out := steps a cut seed az hc inp hs rs ch rowArg len rim q hq row ok v hv j (by simpa [data.base] using hj)
      (by simpa [data.bitsAt,data.base] using permitted) t fr a1 a2 a3 a4 a5
    simpa only [data.wordsAt,Int.toNat_natCast] using out
  obtain ⟨y,k,ex,tm,fr,idx,last,out⟩ := scanThenSeal d w level M words bits V s.imem z a cut seed inp C
    (by change 0<x.n;omega) rfl rim rowArg data q row ok each t f
  exact ⟨y,k,ex,tm.trans (totalCost x.n x.cap c D b e (by omega) (by dsimp [World.cap];omega) he he'),fr,idx,last,out⟩
