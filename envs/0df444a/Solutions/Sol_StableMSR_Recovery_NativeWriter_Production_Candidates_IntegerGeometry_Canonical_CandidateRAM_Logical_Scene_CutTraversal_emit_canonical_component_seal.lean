-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.emit_canonical_component_seal
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T03:01:44.529496+00:00
-- url     : https://prove2.me/submissions/f411f40b-b8c1-40ec-90b2-71db8fbade11

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_SeparatorKeys_name_key_from_tables
import Definitions.Def_StableMSR_FeasibleEntryEmission
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


open Scene.CutTraversal
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
open Scene.CutTraversal
theorem solution (n points boundary table words maxWord : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (isPoint isBoundary : ℕ → Bool) (slot label : ℕ → ℕ)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (count : s.reg 82=(s.output.length:ℤ)) (open_ : s.closed=false)
    (pointsAt : s.reg 247=(points:ℤ)) (boundaryAt : s.reg 241=(boundary:ℤ))
    (valuesAt : s.reg 250=(table:ℤ)) (wordsAt : s.reg 76=(words:ℤ))
    (pointBits : ∀ j < n, 1 ≤ s.heap (points+j) ↔ isPoint j=true)
    (boundaryBits : ∀ j < n, 1 ≤ s.heap (boundary+j) ↔ isBoundary j=true)
    (slots : ∀ j < n,isBoundary j=true → s.heap (table+j)=(slot j:ℤ))
    (labels : ∀ j < n,isBoundary j=true → s.heap (words+slot j)=(label j:ℤ))
    (bounded : ∀ j < n,isBoundary j=true → label j ≤ maxWord) :
    let key := Naming.name ((List.range n).filter isPoint,((List.range n).filter isBoundary).map (fun j => (j,label j)))
    ∃ t k, Logical.Executes n m (chain ((listOf emitFeasible).drop 1)) s t k ∧
      k ≤ 700*(n+1)*(n+maxWord+1)+300+n*(165+6*n) ∧ t.heap=s.heap ∧ t.closed=false ∧
      t.output=s.output++[Instr.seal key] ∧ t.reg 82=(t.output.length:ℤ) ∧
      ∀r, r≤81 ∨ r∈[241,242,243,247,250,251,1085] → t.reg r=s.reg r := by
  let x := ((s.assign 153 (s.reg 247)).assign 154 (s.reg 241)).assign 155 (s.reg 250)
  let key := Naming.name ((List.range n).filter isPoint,((List.range n).filter isBoundary).map (fun j => (j,label j)))
  obtain ⟨u,c,run,cost,named,heap,cur,out,cl⟩ := Scene.SeparatorKeys.name_key_from_tables
    n points boundary table words maxWord m x isPoint isBoundary slot label
    (by simpa [x,State.assign] using one) (by simpa [x,State.assign] using size)
    (by simp [x,State.assign,pointsAt]) (by simp [x,State.assign,boundaryAt]) (by simp [x,State.assign,valuesAt])
    (by simpa [x,State.assign] using wordsAt) pointBits boundaryBits slots labels bounded
  have reg (j : ℕ) (hj : j≤82 ∨ j∈[241,242,243,247,250,251,1085]) : u.reg j=s.reg j := by
    have fr : writesReg j src_name_key=false := by
      simp [src_name_key,src_code_name_push,forCount,chain,writesReg,writesOp]
      simp at hj;omega
    have h153 : j ≠ 153 := by simp at hj;omega
    have h154 : j ≠ 154 := by simp at hj;omega
    have h155 : j ≠ 155 := by simp at hj;omega
    simpa [x,State.assign,h153,h154,h155] using run.preserves j fr
  have h1 := (reg 6 (by decide)).trans one
  have sz := (reg 64 (by decide)).trans size
  have cnt := (reg 82 (by decide)).trans count
  change u.reg 158=(key:ℤ) at named
  let s1 := u.assign 1137 (key:ℤ)
  have e1 : Logical.Executes n m (.op (.regular (.copy 1137 158))) u s1 1 := .op (by simp [Operation.next,regularNext,s1,State.assign,named])
  let s2 := s1.assign 257 (key:ℤ)
  have e2 : Logical.Executes n m (.op (.regular (.copy 257 1137))) s1 s2 1 := .op (by simp [Operation.next,regularNext,s2,s1,State.assign,named])
  let s3 := s2.assign 1142 3
  have e3 : Logical.Executes n m (.op (.regular (.set 1142 3))) s2 s3 1 := .op (by simp [Operation.next,regularNext,s3,s2,s1,State.assign,named])
  let s4 := s3.assign 1144 0
  have e4 : Logical.Executes n m (.op (.regular (.set 1144 0))) s3 s4 1 := .op (by simp [Operation.next,regularNext,s4,s3,s2,s1,State.assign,named])
  let s5 := s4.assign 218 3
  have e5 : Logical.Executes n m (.op (.regular (.copy 218 1142))) s4 s5 1 := .op (by simp [Operation.next,regularNext,s5,s4,s3,s2,s1,State.assign,named])
  let s6 := s5.assign 219 (key:ℤ)
  have e6 : Logical.Executes n m (.op (.regular (.copy 219 257))) s5 s6 1 := .op (by simp [Operation.next,regularNext,s6,s5,s4,s3,s2,s1,State.assign,named])
  let s7 := s6.assign 220 0
  have e7 : Logical.Executes n m (.op (.regular (.copy 220 1144))) s6 s7 1 := .op (by simp [Operation.next,regularNext,s7,s6,s5,s4,s3,s2,s1,State.assign,named])
  let y : Logical.State := {s7.assign 82 (s7.reg 82+1) with output:=s7.output++[.seal key]}
  have recEq : record n s7=.seal key := by simp [record,s7,s6,s5,s4,s3,s2,s1,State.assign]
  have emit : Logical.Executes n m (.op .output) s7 y (200+n*(165+6*n)) := by
    apply Logical.Executes.op
    simp only [Operation.next,recEq]
    simp [State.bitsOK,Instr.tag,Instr.arg,y,s7,s6,s5,s4,s3,s2,s1,State.assign,h1,sz,cnt,out,x,cl,open_]
  let t := y.assign 1141 (y.reg 222)
  have last : Logical.Executes n m (.op (.regular (.copy 1141 222))) y t 1 := .op rfl
  have major := Nat.mul_le_mul_right (n+maxWord+1) (Nat.mul_le_mul_right (n+1) (by decide : 600≤700))
  refine ⟨t,_, (.seq (.op (o:=.regular (.copy 153 247)) rfl) (.seq (.op (o:=.regular (.copy 154 241)) rfl) (.seq (.op (o:=.regular (.copy 155 250)) rfl) (.seq run (.seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 (.seq e7 (.seq emit (.seq last (.skip _)))))))))))))),by omega,heap,cl.trans open_,?_,?_,?_⟩
  · change u.output++[.seal key]=_;rw [out];rfl
  · simp [t,y,s7,s6,s5,s4,s3,s2,s1,State.assign,cnt,out,x]
  · intro j hj
    have hreg:=reg j (by rcases hj with h|h;exact .inl (by omega);exact .inr h)
    have diff : j∉[1141,82,220,219,218,1144,1142,257,1137] := by simp at hj ⊢;omega
    simp at diff;simpa [t,y,s7,s6,s5,s4,s3,s2,s1,State.assign,diff] using hreg

#print axioms solution
