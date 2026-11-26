-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.decode_one_boundary_digit
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T00:58:55.667799+00:00
-- url     : https://prove2.me/submissions/486a1da8-442f-44d4-86a4-8e6c7e7ff3d3

import Definitions.Def_StableMSR_SeparatorOrdinals
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
theorem solution (n : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (M q i back v vec buf bits : ℕ) (hM : 0 < M) (one : s.reg 6 = 1)
    (base : s.reg 70 = (M:ℤ)) (remReg : s.reg 252 = (q:ℤ))
    (len : s.reg 243 = ((back+i+1:ℕ):ℤ)) (idx : s.reg 245 = (i:ℤ))
    (vector : s.reg 242 = (vec:ℤ)) (buffer : s.reg 250 = (buf:ℤ)) (table : s.reg 81 = (bits:ℤ))
    (atVertex : s.heap (vec+back) = (v:ℤ))
    (separate : bits+(v*M+q%M) ≠ buf+v) :
    let loopCode := ((listOf ordinalBody)[3]?).getD .skip
    let step := match ((listOf loopCode)[3]? : Option Program) with
      | some (Program.loop _ _ body) => ((listOf body)[0]?).getD .skip
      | _ => .skip
    ∃ t k, Logical.Executes n m step s t k ∧ k ≤ 400+6*M+16*(q/M) ∧
      t.reg 252 = ((q/M:ℕ):ℤ) ∧ t.reg 255 = ((q%M:ℕ):ℤ) ∧
      t.reg 253 = (if 1 ≤ s.heap (bits+(v*M+q%M)) then s.reg 253 else 0) ∧
      t.heap = Function.update s.heap (buf+v) ((q%M:ℕ):ℤ) ∧
      t.output = s.output ∧ t.closed = s.closed ∧
      ∀ j, j ∉ [1095,1093,1092,1090,254,1097,255,1100,252,1111,1110,1108,1107,1115,253] →
        t.reg j = s.reg j := by
  let s1 := s.assign 1095 1
  have e1 : Executes n m (.op (.regular (.set 1095 1))) s s1 1 := by
    apply Executes.op
    simp [s1, Operation.next,regularNext,State.assign,State.save,one,base,remReg,len,idx,vector,buffer,table,atVertex,hM,separate,Int.toNat_add, Int.toNat_mul] <;> omega
  let s2 := s1.assign 1093 ((back+i:ℕ):ℤ)
  have e2 : Executes n m (.op (.regular (.sub 1093 243 1095))) s1 s2 1 := by
    apply Executes.op
    simp [s2, s1, Operation.next,regularNext,State.assign,State.save,one,base,remReg,len,idx,vector,buffer,table,atVertex,hM,separate,Int.toNat_add, Int.toNat_mul] <;> omega
  let s3 := s2.assign 1092 (back:ℤ)
  have e3 : Executes n m (.op (.regular (.sub 1092 1093 245))) s2 s3 1 := by
    apply Executes.op
    simp [s3, s2, s1, Operation.next,regularNext,State.assign,State.save,one,base,remReg,len,idx,vector,buffer,table,atVertex,hM,separate,Int.toNat_add, Int.toNat_mul] <;> omega
  let s4 := s3.assign 1090 (v:ℤ)
  have e4 : Executes n m (.op (.fetch 1090 242 1092)) s3 s4 64 := by
    apply Executes.op
    simp [s4, s3, s2, s1, Operation.next,regularNext,State.assign,State.save,one,base,remReg,len,idx,vector,buffer,table,atVertex,hM,separate,Int.toNat_add, Int.toNat_mul] <;> omega
  let s5 := s4.assign 254 (v:ℤ)
  have e5 : Executes n m (.op (.regular (.copy 254 1090))) s4 s5 1 := by
    apply Executes.op
    simp [s5, s4, s3, s2, s1, Operation.next,regularNext,State.assign,State.save,one,base,remReg,len,idx,vector,buffer,table,atVertex,hM,separate,Int.toNat_add, Int.toNat_mul] <;> omega
  let s6 := s5.assign 1097 ((q%M:ℕ):ℤ)
  have e6 : Executes n m (.op (.divide false 1097 252 70)) s5 s6 (20+8*(q/M)) := by
    apply Executes.op
    simp [s6, s5, s4, s3, s2, s1, Operation.next,regularNext,State.assign,State.save,one,base,remReg,len,idx,vector,buffer,table,atVertex,hM,separate,Int.toNat_add, Int.toNat_mul] <;> omega
  let s7 := s6.assign 255 ((q%M:ℕ):ℤ)
  have e7 : Executes n m (.op (.regular (.copy 255 1097))) s6 s7 1 := by
    apply Executes.op
    simp [s7, s6, s5, s4, s3, s2, s1, Operation.next,regularNext,State.assign,State.save,one,base,remReg,len,idx,vector,buffer,table,atVertex,hM,separate,Int.toNat_add, Int.toNat_mul] <;> omega
  let s8 := s7.assign 1100 ((q/M:ℕ):ℤ)
  have e8 : Executes n m (.op (.divide true 1100 252 70)) s7 s8 (20+8*(q/M)) := by
    apply Executes.op
    simp [s8, s7, s6, s5, s4, s3, s2, s1, Operation.next,regularNext,State.assign,State.save,one,base,remReg,len,idx,vector,buffer,table,atVertex,hM,separate,Int.toNat_add, Int.toNat_mul] <;> omega
  let s9 := s8.assign 252 ((q/M:ℕ):ℤ)
  have e9 : Executes n m (.op (.regular (.copy 252 1100))) s8 s9 1 := by
    apply Executes.op
    simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, Operation.next,regularNext,State.assign,State.save,one,base,remReg,len,idx,vector,buffer,table,atVertex,hM,separate,Int.toNat_add, Int.toNat_mul] <;> omega
  let s10 := s9.save (buf+v) ((q%M:ℕ):ℤ)
  have e10 : Executes n m (.op (.save 250 254 255)) s9 s10 64 := by
    apply Executes.op
    simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Operation.next,regularNext,State.assign,State.save,one,base,remReg,len,idx,vector,buffer,table,atVertex,hM,separate,Int.toNat_add, Int.toNat_mul] <;> omega
  let s11 := s10.assign 1111 ((v*M:ℕ):ℤ)
  have e11 : Executes n m (.op (.multiply 1111 254 70)) s10 s11 (8+6*M) := by
    apply Executes.op
    simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Operation.next,regularNext,State.assign,State.save,one,base,remReg,len,idx,vector,buffer,table,atVertex,hM,separate,Int.toNat_add, Int.toNat_mul] <;> omega
  let s12 := s11.assign 1110 ((v*M+q%M:ℕ):ℤ)
  have e12 : Executes n m (.op (.regular (.add 1110 1111 255))) s11 s12 1 := by
    apply Executes.op
    simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Operation.next,regularNext,State.assign,State.save,one,base,remReg,len,idx,vector,buffer,table,atVertex,hM,separate,Int.toNat_add, Int.toNat_mul] <;> omega
  let s13 := s12.assign 1108 (s.heap (bits+(v*M+q%M)))
  have e13 : Executes n m (.op (.fetch 1108 81 1110)) s12 s13 64 := by
    apply Executes.op
    have addr : s12.reg 81 + s12.reg 1110 = ((bits+(v*M+q%M):ℕ):ℤ) := by
      simp [s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,State.assign,State.save,table]
    have cell : s12.heap (bits+(v*M+q%M)) = s.heap (bits+(v*M+q%M)) := by
      change (Function.update s.heap (buf+v) ((q%M:ℕ):ℤ)) _ = _
      exact Function.update_of_ne separate _ _
    simp only [Operation.next,addr,Int.natCast_nonneg,if_true,Int.toNat_natCast,cell,s13]
  change ∃ t k, Executes n m (chain [.op (.regular (.set 1095 1)),.op (.regular (.sub 1093 243 1095)),.op (.regular (.sub 1092 1093 245)),.op (.fetch 1090 242 1092),.op (.regular (.copy 254 1090)),.op (.divide false 1097 252 70),.op (.regular (.copy 255 1097)),.op (.divide true 1100 252 70),.op (.regular (.copy 252 1100)),.op (.save 250 254 255),.op (.multiply 1111 254 70),.op (.regular (.add 1110 1111 255)),.op (.fetch 1108 81 1110),.cond 6 1108 (.op (.regular (.set 1107 0))) (.op (.regular (.set 1107 1))),.cond 6 1107 (chain [.op (.regular (.set 1115 0)),.op (.regular (.copy 253 1115))]) .skip]) s t k ∧ _
  by_cases good : 1 ≤ s.heap (bits+(v*M+q%M))
  · let s14 := s13.assign 1107 0
    have e14 : Executes n m (.cond 6 1108 (.op (.regular (.set 1107 0))) (.op (.regular (.set 1107 1)))) s13 s14 2 := by
      apply Executes.yes (a:=1)
      · simpa [s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,State.assign,State.save,one] using good
      · exact .op rfl
    let t := s14
    have e15 : Executes n m (.cond 6 1107 (chain [.op (.regular (.set 1115 0)),.op (.regular (.copy 253 1115))]) .skip) s14 t 2 := by
      apply Executes.no (a:=1)
      · simp [s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,State.assign,State.save,one,good]
      · exact .skip _
    refine ⟨t,_, (.seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 (.seq e7 (.seq e8 (.seq e9 (.seq e10 (.seq e11 (.seq e12 (.seq e13 (.seq e14 (.seq e15 (.skip _)))))))))))))))),by omega,?_,?_,?_,?_,rfl,rfl,?_⟩
    all_goals first
      | intro j hj; simp at hj; simp [t,s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,State.assign,State.save,hj]
      | simp [t,s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,State.assign,State.save,good]
  · let s14 := s13.assign 1107 1
    have e14 : Executes n m (.cond 6 1108 (.op (.regular (.set 1107 0))) (.op (.regular (.set 1107 1)))) s13 s14 2 := by
      apply Executes.no (a:=1)
      · simpa [s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,State.assign,State.save,one] using good
      · exact .op rfl
    let t := (s14.assign 1115 0).assign 253 0
    have e15 : Executes n m (.cond 6 1107 (chain [.op (.regular (.set 1115 0)),.op (.regular (.copy 253 1115))]) .skip) s14 t 6 := by
      apply Executes.yes (a:=5)
      · simp [s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,State.assign,State.save,one,good]
      · exact .seq (.op (o:=.regular (.set 1115 0)) (s:=s14) (t:=s14.assign 1115 0) (k:=1) rfl) (.seq (.op (o:=.regular (.copy 253 1115)) (k:=1) (by simp [Operation.next,regularNext,t,State.assign])) (.skip _))
    refine ⟨t,_, (.seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 (.seq e7 (.seq e8 (.seq e9 (.seq e10 (.seq e11 (.seq e12 (.seq e13 (.seq e14 (.seq e15 (.skip _)))))))))))))))),by omega,?_,?_,?_,?_,rfl,rfl,?_⟩
    all_goals first
      | intro j hj; simp at hj; simp [t,s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,State.assign,State.save,hj]
      | simp [t,s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,State.assign,State.save,good]

#print axioms solution
