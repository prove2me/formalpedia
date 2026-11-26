-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.decode_boundary_scratch_vector
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T01:02:37.307738+00:00
-- url     : https://prove2.me/submissions/a1b7426e-f754-4bf0-bbfe-495e28989195

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_decode_one_boundary_digit
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
open Scene.CutTraversal
theorem solution (n : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (M q L vec buf bits : ℕ) (vertex : ℕ → ℕ)
    (pos : 0 < M) (one : s.reg 6 = 1) (base : s.reg 70 = (M:ℤ))
    (initial : s.reg 252 = (q:ℤ)) (len : s.reg 243 = (L:ℤ))
    (vector : s.reg 242 = (vec:ℤ)) (buffer : s.reg 250 = (buf:ℤ)) (table : s.reg 81 = (bits:ℤ))
    (readVertex : ∀ i < L, s.heap (vec+(L-1-i)) = (vertex i:ℤ))
    (bounded : ∀ i < L, vertex i < n) (vecEnd : vec+L ≤ buf) (tableEnd : bits+n*M ≤ buf) :
    let loopCode := ((listOf ordinalBody)[3]?).getD .skip
    let digit := fun i => (q / M^i) % M
    let heapAt := (List.range L).foldl (fun (h : ℕ → ℤ) i =>
      Function.update h (buf+vertex i) (digit i:ℤ)) s.heap
    let ok := (List.range L).all (fun i => decide (1 ≤ s.heap (bits+(vertex i*M+digit i))))
    ∃ t k, Logical.Executes n m loopCode s t k ∧ k ≤ 9+L*(405+6*M+16*q) ∧
      t.reg 252 = ((q/M^L:ℕ):ℤ) ∧ t.heap = heapAt ∧
      t.reg 253 = (if ok then s.reg 253 else 0) ∧
      t.output = s.output ∧ t.closed = s.closed ∧
      ∀ j, j ∉ [245,1089,1095,1093,1092,1090,254,1097,255,1100,252,1111,1110,1108,1107,1115,253] →
        t.reg j = s.reg j := by
  let loopCode := ((listOf ordinalBody)[3]?).getD .skip
  let step : Program := match ((listOf loopCode)[3]? : Option Program) with
    | some (Program.loop _ _ body) => ((listOf body)[0]?).getD .skip
    | _ => .skip
  have source : loopCode = forCount 245 1089 243 step := rfl
  let digit := fun i : ℕ => q / M^i % M
  let H := fun j => (List.range j).foldl (fun (h : ℕ → ℤ) i =>
    Function.update h (buf+vertex i) (digit i:ℤ)) s.heap
  let valid := fun j => (List.range j).all (fun i => decide (1 ≤ s.heap (bits+(vertex i*M+digit i))))
  let regs : List ℕ := [245,1089,1095,1093,1092,1090,254,1097,255,1100,252,1111,1110,1108,1107,1115,253]
  have old (j a : ℕ) (ha : a < buf) : H j a = s.heap a := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have ne : a ≠ buf+vertex j := by omega
      simpa [H,List.range_succ,List.foldl_append,Function.update_of_ne ne] using ih
  let P := fun i (t : Logical.State) =>
    t.reg 252 = ((q / M^i:ℕ):ℤ) ∧ t.heap=H i ∧ t.reg 253=(if valid i then s.reg 253 else 0) ∧
    t.output=s.output ∧ t.closed=s.closed ∧ ∀ j, j∉regs → t.reg j=s.reg j
  have control (i : ℕ) (t : Logical.State) (r : ℕ) (v : ℤ) (hr : r=245 ∨ r=1089) (ht : P i t) :
      P i (t.assign r v) := by
    obtain ⟨rem',heap,flag,out,closed,keep⟩ := ht
    rcases hr with rfl|rfl <;> refine ⟨?_,heap,?_,out,closed,?_⟩
    all_goals first
      | simpa [State.assign] using rem'
      | simpa [State.assign] using flag
      | intro j hj; have hold:=keep j hj; simp [regs] at hj; simpa [State.assign,hj] using hold
  have start : P 0 s := by
    refine ⟨by simpa using initial,rfl,by simp [valid],rfl,rfl,fun _ _ => rfl⟩
  have run := source_for (N:=n) (input:=m) 245 1089 243 L (400+6*M+16*q) step P (by decide) (by decide) s len
    (control _ _ _ _ (.inr rfl) (control _ _ _ _ (.inr rfl) (control _ _ _ _ (.inl rfl) start))) (by
    intro i hi t ht ix last
    obtain ⟨rem',heap,flag,out,closed,keep⟩ := ht
    have back : L-1-i+i+1=L := by omega
    have vl : vec+(L-1-i) < buf := by omega
    have tvertex := (congrFun heap (vec+(L-1-i))).trans ((old _ _ vl).trans (readVertex i hi))
    have dlt : digit i < M := Nat.mod_lt _ pos
    have slot : vertex i*M+digit i < n*M := by
      calc vertex i*M+digit i < vertex i*M+M := Nat.add_lt_add_left dlt _
           _ = (vertex i+1)*M := (Nat.succ_mul _ _).symm
           _ ≤ _ := Nat.mul_le_mul_right M (bounded i hi)
    have bitOld : t.heap (bits+(vertex i*M+digit i)) = s.heap (bits+(vertex i*M+digit i)) :=
      (congrFun heap _).trans (old _ _ (by omega))
    obtain ⟨y,k,ex,cost,carry,_,flag',mem',output',closed',stay⟩ := decode_one_boundary_digit n m t
      M (q/M^i) i (L-1-i) (vertex i) vec buf bits pos ((keep 6 (by decide)).trans one)
      ((keep 70 (by decide)).trans base) rem' (by rw [back];exact (keep 243 (by decide)).trans len) ix
      ((keep 242 (by decide)).trans vector) ((keep 250 (by decide)).trans buffer) ((keep 81 (by decide)).trans table)
      tvertex (by change bits+(vertex i*M+digit i) ≠ buf+vertex i;omega)
    have next : P (i+1) y := by
      refine ⟨?_,?_,?_,output'.trans out,closed'.trans closed,?_⟩
      · simpa [pow_succ,Nat.div_div_eq_div_mul] using carry
      · rw [mem',heap];simp [H,List.range_succ,List.foldl_append,digit]
      · change y.reg 253=(if valid (i+1) then _ else _)
        change y.reg 253=(if 1 ≤ t.heap (bits+(vertex i*M+digit i)) then _ else _) at flag'
        rw [flag',bitOld,flag]
        by_cases ok : 1 ≤ s.heap (bits+(vertex i*M+digit i)) <;> simp [valid,List.range_succ,ok]
      · intro j hj; exact (stay j (by simp [regs] at hj; simp [hj])).trans (keep j hj)
    have qt : (q/M^i)/M ≤ q := (Nat.div_le_self ..).trans (Nat.div_le_self ..)
    exact ⟨y,k,ex,by omega,stay _ (by decide),stay _ (by decide),control _ _ _ _ (.inl rfl) next⟩)
  obtain ⟨t,k,ex,tm,done_⟩ := run
  exact ⟨t,k,(by change Logical.Executes n m loopCode s t k; rw [source];exact ex),by simpa only [show 400+6*M+16*q+5=405+6*M+16*q by omega] using tm,done_⟩

#print axioms solution
