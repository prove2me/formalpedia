-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.native_ordered_production_table
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T23:24:07.011437+00:00
-- url     : https://prove2.me/submissions/6aa0a082-534c-4dad-8aaa-df5b83196645
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_native_live_production_table
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_native_slot_classification
set_option linter.all false
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
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
namespace StableMSR.Recovery.NativeWriter.Relative.Machine
theorem word_inj {j f a b : ℕ} (hj : j<8) (hf : f<8) : word j a=word f b ↔ j=f ∧ a=b := by
  unfold word;omega


end StableMSR.Recovery.NativeWriter.Relative.Machine
namespace StableMSR.Recovery.NativeWriter.Production.RAM
open Relative.Machine
theorem cell_ne_word {a i j k : ℕ} (hk:k<7) : cell a i≠word k j := by
  unfold cell;rw [ne_eq,word_inj (by decide) (by omega)];omega
theorem word_ne_cell {a i j k : ℕ} (hk:k<7) : word k j≠cell a i := Ne.symm (cell_ne_word hk)

end StableMSR.Recovery.NativeWriter.Production.RAM
namespace StableMSR.Recovery.NativeWriter.Production.Classify
open Compiler OracleQueries WindowCSP WindowProfiles Relative.Machine
open scoped Classical
noncomputable def kind (x:World) (r:ℕ) : ℤ :=
  if r%x.n∈keys x (r/x.n) then if 0<scale x (r/x.n) then 0 else -2 else -1

end StableMSR.Recovery.NativeWriter.Production.Classify
namespace StableMSR.Recovery.NativeWriter.Production.Classify
open Compiler OracleQueries WindowCSP WindowProfiles RAM Relative.Machine
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1400000

/-- The absent and stopped encodings consist of two header words. -/
def header : List Op := [.pointerConst 27 (cell 0 0),.pointerConst 28 0,.integerStore 27 28,
  .pointerConst 27 (cell 0 1),.integerStore 27 6]

theorem empty_script (x:World) (h w r:ℕ) (hs:kind x r<0) : regionalScript x h w r=⟨[],kind x r⟩ := by
  by_cases key:r%x.n∈keys x (r/x.n)
  · by_cases live:0<scale x (r/x.n)
    · simp [kind,key,live] at hs
    · simp [regionalScript,kind,key,live]
  · simp [regionalScript,kind,key]

theorem live_of_sign (x:World) (r:ℕ) (hs:¬kind x r≤-1) : r%x.n∈keys x (r/x.n) ∧ 0<scale x (r/x.n) := by
  by_cases key:r%x.n∈keys x (r/x.n)
  · by_cases live:0<scale x (r/x.n)
    · exact ⟨key,live⟩
    · simp [kind,key,live] at hs
  · simp [kind,key] at hs

theorem header_run (x:World) (s:Store) (h w r:ℕ) (rd:Ready x s) (v:s.ptrs 6=kind x r) (hs:kind x r<0) :
    let t:=perform x.dist s header
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    Stored x.n t.imem (regionalScript x h w r) := by
  let t:=perform x.dist s header
  have regs (i:ℕ) (hi:i<27) : t.ptrs i=s.ptrs i:=by
    simp [t,header,perform,Op.eval,Function.update_of_ne (by omega:i≠27),Function.update_of_ne (by omega:i≠28)]
  have mem (q:ℤ) : t.imem q=if q=cell 0 1 then kind x r else if q=cell 0 0 then 0 else s.imem q:=by
    simp [t,header,perform,Op.eval,Function.update_apply,v]
  refine ⟨⟨fun ax=>(regs _ (by cases ax <;> decide)).trans (rd.1 ax),?_⟩,?_,?_,?_⟩
  · intro q;rw [mem,if_neg (by unfold cell word;omega),if_neg (by unfold cell word;omega),rd.2]
  · intro i hi;exact regs i (by simp at hi;omega)
  · intro j lo hi a;rw [mem];simp [word_ne_cell (by omega:j<7)]
  · rw [empty_script x h w r hs]
    exact ⟨by rw [mem];simp [cell,word],by rw [mem];simp,fun i hi=>by simp at hi⟩

end StableMSR.Recovery.NativeWriter.Production.Classify
namespace StableMSR.Recovery.NativeWriter.Production.Classify
open Compiler OracleQueries WindowCSP WindowProfiles RAM Relative.Machine
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

theorem source_from_live (input:∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,
  ∀(x : World) (s : Store),1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
  ∀r p : ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
  r%x.n∈WindowProfiles.keys x (r/x.n) → 0<scale x (r/x.n) →
  ∃t z,Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    Stored x.n t.imem (regionalScript x (budget (e:ℝ)) (widthBound (e:ℝ)) r))
    (detect:∃ (A:ℕ) (cmd:Cmd),∀(x:World) (s:Store) (r:ℕ),Ready x s → s.ptrs 3=(r:ℤ) → 0<x.n → r<x.rows*x.n →
    ∃t z,Executes x.dist cmd s t z ∧ z≤A*(1+x.n)*(1+x.rows) ∧ t.imem=s.imem ∧
      (∀i<6,t.ptrs i=s.ptrs i) ∧
      t.ptrs 6=(if r%x.n∈WindowProfiles.keys x (r/x.n) then if 0<scale x (r/x.n) then 0 else -2 else -1) ∧
      t.ptrs 14 = -1) :
    ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,Source e c D b cmd := by
  obtain ⟨c,D,b,offer⟩:=input
  obtain ⟨A,test,scan⟩:=detect
  refine ⟨A+c+8,D+2,b,?_⟩
  intro e he hl
  obtain ⟨live,guarantee⟩:=offer e he hl
  refine ⟨.seq test (.ite (.pointerLE 6 14) (line header) live),?_⟩
  intro x s k kn metric rd r p slot offset actual
  obtain ⟨t,z,go,cost,mem,low,sign,minus⟩:=scan x s r rd slot (by omega) actual
  change t.ptrs 6=kind x r at sign
  have ready:Ready x t:=⟨fun ax=>(low _ (by cases ax <;> decide)).trans (rd.1 ax),fun q=>(congrFun mem _).trans (rd.2 q)⟩
  have ts: t.ptrs 3=(r:ℤ):=(low 3 (by decide)).trans slot
  have tp: t.ptrs 4=(p:ℤ):=(low 4 (by decide)).trans offset
  have testEq:(Cond.pointerLE 6 14).test t ↔ kind x r≤-1:=by change t.ptrs 6 ≤ t.ptrs 14 ↔ _;rw [sign,minus]
  let phi:=x.cap^(D+2)*x.n^(b*parameterEnvelope (e:ℝ))
  have cap:1≤x.cap:=by unfold World.cap;omega
  have npos:1≤x.n:=by omega
  have pow:1≤x.n^(b*parameterEnvelope (e:ℝ)):=Nat.one_le_pow _ _ npos
  have cp:x.cap^2≤x.cap^(D+2):=Nat.pow_le_pow_right cap (by omega)
  have d:x.cap^D≤x.cap^(D+2):=Nat.pow_le_pow_right cap (by omega)
  have cat: (1+x.n)*(1+x.rows)≤phi:=calc
    _ ≤ x.cap*x.cap := Nat.mul_le_mul (by unfold World.cap;omega) (by unfold World.cap;omega)
    _ = x.cap^2 := by ring
    _ ≤ phi := cp.trans (Nat.le_mul_of_pos_right _ pow)
  have left:z≤A*phi:= (by simpa only [Nat.mul_assoc] using cost : z≤A*((1+x.n)*(1+x.rows))).trans (Nat.mul_le_mul_left _ cat)
  have one:1≤phi:=by nlinarith [cat,Nat.zero_le (x.n*x.rows)]
  have target:(A+c+8)*x.cap^(D+2)*x.n^(b*parameterEnvelope (e:ℝ))=(A+c+8)*phi:=by simp only [phi,Nat.mul_assoc]
  by_cases dead:kind x r≤-1
  · let v:=perform x.dist t header
    obtain ⟨fin,regs,lanes,out⟩:=header_run x t (budget (e:ℝ)) (widthBound (e:ℝ)) r ready sign (by omega)
    refine ⟨v,_,.seq go (.ite_true (testEq.mpr dead) (line_exec x.dist t _)),?_,fin,?_,?_,out⟩
    · rw [target];change z+(1+5)≤_;nlinarith
    · intro i hi;exact (regs i hi).trans (low i (by simp at hi;omega))
    · intro j lo hi a;exact (lanes j lo hi a).trans (congrFun mem _)
  · obtain ⟨key,pos⟩:=live_of_sign x r dead
    obtain ⟨v,y,compiled,time,fin,regs,lanes,out⟩:=guarantee x t k kn metric ready r p ts tp actual key pos
    refine ⟨v,_,.seq go (.ite_false (fun h=>dead (testEq.mp h)) compiled),?_,fin,?_,?_,out⟩
    · have right:y≤c*phi:=by
        apply time.trans
        calc c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ≤ c*x.cap^(D+2)*x.n^(b*parameterEnvelope (e:ℝ)) :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_left c d)
             _ = c*phi := by simp [phi,Nat.mul_assoc]
      rw [target];nlinarith
    · intro i hi;exact (regs i hi).trans (low i (by simp at hi;omega))
    · intro j lo hi a;exact (lanes j lo hi a).trans (congrFun mem _)

end StableMSR.Recovery.NativeWriter.Production.Classify
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit
theorem solution :
    ∃ c D b : ℕ, ∀ e : ℚ, 0<e → e<1 → ∃cmd : Cmd, Source e c D b cmd := Classify.source_from_live native_live_production_table native_slot_classification
