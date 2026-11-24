-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.native_live_production_table
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T23:41:34.898484+00:00
-- url     : https://prove2.me/submissions/d1eaf7de-6e91-4e2a-8da9-bf0d95c8ef2f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_native_unfiltered_candidate_source
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_native_candidate_filter
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_unfiltered_scan_is_exact
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_unfiltered_candidate_bound
set_option linter.all false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates
open Compiler OracleQueries WindowCSP SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
theorem live_from_raw (raw : ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,
  ∀(x : World) (s : Store),1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
  ∀r p : ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
  r%x.n∈WindowProfiles.keys x (r/x.n) → 0<scale x (r/x.n) →
  ∃t z,Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    ∃enc:Key→ℕ,Function.Injective enc ∧
      let d:=SingleCodes.instanceOf x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) (budget (e:ℝ))
      Input x.n t.imem (tape enc d (widthBound (e:ℝ))))
    (native : ∃ (A:ℕ) (cmd:Cmd),∀(x:World) (s:Store) (xs:List Candidates.Instr),Ready x s → Input x.n s.imem xs →
    ∃t z,Executes x.dist cmd s t z ∧ z≤A*(1+x.n)*(1+xs.length) ∧ Ready x t ∧
      (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧ (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
      Stored x.n t.imem (Candidates.eval xs))
    (exactScan : ∀(enc:Key→ℕ),Function.Injective enc → ∀(d:Instance) (w:ℕ),Candidates.eval (tape enc d w)=⟨(chart d w).1,((chart d w).2:ℤ)⟩)
    (limit : ∀(x:World) (u i:ℕ) (e:ℚ) (enc:Key→ℕ),0<e → e<1 → 2≤x.n →
      (tape enc (SingleCodes.instanceOf x (WindowProfiles.piece x u i) (scale x u) (budget (e:ℝ))) (widthBound (e:ℝ))).length≤x.n^(75*parameterEnvelope (e:ℝ))) :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,
  ∀(x : World) (s : Store),1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
  ∀r p : ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
  r%x.n∈WindowProfiles.keys x (r/x.n) → 0<scale x (r/x.n) →
  ∃t z,Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    Stored x.n t.imem (regionalScript x (budget (e:ℝ)) (widthBound (e:ℝ)) r) := by
  obtain ⟨c,D,b,raw⟩:=raw
  obtain ⟨A,filter,filterOK⟩:=native
  refine ⟨c+2*A,D+1,b+75,?_⟩
  intro e he hl
  obtain ⟨emit,emitOK⟩:=raw e he hl
  refine ⟨.seq emit filter,?_⟩
  intro x s k kn metric rd r p slot off actual key live
  let d:=SingleCodes.instanceOf x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) (budget (e:ℝ))
  let w:=widthBound (e:ℝ)
  obtain ⟨t,z,first,cost,ready,regs,mem,enc,inj,buf⟩:=emitOK x s k kn metric rd r p slot off actual key live
  let xs:=tape enc d w
  obtain ⟨v,y,second,bound,endReady,low,cols,stored⟩:=filterOK x t xs ready buf
  have matchTable:Candidates.eval xs=regionalScript x (budget (e:ℝ)) w r:=by
    simpa only [regionalScript,key,live,ite_true,d,w,xs] using exactScan enc inj d w
  rw [matchTable] at stored
  refine ⟨v,z+y,.seq first second,?_,endReady,fun j hj=>(low j hj).trans (regs j hj),
    fun j a b k=>(cols j a b k).trans (mem j a b k),stored⟩
  have sz:=limit x (r/x.n) (r%x.n) e enc he hl (by omega)
  change xs.length≤_ at sz
  let E:=parameterEnvelope (e:ℝ)
  have hc:1≤x.cap:=by unfold World.cap;omega
  have nc:1+x.n≤x.cap:=by unfold World.cap;omega
  have hn:1≤x.n:=by omega
  have pow1:1≤x.n^(75*E):=Nat.one_le_pow _ _ hn
  have size:1+xs.length≤2*x.n^(75*E):=by change xs.length≤x.n^(75*E) at sz;omega
  have d1:x.cap^D≤x.cap^(D+1):=Nat.pow_le_pow_right hc (by omega)
  have d2:x.cap≤x.cap^(D+1):=by simpa using (Nat.pow_le_pow_right (n:=x.cap) hc (show 1≤D+1 by omega))
  have e1:x.n^(b*E)≤x.n^((b+75)*E):=Nat.pow_le_pow_right hn (Nat.mul_le_mul_right E (by omega))
  have e2:x.n^(75*E)≤x.n^((b+75)*E):=Nat.pow_le_pow_right hn (Nat.mul_le_mul_right E (by omega))
  have left:=cost.trans (Nat.mul_le_mul (Nat.mul_le_mul_left c d1) e1)
  have right:y≤(2*A)*x.cap^(D+1)*x.n^((b+75)*E):=calc
    y ≤ A*(1+x.n)*(1+xs.length) := bound
    _ ≤ A*x.cap^(D+1)*(2*x.n^(75*E)) := Nat.mul_le_mul (Nat.mul_le_mul_left A (nc.trans d2)) size
    _ = (2*A)*x.cap^(D+1)*x.n^(75*E) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ e2
  simpa only [Nat.add_mul] using Nat.add_le_add left right
end StableMSR.Recovery.NativeWriter.Production.Candidates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates
theorem solution :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,
  ∀(x : World) (s : Store),1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
  ∀r p : ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
  r%x.n∈WindowProfiles.keys x (r/x.n) → 0<scale x (r/x.n) →
  ∃t z,Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    Stored x.n t.imem (regionalScript x (budget (e:ℝ)) (widthBound (e:ℝ)) r) := live_from_raw native_unfiltered_candidate_source native_candidate_filter unfiltered_scan_is_exact unfiltered_candidate_bound
