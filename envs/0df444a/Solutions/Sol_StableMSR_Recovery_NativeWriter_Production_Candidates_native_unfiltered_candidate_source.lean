-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.native_unfiltered_candidate_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T00:21:33.484795+00:00
-- url     : https://prove2.me/submissions/8089c616-8a69-4013-a0ae-32547f910610
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_native_integer_candidate_source
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_native_metric_table
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_integer_instance_exact
set_option linter.all false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open Compiler OracleQueries WindowCSP SingleCircuit
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem transfer {n:ℕ} {d:Fin n→Fin n→ℝ} (g:Fin n→Fin n→ℝ) {c:Cmd} {s t:Store} {z:ℕ}
    (ex:Executes d c s t z) (h:IntegerCmd c) : Executes g c s t z := by
  induction ex with
  | skip=>exact .skip _
  | atom o s=> cases o <;> first | exact .atom _ _ | contradiction
  | seq _ _ ih jh=>exact .seq (ih h.1) (jh h.2)
  | ite_true cond _ ih=>exact .ite_true cond (ih h.2.1)
  | ite_false cond _ ih=>exact .ite_false cond (ih h.2.2)
  | while_false cond=>exact .while_false cond
  | while_true cond _ _ ih jh=>exact .while_true cond (ih h.2) (jh h)

theorem word_ne_table (j a i:ℕ) (lo:1≤j) (hi:j≤6) : word j a≠cell 6 i:=by
  intro eq;unfold cell word at eq;push_cast at eq;omega

theorem compose (integerSource : ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,IntegerCmd cmd ∧
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃t z,Executes (fun (_ _:Fin x.n)=>(0:ℝ)) cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    ∃enc:Key→ℕ,Function.Injective enc ∧
      Input x.n t.imem (tape enc (data x s.imem r (budget (e:ℝ))) (widthBound (e:ℝ)))) (nativeTable : ∃cmd:Cmd,∀(x:World) (s:Store),Ready x s → 0<x.n → ∀r:ℕ,s.ptrs 3=(r:ℤ) → r<x.rows*x.n →
    ∃t z,Executes x.dist cmd s t z ∧
      z≤200*(1+x.rows+(1+x.n*x.n)^2) ∧ t.queries=s.queries+x.n*x.n+1 ∧
      Ready x t ∧ (∀j<6,t.ptrs j=s.ptrs j) ∧
      (∀q:ℤ,(∀j:ℕ,q≠cell 6 j) → t.imem q=s.imem q) ∧ Prepared x (scale x (r/x.n)) t.imem)
    (exactTable : ∀(x:World) (W:Cluster x.n) (R:ℝ) (h:ℕ) (m:ℤ→ℤ)
    (hn:0<x.n) (pos:0<R) (metric:IsMetricArray x.dist) (t:Prepared x R m) ,
    SingleCodes.instanceOf (matrix x m) W (unit x.n:ℝ) h=SingleCodes.instanceOf x W R h ∧ Bounded x.n m) :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,
  ∀(x : World) (s : Store),1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
  ∀r p : ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
  r%x.n∈WindowProfiles.keys x (r/x.n) → 0<scale x (r/x.n) →
  ∃t z,Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    ∃enc:Key→ℕ,Function.Injective enc ∧
      let d:=SingleCodes.instanceOf x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) (budget (e:ℝ))
      Input x.n t.imem (tape enc d (widthBound (e:ℝ))) := by
  obtain ⟨c,D,b,generate⟩:=integerSource
  obtain ⟨pre,preOK⟩:=nativeTable
  refine ⟨1200+c,D+4,b,?_⟩
  intro e he hl
  obtain ⟨cmd,pure,run⟩:=generate e he hl
  refine ⟨.seq pre cmd,?_⟩
  intro x s hk kn metric rd r p slot off live key pos
  have hn:0<x.n:=by omega
  obtain ⟨u,y,ey,cy,queries,ru,ptr,frame,table⟩:=preOK x s rd hn r slot live
  have eq:=exactTable x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) (budget (e:ℝ)) u.imem hn pos metric table
  obtain ⟨v,z,ez,cz,rv,regs,words,enc,inj,tapeOK⟩:=run x u hk kn ru eq.2 r p
    ((ptr 3 (by decide)).trans slot) ((ptr 4 (by decide)).trans off) live key
  refine ⟨v,y+z,.seq ey (transfer x.dist ez pure),?_,rv,?_,?_,enc,inj,?_⟩
  · let E:=x.n^(b*parameterEnvelope (e:ℝ))
    have cp:1≤x.cap:=by unfold World.cap;omega
    have nc:x.n≤x.cap:=by unfold World.cap;omega
    have rows:x.rows≤x.cap:=by unfold World.cap;omega
    have c2:1≤x.cap^2:=Nat.one_le_pow _ _ cp
    have c4:1≤x.cap^4:=Nat.one_le_pow _ _ cp
    have c14:x.cap≤x.cap^4:=by simpa using (Nat.pow_le_pow_right (n:=x.cap) cp (show 1≤4 by decide))
    have n2:x.n*x.n≤x.cap^2:=by simpa [pow_two] using Nat.mul_le_mul nc nc
    have box:1+x.n*x.n≤2*x.cap^2:=by omega
    have sq: (1+x.n*x.n)^2≤4*x.cap^4:=calc
      _≤(2*x.cap^2)^2:=Nat.pow_le_pow_left box _
      _=4*x.cap^4:=by ring
    have py:y≤1200*x.cap^4:=by omega
    have small:x.cap^4≤x.cap^(D+4):=Nat.pow_le_pow_right cp (by omega)
    have large:x.cap^D≤x.cap^(D+4):=Nat.pow_le_pow_right cp (by omega)
    have ee:1≤E:=Nat.one_le_pow _ _ hn
    have left:y≤1200*x.cap^(D+4)*E:=by
      have h:=Nat.mul_le_mul (Nat.mul_le_mul_left 1200 small) ee
      exact py.trans (by simpa using h)
    have right:z≤c*x.cap^(D+4)*E:=cz.trans (Nat.mul_le_mul_right E (Nat.mul_le_mul_left c large))
    simpa only [Nat.add_mul] using Nat.add_le_add left right
  · intro j hj;exact (regs j hj).trans (ptr j (by simp at hj;omega))
  · intro j lo hi a;exact (words j lo hi a).trans (frame _ (word_ne_table j a · lo hi))
  · simpa only [data,eq.1] using tapeOK

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
theorem solution :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,
  ∀(x : World) (s : Store),1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
  ∀r p : ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
  r%x.n∈WindowProfiles.keys x (r/x.n) → 0<scale x (r/x.n) →
  ∃t z,Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    ∃enc:Key→ℕ,Function.Injective enc ∧
      let d:=SingleCodes.instanceOf x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) (budget (e:ℝ))
      Input x.n t.imem (tape enc d (widthBound (e:ℝ))) := StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.compose StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.native_integer_candidate_source StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.native_metric_table StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.integer_instance_exact
