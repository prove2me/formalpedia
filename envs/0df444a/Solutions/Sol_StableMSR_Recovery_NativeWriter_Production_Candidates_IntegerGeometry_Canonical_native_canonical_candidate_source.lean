-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.native_canonical_candidate_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T01:24:45.11896+00:00
-- url     : https://prove2.me/submissions/00c87b57-d61d-477d-8e4c-1b950bfc4697
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_StableMSR_CandidateInterpreter
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_bounded_tape_evaluation
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_bounded_run_is_native
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Naming
open SingleCircuit
theorem push_pos (a z:ℕ) : 0<push a z := by induction z <;> simp [push] <;> omega
theorem push_inj (a b x y:ℕ) (h:push a x=push b y) : a=b ∧ x=y := by
  induction x generalizing y with
  | zero=>cases y <;> simp only [push] at h <;> omega
  | succ x ih=>
    cases y with
    | zero=>simp only [push] at h;omega
    | succ y=>
      simp only [push] at h
      obtain ⟨eq,eq'⟩:=ih y (by omega);exact ⟨eq,by omega⟩

theorem code_inj : Function.Injective code := by
  intro xs;induction xs with
  | nil=>
    intro ys h;cases ys with
    | nil=>rfl
    | cons y ys=>have :=push_pos (code ys) y;change 0=push (code ys) y at h;omega
  | cons x xs ih=>
    intro ys h;cases ys with
    | nil=>have :=push_pos (code xs) x;change push (code xs) x=0 at h;omega
    | cons y ys=>
      obtain ⟨tail,eq⟩:=push_inj _ _ _ _ h
      rw [eq,ih tail]

theorem pair_inj : Function.Injective pairs := by
  intro xs;induction xs with
  | nil=>intro ys h;cases ys <;> simp_all [pairs]
  | cons p xs ih=>
    intro ys h;cases ys with
    | nil=>simp [pairs] at h
    | cons q ys=>
      change p.1::p.2::pairs xs=q.1::q.2::pairs ys at h
      simp only [List.cons.injEq] at h
      rw [Prod.ext h.1 h.2.1,ih h.2.2]

theorem split_digits (c c' a a':List ℕ)
    (h:c.map Nat.succ++(0::a)=c'.map Nat.succ++(0::a')) : c=c' ∧ a=a' := by
  induction c generalizing c' with
  | nil=>cases c' <;> simp_all
  | cons p c ih=>
    cases c' with
    | nil=>simp at h
    | cons q c'=>
      simp only [List.map_cons,List.cons_append,List.cons.injEq,Nat.succ.injEq] at h
      obtain ⟨he,ha⟩:=ih c' h.2;exact ⟨by rw [h.1,he],ha⟩

theorem name_injective : Function.Injective name := by
  rintro ⟨c,a⟩ ⟨c',a'⟩ h
  have eq:=congrArg List.reverse (code_inj h)
  simp only [List.reverse_reverse,digits,List.append_assoc,List.singleton_append] at eq
  obtain ⟨cEq,aEq⟩:=split_digits _ _ _ _ eq
  exact Prod.ext cEq (pair_inj aEq)

theorem accumulated (xs:List ℕ) : xs.foldl push 0=code xs.reverse := by
  induction xs using List.reverseRecOn with
  | nil=>rfl
  | append_singleton xs a ih=>simp [List.foldl_append,ih,code]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Naming

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open Compiler OracleQueries WindowCSP SingleCircuit
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem to_raw (checked : ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃F t,F≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    CandidateRAM.run F [CandidateRAM.code (budget (e:ℝ)) (widthBound (e:ℝ))] (CandidateRAM.banks s)=some t ∧
    (∀q:ℤ,(∀i:ℕ,q≠cell 5 i ∧ q≠cell 7 i) → t.mem q=s.imem q) ∧
    Candidates.Input x.n t.mem (tape CandidateRAM.Naming.name (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ))))
    (execution : ∀ {n:ℕ} (d:Fin n→Fin n→ℝ) (s:Store) (h w fuel:ℕ) (t:Banks),
      run fuel [code h w] (banks s)=some t →
      ∃z,Executes d (program h w) s (restore s t) z ∧ z≤2*fuel ∧ (∀j<6,t.reg j=s.ptrs j))
    (injective:Function.Injective Naming.name) :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,IntegerCmd cmd ∧
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃t z,Executes (fun (_ _:Fin x.n)=>(0:ℝ)) cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    ∃enc:Key→ℕ,Function.Injective enc ∧
      Input x.n t.imem (tape enc (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ))) := by
  obtain ⟨c,D,b,ok⟩:=checked
  refine ⟨2*c,D,b,?_⟩
  intro e he hl
  let h:=budget (e:ℝ)
  let w:=widthBound (e:ℝ)
  refine ⟨program h w,integer h w,?_⟩
  intro x s hk kn rd bounded r p regR regP live key
  obtain ⟨F,t,cf,done,frame,tapeOK⟩:=ok e he hl x s hk kn rd bounded r p regR regP live key
  obtain ⟨z,ex,steps,regs⟩:=execution (fun (_ _:Fin x.n)=>(0:ℝ)) s h w F t done
  refine ⟨restore s t,z,ex,?_,?_,?_,?_,Naming.name,injective,tapeOK⟩
  · apply steps.trans
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 cf
  · refine ⟨fun ax=>(regs _ (by cases ax <;> decide)).trans (rd.1 ax),?_⟩
    intro q;exact (frame (q:ℤ) (by intro i;unfold cell word;push_cast;constructor <;> omega)).trans (rd.2 q)
  · intro i hi;exact regs i (by simp at hi;omega)
  · intro j lo hi a
    apply frame
    intro i;unfold cell word;push_cast;constructor <;> omega
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical
theorem solution :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,IntegerCmd cmd ∧
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃t z,Executes (fun (_ _:Fin x.n)=>(0:ℝ)) cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    ∃enc:Key→ℕ,Function.Injective enc ∧
      Input x.n t.imem (tape enc (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ))) := CandidateRAM.to_raw CandidateRAM.bounded_tape_evaluation CandidateRAM.bounded_run_is_native CandidateRAM.Naming.name_injective
