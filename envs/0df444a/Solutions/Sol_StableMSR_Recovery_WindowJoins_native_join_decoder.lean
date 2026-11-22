-- Prove2me | solution 1 for StableMSR.Recovery.WindowJoins.native_join_decoder
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:51:44.086071+00:00
-- url     : https://prove2.me/submissions/b6dc83dd-7758-4b13-8f39-ebbec36d9944

import Theorems.Thm_StableMSR_Recovery_WindowJoins_join_row_expressions
import Theorems.Thm_StableMSR_Recovery_WindowJoins_clocked_row_iteration
import Theorems.Thm_StableMSR_Recovery_WindowJoins_topological_join_evaluation
import Theorems.Thm_StableMSR_Recovery_WindowJoins_join_outputs_are_profiles
import Theorems.Thm_StableMSR_Recovery_OracleQueries_bounded_oracle_expression_compiler
import Definitions.Def_StableMSR_WindowJoins
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles (Mem replace profileSpec Profiles Owned piece keys index active token contains)
open StableMSR.Recovery.RegionalBallDP (Word field word legalize weight Writes)
open StableMSR.Recovery.WindowJoins
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open Polynomial
theorem solution : ∃p : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (e : ℚ) (H : ℕ) (s : Store),
    0< x.k → 0< x.n → let y:=worldOf x.k H x.dist s
    Ready y s → Encodes x e y → ∃t z,Executes x.dist cmd s t z ∧ z≤ p.eval y.cap ∧
    Ready (worldOf x.k x.rows x.dist t) t ∧ Profiles x e (worldOf x.k x.rows x.dist t).mem := by
  obtain ⟨F,G,J,S⟩:=join_row_expressions
  obtain ⟨p,dp,run⟩:=clocked_row_iteration seed advance project F G J (by intro x;simp [seed])
    (by intro x;simp [advance])
  obtain ⟨q,engine⟩:=bounded_oracle_expression_compiler _ S
  obtain ⟨read,fetch⟩:=engine 3 (fun _=>0) (by decide) (fun _=>by decide)
  refine ⟨p+q+1,dp.seq (read.seq (.atom (.pointerCopy 2 3))),?_⟩
  intro x e H s hk hn;dsimp only;intro ready cert
  let y:=worldOf x.k H x.dist s
  have pos : 0< H:=by have h:=cert.shape;change 1+5*slots y< H at h;omega
  obtain ⟨a,l,ea,ta,ar,h,ini,steps,last⟩:=run y s hk pos ready
  let z:=worldOf x.k H x.dist a
  obtain ⟨same,ok⟩:=topological_join_evaluation y hk hn cert.shape h z.mem ini steps last
  have content:=join_outputs_are_profiles x e H y.mem z.mem hn hk cert ok
  obtain ⟨t,j,et,keep,val,bound⟩:=fetch z a (fun _=>x.n) ar (fun _=>ar.1 .points)
  let final:=(Op.pointerCopy 2 3).eval x.dist t
  have restore : t.ptrs 3=(x.rows:ℤ):=(congrArg Prod.fst val).trans (same.trans cert.scenes)
  have point : t.ptrs 0=(x.n:ℤ):=(keep.1 _ (by decide)).1.trans (ar.1 .points)
  have block : t.ptrs 1=(x.k:ℤ):=(keep.1 _ (by decide)).1.trans (ar.1 .blocks)
  have mem : (worldOf x.k x.rows x.dist final).mem=z.mem:=by funext i;exact congrFun keep.2 (i:ℤ)
  refine ⟨final,_,.seq ea (.seq et (.atom _ _)),?_,⟨?_,fun _=>rfl⟩,by rw [mem];exact content⟩
  · simp only [eval_add,eval_one];change l+(j+1)≤ p.eval y.cap+q.eval y.cap+1
    change j≤ q.eval y.cap at bound;omega
  · intro a;cases a <;> simp [final,Op.eval,Function.update,World.size,Axis.reg,worldOf,point,block,restore]
