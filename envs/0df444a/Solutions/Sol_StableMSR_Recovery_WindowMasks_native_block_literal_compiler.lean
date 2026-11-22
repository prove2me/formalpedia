-- Prove2me | solution 1 for StableMSR.Recovery.WindowMasks.native_block_literal_compiler
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:28:37.394169+00:00
-- url     : https://prove2.me/submissions/99ba153e-a99a-4e5f-b16d-66b6fd0c83fc

import Definitions.Def_StableMSR_WindowBlockMasks
import Theorems.Thm_StableMSR_Recovery_WindowMasks_block_incidence_expressions
import Theorems.Thm_StableMSR_Recovery_WindowMasks_physical_block_literals
import Theorems.Thm_StableMSR_Recovery_FewBallRows_tabulate_ball_row_expressions
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
open StableMSR.Recovery.WindowMasks
open Polynomial
private def copyCell (a b : ℕ) : Cmd :=
  .seq (.atom (.pointerConst 3 a)) (.seq (.atom (.integerLoad 4 3)) (.seq (.atom (.pointerConst 3 b)) (.atom (.integerStore 3 4))))
private lemma copies {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (a b : ℕ) :
    ∃t,Executes d (copyCell a b) s t 4 ∧ (∀i<3,t.ptrs i=s.ptrs i) ∧
    ∀i : ℤ,t.imem i=if i=(b:ℤ) then s.imem (a:ℤ) else s.imem i:=by
  let u:=(Op.pointerConst 3 a).eval d s;let v:=(Op.integerLoad 4 3).eval d u
  let r:=(Op.pointerConst 3 b).eval d v;let t:=(Op.integerStore 3 4).eval d r
  refine ⟨t,.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _))),?_,?_⟩
  · intro i hi;simp [t,r,v,u,Op.eval,Function.update_of_ne,show i≠3 by omega,show i≠4 by omega]
  · intro i;by_cases h : i=(b:ℤ) <;> simp [t,r,v,u,Op.eval,Function.update,h]
theorem solution : ∃P : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (e : ℚ) (H : ℕ) (s : Store),1≤ x.k → x.k< x.n →
    IsMetricArray x.dist → let y:=worldOf x.k H x.dist s
    Ready y s → Describes x e y → ∃t z,Executes x.dist cmd s t z ∧ z≤ P.eval y.cap ∧
      Ready (worldOf x.k H x.dist t) t ∧ Presents x e (worldOf x.k H x.dist t) := by
  obtain ⟨P,tab,run⟩:=FewBallRows.tabulate_ball_row_expressions normalized block_incidence_expressions
  refine ⟨P+C 8,tab.seq ((copyCell 3 0).seq (copyCell 4 1)),?_⟩
  intro x e H s hk kn dm;dsimp only;intro start cert
  let y:=worldOf x.k H x.dist s
  obtain ⟨a,l,ex,bound,ready,wr⟩:=run y s start
  obtain ⟨b,ec,bc,bm⟩:=copies x.dist a 3 0
  obtain ⟨t,ed,tc,tm⟩:=copies x.dist b 4 1
  let z:=worldOf x.k H x.dist t
  have big : 1+5*WindowPorts.capacity y< H:=cert.space
  have h0 : 0< H:=by omega
  obtain ⟨ar,aw⟩:=wr 0 h0 0 hk
  change a.imem ((addr x.k 0 0:ℕ):ℤ)=normalized y 0 0 false at ar
  change a.imem ((addr x.k 0 0+1:ℕ):ℤ)=normalized y 0 0 true at aw
  have az : a.imem 3=(rawSize y:ℤ):=by simpa [addr,normalized] using ar
  have aa : a.imem 4=y.mem 1:=by simpa [addr,normalized] using aw
  have out0 : z.mem 0=(rawSize y:ℤ):=by change t.imem 0=_;simp [tm,bm,az]
  have out1 : z.mem 1=y.mem 1:=by change t.imem 1=_;simp [tm,bm,aa]
  have old (i : ℕ) (hi : 1< i) : z.mem i=a.imem (i:ℤ):=by
    change t.imem (i:ℤ)=_;rw [tm,if_neg (by omega),bm,if_neg (by omega)]
  have rd : Ready z t:=by
    refine ⟨?_,fun _=>rfl⟩
    intro ax;have lt : ax.reg<3:=by cases ax <;> decide
    rw [tc _ lt,bc _ lt];exact ready.1 ax
  have fill : Writes y z normalized:=by
    intro r hr j hj side;obtain ⟨one,two⟩:=wr r hr j hj
    have lo : 1< addr x.k r j:=by unfold addr;omega
    cases side
    · change z.mem (addr x.k r j)=_;rw [old _ lo];exact one
    · change z.mem (addr x.k r j+1)=_;rw [old _ (by omega)];exact two
  refine ⟨t,_,.seq ex (.seq ec ed),?_,rd,?_⟩
  · simp only [eval_add,eval_C];change l+(4+4)≤ P.eval y.cap+8;omega
  by_cases nonneg : 0≤ y.mem 0
  · have same: z.mem 0=y.mem 0:=out0.trans (Int.toNat_of_nonneg nonneg)
    exact physical_block_literals x e H y.mem z.mem hk kn dm cert same out1 fill
  · have zero : rawSize y=0:=Int.toNat_of_nonpos (by omega)
    have empty : x.rows=0:=by
      by_contra ne
      have h:=(cert.targets 0 (by omega) 0 (by omega)).1
      change 0*x.n+0< rawSize y at h;rw [zero] at h;omega
    refine ⟨?_,out1.trans cert.scenes,?_⟩
    · have sizes : rawSize z=rawSize y:=by change (z.mem 0).toNat=_;rw [out0,Int.toNat_natCast]
      change 1+5*(1+rawSize z*x.n*x.n)< H;rw [sizes];exact big
    · intro u hu;omega
