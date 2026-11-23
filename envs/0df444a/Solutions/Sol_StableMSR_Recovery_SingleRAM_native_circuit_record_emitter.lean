-- Prove2me | solution 1 for StableMSR.Recovery.SingleRAM.native_circuit_record_emitter
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:12:31.833802+00:00
-- url     : https://prove2.me/submissions/1482879a-722a-4d14-a32e-fb0b75d4d19a

import Definitions.Def_StableMSR_SingleCircuitRAM
import Theorems.Thm_StableMSR_Recovery_SingleRAM_fixed_circuit_packing_expressions
import Theorems.Thm_StableMSR_Recovery_SingleRAM_dense_record_board_decoding
import Theorems.Thm_StableMSR_Recovery_FewBallRows_tabulate_ball_row_expressions
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 15000
open StableMSR.Recovery StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleCircuit
open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog
open StableMSR.Recovery.WindowProfiles (subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Writes field)
open StableMSR.Recovery.SingleRAM
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
theorem solution : ∃P : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (s : Store) (g : Gates) (roots : ℕ→ℕ),
    0< x.k → 0< x.n → 1+5*(1+3*g.size*x.n*x.n)< x.rows → Ready x s → Input x g roots →
    ∃t z,Executes x.dist cmd s t z ∧ z≤ P.eval x.cap ∧ let y:=worldOf x.k x.rows x.dist t
      Ready y t ∧ y.mem 1=x.mem 1 ∧ denotes y g roots := by
  obtain ⟨P,tab,run⟩:=FewBallRows.tabulate_ball_row_expressions packCell fixed_circuit_packing_expressions
  refine ⟨P+C 8,tab.seq ((copyCell 3 0).seq (copyCell 4 1)),?_⟩
  intro x s g roots hk hn big start src
  obtain ⟨a,l,ex,bound,ready,wr⟩:=run x s start
  obtain ⟨b,ec,bc,bm⟩:=copies x.dist a 3 0
  obtain ⟨t,ed,tc,tm⟩:=copies x.dist b 4 1
  let z:=worldOf x.k x.rows x.dist t
  obtain ⟨ar,aw⟩:=wr 0 (by omega) 0 hk
  change a.imem ((addr x.k 0 0:ℕ):ℤ)=packCell x 0 0 false at ar
  change a.imem ((addr x.k 0 0+1:ℕ):ℤ)=packCell x 0 0 true at aw
  have az : a.imem 3=(3*rawSize x:ℕ):=by simpa [addr,packCell] using ar
  have aa : a.imem 4=x.mem 1:=by simpa [addr,packCell] using aw
  have head : z.mem 0=(3*g.size:ℕ):=by change t.imem 0=_;simp [tm,bm,az,src.1]
  have scene : z.mem 1=x.mem 1:=by change t.imem 1=_;simp [tm,bm,aa]
  have old (i : ℕ) (hi : 1< i) : z.mem i=a.imem (i:ℤ):=by
    change t.imem (i:ℤ)=_;rw [tm,if_neg (by omega),bm,if_neg (by omega)]
  have rd : Ready z t:=by
    refine ⟨?_,fun _=>rfl⟩;intro ax;have lt : ax.reg<3:=by cases ax <;> decide
    rw [tc _ lt,bc _ lt];exact ready.1 ax
  have fill : Writes x z packCell:=by
    intro r hr j hj side;obtain ⟨one,two⟩:=wr r hr j hj
    have lo : 1< addr x.k r j:=by unfold addr;omega
    cases side
    · change z.mem (addr x.k r j)=_;rw [old _ lo];exact one
    · change z.mem (addr x.k r j+1)=_;rw [old _ (by omega)];exact two
  refine ⟨t,_,.seq ex (.seq ec ed),?_,rd,scene,?_⟩
  · simp only [eval_add,eval_C];omega
  exact dense_record_board_decoding x x.k x.rows z.mem g roots hk hn rfl rfl big src (by rw [head,Int.toNat_natCast]) fill
