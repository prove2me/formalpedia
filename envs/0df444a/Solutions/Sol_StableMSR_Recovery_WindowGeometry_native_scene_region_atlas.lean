-- Prove2me | solution 1 for StableMSR.Recovery.WindowGeometry.native_scene_region_atlas
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:40:58.242516+00:00
-- url     : https://prove2.me/submissions/c460c86c-c44f-47f4-a518-a8a29f7bda67

import Definitions.Def_StableMSR_SceneRegionAtlas
import Theorems.Thm_StableMSR_Recovery_WindowGeometry_least_label_region_test
import Theorems.Thm_StableMSR_Recovery_WindowGeometry_scene_region_initialization_expressions
import Theorems.Thm_StableMSR_Recovery_WindowGeometry_native_regional_geometry
import Theorems.Thm_StableMSR_Recovery_OracleQueries_bounded_oracle_expression_compiler
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
open StableMSR.Recovery.WindowGeometry
open Polynomial
private noncomputable def limit : Polynomial ℕ:=X+C 2+X+X^2
private lemma monoP (P : Polynomial ℕ) {a b : ℕ} (h : a≤ b) : P.eval a≤ P.eval b:=by
  rw [Polynomial.eval_eq_sum_range,Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum (fun _ _=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _))
private lemma subAt (x : World) (p q : ℕ) (h : q< x.rows) : subR x (p+q) p=q:=by
  unfold subR;rw [Finset.sum_eq_single q]
  · simp
  · intro j _ ne;exact if_neg (by omega)
  · intro no;exact (no (Finset.mem_range.mpr h)).elim
set_option maxHeartbeats 400000 in
theorem solution : ∃P : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (s : Store),0< x.k → Ready x s →
    ∃t z,Executes x.dist cmd s t z ∧ z≤ P.eval x.cap ∧
      let y:=worldOf x.k (tableHeight x) x.dist t
      Ready y t ∧ SceneAtlas x (x.mem 0).toNat (x.mem 1).toNat y.mem := by
  obtain ⟨dim,express⟩:=scene_region_initialization_expressions
  obtain ⟨A,engine⟩:=bounded_oracle_expression_compiler _ dim
  obtain ⟨allocate,alloc⟩:=engine 3 (fun _=>0) (by decide) (fun _=>by decide)
  obtain ⟨B,make,construct⟩:=FewBallRows.tabulate_ball_row_expressions prepare express
  obtain ⟨G,geo,run⟩:=native_regional_geometry
  refine ⟨A+1+(B+G).comp limit,allocate.seq (Cmd.seq (.atom (.pointerCopy 2 3)) (make.seq geo)),?_⟩
  intro x s hk ready
  obtain ⟨s',l,ea,keep,res,timeA⟩:=alloc x s (fun _=>x.n) ready (fun _=>ready.1 .points)
  let H:=tableHeight x;let y:World:={x with rows:=H}
  let a:=(Op.pointerCopy 2 3).eval x.dist s'
  have p0 : s'.ptrs 0=(x.n:ℤ):=(keep.1 0 (by decide)).1.trans (ready.1 .points)
  have p1 : s'.ptrs 1=(x.k:ℤ):=(keep.1 1 (by decide)).1.trans (ready.1 .blocks)
  have p3 : s'.ptrs 3=(H:ℤ):=congrArg Prod.fst res
  have ar : Ready y a:=by
    refine ⟨?_,fun i=>(congrFun keep.2 _).trans (ready.2 i)⟩
    intro ax;cases ax <;> simp [a,Op.eval,World.size,Axis.reg,Function.update,p0,p1,p3,y]
  obtain ⟨b,z,eb,timeB,br,wr⟩:=construct y a ar
  let v:=worldOf x.k H x.dist b
  have room : 2+v.n+v.n*v.n≤ v.rows:=Nat.le_refl _
  obtain ⟨t,j,eg,timeG,rd,atlas⟩:=run v b hk room br
  let u:=(x.mem 0).toNat;let i:=(x.mem 1).toNat
  have lo : 1< H:=by dsimp [H,tableHeight];omega
  have mem (p : Point x.n) : inside v p.val ↔ p∈piece x u i:=by
    have h0 : 2+p.val< H:=by dsimp [H,tableHeight];have:=p.isLt;omega
    have h:= (wr (2+p.val) h0 0 hk).1
    have off : subR y (2+p.val) 2=p.val:=subAt y 2 p.val (by change p.val< H;omega)
    change center v (2+p.val) 0=prepare y (2+p.val) 0 false at h
    have eq : center v (2+p.val) 0=(if canonical x u i p.val then 1 else 0):=by
      change center v (2+p.val) 0=(if 2+p.val=0 then _ else if 2+p.val=1 then _ else if canonical y u i (subR y (2+p.val) 2) then 1 else 0) at h
      rw [if_neg (by omega),if_neg (by omega),off] at h;exact h
    change 0< center v (2+p.val) 0 ↔ _;rw [eq,←least_label_region_test]
    by_cases yes : canonical x u i p.val <;> simp [yes]
  have reg : region v=piece x u i:=by
    change Finset.univ.filter (fun p : Point x.n=>inside v p.val)=piece x u i
    apply Finset.ext;intro p;constructor
    · intro hp;exact (mem p).mp (Finset.mem_filter.mp hp).2
    · intro hp;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mem p).mpr hp⟩
  have left:= (wr 0 (by change 0< H;omega) 0 hk).1
  have right:= (wr 1 lo 0 hk).1
  have ret : unitR v=scale x u:=by
    change center v 0 0=prepare y 0 0 false at left
    change center v 1 0=prepare y 1 0 false at right
    unfold unitR;rw [left,right];rfl
  refine ⟨t,_,.seq ea (.seq (.atom _ _) (.seq eb eg)),?_,rd,?_⟩
  · have nle : x.n≤ x.cap:=by unfold World.cap;omega
    have np:=Nat.mul_le_mul nle nle
    have upper : y.cap≤ limit.eval x.cap:=by
      simp only [limit,eval_pow,eval_mul,eval_add,eval_X,eval_C,pow_two]
      change x.n+x.k+(2+x.n+x.n*x.n)+1≤_
      have b:x.n+x.k+1≤ x.cap:=by unfold World.cap;omega
      omega
    have aB:=(monoP B upper);have aG:=(monoP G upper)
    change j≤ G.eval y.cap at timeG
    simp only [eval_add,eval_one,eval_comp];omega
  · dsimp only [Atlas] at atlas
    rw [reg,ret] at atlas
    exact atlas
