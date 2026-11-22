-- Prove2me | solution 1 for StableMSR.Recovery.WindowCSP.window_tree_plan
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T16:13:03.904557+00:00
-- url     : https://prove2.me/submissions/b9bfcc60-48a5-4615-8095-7724f2e3ec8b

import Theorems.Thm_StableMSR_Recovery_WindowCSP_finite_pairwise_cost_plan
import Definitions.Def_StableMSR_WindowPlans
import Definitions.Def_StableMSR_WindowCSP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
open StableMSR.Recovery.TreeDP
theorem solution (x : World) (W : Cluster x.n) (R : ℝ) (h w : ℕ)
    (tw : RobertsonSeymour1986.GM5.TreewidthLE (interactionGraph x.dist R W) w) :
    ∃p : TreeDP.Plan ↥(greedyNet x.dist R W) (Partition x.n),realizesWindows x W R h w p := by
  classical
  let N:=greedyNet x.dist R W
  let V:=↥N
  let G:=interactionGraph x.dist R W
  let owner:=anchor x.dist W R
  let D (v : ↥N):=traceMenu x h (window x.dist W R v)
  let test (v w : ↥N) (a b : Partition x.n):=compatible owner v w a b
  let cnt (v : ↥N) (a : Partition x.n):=(owned owner v a).card
  let pay (v : ↥N) (a : Partition x.n):=cost x.dist (owned owner v a)
  let B:=(h+1)*CartesianBallRows.rows x.n (h+1)+1
  have bd (v : ↥N) : (D v).card≤ B := by
    unfold D traceMenu
    apply (Finset.card_filter_le ..).trans
    apply Finset.card_image_le.trans
    simp [B]
  obtain ⟨p,co,lo,nn,all,volume,opt⟩:=finite_pairwise_cost_plan G w tw D ∅ test cnt pay B (by dsimp [B];omega) bd
  let res (P : Pick x.n) (v : ↥N):=P v.val
  let ext (f : ↥N→Partition x.n) (v : Point x.n):=if hv : v∈N then f ⟨v,hv⟩ else ∅
  have ret (f : ↥N→Partition x.n) : res (ext f)=f := by funext v;simp [res,ext,v.property]
  have val (P : Pick x.n) : valid x W R h P ↔ admissible G D test (res P) := by
    constructor
    · rintro ⟨a,b⟩;exact ⟨fun v=>a v.val v.property,b⟩
    · rintro ⟨a,b⟩;exact ⟨fun v hv=>a ⟨v,hv⟩,b⟩
  have num (P : Pick x.n) : number x W R P=∑v,cnt v (res P v) :=
    (Finset.sum_coe_sort N _).symm
  have price (P : Pick x.n) : WindowCSP.price x W R P=∑v,pay v (res P v) :=
    (Finset.sum_coe_sort N _).symm
  have dom : Fintype.card ↥N≤ x.n:=by
    rw [Fintype.card_coe]
    exact (Finset.card_le_univ N).trans_eq (Fintype.card_fin _)
  have factor : 2*Fintype.card ↥N+1≤2*x.n+1:=by omega
  refine ⟨p,co,lo,nn.trans factor,all,?_,?_⟩
  · intro cap;obtain ⟨safe,raw⟩:=volume cap
    exact ⟨safe.trans (Nat.mul_le_mul_right _ factor),raw.trans (Nat.mul_le_mul_right _ factor)⟩
  · intro cap j hj P ok eq
    obtain ⟨u,hu,g,uj,ag,cg,pg,best⟩:=opt cap j hj (res P) ((val P).mp ok) ((num P).symm.trans eq)
    refine ⟨u,hu,ext g,uj,(val _).mpr (by rwa [ret]),?_,?_,?_⟩
    · rwa [num,ret]
    · rwa [price,ret]
    · intro Q okQ cntQ
      exact (best _ ((val Q).mp okQ) ((num Q).symm.trans cntQ)).trans_eq (price Q).symm

