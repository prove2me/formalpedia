-- Prove2me | solution 1 for StableMSR.Recovery.SingleCodes.regional_circuit_input_exact
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:13:47.222713+00:00
-- url     : https://prove2.me/submissions/1e15967a-076f-4568-aaf9-aebda4976fff

import Definitions.Def_StableMSR_SingleWindowCodes
import Theorems.Thm_StableMSR_Recovery_SingleCodes_finite_ball_word_menu_exact
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
open StableMSR.Recovery StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.WindowCuts StableMSR.Recovery.SingleSearch
open RobertsonSeymour1986.GM5
open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.Supplement
open StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleWindows
open StableMSR.Recovery.WindowProfiles (piece keys)
open StableMSR.Recovery.SingleCodes StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
theorem solution (x : World) (W : Cluster x.n) (R : ℝ) (h : ℕ) :
    let d:=instanceOf x W R h;let N:=greedyNet x.dist R W
    (∀v : Point x.n,d.active v.val=true ↔ v∈N) ∧
    (∀u v : ↥N,d.edge u.val.val v.val.val=true ↔ (interactionGraph x.dist R W).Adj u v) ∧
    (∀v : Point x.n,∀P : Partition x.n,P∈traceMenu x h (window x.dist W R v) ↔ ∃c∈d.menu v.val,SingleCodes.decode x (window x.dist W R v) h c=P) ∧
    (∀u v : Point x.n,∀c k,d.test u.val v.val c k=true ↔ compatible (anchor x.dist W R) u v (SingleCodes.decode x (window x.dist W R u) h c) (SingleCodes.decode x (window x.dist W R v) h k)) ∧
    ∀v : Point x.n,∀c : ℕ,∀m : List ℕ,m∈d.owned v.val c ↔
      ∃C∈owned (anchor x.dist W R) v (SingleCodes.decode x (window x.dist W R v) h c),m=C.toList.map Fin.val := by
  classical
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro v;simp [instanceOf,SingleCodes.lookup,v.isLt]
  · intro u v
    simp only [instanceOf,SingleCodes.lookup,dif_pos u.val.isLt,dif_pos v.val.isLt,decide_eq_true_eq]
    change (u.val≠v.val ∧ x.dist u.val v.val≤8*R ∧ x.dist v.val u.val≤8*R) ↔
      (u.val≠v.val ∧ u.val∈greedyNet x.dist R W ∧ v.val∈greedyNet x.dist R W ∧ x.dist u.val v.val≤8*R ∧ x.dist v.val u.val≤8*R)
    simp only [u.property,v.property,true_and]
  · intro v P;simpa [instanceOf,SingleCodes.lookup,v.isLt] using finite_ball_word_menu_exact x (window x.dist W R v) h P
  · intro u v c k;simp [instanceOf,SingleCodes.lookup,u.isLt,v.isLt]
  · intro v c m;simp only [instanceOf,SingleCodes.lookup,dif_pos v.isLt,blockList,List.mem_map,Finset.mem_toList]
    constructor <;> rintro ⟨C,hC,eq⟩ <;> exact ⟨C,hC,eq.symm⟩
