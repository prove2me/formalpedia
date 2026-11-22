-- Prove2me | solution 1 for StableMSR.Recovery.WindowProfiles.bounded_width_profile_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:09:58.523792+00:00
-- url     : https://prove2.me/submissions/b88fba03-7fb6-4767-9c0d-6b93cb40b292

import Theorems.Thm_StableMSR_Recovery_WindowProfiles_partition_endpoint_word
import Theorems.Thm_StableMSR_Recovery_WindowCSP_window_tree_plan
import Theorems.Thm_StableMSR_Recovery_WindowCSP_pairwise_windows_glue
import Definitions.Def_StableMSR_WindowPlans
import Definitions.Def_StableMSR_WindowProfiles
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.Supplement StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

theorem solution (x : World) (W : Cluster x.n) (R : ℝ) (h w : ℕ) (dm : IsMetricArray x.dist) (pos : 0≤ R)
    (tw : RobertsonSeymour1986.GM5.TreewidthLE (interactionGraph x.dist R W) w) :
    ∃p : TreeDP.Plan ↥(greedyNet x.dist R W) (Partition x.n), realizesWindows x W R h w p ∧
    ∀c≤ x.k,∀P : Pick x.n,valid x W R h P → number x W R P=c →
      ∃t∈TreeDP.solve x.k p,∃v : RegionalBallDP.Word,t.2.1=c ∧ Owned x W c v ∧
        RegionalBallDP.weight x c v=t.2.2 ∧ (∀j< c,∀s,∃a∈W,v j s=(a.val:ℤ)) ∧
        ∀Q : Pick x.n,valid x W R h Q → number x W R Q=c → t.2.2≤ WindowCSP.price x W R Q := by
  obtain ⟨p,plan⟩:=window_tree_plan x W R h w tw
  refine ⟨p,plan,?_⟩
  intro c hc P ok num
  obtain ⟨t,ht,Q,count,validQ,nQ,pQ,least⟩:=plan.2.2.2.2.2 x.k c hc P ok num
  obtain ⟨feas,costQ,_⟩:=pairwise_windows_glue x W R h Q dm pos validQ
  rw [nQ] at feas
  obtain ⟨v,owns,costV,ends⟩:=partition_endpoint_word x W c _ hc feas
  exact ⟨t,ht,v,count,owns,costV.trans (costQ.trans pQ),ends,least⟩

