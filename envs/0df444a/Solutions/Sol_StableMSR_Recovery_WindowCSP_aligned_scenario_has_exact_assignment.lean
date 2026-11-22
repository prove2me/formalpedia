-- Prove2me | solution 1 for StableMSR.Recovery.WindowCSP.aligned_scenario_has_exact_assignment
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T16:10:46.70878+00:00
-- url     : https://prove2.me/submissions/56f4acb5-3159-4895-8698-fa25b1d44772

import Theorems.Thm_StableMSR_Recovery_WindowCSP_stable_region_exact_table
import Theorems.Thm_StableMSR_Recovery_WindowCSP_pairwise_windows_glue
import Theorems.Thm_StableMSR_Recovery_Supplement_local_treewidth
import Definitions.Def_StableMSR_WindowPlans
import Definitions.Def_StableMSR_WindowCSP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
private lemma unionCosts {n : ℕ} (d : Point n→Point n→ℝ) (R : Partition n)
    (parts : Feasible Finset.univ R.card R) (T : Cluster n→Partition n)
    (localOK : ∀W∈R,Feasible W (T W).card (T W)) :
    Feasible Finset.univ (∑W ∈ R,(T W).card) (R.biUnion T) ∧
      cost d (R.biUnion T)=∑W ∈ R,cost d (T W) := by
  classical
  have sub {W C : Cluster n} (hw : W∈R) (hc : C∈T W) : C⊆W := by
    intro i hi
    rw [← (localOK W hw).2.2.2]
    exact Finset.mem_biUnion.mpr ⟨C,hc,hi⟩
  have sep : (R : Set (Cluster n)).PairwiseDisjoint T := by
    intro W hw V hv ne
    apply Finset.disjoint_left.mpr
    intro C cw cv
    obtain ⟨p,hp⟩:=(localOK W hw).2.1 C cw
    exact Finset.disjoint_left.mp (parts.2.2.1 hw hv ne) (sub hw cw hp) (sub hv cv hp)
  refine ⟨⟨Finset.card_biUnion sep,?_,?_,?_⟩,Finset.sum_biUnion sep⟩
  · intro C hc;obtain ⟨W,hw,cw⟩:=Finset.mem_biUnion.mp hc
    exact (localOK W hw).2.1 C cw
  · intro C hc D hd ne
    obtain ⟨W,hw,cw⟩:=Finset.mem_biUnion.mp hc
    obtain ⟨V,hv,dv⟩:=Finset.mem_biUnion.mp hd
    by_cases eq : W=V
    · subst V;exact (localOK W hw).2.2.1 cw dv ne
    · exact Finset.disjoint_left.mpr (fun p pc pd=>
        Finset.disjoint_left.mp (parts.2.2.1 hw hv eq) (sub hw cw pc) (sub hv dv pd))
  · apply Finset.eq_univ_of_forall
    intro p
    obtain ⟨W,hw,pw⟩:=Finset.mem_biUnion.mp (parts.2.2.2 ▸ Finset.mem_univ p)
    obtain ⟨C,cw,pc⟩:=Finset.mem_biUnion.mp ((localOK W hw).2.2.2.symm ▸ pw)
    exact Finset.mem_biUnion.mpr ⟨C,Finset.mem_biUnion.mpr ⟨W,hw,cw⟩,pc⟩
private lemma restrictedUnion {n k : ℕ} {R O : Partition n} (parts : Feasible Finset.univ R.card R)
    (feas : Feasible Finset.univ k O) (aligned : ∀W∈R,Aligned O W) :
    R.biUnion (restrictPartition O)=O := by
  ext C;constructor
  · intro h;obtain ⟨W,_,hc⟩:=Finset.mem_biUnion.mp h
    exact (Finset.mem_filter.mp hc).1
  · intro hc
    obtain ⟨p,cp⟩:=feas.2.1 C hc
    obtain ⟨W,hw,pw⟩:=Finset.mem_biUnion.mp (parts.2.2.2 ▸ Finset.mem_univ p)
    obtain ⟨F,sF,un⟩:=aligned W hw
    obtain ⟨D,hd,pd⟩:=Finset.mem_biUnion.mp (un.symm ▸ pw)
    have eq : C=D := by
      by_contra ne;exact Finset.disjoint_left.mp (feas.2.2.1 hc (sF hd) ne) cp pd
    refine Finset.mem_biUnion.mpr ⟨W,hw,Finset.mem_filter.mpr ⟨hc,?_⟩⟩
    rw [eq,←un];intro i hi;exact Finset.mem_biUnion.mpr ⟨D,hd,hi⟩
private lemma labelPartition (x : World) (s : ℕ) : Feasible Finset.univ (regions x s).card (regions x s) := by
  classical
  let cell (i : Point x.n):=(Finset.univ : Cluster x.n).filter (fun j=>label x s j=label x s i)
  have mem {i j : Point x.n} : j∈cell i ↔ label x s j=label x s i := by simp [cell]
  refine ⟨rfl,?_,?_,?_⟩
  · intro W hw;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hw
    exact ⟨i,mem.mpr rfl⟩
  · intro U hu V hv ne
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hu;obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hv
    apply Finset.disjoint_left.mpr;intro z zi zj
    have eq:=(mem.mp zi).symm.trans (mem.mp zj)
    apply ne;ext q;change q∈cell i ↔ q∈cell j;rw [mem,mem,eq]
  · apply Finset.eq_univ_of_forall;intro i
    exact Finset.mem_biUnion.mpr ⟨cell i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,mem.mpr rfl⟩
theorem solution (x : World) (s : ℕ) (e : ℝ) (he : 0< e) (hl : e<1)
    (hk : 1≤ x.k) (hn : x.k< x.n) (dm : IsMetricArray x.dist) (O : Partition x.n)
    (hs : Stable x.dist x.k (1+e) O) (hp : 0< scale x s) (eq : scale x s=largestRadius x.dist O)
    (al : ∀W∈regions x s,Aligned O W ∧ diameter x.dist W≤ densityScale x.dist O e) :
    (∀W∈regions x s,RobertsonSeymour1986.GM5.TreewidthLE (interactionGraph x.dist (scale x s) W) (widthBound e)) ∧
    ∃P : Cluster x.n→Pick x.n,(∀W∈regions x s,valid x W (scale x s) (budget e) (P W)) ∧
      (∑W ∈ regions x s,number x W (scale x s) (P W))=x.k ∧
      (∑W ∈ regions x s,WindowCSP.price x W (scale x s) (P W))=cost x.dist O := by
  classical
  let R:=largestRadius x.dist O
  have pos : 0< R:=by change 0< largestRadius x.dist O;rwa [←eq]
  have parts:=labelPartition x s
  have available (w : ↥(regions x s)) : ∃Q : Pick x.n,valid x w R (budget e) Q ∧
      number x w R Q=(restrictPartition O w).card ∧
      WindowCSP.output x w R Q=restrictPartition O w ∧ WindowCSP.price x w R Q=cost x.dist (restrictPartition O w) := by
    obtain ⟨_,_,_,_,_,Q,validQ,_,num,out,paid,_⟩:=stable_region_exact_table x w e he hl hk hn dm O hs pos
      (parts.2.1 _ w.property) (al _ w.property).1 (al _ w.property).2
    exact ⟨Q,validQ,num,out,paid⟩
  choose get cert using available
  let P (W : Cluster x.n) : Pick x.n:=if hw : W∈regions x s then get ⟨W,hw⟩ else fun _=>∅
  have picked (W : Cluster x.n) (hw : W∈regions x s) : P W=get ⟨W,hw⟩:=dif_pos hw
  have validP (W : Cluster x.n) (hw : W∈regions x s) : valid x W R (budget e) (P W) := by
    rw [picked W hw];exact (cert ⟨W,hw⟩).1
  have sums (W : Cluster x.n) (hw : W∈regions x s) :
      Feasible W (number x W R (P W)) (restrictPartition O W) ∧
      cost x.dist (restrictPartition O W)=WindowCSP.price x W R (P W) := by
    have f:=(pairwise_windows_glue x W R (budget e) (P W) dm pos.le (validP W hw)).1
    rw [picked W hw] at f ⊢
    exact ⟨(cert ⟨W,hw⟩).2.2.1 ▸ f,(cert ⟨W,hw⟩).2.2.2.symm⟩
  have locals (W : Cluster x.n) (hw : W∈regions x s) : Feasible W (restrictPartition O W).card (restrictPartition O W) :=
    (sums W hw).1.1.symm ▸ (sums W hw).1
  have un:=restrictedUnion parts hs.1 (fun W hw=>(al W hw).1)
  obtain ⟨cnt,price⟩:=unionCosts x.dist _ parts (restrictPartition O) locals
  rw [un] at cnt price
  rw [eq]
  obtain ⟨_,_,_,tw⟩:=local_treewidth
  refine ⟨?_,P,validP,?_,?_⟩
  · intro W hw
    have ee : 1+e-1=e := by ring
    have wt:=tw x.n x.k x.dist (1+e) O hk hn dm (by linarith) (by linarith) hs W (al W hw).1
      (by rw [ee];exact (al W hw).2)
    simpa only [ee] using wt
  · exact (Finset.sum_congr rfl (fun W hw=>(sums W hw).1.1.symm)).trans (cnt.1.symm.trans hs.1.1)
  · exact (Finset.sum_congr rfl (fun W hw=>(sums W hw).2.symm)).trans price.symm

