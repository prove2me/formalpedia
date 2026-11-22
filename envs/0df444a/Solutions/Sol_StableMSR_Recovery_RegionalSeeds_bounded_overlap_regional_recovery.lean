-- Prove2me | solution 1 for StableMSR.Recovery.RegionalSeeds.bounded_overlap_regional_recovery
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T13:19:55.398414+00:00
-- url     : https://prove2.me/submissions/ca3bd850-390b-4c9a-bb98-9fd84a49693d

import Theorems.Thm_StableMSR_Recovery_RegionalSeeds_bounded_local_large_cluster_menus
import Definitions.Def_StableMSR_RegionalSeeds
import Definitions.Def_StableMSR_RegionalBallDP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
open StableMSR.Recovery.RegionalSeeds
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
theorem solution (x : World) (h : ℕ) (hk : 1≤x.k) (hn : x.k<x.n)
    (dm : IsMetricArray x.dist) (e : ℝ) (he : 0<e) (hl : e<1)
    (O R : Partition x.n) (hs : Stable x.dist x.k (1+e) O)
    (parts : Feasible Finset.univ R.card R)
    (aligned : ∀W∈R,Aligned O W)
    (overlap : ∀W∈R,(meeting (largeClusters x.dist O e) W).card≤h) :
    (∀W∈R,(RegionalSeeds.traceMenu x h W).card≤(h+1)*rows x.n (h+1)) ∧
    (∃T : Cluster x.n→Partition x.n,(∀W∈R,T W∈RegionalSeeds.traceMenu x h W) ∧
      (∑W ∈ R,(T W).card)=x.k ∧ R.biUnion T=O ∧
      (∑W ∈ R,cost x.dist (T W))=cost x.dist O) ∧
    ∀T : Cluster x.n→Partition x.n,(∀W∈R,T W∈RegionalSeeds.traceMenu x h W) →
      (∑W ∈ R,(T W).card)=x.k →
      Feasible Finset.univ x.k (R.biUnion T) ∧
      cost x.dist (R.biUnion T)=(∑W ∈ R,cost x.dist (T W)) ∧
      cost x.dist O≤(∑W ∈ R,cost x.dist (T W)) ∧
      ((∑W ∈ R,cost x.dist (T W))=cost x.dist O → R.biUnion T=O) := by
  classical
  have menu (W : Cluster x.n) := bounded_local_large_cluster_menus x h W hk hn dm
  have fromMenu (T : Cluster x.n→Partition x.n) (hT : ∀W∈R,T W∈traceMenu x h W) :=
    unionCosts x.dist R parts T (fun W hw=>(menu W).2.1 _ (hT W hw))
  have present : ∀W∈R,restrictPartition O W∈traceMenu x h W := by
    intro W hw;exact ((menu W).2.2 e he hl O hs (overlap W hw)).2 (aligned W hw)
  have union:=restrictedUnion parts hs.1 aligned
  obtain ⟨ok,price⟩:=fromMenu _ present
  rw [union] at ok price
  have opt : UniqueOptimal x.dist Finset.univ x.k O := by
    apply hs.2
    obtain ⟨metric,hm⟩:=dm
    letI : MetricSpace (Point x.n):=metric
    refine ⟨fun a b=>by simpa only [hm] using dist_comm a b,?_⟩
    intro a b
    have nonneg : 0≤x.dist a b := by rw [←hm];exact dist_nonneg
    exact ⟨le_rfl,by nlinarith [mul_nonneg he.le nonneg]⟩
  refine ⟨fun W _=>(menu W).1,⟨restrictPartition O,present,ok.1.symm.trans hs.1.1,union,price.symm⟩,?_⟩
  intro T hT count
  obtain ⟨good,score'⟩:=fromMenu T hT
  rw [count] at good
  have low:=opt.1.2 _ good
  rw [score'] at low
  refine ⟨good,score',low,?_⟩
  intro tied
  apply opt.2
  refine ⟨good,?_⟩
  intro Q hQ;rw [score',tied];exact opt.1.2 _ hQ

