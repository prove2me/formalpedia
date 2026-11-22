-- Prove2me | solution 1 for StableMSR.Recovery.WindowProfiles.partition_endpoint_word
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:17:51.596845+00:00
-- url     : https://prove2.me/submissions/d7fdd142-c789-4ef1-b54a-8fc070d74d3b

import Definitions.Def_StableMSR_WindowProfiles
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.Supplement StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

private lemma oracleFin {n : ℕ} (d : Point n→Point n→ℝ) (i j : Fin n) :
    MinSumFPT.oracleAnswer d (i.val:ℤ) (j.val:ℤ)=d i j:=by
  simp [MinSumFPT.oracleAnswer,MinSumFPT.toPoint,i.isLt,j.isLt]
theorem solution (x : World) (W : Cluster x.n) (c : ℕ) (Q : Partition x.n) (hc : c≤ x.k) (feas : Feasible W c Q) :
    ∃v : RegionalBallDP.Word,Owned x W c v ∧ RegionalBallDP.weight x c v=cost x.dist Q ∧
      ∀j< c,∀s,∃p∈W,v j s=(p.val:ℤ) := by
  classical
  let E : Fin c ≃ Q:=(Finset.equivFinOfCardEq feas.1).symm
  let B (j : Fin c) : Cluster x.n:=(E j).val
  have mem (j : Fin c) : B j∈Q:=(E j).property
  have sub (j : Fin c) : B j⊆W:=by
    intro a ha;rw [←feas.2.2.2];exact Finset.mem_biUnion.mpr ⟨_,mem j,ha⟩
  have witnesses (j : Fin c) : ∃a b : Point x.n,a∈B j ∧ b∈B j ∧ x.dist a b=radius x.dist (B j) ∧
      ∀p∈B j,x.dist a p≤ x.dist a b:=by
    have ne:=feas.2.1 _ (mem j)
    obtain ⟨a,ha,ec⟩:=Finset.exists_mem_eq_inf' ne (eccentricity x.dist (B j))
    obtain ⟨b,hb,eb⟩:=Finset.exists_mem_eq_sup' ne (x.dist a)
    refine ⟨a,b,ha,hb,?_,?_⟩
    · rw [radius,dif_pos ne,ec,eccentricity,dif_pos ne,eb]
    · intro p hp;rw [←eb];exact Finset.le_sup' _ hp
  choose a b ha hb rad hits using witnesses
  let v : RegionalBallDP.Word:=fun j s=>if h : j< c then if s then ((b ⟨j,h⟩).val:ℤ) else ((a ⟨j,h⟩).val:ℤ) else 0
  have centerVal (j : Fin c) : v j.val false=((a j).val:ℤ):=by simp [v,j.isLt]
  have witVal (j : Fin c) : v j.val true=((b j).val:ℤ):=by simp [v,j.isLt]
  have legal (j : ℕ) (hj : j< c) (s : Bool) : ∃p∈W,v j s=(p.val:ℤ):=by
    let t : Fin c:=⟨j,hj⟩
    cases s
    · exact ⟨a t,sub t (ha t),centerVal t⟩
    · exact ⟨b t,sub t (hb t),witVal t⟩
  refine ⟨v,⟨fun j hj=>legal j hj false,?_,?_⟩,?_,legal⟩
  · intro j hj z hz eq
    let s : Fin c:=⟨j,hj⟩;let t : Fin c:=⟨z,hz⟩
    have same : a s=a t:=Fin.ext (Int.ofNat.inj ((centerVal s).symm.trans (eq.trans (centerVal t))))
    by_contra ne
    have neq : B s≠B t:=fun e=>ne (congrArg Fin.val (E.injective (Subtype.ext e)))
    exact Finset.disjoint_left.mp (feas.2.2.1 (mem s) (mem t) neq) (ha s) (same ▸ ha t)
  · intro q hq
    rw [←feas.2.2.2] at hq;obtain ⟨K,hK,qK⟩:=Finset.mem_biUnion.mp hq
    let j:=E.symm ⟨K,hK⟩
    have bj : B j=K:=congrArg Subtype.val (E.apply_symm_apply ⟨K,hK⟩)
    refine ⟨j.val,j.isLt,?_⟩
    unfold contains RegionalBallDP.containsPoint;rw [centerVal,witVal,oracleFin,oracleFin]
    exact hits j q (bj ▸ qK)
  · unfold RegionalBallDP.weight;rw [←Finset.sum_filter]
    have eq : (Finset.range x.k).filter (fun j=>j< c)=Finset.range c:=by
      ext j;simp only [Finset.mem_filter,Finset.mem_range];omega
    rw [eq,←Fin.sum_univ_eq_sum_range]
    calc
       _ = ∑j : Fin c,radius x.dist (B j):=by
         apply Finset.sum_congr rfl;intro j _
         rw [centerVal,witVal,oracleFin,rad]
       _ = ∑K : Q,radius x.dist K.val:=E.sum_comp (fun K=>radius x.dist K.val)
       _ = cost x.dist Q:=Finset.sum_attach _ _

