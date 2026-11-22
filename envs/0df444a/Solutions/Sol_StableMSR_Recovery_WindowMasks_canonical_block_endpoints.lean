-- Prove2me | solution 1 for StableMSR.Recovery.WindowMasks.canonical_block_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:27:24.261323+00:00
-- url     : https://prove2.me/submissions/a5603bfc-7837-4f58-a67e-65c74aed5145

import Definitions.Def_StableMSR_WindowBlockMasks
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
private lemma firstHit (n : ℕ) (P : ℕ→Prop) (ex : ∃i< n,P i) : ∃i< n,P i ∧ first n P=(i:ℤ):=by
  classical
  let S:=(Finset.range n).filter P
  obtain ⟨a,an,pa⟩:=ex
  have ne : S.Nonempty:=⟨a,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr an,pa⟩⟩
  let i:=S.min' ne
  obtain ⟨im,good⟩:=Finset.mem_filter.mp (S.min'_mem ne)
  have il : i< n:=Finset.mem_range.mp im
  have least (j : ℕ) (jn : j< n) (pj : P j) : i≤ j:=S.min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr jn,pj⟩)
  refine ⟨i,il,good,?_⟩;unfold first;rw [Finset.sum_eq_single i]
  · exact if_pos ⟨good,fun j hj ji pj=>by have:=least j hj pj;omega⟩
  · intro j hj neq;apply if_neg;rintro ⟨pj,prior⟩
    have le:=least j (Finset.mem_range.mp hj) pj;exact prior i il (by omega) good
  · exact fun no=>(no im).elim
private lemma firstIn (n : ℕ) (hn : 0< n) (P : ℕ→Prop) : 0≤ first n P ∧ first n P<(n:ℤ):=by
  by_cases ex : ∃i< n,P i
  · obtain ⟨i,hi,_,eq⟩:=firstHit n P ex;rw [eq];omega
  · have zero : first n P=0:=Finset.sum_eq_zero (fun i hi=>if_neg (fun t=>ex ⟨i,Finset.mem_range.mp hi,t.1⟩))
    rw [zero];omega
private lemma dFin (x : World) (a b : Point x.n) : FewBallRows.distAt x a.val b.val=x.dist a b:=by
  simp [FewBallRows.distAt,MinSumFPT.oracleAnswer,MinSumFPT.toPoint,a.isLt,b.isLt]
private lemma minimalPair (x : World) (q : ℕ) (ne : (block x q).Nonempty) :
    ∃a b : Point x.n,cheapest x q a.val b.val ∧ x.dist a b=radius x.dist (block x q):=by
  classical
  let C:=block x q
  have M (i : Point x.n) : i∈C ↔ marked x q i.val:=by simp [C,block]
  obtain ⟨a,ha,ea⟩:=Finset.exists_mem_eq_inf' ne (eccentricity x.dist C)
  obtain ⟨b,hb,eb⟩:=Finset.exists_mem_eq_sup' ne (x.dist a)
  have rad : x.dist a b=radius x.dist C:=by rw [radius,dif_pos ne,ea,eccentricity,dif_pos ne,eb]
  refine ⟨a,b,⟨⟨(M a).mp ha,(M b).mp hb,?_⟩,?_⟩,rad⟩
  · intro t ht mark;let p : Point x.n:=⟨t,ht⟩
    change FewBallRows.distAt x a.val p.val≤_;rw [dFin,dFin,←eb]
    exact Finset.le_sup' _ ((M p).mpr mark)
  · intro t ht l hl encl;let i : Point x.n:=⟨t,ht⟩;let j : Point x.n:=⟨l,hl⟩
    change FewBallRows.distAt x a.val b.val≤ FewBallRows.distAt x i.val j.val
    rw [dFin,dFin,rad,radius,dif_pos ne]
    apply (Finset.inf'_le _ ((M i).mpr encl.1)).trans
    unfold eccentricity;rw [dif_pos ne];apply Finset.sup'_le
    intro p hp;have bound:=encl.2.2 p.val p.isLt ((M p).mp hp)
    change FewBallRows.distAt x i.val p.val≤ FewBallRows.distAt x i.val j.val at bound
    simpa only [dFin] using bound
theorem solution (x : World) (q : ℕ) (hk : 1≤ x.k) (hn : 0< x.n) :
    let C:=block x q;let c:=chargeCount x q;let w:=trimWord c (oneWord x q)
    c=(emit C).length ∧ Owned x C c w ∧ weight x c w=payment x.dist (emit C) ∧
    (∀j s,0≤ oneWord x q j s ∧ oneWord x q j s<(x.n:ℤ)) := by
  classical
  let C:=block x q
  have M (i : Point x.n) : i∈C ↔ marked x q i.val:=by simp [C,block]
  have legal (j : ℕ) (s : Bool) : 0≤ oneWord x q j s ∧ oneWord x q j s<(x.n:ℤ):=by
    by_cases h : j=0
    · subst j;cases s
      · simpa [oneWord,chosen] using firstIn x.n hn (fun a=>∃b< x.n,cheapest x q a b)
      · simpa [oneWord,farthest] using firstIn x.n hn (fun b=>cheapest x q (chosen x q).toNat b)
    · simp [oneWord,h,hn]
  by_cases ne : C.Nonempty
  · obtain ⟨a,b,opt,rad⟩:=minimalPair x q ne
    obtain ⟨c,cn,has,ce⟩:=firstHit x.n (fun c=>∃w< x.n,cheapest x q c w) ⟨a.val,a.isLt,b.val,b.isLt,opt⟩
    change chosen x q=(c:ℤ) at ce
    obtain ⟨w,wn,best,we⟩:=firstHit x.n (fun w=>cheapest x q (chosen x q).toNat w) (by simpa [ce] using has)
    change farthest x q=(w:ℤ) at we
    simp only [ce,Int.toNat_natCast] at best
    let i : Point x.n:=⟨c,cn⟩;let j : Point x.n:=⟨w,wn⟩
    have cost : FewBallRows.distAt x c w=radius x.dist C:=
      (le_antisymm (best.2 _ a.isLt _ b.isLt opt.1) (opt.2 c cn w wn best.1)).trans ((dFin ..).trans rad)
    have count : chargeCount x q=1:=if_pos ⟨c,cn,best.1.1⟩
    have centerVal : trimWord 1 (oneWord x q) 0 false=(c:ℤ):=by simp [trimWord,oneWord,ce]
    have farVal : trimWord 1 (oneWord x q) 0 true=(w:ℤ):=by simp [trimWord,oneWord,we]
    change chargeCount x q=(emit C).length ∧ _
    rw [count]
    refine ⟨by simp [emit,ne],⟨?_,?_,?_⟩,?_,legal⟩
    · intro l hl
      have eq : l=0:=by omega
      rw [eq];exact ⟨i,(M i).mpr best.1.1,centerVal⟩
    · intro l hl m hm _;omega
    · intro p hp;refine ⟨0,by decide,?_⟩
      unfold WindowProfiles.contains RegionalBallDP.containsPoint;rw [centerVal,farVal]
      exact best.1.2.2 p.val p.isLt ((M p).mp hp)
    · unfold weight;rw [←Finset.sum_filter]
      have f : (Finset.range x.k).filter (fun j=>j<1)={0}:=by
        ext j;simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_singleton];omega
      rw [f,Finset.sum_singleton,centerVal,farVal]
      change FewBallRows.distAt x c w=payment x.dist (emit C);simpa [payment,emit,ne] using cost
  · have count : chargeCount x q=0:=if_neg (fun ⟨i,hi,mark⟩=>ne ⟨⟨i,hi⟩,(M _).mpr mark⟩)
    change chargeCount x q=(emit C).length ∧ _
    rw [count]
    refine ⟨by simp [emit,ne],⟨by simp,by simp,fun p hp=>(ne ⟨p,hp⟩).elim⟩,?_,legal⟩
    change weight x 0 _=payment x.dist (emit C);simp [weight,payment,emit,ne]
