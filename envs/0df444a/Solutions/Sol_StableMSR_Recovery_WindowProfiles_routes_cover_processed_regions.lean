-- Prove2me | solution 1 for StableMSR.Recovery.WindowProfiles.routes_cover_processed_regions
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:14:00.690898+00:00
-- url     : https://prove2.me/submissions/5520b972-0176-45d6-baa7-f53c0b5656ae

import Definitions.Def_StableMSR_WindowProfiles
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.Supplement StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

open StableMSR.Recovery.RegionalBallDP (Route Word splice)
private lemma lastArc {y : World} {r : ℕ} {w : Word} (h : Route y r w) (ne : r≠1) :
    ∃q v,RegionalBallDP.link y r q ∧ Route y (RegionalBallDP.parent y q) v ∧ w=splice y r q v:=by
  cases h with
  | root => contradiction
  | append vt lk path => exact ⟨_,_,lk,path,rfl⟩
theorem solution (x : World) (m g : Mem) (G : Grid (replace x m) g) (u : ℕ) (hu : u< x.rows)
    (fits : ∀i< x.n,∀b≤ x.k,active (replace x m) u i b →
      Owned x (piece x u i) b (token (replace x m) u i b)) :
    ∀i< x.n,∀b≤ x.k,∀v,RegionalBallDP.Route (arena (replace x m) g) (node x.n u i b) v →
      Owned x (Finset.univ.filter (fun p=>(rep x u p).val< i+1)) b v := by
  classical
  let y:=arena (replace x m) g
  let stageSet (t : ℕ) : Cluster x.n:=Finset.univ.filter (fun p=>(rep x u p).val< t)
  have join (i a b : ℕ) (ab : a≤ b) (v w : Word)
      (old : Owned x (stageSet i) a v) (new : Owned x (piece x u i) (b-a) (token (replace x m) u i (b-a)))
      (lo : ∀j< a,∀s,w j s=v j s)
      (hi : ∀j,a≤ j → j< b → ∀s,w j s=token (replace x m) u i (b-a) (j-a) s) :
      Owned x (stageSet (i+1)) b w:=by
    let F:=token (replace x m) u i (b-a)
    have idOld (j) (h : j< a) : ∃p : Point x.n,(rep x u p).val< i ∧ w j false=(p.val:ℤ):=by
      obtain ⟨p,hp,eq⟩:=old.1 j h
      exact ⟨p,(Finset.mem_filter.mp hp).2,(lo j h false).trans eq⟩
    have idNew (j) (l : a≤ j) (h : j< b) : ∃p : Point x.n,(rep x u p).val=i ∧ w j false=(p.val:ℤ):=by
      obtain ⟨p,hp,eq⟩:=new.1 (j-a) (by omega)
      exact ⟨p,(Finset.mem_filter.mp hp).2,(hi j l h false).trans eq⟩
    have mixed (j t) (l : j< a) (h : a≤ t) (tb : t< b) : w j false≠w t false:=by
      obtain ⟨p,hp,ep⟩:=idOld j l;obtain ⟨q,hq,eq⟩:=idNew t h tb
      intro same;have pq : p=q:=Fin.ext (by exact_mod_cast ep.symm.trans (same.trans eq))
      subst q;omega
    refine ⟨?_,?_,?_⟩
    · intro j hj;by_cases h : j< a
      · obtain ⟨p,hp,eq⟩:=idOld j h;exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩,eq⟩
      · obtain ⟨p,hp,eq⟩:=idNew j (by omega) hj;exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩,eq⟩
    · intro j hj t ht eq
      by_cases l : j< a <;> by_cases r : t< a
      · rw [lo j l false,lo t r false] at eq;exact old.2.1 j l t r eq
      · exact (mixed j t l (by omega) ht eq).elim
      · exact (mixed t j r (by omega) hj eq.symm).elim
      · rw [hi j (by omega) hj false,hi t (by omega) ht false] at eq
        have h:=new.2.1 (j-a) (by omega) (t-a) (by omega) eq;omega
    · intro p hp;have small:=(Finset.mem_filter.mp hp).2
      by_cases h : (rep x u p).val< i
      · obtain ⟨j,l,hit⟩:=old.2.2 p (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
        refine ⟨j,by omega,?_⟩;unfold contains RegionalBallDP.containsPoint at hit ⊢
        rw [lo j l false,lo j l true];exact hit
      · have same : (rep x u p).val=i:=by omega
        obtain ⟨t,l,hit⟩:=new.2.2 p (Finset.mem_filter.mpr ⟨Finset.mem_univ _,same⟩)
        have low : a≤ a+t:=by omega
        have high : a+t< b:=by omega
        refine ⟨a+t,high,?_⟩;unfold contains RegionalBallDP.containsPoint at hit ⊢
        rw [hi _ low high false,hi _ low high true,Nat.add_sub_cancel_left];exact hit
  have go (i : ℕ) (hi : i< x.n) (b : ℕ) (hb : b≤ x.k) (w : Word)
      (path : Route y (node x.n u i b) w) : Owned x (stageSet (i+1)) b w:=by
    induction i using Nat.strong_induction_on generalizing b w with
    | h i ih =>
      have ne : node x.n u i b≠1:=by unfold node;omega
      obtain ⟨q,v,lk,pathV,rfl⟩:=lastArc path ne
      obtain ⟨a,ok,rfl⟩:=G.pred u hu i hi b hb q lk
      obtain ⟨_,par,vals⟩:=G.step u hu i hi b hb a ok
      have ab:=ok.1
      have nodeWidth : RegionalBallDP.width y (node x.n u i b)=b:=(G.states u hu i hi b hb).2
      have parentWidth : RegionalBallDP.width y (prior (replace x m).n u i a)=a:=by
        cases i with
        | zero => exact (show RegionalBallDP.width y 1=0 from if_pos rfl).trans (ok.2.1 rfl).symm
        | succ j => exact (G.states u hu j (by change j< x.n;omega) a (by change a≤ x.k;omega)).2
      have old : Owned x (stageSet i) a v:=by
        cases i with
        | zero =>
          have az:=ok.2.1 rfl;subst a
          refine ⟨by simp,by simp,?_⟩;intro p h
          exact (Nat.not_lt_zero _ (Finset.mem_filter.mp h).2).elim
        | succ j =>
          apply ih j (by omega) (by omega) a (by omega) v
          rw [par] at pathV;exact pathV
      apply join i a b ab v _ old (fits i hi (b-a) (by omega) ok.2.2)
      · intro j hj s;unfold splice;rw [par,parentWidth,if_pos hj]
      · intro j hj jb s;unfold splice
        rw [par,parentWidth,if_neg (by omega),nodeWidth,if_pos jb]
        exact vals j hj jb s
  exact go

