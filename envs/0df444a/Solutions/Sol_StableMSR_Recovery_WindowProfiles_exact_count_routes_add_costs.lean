-- Prove2me | solution 1 for StableMSR.Recovery.WindowProfiles.exact_count_routes_add_costs
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:09:58.556269+00:00
-- url     : https://prove2.me/submissions/891d64c5-82bb-4e53-9023-a328443a764d

import Definitions.Def_StableMSR_WindowProfiles
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.Supplement StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

open StableMSR.Recovery.RegionalBallDP (Route weight splice)
private lemma shortSum (x : World) (c : ℕ) (hc : c≤ x.k) (w : RegionalBallDP.Word) :
    weight x c w=∑j∈Finset.range c,MinSumFPT.oracleAnswer x.dist (w j false) (w j true):=by
  classical
  unfold weight;rw [←Finset.sum_filter]
  have eq : (Finset.range x.k).filter (fun j=>j< c)=Finset.range c:=by
    ext j;simp only [Finset.mem_filter,Finset.mem_range];omega
  rw [eq]
theorem solution (x : World) (g : Mem) (G : Grid x g) (u : ℕ) (hu : u< x.rows) (hn : 0< x.n) (d : ℕ→ℕ)
    (total : (∑i∈Finset.range x.n,d i)=x.k) (act : ∀i< x.n,active x u i (d i)) :
    ∃v,RegionalBallDP.Route (arena x g) (node x.n u (x.n-1) x.k) v ∧
      RegionalBallDP.weight x x.k v=∑i∈Finset.range x.n,RegionalBallDP.weight x (d i) (token x u i (d i)) := by
  classical
  let y:=arena x g
  let A (t : ℕ):=∑i∈Finset.range t,d i
  let B (t : ℕ):=∑i∈Finset.range t,weight x (d i) (token x u i (d i))
  have count (i) (hi : i≤ x.n) : A i≤ x.k:=by
    rw [←total];exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi) (fun _ _ _=>Nat.zero_le _)
  have plusA (i) : A (i+1)=A i+d i:=Finset.sum_range_succ ..
  have plusB (i) : B (i+1)=B i+weight x (d i) (token x u i (d i)):=Finset.sum_range_succ ..
  have go (i : ℕ) (hi : i≤ x.n) : ∃v,Route y (prior x.n u i (A i)) v ∧ weight x (A i) v=B i :=by
    induction i with
    | zero =>
      refine ⟨RegionalBallDP.blank,.root,?_⟩;simp [A,B,weight]
    | succ i ih =>
      have il : i< x.n:=hi
      obtain ⟨v,path,costV⟩:=ih (by omega)
      let a:=A i;let b:=A (i+1)
      have ab : a≤ b:=by dsimp [a,b];rw [plusA];omega
      have diff : b-a=d i:=by dsimp [a,b];rw [plusA];omega
      have root : i=0 → a=0:=by rintro rfl;simp [a,A]
      have ok : allowed x u i a b:=⟨ab,root,diff ▸ act i il⟩
      obtain ⟨lk,pr,field⟩:=G.step u hu i il b (count _ hi) a ok
      have wd :=(G.states u hu i il b (count _ hi)).2
      have par : RegionalBallDP.width y (prior x.n u i a)=a:=by
        cases i with
        | zero => exact (show RegionalBallDP.width y 1=0 from if_pos rfl).trans (root rfl).symm
        | succ t => exact (G.states u hu t (by omega) a (count _ (by omega))).2
      let q:=arc x.n u i a b
      let t:=node x.n u i b
      let w:=splice y t q v
      have before (j : ℕ) (hj : j< a) (s : Bool) : w j s=v j s:=by
        change (if j< RegionalBallDP.width y (RegionalBallDP.parent y q) then _ else _)=_
        rw [pr,par,if_pos hj]
      have after (j : ℕ) (hj : j< d i) (s : Bool) : w (a+j) s=token x u i (d i) j s:=by
        have low : a≤ a+j:=by omega
        have high : a+j< b:=by omega
        unfold w splice;change (if a+j< RegionalBallDP.width y (RegionalBallDP.parent y q) then _ else if a+j< RegionalBallDP.width y t then _ else _)=_
        rw [pr,par,wd,if_neg (by omega),if_pos high,field (a+j) low high s,diff,Nat.add_sub_cancel_left]
      have route : Route y t w:=.append (G.states u hu i il b (count _ hi)).1 lk (pr ▸ path)
      refine ⟨w,route,?_⟩
      rw [plusB,←costV,shortSum x b (count _ hi),shortSum x a (count _ (by omega)),shortSum x (d i) (by have eq:=plusA i;have bb:=count (i+1) hi;omega)]
      rw [show b=a+d i by dsimp [a,b];exact plusA _,Finset.sum_range_add]
      congr 1
      · apply Finset.sum_congr rfl;intro j h;rw [before j (Finset.mem_range.mp h) false,before j (Finset.mem_range.mp h) true]
      · apply Finset.sum_congr rfl;intro j h;rw [after j (Finset.mem_range.mp h) false,after j (Finset.mem_range.mp h) true]
  obtain ⟨v,path,w⟩:=go x.n le_rfl
  have eq : A x.n=x.k:=total
  rw [eq] at path w
  exact ⟨v,by simpa only [prior,if_neg (by omega : x.n≠0)] using path,w⟩

