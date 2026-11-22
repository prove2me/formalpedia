-- Prove2me | solution 1 for StableMSR.Recovery.WindowJoins.append_radius_sum
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:47:07.478435+00:00
-- url     : https://prove2.me/submissions/4568bc16-634f-4bab-82b9-e4d11e65aaa5

import Definitions.Def_StableMSR_WindowJoins
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles (Mem replace profileSpec Profiles Owned piece keys index active token contains)
open StableMSR.Recovery.RegionalBallDP (Word field word legalize weight Writes)
open StableMSR.Recovery.WindowJoins
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
private lemma shortSum (x : World) (c : ℕ) (hc : c≤ x.k) (w : RegionalBallDP.Word) :
    weight x c w=∑j∈Finset.range c,MinSumFPT.oracleAnswer x.dist (w j false) (w j true):=by
  classical
  unfold weight;rw [←Finset.sum_filter]
  have eq : (Finset.range x.k).filter (fun j=>j< c)=Finset.range c:=by
    ext j;simp only [Finset.mem_filter,Finset.mem_range];omega
  rw [eq]
private lemma offset (k a i : ℕ) (hi : i< k) : shift k (a+i) a=i :=by
  unfold shift;rw [Finset.sum_eq_single i]
  · simp
  · intro b _ ne;exact if_neg (fun e=>ne (Nat.add_left_cancel e))
  · exact fun no=>(no (Finset.mem_range.mpr hi)).elim
theorem solution (x : World) (a b : ℕ) (h : a+b≤ x.k) (L R : Word) :
    weight x (a+b) (appendWords x.k a (a+b) L R)=weight x a L+weight x b R := by
  rw [shortSum x (a+b) h,shortSum x a (by omega),shortSum x b (by omega),Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl;intro j hj;simp [appendWords,Finset.mem_range.mp hj]
  · apply Finset.sum_congr rfl;intro j hj;have hj':=Finset.mem_range.mp hj
    have h₁ : ¬a+j< a:=by omega
    have h₂ : a+j< a+b:=by omega
    simp [appendWords,h₁,h₂,offset x.k a j (by omega)]
