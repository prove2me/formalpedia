-- Prove2me | solution 1 for StableMSR.Recovery.WindowPorts.counted_state_addresses
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:19:17.055144+00:00
-- url     : https://prove2.me/submissions/a0ec9511-0036-4463-ba24-add02a05b8e9

import Definitions.Def_StableMSR_WindowPorts
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
private lemma splitRadix {n a i : ℕ} (h : i< n) : (a*n+i)/n=a ∧ (a*n+i)%n=i:=by
  have pos : 0< n:=by omega
  constructor
  · rw [Nat.mul_comm a n,Nat.mul_add_div pos,Nat.div_eq_of_lt h,Nat.add_zero]
  · simp [Nat.add_mod,Nat.mod_eq_of_lt h]
private lemma unticket {n q a b : ℕ} (ha : a< n) (hb : b< n) :
    sourceRow n (ticket n q a b)=q ∧ firstCount n (ticket n q a b)=a ∧ lastCount n (ticket n q a b)=b:=by
  have e : ticket n q a b-1=(q*n+a)*n+b:=by unfold ticket;omega
  have t:=splitRadix (a:=q*n+a) hb;have u:=splitRadix (a:=q) ha
  simp only [sourceRow,firstCount,lastCount,e,t.1,t.2,u.1,u.2,and_self]
private lemma nextDigit {n a b i : ℕ} (hi : i< n) (h : a< b) (j : ℕ) : a*n+i< b*n+j:=by
  have one : a*n+i<(a+1)*n:=by rw [Nat.succ_mul];omega
  exact one.trans_le ((Nat.mul_le_mul_right n h).trans (Nat.le_add_right ..))
private lemma shortTicket {n q a b m : ℕ} (hq : q< m) (ha : a< n) (hb : b< n) : ticket n q a b< volume m n:=by
  have one:=nextDigit ha hq 0;have two:=nextDigit hb (show q*n+a< m*n by omega) 0
  unfold ticket volume;omega
private lemma ticketPos (n q a b : ℕ) : 0< ticket n q a b:=by unfold ticket;omega
theorem solution (B : Board) (n k : ℕ) (hk : 1≤ k) (kn : k< n) :
    (∀p< B.size,∀i≤ k,stage n p i< volume B.size n ∧ finish n p i< volume B.size n ∧
      (lower B n k).len (stage n p i)=i ∧ (lower B n k).len (finish n p i)=i) ∧
    (∀p q i j,i≤ k → j≤ k → p< q → finish n p i< stage n q j) ∧
    (∀p i j,i≤ k → j≤ k → stage n p i< finish n p j) ∧
    (∀p q i j,i≤ k → j≤ k → stage n p i≠finish n q j) ∧
    (∀p q i j,i≤ k → j≤ k → finish n p i=finish n q j → p=q ∧ i=j) ∧
    (∀p q i j,i≤ k → j≤ k → stage n p i=stage n q j → p=q ∧ i=j) := by
  have cap (p : ℕ) (hp : p< B.size) : 2*p+1< B.size*n:=by
    have t:=Nat.mul_le_mul_left B.size (show 2≤ n by omega);omega
  have inst (p j : ℕ) (hp : p< B.size) (hj : j≤ k) :
      stage n p j< volume B.size n ∧ finish n p j< volume B.size n:=by
    have h:=cap p hp
    have a:=nextDigit (show j< n by omega) (show 2*p< B.size*n by omega) 0
    have b:=nextDigit (show j< n by omega) h 0
    unfold stage finish volume;omega
  have parts (a i b j : ℕ) (hi : i< n) (hj : j< n) (h : 1+a*n+i=1+b*n+j) : a=b ∧ i=j:=by
    have eq : a*n+i=b*n+j:=by omega
    have x:=splitRadix (a:=a) hi;have y:=splitRadix (a:=b) hj;rw [eq] at x;omega
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro p hp j hj;obtain ⟨s,f⟩:=inst p j hp hj
    have es : stage n p j-1=(2*p)*n+j:=by unfold stage;omega
    have ef : finish n p j-1=(2*p+1)*n+j:=by unfold finish;omega
    exact ⟨s,f,by simp [lower,s,expandLen,es,(splitRadix (a:=2*p) (show j< n by omega)).2,Nat.min_eq_right hj],
      by simp [lower,f,expandLen,ef,(splitRadix (a:=2*p+1) (show j< n by omega)).2,Nat.min_eq_right hj]⟩
  · intro p q i j hi hj h
    have t:=nextDigit (show i< n by omega) (show 2*p+1<2*q by omega) j;unfold stage finish;omega
  · intro p i j hi hj
    have t:=nextDigit (show i< n by omega) (show 2*p<2*p+1 by omega) j;unfold stage finish;omega
  · intro p q i j hi hj eq;have t:=parts _ _ _ _ (by omega) (by omega) eq;omega
  · intro p q i j hi hj eq;have t:=parts _ _ _ _ (by omega) (by omega) eq;omega
  · intro p q i j hi hj eq;have t:=parts _ _ _ _ (by omega) (by omega) eq;omega
