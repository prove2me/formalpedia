-- Prove2me | solution 1 for StableMSR.Recovery.WindowPorts.counted_ticket_classification
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:19:17.165664+00:00
-- url     : https://prove2.me/submissions/f3c7d8f9-dda5-4257-9111-35845d11133c

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
theorem solution (B : Board) (n k : ℕ) (hk : 1≤ k) (kn : k< n) (v z : ℕ) :
    WindowJoins.arc (lower B n k) v z ↔ TicketCase B n k v z := by
  let g:=lower B n k
  have np : 0< n:=by omega
  constructor
  · rintro ⟨small,loc⟩
    by_cases zz : z=0
    · subst z
      have h : (0:ℤ)=(v:ℤ):=loc
      have val : v=0:=by omega
      subst v;exact .zero
    let s:=z-1;let a:=firstCount n z;let b:=lastCount n z;let q:=sourceRow n z
    have al : a< n:=Nat.mod_lt _ np
    have bl : b< n:=Nat.mod_lt _ np
    have ra (m : ℕ) : m/n*n+m%n=m:=Nat.div_add_mod' ..
    have code : z=ticket n q a b:=by
      unfold ticket;change z=1+(s/n/n*n+s/n%n)*n+s%n;rw [ra, Nat.add_assoc,ra];dsimp [s];omega
    have what : activeTicket B n k q a b=(v:ℤ):=by simpa only [lower,if_neg zz] using loc
    simp only [activeTicket] at what
    split at what
    · rename_i h;obtain ⟨atom,eq,cap,bz⟩:=h
      have veq : v=finish n (B.dest q) a:=by exact_mod_cast what.symm
      rw [veq,code,eq,bz];exact .atom q atom (eq ▸ cap)
    · split at what
      · rename_i h;obtain ⟨l,cap,bz⟩:=h
        have veq : v=stage n (B.dest q) a:=by exact_mod_cast what.symm
        rw [veq,code,bz];exact .left q a l cap
      · split at what
        · rename_i h
          have veq : v=finish n (B.dest q) (a+b):=by exact_mod_cast what.symm
          rw [veq,code];exact .right q a b h.1 h.2
        · omega
  · intro rule;cases rule with
    | zero => exact ⟨by change 0<1+_;omega,rfl⟩
    | atom q h cap =>
      have lo : B.arity q< n:=by omega
      obtain ⟨u,v,w⟩:=unticket (q:=q) lo (show 0< n by omega)
      refine ⟨shortTicket h.1 lo np,?_⟩
      simp [lower,Nat.ne_of_gt (ticketPos ..),u,v,w,activeTicket,h,cap]
    | left q i h cap =>
      obtain ⟨u,v,w⟩:=unticket (q:=q) (show i< n by omega) np
      refine ⟨shortTicket h.1 (by omega) np,?_⟩
      have na : ¬initial B q (B.dest q):=fun t=>by have:=t.2.1;have:=h.2.1;omega
      simp [lower,Nat.ne_of_gt (ticketPos ..),u,v,w,activeTicket,na,h,cap]
    | right q a b h cap =>
      obtain ⟨u,v,w⟩:=unticket (q:=q) (show a< n by omega) (show b< n by omega)
      refine ⟨shortTicket h.1 (by omega) (by omega),?_⟩
      have na : ¬initial B q (B.dest q):=fun t=>by have:=t.2.1;have:=h.2.1;omega
      have nl : ¬port B 1 q (B.dest q):=fun t=>by have:=t.2.1;have:=h.2.1;omega
      simp [lower,Nat.ne_of_gt (ticketPos ..),u,v,w,activeTicket,na,nl,h,cap]
