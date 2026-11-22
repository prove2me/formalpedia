-- Prove2me | solution 1 for StableMSR.Recovery.WindowPorts.factored_ports_exact_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:19:17.113443+00:00
-- url     : https://prove2.me/submissions/f6d9abd0-aa18-4c5f-a436-1770e0479729

import Definitions.Def_StableMSR_WindowPorts
import Theorems.Thm_StableMSR_Recovery_WindowPorts_counted_ticket_classification
import Theorems.Thm_StableMSR_Recovery_WindowPorts_counted_state_addresses
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
private lemma fieldSpec (B : Board) (n k q a b : ℕ) (ha : a< n) (hb : b< n) :
    let g:=lower B n k;let z:=ticket n q a b
    (g.fork z ↔ B.tag q≠0) ∧
    g.lhs z=(if B.tag q=1 then finish n (B.child q) a else stage n (B.dest q) a) ∧
    g.rhs z=(if B.tag q=1 then 0 else finish n (B.child q) b) ∧ g.payload z=B.value q:=by
  obtain ⟨i,j,l⟩:=unticket (q:=q) ha hb
  simp [lower,Nat.ne_of_gt (ticketPos ..),i,j,l]
private lemma tailZero {B : Board} {k p c : ℕ} {w : Word} (h : Reach k B p c w) :
    ∀j,c≤ j → ∀s,w j s=0:=by
  cases h with
  | literal h cap => intro j hj s;exact if_neg (by omega)
  | @fork l r p a b u v hl hr one two cap => intro j hj s;simp [appendWords,show ¬j< a by omega,show ¬j< a+b by omega]
private lemma endCopy {B : Board} {k p c : ℕ} {w : Word} (h : Reach k B p c w) (other : Word) :
    appendWords k c c w other=w:=by
  funext j s;by_cases hi : j< c
  · simp [appendWords,hi]
  · simp [appendWords,hi,tailZero h j (by omega) s]
private def Meaning (B : Board) (n k v : ℕ) (w : Word) :=
  (∀p c,p< B.size → c≤ k → v=finish n p c → Reach k B p c w) ∧
  (∀p c,p< B.size → c≤ k → v=stage n p c → ∃l,port B 1 l p ∧ Reach k B (B.child l) c w)
private lemma semanticSound (B : Board) (n k : ℕ) (hk : 1≤ k) (kn : k< n) :
    ∀v w,Derives k (lower B n k) v w → Meaning B n k v w:=by
  let g:=lower B n k
  obtain ⟨addr,order,between,dis,injF,injS⟩:=counted_state_addresses B n k hk kn
  have zeroMeans (w : Word) : Meaning B n k 0 w:=by
    constructor <;> intro p c hp hc eq
    · unfold finish at eq;omega
    · unfold stage at eq;omega
  have onFinish {p c : ℕ} {w : Word} (hc : c≤ k) (h : Reach k B p c w) : Meaning B n k (finish n p c) w:=by
    constructor
    · intro r t _ ht eq;obtain ⟨rfl,rfl⟩:=injF _ _ _ _ hc ht eq;exact h
    · intro r t _ ht eq;exact (dis _ _ _ _ ht hc eq.symm).elim
  have onStage {p c t : ℕ} {w : Word} (hc : c≤ k) (pr : port B 1 t p) (rr : Reach k B (B.child t) c w) :
      Meaning B n k (stage n p c) w:=by
    constructor
    · intro r j _ hj eq;exact (dis _ _ _ _ hc hj eq).elim
    · intro r j _ hj eq;obtain ⟨rfl,rfl⟩:=injS _ _ _ _ hc hj eq;exact ⟨t,pr,rr⟩
  intro v w der;induction der with
  | @leaf v z valid leaf =>
    cases (counted_ticket_classification B n k hk kn _ _).mp valid with
    | zero => exact zeroMeans _
    | atom q h cap =>
      obtain ⟨fr,_,_,pay⟩:=fieldSpec B n k q (B.arity q) 0 (by omega) (by omega)
      have sz:=(addr _ h.2.2.2 _ cap).2.2.2
      apply onFinish cap
      have eq : atomWord (lower B n k) (finish n (B.dest q) (B.arity q)) (ticket n q (B.arity q) 0)=trimWord (B.arity q) (B.value q):=by
        funext j s;unfold atomWord trimWord;rw [sz,pay]
      rw [eq];exact .literal h cap
    | left q i h cap =>
      have f:=(fieldSpec B n k q i 0 (by omega) (by omega)).1;exact (leaf (f.mpr (by have:=h.2.1;omega))).elim
    | right q a b h cap =>
      have f:=(fieldSpec B n k q a b (by omega) (by omega)).1;exact (leaf (f.mpr (by have:=h.2.1;omega))).elim
  | @join v z u w valid fork jt du dw iu iw =>
    cases (counted_ticket_classification B n k hk kn _ _).mp valid with
    | zero => exact (fork.1 rfl).elim
    | atom q h cap =>
      exact ((fieldSpec B n k q _ 0 (by omega) (by omega)).1.mp fork h.2.1).elim
    | left q i h cap =>
      obtain ⟨_,l,_,_⟩:=fieldSpec B n k q i 0 (by omega) (by omega)
      rw [if_pos h.2.1] at l
      have small:=(h.2.2.2.2).trans h.2.2.2.1
      have one:=iu.1 _ _ small cap l
      have wlen:=(addr _ small _ cap).2.2.2
      have dlen:=(addr _ h.2.2.2.1 _ cap).2.2.1
      rw [l,wlen,dlen,endCopy one];exact onStage cap h one
    | right q a b h cap =>
      obtain ⟨_,l,r,_⟩:=fieldSpec B n k q a b (by omega) (by omega)
      have nt : B.tag q≠1:=by have:=h.2.1;omega
      rw [if_neg nt] at l r
      obtain ⟨t,pr,one⟩:=iu.2 _ _ h.2.2.2.1 (by omega) l
      have small:=h.2.2.2.2.trans h.2.2.2.1
      have two:=iw.1 _ _ small (by omega) r
      have alen:=(addr _ h.2.2.2.1 a (by omega)).2.2.1
      have dlen:=(addr _ h.2.2.2.1 _ cap).2.2.2
      rw [l,alen,dlen];exact onFinish cap (.fork pr h one two cap)
private lemma semanticComplete (B : Board) (n k : ℕ) (hk : 1≤ k) (kn : k< n) :
    ∀p c w,Reach k B p c w → Derives k (lower B n k) (finish n p c) w:=by
  let g:=lower B n k
  obtain ⟨addr,order,between,_,_,_⟩:=counted_state_addresses B n k hk kn
  have empty : Derives k g 0 (atomWord g 0 0):=
    .leaf ((counted_ticket_classification B n k hk kn 0 0).mpr .zero) (fun f=>f.1 rfl)
  have lzero : g.len 0=0:=by simp [g,lower,expandLen]
  intro p c w reach;induction reach with
  | @literal q p h cap =>
    obtain ⟨hq,t,rfl,sp⟩:=h
    have lit : initial B q (B.dest q):=⟨hq,t,rfl,sp⟩
    let z:=ticket n q (B.arity q) 0
    obtain ⟨fr,_,_,pay⟩:=fieldSpec B n k q (B.arity q) 0 (by omega) (by omega)
    have raw:=Derives.leaf (k:=k) ((counted_ticket_classification B n k hk kn _ _).mpr (.atom q lit cap)) (fun f=>(fr.mp f) t)
    have eq : atomWord (lower B n k) (finish n (B.dest q) (B.arity q)) (ticket n q (B.arity q) 0)=trimWord (B.arity q) (B.value q):=by
      funext j s;unfold atomWord trimWord;rw [(addr _ sp _ cap).2.2.2,pay]
    rwa [eq] at raw
  | @fork l r p a b u v hl hr one two cap iu iv =>
    have leA : a≤ k:=by omega
    have leB : b≤ k:=by omega
    have pl:=hl.2.2.2.1
    have lc:=hl.2.2.2.2.trans pl;have rc:=hr.2.2.2.2.trans pl
    have ld:=hl.2.2.1;have rd:=hr.2.2.1
    let z:=ticket n l a 0;let t:=ticket n r a b
    have aa : WindowJoins.arc g (stage n p a) z:=by
      rw [←ld];exact (counted_ticket_classification B n k hk kn _ _).mpr (.left l a (ld.symm ▸ hl) leA)
    have ab : WindowJoins.arc g (finish n p (a+b)) t:=by
      rw [←rd];exact (counted_ticket_classification B n k hk kn _ _).mpr (.right r a b (rd.symm ▸ hr) cap)
    obtain ⟨fl,la,ra,_⟩:=fieldSpec B n k l a 0 (by omega) (by omega)
    obtain ⟨fr,lb,rb,_⟩:=fieldSpec B n k r a b (by omega) (by omega)
    rw [if_pos hl.2.1] at la ra
    have nr : B.tag r≠1:=by have:=hr.2.1;omega
    rw [if_neg nr,rd] at lb;rw [if_neg nr] at rb
    have sza:=(addr _ pl a leA).2.2.1
    have szl:=(addr _ lc a leA).2.2.2
    have szr:=(addr _ rc b leB).2.2.2
    have szg:=(addr _ pl _ cap).2.2.2
    change g.lhs z=_ at la;change g.rhs z=_ at ra;change g.lhs t=_ at lb;change g.rhs t=_ at rb
    have j1 : joint g (stage n p a) z:=by
      unfold joint;rw [la,ra,szl,lzero,sza]
      exact ⟨order _ _ _ _ leA leA hl.2.2.2.2,by unfold stage;omega,by omega⟩
    have j2 : joint g (finish n p (a+b)) t:=by
      unfold joint;rw [lb,rb,sza,szr,szg]
      exact ⟨between _ _ _ leA cap,(order _ _ _ _ leB leA hr.2.2.2.2).trans (between _ _ _ leA cap),rfl⟩
    have left:=Derives.join aa (fl.mpr (by have:=hl.2.1;omega)) j1 (la.symm ▸ iu) (ra.symm ▸ empty)
    rw [la,szl,sza,endCopy one] at left
    have done:=Derives.join ab (fr.mpr (by have:=hr.2.1;omega)) j2 (lb.symm ▸ left) (rb.symm ▸ iv)
    rwa [lb,sza,szg] at done
theorem solution (B : Board) (n k : ℕ) (hk : 1≤ k) (kn : k< n) (p c : ℕ) (pc : p< B.size) (ck : c≤ k) (u : Word) :
    Derives k (lower B n k) (finish n p c) u ↔ Reach k B p c u := by
  exact ⟨fun d=>(semanticSound B n k hk kn _ _ d).1 _ _ pc ck rfl,semanticComplete B n k hk kn _ _ _⟩
