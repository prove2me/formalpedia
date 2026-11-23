-- Prove2me | solution 1 for StableMSR.Recovery.SingleRAM.dense_record_board_decoding
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:13:52.286032+00:00
-- url     : https://prove2.me/submissions/478c7af4-2521-4a46-803d-df006bfad7e4

import Definitions.Def_StableMSR_SingleCircuitRAM
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 15000
open StableMSR.Recovery StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleCircuit
open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog
open StableMSR.Recovery.WindowProfiles (subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Writes field)
open StableMSR.Recovery.SingleRAM
private lemma subAt (x : World) (p i : ℕ) (h : i< x.rows) : subR x (p+i) p=i:=by
  unfold subR;rw [Finset.sum_eq_single i]
  · simp
  · intro j _ ne;exact if_neg (by omega)
  · intro no;exact (no (Finset.mem_range.mpr h)).elim
private lemma triple (x : World) (a : ℕ) (ha : a< x.rows) : quotient x a=a/3 ∧ slot x a=a%3:=by
  have eq : quotient x a=a/3:=by
    unfold quotient;rw [Finset.sum_eq_single (a/3)]
    · exact if_pos ⟨by omega,by omega⟩
    · intro j _ ne;exact if_neg (by omega)
    · intro no;exact (no (Finset.mem_range.mpr (by omega))).elim
  refine ⟨eq,?_⟩;unfold slot;rw [eq]
  have t:=subAt x (3*(a/3)) (a%3) (by omega)
  rwa [show 3*(a/3)+a%3=a by omega] at t
private lemma divAt (x : World) (a b : ℕ) (ha : a< x.rows) (hb : b< x.n) : divN x (a*x.n+b)=a:=by
  unfold divN;rw [Finset.sum_eq_single a]
  · apply if_pos;constructor
    · omega
    · rw [Nat.succ_mul];omega
  · intro z _ ne;apply if_neg;intro hit
    rcases lt_or_gt_of_ne ne with h|h
    · have aux:=Nat.mul_le_mul_right x.n (show z+1≤ a by omega);omega
    · have aux:=Nat.mul_le_mul_right x.n (show a+1≤ z by omega);rw [Nat.succ_mul] at aux;omega
  · intro no;exact (no (Finset.mem_range.mpr ha)).elim
private lemma tagCode (op : Gate) (j : ℕ) : tagFor (opCode op) j=tinyTag op j:=by cases op <;> simp [tagFor,opCode,tinyTag]
private lemma childCode (op : Gate) (j : ℕ) : childFor (opCode op) (leftID op:ℤ) (rightID op:ℤ) j=(tinyChild op j:ℤ):=by
  cases op <;> by_cases z : j=0 <;> by_cases o : j=1 <;> simp [childFor,opCode,leftID,rightID,tinyChild,z,o]
theorem solution (x : World) (k H : ℕ) (m : ℕ→ℤ) (g : Gates) (roots : ℕ→ℕ)
    (hk : 0< x.k) (hn : 0< x.n) (eqk : k=x.k) (eqH : H=x.rows)
    (big : 1+5*(1+3*g.size*x.n*x.n)< H) (src : Input x g roots)
    (head : (m 0).toNat=3*g.size) (wr : Writes x {x with k:=k,rows:=H,mem:=m} packCell) :
    denotes {x with k:=k,rows:=H,mem:=m} g roots := by
  classical
  subst k;subst H
  let y:={x with mem:=m};let M:=3*g.size
  have cap : 1+5*(1+M*x.n*x.n)< x.rows:=big
  have M1 : M≤ M*x.n:=Nat.le_mul_of_pos_right _ hn
  have M2 : M*x.n≤ M*x.n*x.n:=Nat.le_mul_of_pos_right _ hn
  have hs : rawSize y=M:=head
  have si : 3*rawSize x=M:=congrArg (3*·) src.1
  refine ⟨?_,hs,?_⟩
  · change 1+5*(1+rawSize y*x.n*x.n)< x.rows;rw [hs];exact cap
  intro q hq;change q< M at hq
  have qr : q< x.rows:=by omega
  let j:=q%3;let p:=q/3
  have pg : p< g.size:=by dsimp [M,p] at *;omega
  have tt:=triple x q qr
  have fields:=src.2.1 (q/3) pg
  have val (b : ℕ) (hb : b≤3) (s : Bool) : readBand y b q 0 s=packCell x (1+b*M+q) 0 s:=by
    unfold readBand;rw [hs];exact wr _ (by interval_cases b <;> omega) 0 hk s
  have T:=val 0 (by decide) false;have D:=val 0 (by decide) true
  have C:=val 1 (by decide) false;have R:=val 3 (by decide) false
  simp only [Nat.zero_mul,Nat.add_zero] at T D
  have a1:=subAt x 1 q qr;have a2:=subAt x (1+M) q qr;have a4:=subAt x (1+3*M) q qr
  have tval : readBand y 0 q 0 false=tinyTag (gateAt g p) j:=by
    simpa only [packCell,si,if_neg (show 1+q≠0 by omega),if_pos (show 1+q<1+M by omega),Bool.false_eq_true,if_false,a1,tt.1,tt.2,fields.1,tagCode] using T
  have dval : readBand y 0 q 0 true=(p:ℤ):=by
    simpa only [packCell,si,if_neg (show 1+q≠0 by omega),if_pos (show 1+q<1+M by omega),if_true,a1,tt.1] using D
  have cval : readBand y 1 q 0 false=(tinyChild (gateAt g p) j:ℤ):=by
    simpa only [Nat.one_mul,packCell,si,if_neg (show 1+M+q≠0 by omega),if_neg (show ¬1+M+q<1+M by omega),if_pos (show 1+M+q<1+2*M by omega),a2,tt.1,tt.2,fields.1,fields.2.1,fields.2.2,childCode] using C
  have rval : readBand y 3 q 0 false=(roots q:ℤ):=by
    simpa only [packCell,si,if_neg (show 1+3*M+q≠0 by omega),if_neg (show ¬1+3*M+q<1+M by omega),if_neg (show ¬1+3*M+q<1+2*M by omega),if_neg (show ¬1+3*M+q<1+3*M by omega),if_pos (show 1+3*M+q<1+4*M by omega),a4,src.2.2.1 q hq] using R
  refine ⟨tval,(congrArg Int.toNat dval).trans (Int.toNat_natCast _),(congrArg Int.toNat cval).trans (Int.toNat_natCast _),(congrArg Int.toNat rval).trans (Int.toNat_natCast _),?_⟩
  ext v
  have vi:=v.isLt;change v.val< x.n at vi
  let off:=q*x.n+v.val;let t:=off/2;let a:=t/x.k;let b:=t%x.k
  have low : off< M*x.n:=by
    have le:=Nat.mul_le_mul_right x.n (show q+1≤ M by omega);rw [Nat.succ_mul] at le;dsimp [off];omega
  have al : a≤ off:=(Nat.div_le_self ..).trans (Nat.div_le_self ..)
  have bl : b< x.k:=Nat.mod_lt _ hk
  have row : 1+4*M+a< x.rows:=by omega
  have diff:=subAt x (1+4*M) a (by omega)
  have de:=divAt x q v.val qr vi
  have rem : remN x off=v.val:=by unfold remN;rw [show divN x off=q from de];exact subAt x _ _ (by omega)
  let side : Bool:=decide (off%2=1)
  have tb : a*x.k+b=t:=by dsimp [a,b];rw [Nat.mul_comm,Nat.div_add_mod]
  have coordinate : 2*(a*x.k+b)+(if side then 1 else 0)=off:=by
    rw [tb];dsimp [side,t];by_cases h:off%2=1 <;> simp [h] <;> omega
  have write:=wr (1+4*M+a) row b bl side
  have got : field y (1+4*M+a) b side=inputBit x p v.val:=by
    simpa only [packCell,si,if_neg (show 1+4*M+a≠0 by omega),if_neg (show ¬1+4*M+a<1+M by omega),if_neg (show ¬1+4*M+a<1+2*M by omega),if_neg (show ¬1+4*M+a<1+3*M by omega),if_neg (show ¬1+4*M+a<1+4*M by omega),diff,coordinate,show divN x off=q from de,rem,tt.1] using write
  have addreq : addr x.k (1+4*M+a) b+(if side then 1 else 0)=addr x.k (1+4*M) 0+off:=by
    unfold addr;rw [Nat.add_mul];omega
  have actual : field y (1+4*M+a) b side=y.mem (addr x.k (1+4*M) 0+off):=by
    cases hs:side <;> simp [field,center,witness,addreq,hs,y] at addreq ⊢ <;> congr 1 <;> omega
  have bit : y.mem (addr x.k (1+4*M) 0+off)=inputBit x p v.val:=actual.symm.trans got
  change v∈WindowMasks.block y q ↔ v∈maskAt x.n g q
  simp only [WindowMasks.block,maskAt,Finset.mem_filter,Finset.mem_univ,true_and,List.contains_iff_mem]
  change (0< y.mem (addr x.k (1+4*rawSize y) 0+q*x.n+v.val)) ↔ _
  rw [Nat.add_assoc]
  change (0< y.mem (addr x.k (1+4*rawSize y) 0+off)) ↔ _
  rw [hs,bit];exact src.2.2.2 p pg v
