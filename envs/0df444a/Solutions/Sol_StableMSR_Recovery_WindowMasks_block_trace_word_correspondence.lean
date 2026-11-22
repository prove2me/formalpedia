-- Prove2me | solution 1 for StableMSR.Recovery.WindowMasks.block_trace_word_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:26:25.231052+00:00
-- url     : https://prove2.me/submissions/b10b548c-c497-48c6-84e2-155c5c308df2

import Definitions.Def_StableMSR_WindowBlockMasks
import Theorems.Thm_StableMSR_Recovery_WindowMasks_canonical_block_endpoints
import Theorems.Thm_StableMSR_Recovery_WindowJoins_append_radius_sum
import Theorems.Thm_StableMSR_Recovery_WindowJoins_append_disjoint_owned_covers
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
private lemma emitSupport {n : ℕ} (C : Cluster n) : support (emit C)=C:=by
  by_cases h : C.Nonempty
  · simp [support,emit,h]
  · have e:=Finset.not_nonempty_iff_eq_empty.mp h;subst C;simp [support,emit]
private lemma appSupport {n : ℕ} (L R : List (Cluster n)) : support (L++R)=support L∪support R:=by
  ext p;simp [support,or_and_right,exists_or]
private lemma separate {n : ℕ} {L R : List (Cluster n)} (h : (L++R).Pairwise Disjoint) : Disjoint (support L) (support R):=by
  obtain ⟨_,_,cross⟩:=List.pairwise_append.mp h
  apply Finset.disjoint_left.mpr;intro p pl pr
  obtain ⟨C,c,pc⟩:=Finset.mem_biUnion.mp pl;obtain ⟨D,d,pd⟩:=Finset.mem_biUnion.mp pr
  exact Finset.disjoint_left.mp (cross C (List.mem_toFinset.mp c) D (List.mem_toFinset.mp d)) pc pd
theorem solution (x : World) (B : Board) (hk : 1≤ x.k) (hn : 0< x.n)
    (counts : ∀q< B.size,B.arity q=chargeCount x q)
    (values : ∀q< B.size,∀j< x.k,∀s,B.value q j s=oneWord x q j s) :
    (∀p c w,Reach x.k B p c w → ∃L,Trace B (block x) p L ∧ L.length=c ∧
      weight x c w=payment x.dist L ∧ (L.Pairwise Disjoint → Owned x (support L) c w)) ∧
    ∀p L,Trace B (block x) p L → L.length≤ x.k → ∃w,Reach x.k B p L.length w ∧
      weight x L.length w=payment x.dist L := by
  have literal (q : ℕ) (hq : q< B.size) (ha : B.arity q≤ x.k) :
      B.arity q=(emit (block x q)).length ∧
      weight x (B.arity q) (trimWord (B.arity q) (B.value q))=payment x.dist (emit (block x q)) ∧
      Owned x (support (emit (block x q))) (B.arity q) (trimWord (B.arity q) (B.value q)):=by
    obtain ⟨len,own,cost,_⟩:=canonical_block_endpoints x q hk hn
    have eq : trimWord (B.arity q) (B.value q)=trimWord (chargeCount x q) (oneWord x q):=by
      funext j s;by_cases h : j< B.arity q
      · have hi:=values q hq j (h.trans_le ha) s
        simp only [trimWord,←counts q hq,h,if_true,hi]
      · simp only [trimWord,←counts q hq,h,if_false]
    rw [eq,counts q hq,emitSupport];exact ⟨len,cost,own⟩
  constructor
  · intro p c w der;induction der with
    | @literal q p init cap =>
      obtain ⟨len,cost,own⟩:=literal q init.1 cap
      exact ⟨_,.literal init,len.symm,cost,fun _=>own⟩
    | @fork l r p a b u v hl hr dl dr cap il ir =>
      obtain ⟨L,tl,ll,costL,ownL⟩:=il;obtain ⟨R,tr,rl,costR,ownR⟩:=ir
      refine ⟨L++R,.fork hl hr tl tr,by simp [ll,rl],?_,?_⟩
      · rw [WindowJoins.append_radius_sum x a b cap,costL,costR];simp [payment]
      · intro pair;obtain ⟨one,two,_⟩:=List.pairwise_append.mp pair;rw [appSupport]
        exact (WindowJoins.append_disjoint_owned_covers x _ _ a b cap (separate pair) u v (ownL one) (ownR two)).1
  · intro p L h;induction h with
    | @literal q p init =>
      intro cap;have le:=(canonical_block_endpoints x q hk hn).1
      have ar: B.arity q=(emit (block x q)).length:=(counts q init.1).trans le
      rw [←ar] at cap ⊢;exact ⟨_,.literal init cap,(literal q init.1 cap).2.1⟩
    | @fork l r p L R hl hr tl tr il ir =>
      intro cap;rw [List.length_append] at cap ⊢
      obtain ⟨u,du,uw⟩:=il (by omega);obtain ⟨v,dv,vw⟩:=ir (by omega)
      refine ⟨_,.fork hl hr du dv cap,?_⟩
      rw [WindowJoins.append_radius_sum x _ _ cap,uw,vw];simp [payment]
