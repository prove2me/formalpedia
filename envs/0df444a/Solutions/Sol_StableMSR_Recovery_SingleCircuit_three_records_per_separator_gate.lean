-- Prove2me | solution 1 for StableMSR.Recovery.SingleCircuit.three_records_per_separator_gate
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:13:33.619044+00:00
-- url     : https://prove2.me/submissions/8134b096-ed2b-44cf-9cfa-76b4af21e267

import Definitions.Def_StableMSR_SingleSeparatorCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 15000
open StableMSR.Recovery StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleCircuit
private lemma literalSlot {g : Gates} {roots : ℕ→ℕ} {q p : ℕ} (h : initial (boardOf g roots) q p) :
    p< g.size ∧ q/3=p ∧ tinyTag (gateAt g p) (q%3)=0:=by
  obtain ⟨h1,h2,h3,_⟩:=h
  change q<3*g.size at h1;change q/3=p at h3
  change tinyTag (gateAt g (q/3)) (q%3)=0 at h2
  exact ⟨by omega,h3,h3 ▸ h2⟩
private lemma portSlot {g : Gates} {roots : ℕ→ℕ} {q p : ℕ} {t : ℤ} (h : port (boardOf g roots) t q p) :
    p< g.size ∧ tinyTag (gateAt g p) (q%3)=t ∧ (boardOf g roots).child q=tinyChild (gateAt g p) (q%3) ∧ (boardOf g roots).child q< p:=by
  obtain ⟨h1,h2,h3,_,h4⟩:=h
  change q<3*g.size at h1;change q/3=p at h3
  change tinyTag (gateAt g (q/3)) (q%3)=t at h2
  exact ⟨by omega,h3 ▸ h2,by change tinyChild (gateAt g (q/3)) _=_;rw [h3],h4⟩
private lemma mkLit {g : Gates} (roots : ℕ→ℕ) {p : ℕ} {pts : List ℕ} (hp : p< g.size) (e : gateAt g p=.atom pts) : initial (boardOf g roots) (3*p) p:=by
  have d : 3*p/3=p:=by omega
  refine ⟨by change 3*p<3*g.size;omega,?_,d,by change p<3*g.size;omega⟩
  change tinyTag (gateAt g (3*p/3)) (3*p%3)=0;simp [d,e,tinyTag]
private lemma mkPort {g : Gates} (roots : ℕ→ℕ) {p j : ℕ} {t : ℤ} (hp : p< g.size) (hj : j<3)
    (tag : tinyTag (gateAt g p) j=t) (ord : tinyChild (gateAt g p) j< p) :
    port (boardOf g roots) t (3*p+j) p ∧ (boardOf g roots).child (3*p+j)=tinyChild (gateAt g p) j:=by
  have div : (3*p+j)/3=p:=by omega
  have mod : (3*p+j)%3=j:=by omega
  have item : (boardOf g roots).child (3*p+j)=tinyChild (gateAt g p) j:=by change tinyChild _ _=_;rw [div,mod]
  exact ⟨⟨by change 3*p+j<3*g.size;omega,by change tinyTag _ _=t;simpa only [div,mod] using tag,div,by change p<3*g.size;omega,item ▸ ord⟩,item⟩
private lemma atZero {n : ℕ} {g : Gates} (zero : gateAt g 0=.atom []) {L : List (Cluster n)} (h : Language n g 0 L) : L=[]:=by
  cases h with
  | lit _ e=>rw [zero] at e;injection e with v;subst_vars;simp [emit]
  | both _ _ h _ _ _=>omega
  | left _ _ h _=>omega
  | right _ _ h _=>omega
theorem solution (n : ℕ) (g : Gates) (roots : ℕ→ℕ) (live : 0< g.size) (zero : gateAt g 0=.atom [])
    (p : ℕ) (L : List (Cluster n)) :
    WindowMasks.Trace (boardOf g roots) (maskAt n g) p L ↔ Language n g p L := by
  classical
  let B:=boardOf g roots;let F:=maskAt n g
  constructor
  · intro found;induction found with
    | @literal q p hp=>
      obtain ⟨live,d,tag⟩:=literalSlot hp
      cases e:gateAt g p with
      | stop=>simp [e,tinyTag] at tag
      | atom pts=>simpa [maskAt,d,e,tinyMask] using (Language.lit (n:=n) live e)
      | both i j=>simp [e,tinyTag] at tag;split_ifs at tag <;> omega
      | either i j=>simp [e,tinyTag] at tag;split_ifs at tag <;> omega
    | @fork q r p W Z l h _ _ il ir=>
      obtain ⟨pg,tl,cl,ol⟩:=portSlot l;obtain ⟨_,tr,cr,orr⟩:=portSlot h
      cases e:gateAt g p with
      | stop=>simp [e,tinyTag] at tl
      | atom pts=>simp [e,tinyTag] at tl;split_ifs at tl <;> omega
      | both i j=>
        have dl : q%3=0:=by by_contra no;simp [e,tinyTag,no] at tl;split_ifs at tl <;> omega
        have dr : r%3=1:=by by_contra no;by_cases x:r%3=0 <;> simp [e,tinyTag,x,no] at tr
        simp [e,tinyChild,dl] at cl;simp [e,tinyChild,dr] at cr
        rw [cl] at ol il;rw [cr] at orr ir
        exact .both pg e ol orr il ir
      | either i j=>
        have dl : q%3=0 ∨ q%3=1:=by by_contra no;simp [e,tinyTag,no] at tl;split_ifs at tl <;> omega
        have dr : r%3=2:=by by_contra no;by_cases x:r%3=0 ∨ r%3=1 <;> simp [e,tinyTag,x,no] at tr
        simp [e,tinyChild,dr] at cr;rw [cr] at ir
        have empty:=atZero zero ir;subst Z;rw [List.append_nil]
        rcases dl with d|d
        · simp [e,tinyChild,d] at cl;rw [cl] at il ol;exact .left pg e ol il
        · simp [e,tinyChild,d] at cl;rw [cl] at il ol;exact .right pg e ol il
  · have blank : Trace B F 0 []:=by
      have tr:=Trace.literal (F:=F) (mkLit roots live zero)
      simpa [B,F,maskAt,zero,tinyMask,emit] using tr
    intro h;induction h with
    | @lit p pts h e=>
      have tr:=Trace.literal (F:=F) (mkLit roots h e)
      have eq : 3*p/3=p:=by omega
      simpa [F,maskAt,eq,e,tinyMask] using tr
    | @both p i j L R hp e li rj _ _ il ir=>
      have l:=mkPort roots (j:=0) (t:=1) hp (by decide) (by simp [e,tinyTag]) (by simpa [e,tinyChild] using li)
      have r:=mkPort roots (j:=1) (t:=2) hp (by decide) (by simp [e,tinyTag]) (by simpa [e,tinyChild] using rj)
      exact .fork l.1 r.1 (by rw [l.2];simpa [e,tinyChild] using il) (by simpa [r.2,e,tinyChild] using ir)
    | @left p i j L hp e li _ ih=>
      have l:=mkPort roots (j:=0) (t:=1) hp (by decide) (by simp [e,tinyTag]) (by simpa [e,tinyChild] using li)
      have r:=mkPort roots (j:=2) (t:=2) hp (by decide) (by simp [e,tinyTag]) (by simp [e,tinyChild];omega)
      have tr:=Trace.fork l.1 r.1 (L:=L) (R:=[]) (F:=F) (by rw [l.2];simpa [e,tinyChild] using ih) (by simpa [r.2,e,tinyChild] using blank)
      simpa [F] using tr
    | @right p i j L hp e rj _ ih=>
      have l:=mkPort roots (j:=1) (t:=1) hp (by decide) (by simp [e,tinyTag]) (by simpa [e,tinyChild] using rj)
      have r:=mkPort roots (j:=2) (t:=2) hp (by decide) (by simp [e,tinyTag]) (by simp [e,tinyChild];omega)
      have tr:=Trace.fork l.1 r.1 (L:=L) (R:=[]) (F:=F) (by rw [l.2];simpa [e,tinyChild] using ih) (by simpa [r.2,e,tinyChild] using blank)
      simpa [F] using tr
