-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.ordered_production_replay
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T23:08:32.120043+00:00
-- url     : https://prove2.me/submissions/944ee98e-1850-4151-9bc2-4d237c804ff7

import Definitions.Def_StableMSR_SeparatorProductionEvents
set_option linter.all false
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

def imperative {S V:Type} (E:Algebra S V) (d:Instance) (w:ℕ) : S×V := Id.run do
  let all:=vertices d
  let small:=cuts all (min w d.n)
  let mut g:=E.initial
  let mut tab : Table V:=[]
  for k in List.range d.n do
    for s in small do
      for c in keysFor d all s do
        if c.length==k+1 && rimOf d c==s then
          for a in assignments d s do
            let mut acc:=E.fail
            for v in c do
              for x in d.menu v do
                let b:=(v,x)::a
                if localOK d b then
                  if let some ids:=refs d tab c v b then
                    let pair:=E.alternative g acc v x ids
                    g:=pair.1
                    acc:=pair.2
            tab:=((c,a),acc)::tab
  if let some ids:=(parts d all).mapM (m:=Option) (fun c=>lookup tab c []) then return E.finish g ids
  return (g,E.fail)

def body (g : Gates) (masks : List (List ℕ)) (sons : List ℕ) : Gates×ℕ := Id.run do
  let mut a:=g
  let mut tail:=0
  for m in masks do
    let l:=a.size
    a:=a.push (.atom m)
    let p:=a.size
    a:=a.push (.both tail l)
    tail:=p
  for s in sons do
    let p:=a.size
    a:=a.push (.both tail s)
    tail:=p
  return (a,tail)

def gateAlgebra (d:Instance) : Algebra Gates ℕ where
  initial:=#[.atom [],.stop]
  fail:=1
  alternative:=fun g acc v x ids=>
    let pair:=body g (d.owned v x) ids
    (pair.1.push (.either acc pair.2),pair.1.size)
  finish:=fun g ids=>body g [] ids

theorem loop_eq {A B:Type} (l:List A) (b:B) (f:A→B→Id (ForInStep B)) (g:B→A→B)
    (step:∀a b,f a b=.yield (g b a)) : (forIn l b f:Id B)=l.foldl g b := by
  have eq:f=(fun a b=>pure (ForInStep.yield (g b a))):=by funext a b;exact step a b
  rw [eq];exact List.forIn_pure_yield_eq_foldl _ _

end StableMSR.Recovery.TightLanguage

namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

theorem source_eq (d:Instance) (w:ℕ) : compileRegion d w=imperative (gateAlgebra d) d w := by
  set_option smartUnfolding false in rfl

section
variable {S V:Type} (E:Algebra S V) (d:Instance)

def offerLoop (tab:Table V) (c:List ℕ) (a:Assignment) (v x:ℕ) (p:S×V) : ForInStep (S×V) :=
  let b:=(v,x)::a
  if localOK d b then
    match refs d tab c v b with
    | some ids=>.yield (E.alternative p.1 p.2 v x ids)
    | _=>.yield p
  else .yield p

def optionLoop (tab:Table V) (c:List ℕ) (a:Assignment) (g:S) : S×V :=
  Id.run (forIn c (g,E.fail) (fun v p=>pure (.yield
    (Id.run (forIn (d.menu v) p (fun x q=>pure (offerLoop E d tab c a v x q)))))))

theorem options_fold (tab:Table V) (c:List ℕ) (a:Assignment) (g:S) :
    optionLoop E d tab c a g=collect E d tab c a g := by
  unfold optionLoop collect
  apply loop_eq
  intro v p;apply congrArg ForInStep.yield
  apply loop_eq
  intro x q
  by_cases ok:localOK d ((v,x)::a)=true
  · cases result:refs d tab c v ((v,x)::a) <;> simp only [offerLoop,offer,ok,result,if_true] <;> rfl
  · simp only [offerLoop,offer,ok,if_false];rfl

def assignmentLoop (c:List ℕ) (a:Assignment) (p:S×Table V) : S×Table V :=
  let b:=optionLoop E d p.2 c a p.1
  (b.1,((c,a),b.2)::p.2)

def componentLoop (k:ℕ) (s c:List ℕ) (p:S×Table V) : ForInStep (S×Table V) :=
  if c.length==k+1 && rimOf d c==s then
    .yield (Id.run (forIn (assignments d s) p (fun a q=>pure (.yield (assignmentLoop E d c a q)))))
  else .yield p

def tableLoop (w:ℕ) : S×Table V :=
  let vs:=vertices d
  let ss:=cuts vs (min w d.n)
  Id.run (forIn (List.range d.n) (E.initial,([]:Table V)) (fun k p=>pure (.yield
    (Id.run (forIn ss p (fun s q=>pure (.yield
      (Id.run (forIn (keysFor d vs s) q (fun c z=>pure (componentLoop E d k s c z)))))))))))

theorem table_fold (w:ℕ) : tableLoop E d w=build E d w := by
  unfold tableLoop build
  apply loop_eq;intro k p;apply congrArg ForInStep.yield
  apply loop_eq;intro s q;apply congrArg ForInStep.yield
  apply loop_eq;intro c z
  unfold componentLoop visit;split
  · apply congrArg ForInStep.yield
    apply loop_eq;intro a t
    simp only [assignmentLoop,install,options_fold];rfl
  · rfl

def rawTable {S V:Type} (E:Algebra S V) (d:Instance) (w:ℕ) : S×Table V := Id.run do
  let all:=vertices d
  let small:=cuts all (min w d.n)
  let mut g:=E.initial
  let mut tab : Table V:=[]
  for k in List.range d.n do
    for s in small do
      for c in keysFor d all s do
        if c.length==k+1 && rimOf d c==s then
          for a in assignments d s do
            let mut acc:=E.fail
            for v in c do
              for x in d.menu v do
                let b:=(v,x)::a
                if localOK d b then
                  if let some ids:=refs d tab c v b then
                    let pair:=E.alternative g acc v x ids
                    g:=pair.1
                    acc:=pair.2
            tab:=((c,a),acc)::tab
  return (g,tab)

theorem raw_eq (w:ℕ) : rawTable E d w=tableLoop E d w := by
  set_option smartUnfolding false in rfl

theorem normalized (w:ℕ) : imperative E d w=scan E d w := by
  let st:=rawTable E d w
  have raw: imperative E d w=(if let some ids:=(parts d (vertices d)).mapM (m:=Option) (fun c=>lookup st.2 c []) then E.finish st.1 ids else (st.1,E.fail)):=by
    set_option smartUnfolding false in rfl
  rw [raw]
  unfold scan
  have eq:st=build E d w:=(raw_eq E d w).trans (table_fold E d w)
  rw [eq]
  dsimp only
  cases z:(parts d (vertices d)).mapM (m:=Option) (fun c=>lookup (build E d w).2 c []) <;> rfl
end
end StableMSR.Recovery.TightLanguage
namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
theorem body_fold (g:Gates) (ms:List (List ℕ)) (ids:List ℕ) :
    body g ms ids=ids.foldl sonStep (ms.foldl litStep (g,0)) := by
  let ml:=fun (m:List ℕ) (z:Gates×ℕ)=>(pure (.yield (litStep z m)):Id (ForInStep (Gates×ℕ)))
  let sl:=fun (p:ℕ) (z:Gates×ℕ)=>(pure (.yield (sonStep z p)):Id (ForInStep (Gates×ℕ)))
  change (forIn ids (forIn ms (g,0) ml:Id (Gates×ℕ)) sl:Id (Gates×ℕ))=_
  rw [loop_eq ms _ ml litStep (fun _ _=>rfl),loop_eq ids _ sl sonStep (fun _ _=>rfl)]

end StableMSR.Recovery.TightLanguage
namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

inductive Aligned {A B:Type} (R:A→B→Prop) : List A→List B→Prop where
  | nil : Aligned R [] []
  | cons {x y xs ys} : R x y → Aligned R xs ys → Aligned R (x::xs) (y::ys)

theorem Aligned.weaken {A B:Type} {R T:A→B→Prop} {xs:List A} {ys:List B}
    (h:Aligned R xs ys) (imp:∀x y,R x y → T x y) : Aligned T xs ys := by
  induction h with
  | nil=>exact .nil
  | cons a _ ih=>exact .cons (imp _ _ a) ih

inductive Matched {A B:Type} (R:A→B→Prop) : Option A→Option B→Prop where
  | none : Matched R none none
  | some {x y} : R x y → Matched R (some x) (some y)

def TablesAgree {A B:Type} (R:A→B→Prop) : Table A→Table B→Prop :=
  Aligned (fun a b=>a.1=b.1 ∧ R a.2 b.2)

theorem lookup_agrees {A B:Type} {R:A→B→Prop} {ta:Table A} {tb:Table B} (h:TablesAgree R ta tb)
    (c:List ℕ) (a:Assignment) : Matched R (lookup ta c a) (lookup tb c a) := by
  induction h with
  | nil=>exact .none
  | @cons x y xs ys pair _ ih=>
    obtain ⟨key,rel⟩:=pair
    by_cases eq:y.1=(c,a)
    · have xx:=key.trans eq;simp [lookup,List.find?_cons,xx,eq];exact .some rel
    · have xx:x.1≠(c,a):=fun t=>eq (key.symm.trans t)
      simpa [lookup,List.find?_cons,xx,eq] using ih

theorem queries_agree {A B I:Type} {R:A→B→Prop} (is:List I) (f:I→Option A) (g:I→Option B)
    (eq:∀i,Matched R (f i) (g i)) : Matched (Aligned R) (is.mapM f) (is.mapM g) := by
  induction is with
  | nil=>exact .some .nil
  | cons i is ih=>
    have h:=eq i
    cases a:f i <;> cases b:g i <;> rw [a,b] at h <;> cases h
    · simp [List.mapM_cons,a,b];exact .none
    · rename_i x y rel
      cases c:is.mapM f <;> cases e:is.mapM g <;> rw [c,e] at ih <;> cases ih
      · simp [List.mapM_cons,a,b,c,e];exact .none
      · rename_i tail
        simp [List.mapM_cons,a,b,c,e];exact .some (.cons rel tail)

theorem fold_agrees {A B I:Type} (R:A→B→Prop) (f:A→I→A) (g:B→I→B)
    (step:∀a b i,R a b → R (f a i) (g b i)) (is:List I) (a:A) (b:B) (start:R a b) :
    R (is.foldl f a) (is.foldl g b) := by
  induction is generalizing a b with
  | nil=>exact start
  | cons i is ih=>exact ih _ _ (step a b i start)

end StableMSR.Recovery.TightLanguage
namespace StableMSR.Recovery.NativeWriter.Production
open SingleCircuit TightLanguage
set_option autoImplicit false
set_option maxHeartbeats 1200000

def Has (s : State) (k v : ℕ) := s.memo[k]?=some v
def Ext (s t : State) := ∀ k v, Has s k v → Has t k v
theorem value_of {s : State} {k v : ℕ} (h : Has s k v) : resolve s k=v := by unfold Has at h; simp [resolve,h]
theorem ext_step (s : State) (e : Event) : Ext s (step s e) := by
  intro k v h
  have lt : k<s.memo.size := by
    by_contra! bad
    simp [Has,Array.getElem?_eq_none bad] at h
  cases e <;> simpa [Has,step,Array.getElem?_push,lt,Nat.ne_of_lt lt] using h

theorem fold_ext (s : State) (es : List Event) : Ext s (es.foldl step s) := by
  induction es generalizing s with
  | nil=>exact fun _ _ h=>h
  | cons e es ih=>exact fun k v h=>ih (step s e) k v (ext_step s e k v h)

theorem play_append (a b : List Event) : play (a++b)=b.foldl step (play a) := List.foldl_append
theorem memo_size (s : State) (es : List Event) : (es.foldl step s).memo.size=s.memo.size+es.length := by
  induction es generalizing s with
  | nil=>simp
  | cons e es ih=>
    have one : (step s e).memo.size=s.memo.size+1 := by cases e <;> simp [step]
    simp [ih,one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem play_size (es : List Event) : (play es).memo.size=es.length+1 := by
  simpa [play,initial,Nat.add_comm] using memo_size initial es

theorem zero_has (es : List Event) : Has (play es) 0 1 := fold_ext initial es 0 1 rfl

theorem masks_fold (s : State) (ms : List (List ℕ)) :
    let t:=(ms.map Event.mask).foldl step s
    (t.gates,t.tail)=ms.foldl litStep (s.gates,s.tail) := by
  induction ms generalizing s with
  | nil=>rfl
  | cons m ms ih=>exact ih (step s (.mask m))

theorem children_fold (s : State) (ks vs : List ℕ) (ok : ks.Forall₂ (Has s) vs) :
    let t:=(ks.map Event.child).foldl step s
    (t.gates,t.tail)=vs.foldl sonStep (s.gates,s.tail) := by
  induction ks generalizing vs s with
  | nil=>cases ok;rfl
  | cons k ks ih=>
    cases ok with
    | cons h hs=>
      let t:=step s (.child k)
      have fr:=ext_step s (.child k)
      have tail:=ih t _ (hs.imp (fun a b hv=>fr a b hv))
      simpa only [List.map_cons,List.foldl_cons,step,sonStep,t,value_of h] using tail

def Block (es : List Event) (g : Gates) := (play es).gates=g ∧ (play es).tail=0

theorem alt_block (es : List Event) (g : Gates) (k u : ℕ) (ms : List (List ℕ)) (ks vs : List ℕ)
    (base : Block es g) (prev : Has (play es) k u) (kids : ks.Forall₂ (Has (play es)) vs) :
    let out:=es++ms.map Event.mask++ks.map Event.child++[Event.join k]
    let pair:=body g ms vs
    Block out (pair.1.push (.either u pair.2)) ∧ Has (play out) out.length pair.1.size := by
  let mid:=es++ms.map Event.mask
  let pre:=mid++ks.map Event.child
  have h1 : ((play mid).gates,(play mid).tail)=ms.foldl litStep (g,0) := by
    simpa only [mid,play_append,base.1,base.2] using masks_fold (play es) ms
  have f1 : Ext (play es) (play mid) := by rw [show mid=es++ms.map Event.mask from rfl,play_append];exact fold_ext _ _ 
  have h2 : ((play pre).gates,(play pre).tail)=body g ms vs := by
    rw [body_fold,←h1]
    simpa only [pre,play_append] using children_fold (play mid) ks vs (kids.imp (fun a b hv=>f1 a b hv))
  have f2 : Ext (play mid) (play pre) := by exact (play_append mid (ks.map Event.child)) ▸ fold_ext (play mid) (ks.map Event.child)
  have hk:=value_of (f2 k u (f1 k u prev))
  have hg:=congrArg Prod.fst h2
  have ht:=congrArg Prod.snd h2
  change Block (pre++[Event.join k]) _ ∧ Has (play (pre++[Event.join k])) (pre++[Event.join k]).length _
  simp only [Block,play_append,List.foldl_cons,List.foldl_nil,step,hk,show (play pre).gates=(body g ms vs).1 from hg,
    show (play pre).tail=(body g ms vs).2 from ht,Has,List.length_append,List.length_singleton]
  rw [←play_size pre]
  simp

theorem finish_block (es : List Event) (g : Gates) (ks vs : List ℕ) (base : Block es g)
    (kids : ks.Forall₂ (Has (play es)) vs) :
    let out:=es++ks.map Event.child++[Event.save]
    let pair:=body g [] vs
    Block out pair.1 ∧ Has (play out) out.length pair.2 := by
  let pre:=es++ks.map Event.child
  have h : ((play pre).gates,(play pre).tail)=body g [] vs := by
    simpa only [pre,play_append,body_fold,List.foldl_nil,base.1,base.2] using children_fold (play es) ks vs kids
  have hg:=congrArg Prod.fst h
  have ht:=congrArg Prod.snd h
  change Block (pre++[Event.save]) _ ∧ Has (play (pre++[Event.save])) (pre++[Event.save]).length _
  simp only [Block,play_append,List.foldl_cons,List.foldl_nil,step,show (play pre).gates=(body g [] vs).1 from hg,
    show (play pre).tail=(body g [] vs).2 from ht,Has,List.length_append,List.length_singleton]
  rw [←play_size pre]
  simp

end StableMSR.Recovery.NativeWriter.Production
namespace StableMSR.Recovery.NativeWriter.Production
open SingleCircuit TightLanguage
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem prefix_has {a b : List Event} (h : a <+: b) : Ext (play a) (play b) := by
  obtain ⟨l,rfl⟩:=h
  rw [play_append a l]
  exact fold_ext _ _

theorem list_rel {R : ℕ→ℕ→Prop} {ks vs : List ℕ} (a : TightLanguage.Aligned R ks vs) : ks.Forall₂ R vs := by
  induction a with
  | nil=>exact .nil
  | cons h _ ih=>exact .cons h ih

theorem tables_keep {a b : List Event} {ta tb : Table ℕ}
    (h : a <+: b) (ok : TablesAgree (Has (play a)) ta tb) : TablesAgree (Has (play b)) ta tb :=
  ok.weaken (fun _ _ hv=>⟨hv.1,prefix_has h _ _ hv.2⟩)

theorem collect_eq (d : Instance) (c : List ℕ) (a : Assignment) (es : List Event) (g : Gates)
    (ta tb : Table ℕ) (base : Block es g) (tables : TablesAgree (Has (play es)) ta tb) :
    let x:=collect (chartAlgebra d) d ta c a es
    let y:=collect (gateAlgebra d) d tb c a g
    (es <+: x.1) ∧ Block x.1 y.1 ∧ Has (play x.1) x.2 y.2 := by
  let J:=fun (p : List Event×ℕ) (q : Gates×ℕ)=>(es <+: p.1) ∧ Block p.1 q.1 ∧ Has (play p.1) p.2 q.2
  change J _ _
  unfold collect
  apply fold_agrees J
  · intro p q v inv
    apply fold_agrees J
    · intro p q x inv
      obtain ⟨ext,good,acc⟩:=inv
      let row:=(v,x)::a
      have sync:Matched (TightLanguage.Aligned (Has (play p.1))) (refs d ta c v row) (refs d tb c v row):=
        queries_agree (parts d (c.erase v)) _ _ (fun t=>lookup_agrees (tables_keep ext tables) _ _)
      by_cases ok:localOK d row=true
      · cases l:refs d ta c v row <;> cases r:refs d tb c v row <;> rw [l,r] at sync <;> cases sync
        · simpa only [J,offer,show localOK d ((v,x)::a)=true from ok,if_true,←show row=(v,x)::a from rfl,l,r,ok,if_true] using And.intro ext (And.intro good acc)
        · rename_i ks vs h
          have done:=alt_block p.1 q.1 p.2 q.2 (d.owned v x) ks vs good acc (list_rel h)
          change (_ <+: (offer _ _ _ _ _ _ _ _).1) ∧ _
          dsimp only [row] at l r
          simp only [offer,show localOK d ((v,x)::a)=true from ok,if_true,l,r,chartAlgebra,gateAlgebra]
          exact ⟨ext.trans ⟨(d.owned v x).map Event.mask++(ks.map Event.child++[Event.join p.2]),by simp [List.append_assoc]⟩,done⟩
      · simpa only [J,offer,if_neg (show localOK d ((v,x)::a)≠true from ok)] using And.intro ext (And.intro good acc)
    · exact inv
  · exact ⟨⟨[],by simp⟩,base,zero_has _⟩

theorem build_eq (d : Instance) (w : ℕ) :
    let p:=build (chartAlgebra d) d w
    let q:=build (gateAlgebra d) d w
    Block p.1 q.1 ∧ TablesAgree (Has (play p.1)) p.2 q.2 := by
  let J:=fun (p : List Event×Table ℕ) (q : Gates×Table ℕ)=>
    Block p.1 q.1 ∧ TablesAgree (Has (play p.1)) p.2 q.2
  change J _ _
  unfold build
  apply fold_agrees J
  · intro p q k h
    apply fold_agrees J
    · intro p q s h
      apply fold_agrees J
      · intro p q c h
        unfold visit
        split
        · apply fold_agrees J
          · intro p q a h
            obtain ⟨ext,block,hv⟩:=collect_eq d c a p.1 q.1 p.2 q.2 h.1 h.2
            exact ⟨block,.cons ⟨rfl,hv⟩ (tables_keep ext h.2)⟩
          · exact h
        · exact h
      · exact h
    · exact h
  · exact ⟨⟨rfl,rfl⟩,.nil⟩

theorem chart_exact (d : Instance) (w : ℕ) : result (chart d w)=compileRegion d w := by
  rw [source_eq,normalized]
  let a:=build (chartAlgebra d) d w
  let b:=build (gateAlgebra d) d w
  let cs:=parts d (vertices d)
  let f:=fun c=>lookup a.2 c []
  let g:=fun c=>lookup b.2 c []
  obtain ⟨base,tables⟩:=build_eq d w
  have sync:Matched (TightLanguage.Aligned (Has (play a.1))) (cs.mapM f) (cs.mapM g):=
    queries_agree cs f g (fun c=>lookup_agrees tables c [])
  unfold chart scan
  dsimp only
  cases l:cs.mapM f <;> cases r:cs.mapM g <;> rw [l,r] at sync <;> cases sync
  · exact Prod.ext base.1 (value_of (zero_has _))
  · rename_i ks vs h
    obtain ⟨block,hv⟩:=finish_block a.1 b.1 ks vs base (list_rel h)
    exact Prod.ext block.1 (value_of hv)

end StableMSR.Recovery.NativeWriter.Production
open StableMSR.Recovery.SingleCircuit StableMSR.Recovery.NativeWriter.Production
theorem solution (d : Instance) (w : ℕ) :
    result (chart d w)=compileRegion d w := chart_exact d w
