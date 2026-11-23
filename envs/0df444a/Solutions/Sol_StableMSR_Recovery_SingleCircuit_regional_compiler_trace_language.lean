-- Prove2me | solution 1 for StableMSR.Recovery.SingleCircuit.regional_compiler_trace_language
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T20:20:42.201443+00:00
-- url     : https://prove2.me/submissions/864fdf32-fb9b-4b12-a13f-1709cfda3ba4

import Definitions.Def_StableMSR_TightComponentTrace
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

structure Semantics {S V:Type} (E:Algebra S V) where
  extension : S→S→Prop
  refl : ∀g,extension g g
  trans : ∀{g t z},extension g t → extension t z → extension g z
  holds : S→V→Lang Letter→Prop
  keep : ∀{g t p L},extension g t → holds g p L → holds t p L
  fail : ∀g,extension E.initial g → holds g E.fail (fun _=>False)
  alt : ∀g p L v x ids ls,extension E.initial g → holds g p L → Aligned (holds g) ids ls →
    let out:=E.alternative g p v x ids
    extension g out.1 ∧ holds out.1 out.2 (fun s=>L s ∨ ∃tail,concatenate ls tail ∧ s=(v,x)::tail)
  finish : ∀g ids ls,extension E.initial g → Aligned (holds g) ids ls →
    let out:=E.finish g ids
    holds out.1 out.2 (concatenate ls)
end StableMSR.Recovery.TightLanguage


namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

section
variable {S V:Type} {E:Algebra S V} (M:Semantics E)

theorem table_keep {g t:S} {a:Table V} {b:Table (Lang Letter)} (ext:M.extension g t)
    (h:TablesAgree (M.holds g) a b) : TablesAgree (M.holds t) a b :=
  h.weaken (fun _ _ pair=>⟨pair.1,M.keep ext pair.2⟩)

theorem collect_correct (d:Instance) (c:List ℕ) (a:Assignment)
    (g:S) (start:M.extension E.initial g) (tab:Table V) (abs:Table (Lang Letter))
    (tables:TablesAgree (M.holds g) tab abs) :
    let out:=collect E d tab c a g
    M.extension g out.1 ∧ M.holds out.1 out.2 (collect wordAlgebra d abs c a ()).2 := by
  let J:=fun (p:S×V) (q:Unit×Lang Letter)=>M.extension g p.1 ∧ M.holds p.1 p.2 q.2
  change J (collect E d tab c a g) (collect wordAlgebra d abs c a ())
  unfold collect
  apply fold_agrees J
  · intro p q v acc
    apply fold_agrees J
    · intro z y x inv
      obtain ⟨later,old⟩:=inv
      have resident:=table_keep M later tables
      let b:=(v,x)::a
      have choices:Matched (Aligned (M.holds z.1)) (refs d tab c v b) (refs d abs c v b):=
        queries_agree (parts d (c.erase v)) _ _ (fun t=>lookup_agrees resident _ _)
      by_cases ok:localOK d b=true
      · cases l:refs d tab c v b <;> cases r:refs d abs c v b <;> rw [l,r] at choices <;> cases choices
        · dsimp only [b] at l r
          simpa only [J,offer,show localOK d ((v,x)::a)=true from ok,if_true,l,r] using And.intro later old
        · rename_i is ls children
          have ext:=M.alt z.1 z.2 y.2 v x is ls (M.trans start later) old children
          change M.extension g (offer E d tab c a v x z).1 ∧ M.holds _ _ (offer wordAlgebra d abs c a v x y).2
          simp only [offer,show localOK d ((v,x)::a)=true from ok,if_true]
          dsimp only [b] at l r
          rw [l,r]
          exact ⟨M.trans later ext.1,ext.2⟩
      · have no:localOK d ((v,x)::a)≠true:=ok
        simpa only [J,offer,if_neg no] using And.intro later old
    · exact acc
  · exact ⟨M.refl _,M.fail g start⟩

theorem build_correct (d:Instance) (w:ℕ) :
    let out:=build E d w
    M.extension E.initial out.1 ∧ TablesAgree (M.holds out.1) out.2 (build wordAlgebra d w).2 := by
  let J:=fun (p:S×Table V) (q:Unit×Table (Lang Letter))=>M.extension E.initial p.1 ∧ TablesAgree (M.holds p.1) p.2 q.2
  change J (build E d w) (build wordAlgebra d w)
  unfold build
  apply fold_agrees J
  · intro p q k acc
    apply fold_agrees J
    · intro p q s acc
      apply fold_agrees J
      · intro p q c acc
        unfold visit
        split
        · apply fold_agrees J
          · intro p q a acc
            obtain ⟨extend,tables⟩:=acc
            have row:=collect_correct M d c a p.1 extend p.2 q.2 tables
            have later:=table_keep M row.1 tables
            exact ⟨M.trans extend row.1,Aligned.cons ⟨rfl,row.2⟩ later⟩
          · exact acc
        · exact acc
      · exact acc
    · exact acc
  · exact ⟨M.refl _,Aligned.nil⟩

theorem scan_correct (d:Instance) (w:ℕ) : M.holds (scan E d w).1 (scan E d w).2 (traces d w) := by
  obtain ⟨extended,agree⟩:=build_correct M d w
  let a:=build E d w
  let b:=build wordAlgebra d w
  let cs:=parts d (vertices d)
  let f:=fun c=>lookup a.2 c []
  let g:=fun c=>lookup b.2 c []
  have sync:Matched (Aligned (M.holds a.1)) (cs.mapM f) (cs.mapM g):=
    queries_agree cs f g (fun c=>lookup_agrees agree c [])
  unfold traces scan;dsimp only
  cases l:cs.mapM f <;> cases r:cs.mapM g <;> rw [l,r] at sync <;> cases sync
  · exact M.fail _ extended
  · rename_i is ls rep
    exact M.finish _ is ls extended rep
end
end StableMSR.Recovery.TightLanguage


namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

def opAt (g:Gates) (p:ℕ) := g[p]?.getD .stop

/-- Circuit semantics over an arbitrary alphabet of emitted symbols. All edges
used by a derivation go strictly backwards in the gate array. -/
inductive Parse {A:Type} (emit:List ℕ→List A) (g:Gates) : ℕ→List A→Prop where
  | lit {p pts} : p<g.size → opAt g p=.atom pts → Parse emit g p (emit pts)
  | both {p i j L R} : p<g.size → opAt g p=.both i j → i<p → j<p →
      Parse emit g i L → Parse emit g j R → Parse emit g p (L++R)
  | left {p i j L} : p<g.size → opAt g p=.either i j → i<p → Parse emit g i L → Parse emit g p L
  | right {p i j L} : p<g.size → opAt g p=.either i j → j<p → Parse emit g j L → Parse emit g p L

def oneGate {A:Type} (emit:List ℕ→List A) (L:ℕ→Lang A) (p:ℕ) (s:List A) : Gate→Prop
  | .stop=>False
  | .atom m=>s=emit m
  | .both a b=>a<p ∧ b<p ∧ product (L a) (L b) s
  | .either a b=>(a<p ∧ L a s) ∨ (b<p ∧ L b s)

theorem parse_iff {A:Type} (emit:List ℕ→List A) (g:Gates) (p:ℕ) (s:List A) :
    Parse emit g p s ↔ p<g.size ∧ oneGate emit (Parse emit g) p s (opAt g p) := by
  constructor
  · intro h
    cases h with
    | lit sz eq=>exact ⟨sz,by rw [eq];rfl⟩
    | both sz eq ha hb hl hr=>exact ⟨sz,by rw [eq]; exact ⟨ha,hb,_,_,hl,hr,rfl⟩⟩
    | left sz eq ha hl=>exact ⟨sz,by rw [eq];exact Or.inl ⟨ha,hl⟩⟩
    | right sz eq hb hr=>exact ⟨sz,by rw [eq];exact Or.inr ⟨hb,hr⟩⟩
  · rintro ⟨sz,h⟩
    cases eq : opAt g p with
    | stop=>rw [eq] at h;exact False.elim h
    | atom m=>rw [eq] at h;change s=_ at h;subst s;exact .lit sz eq
    | both a b=>
      rw [eq] at h
      obtain ⟨ha,hb,u,v,hu,hv,rfl⟩:=h
      exact .both sz eq ha hb hu hv
    | either a b=>
      rw [eq] at h
      rcases h with ⟨ha,h⟩|⟨hb,h⟩
      · exact .left sz eq ha h
      · exact .right sz eq hb h

def Prefix (g h:Gates) := g.size≤h.size ∧ ∀i<g.size,opAt h i=opAt g i
theorem Prefix.refl (g:Gates) : Prefix g g := ⟨Nat.le_refl _,fun _ _=>rfl⟩
theorem Prefix.trans {g h t:Gates} (a:Prefix g h) (b:Prefix h t) : Prefix g t :=
  ⟨Nat.le_trans a.1 b.1, fun i hi=>(b.2 i (Nat.lt_of_lt_of_le hi a.1)).trans (a.2 i hi)⟩
theorem Prefix.push (g:Gates) (op:Gate) : Prefix g (g.push op) := by
  refine ⟨by simp,?_⟩
  intro i hi
  simp [opAt,Array.getElem?_push,hi,Nat.ne_of_lt hi]

theorem prefix_words {A:Type} (emit:List ℕ→List A) {g h:Gates} (ext:Prefix g h)
    (p:ℕ) (hp:p<g.size) (s:List A) : Parse emit h p s ↔ Parse emit g p s := by
  induction p using Nat.strongRecOn generalizing s with
  | ind p ih=>
    have hs:=ext.1
    rw [parse_iff emit h,parse_iff emit g,ext.2 p hp]
    simp only [hp,show p<h.size by omega,true_and]
    cases eq:opAt g p with
    | stop=>rfl
    | atom m=>rfl
    | both a b=>
      constructor
      · rintro ⟨ha,hb,u,v,hu,hv,hs⟩
        exact ⟨ha,hb,u,v,(ih a ha (by omega) u).1 hu,(ih b hb (by omega) v).1 hv,hs⟩
      · rintro ⟨ha,hb,u,v,hu,hv,hs⟩
        exact ⟨ha,hb,u,v,(ih a ha (by omega) u).2 hu,(ih b hb (by omega) v).2 hv,hs⟩
    | either a b=>
      constructor
      · rintro (⟨ha,hu⟩|⟨hb,hv⟩)
        · exact Or.inl ⟨ha,(ih a ha (by omega) s).1 hu⟩
        · exact Or.inr ⟨hb,(ih b hb (by omega) s).1 hv⟩
      · rintro (⟨ha,hu⟩|⟨hb,hv⟩)
        · exact Or.inl ⟨ha,(ih a ha (by omega) s).2 hu⟩
        · exact Or.inr ⟨hb,(ih b hb (by omega) s).2 hv⟩

def Holds {A:Type} (emit:List ℕ→List A) (g:Gates) (p:ℕ) (L:Lang A) :=
  p<g.size ∧ Parse emit g p=L

theorem Holds.keep {A:Type} {emit:List ℕ→List A} {g h:Gates} {p:ℕ} {L:Lang A}
    (ext:Prefix g h) (hL:Holds emit g p L) : Holds emit h p L := by
  refine ⟨Nat.lt_of_lt_of_le hL.1 ext.1,?_⟩
  apply Eq.trans _ hL.2;funext s;exact propext (prefix_words emit ext p hL.1 s)

theorem last_op (g:Gates) (op:Gate) : opAt (g.push op) g.size=op := by simp [opAt]

theorem push_lit {A:Type} (emit:List ℕ→List A) (g:Gates) (m:List ℕ) :
    Holds emit (g.push (.atom m)) g.size (fun s=>s=emit m) := by
  refine ⟨by simp,?_⟩;funext s;apply propext
  rw [parse_iff,last_op];simp [oneGate]

theorem push_both {A:Type} {emit:List ℕ→List A} {g:Gates} {p q:ℕ} {P Q:Lang A}
    (l:Holds emit g p P) (r:Holds emit g q Q) :
    Holds emit (g.push (.both p q)) g.size (product P Q) := by
  have ll:=Holds.keep (Prefix.push g (.both p q)) l
  have rr:=Holds.keep (Prefix.push g (.both p q)) r
  refine ⟨by simp,?_⟩;funext s;apply propext
  rw [parse_iff,last_op];simp [oneGate,l.1,r.1,ll.2,rr.2]

theorem push_either {A:Type} {emit:List ℕ→List A} {g:Gates} {p q:ℕ} {P Q:Lang A}
    (l:Holds emit g p P) (r:Holds emit g q Q) :
    Holds emit (g.push (.either p q)) g.size (fun s=>P s ∨ Q s) := by
  have ll:=Holds.keep (Prefix.push g (.either p q)) l
  have rr:=Holds.keep (Prefix.push g (.either p q)) r
  refine ⟨by simp,?_⟩;funext s;apply propext
  rw [parse_iff,last_op];simp [oneGate,l.1,r.1,ll.2,rr.2]

abbrev startGates : Gates := #[.atom [],.stop]
theorem initial_empty {A:Type} (emit:List ℕ→List A) (unit:emit []=[]) :
    Holds emit startGates 0 emptyWord := by
  refine ⟨by decide,?_⟩;funext s;apply propext
  rw [parse_iff,show opAt startGates 0=.atom [] from rfl]
  simp [show 0<startGates.size by decide,oneGate,unit,emptyWord]
theorem initial_fail {A:Type} (emit:List ℕ→List A) : Holds emit startGates 1 (fun _=>False) := by
  refine ⟨by decide,?_⟩;funext s;apply propext
  rw [parse_iff,show opAt startGates 1=.stop from rfl];simp [oneGate]
end StableMSR.Recovery.TightLanguage


namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

def singleton {A:Type} (x:List A) : Lang A := (·=x)

theorem product_unit_left {A:Type} (L:Lang A) : product emptyWord L=L := by
  funext s;apply propext
  constructor
  · rintro ⟨a,b,rfl,h,rfl⟩;simpa using h
  · intro h;exact ⟨[],s,rfl,h,rfl⟩

theorem product_unit_right {A:Type} (L:Lang A) : product L emptyWord=L := by
  funext s;apply propext
  constructor
  · rintro ⟨a,b,h,rfl,rfl⟩;simpa using h
  · intro h;exact ⟨s,[],h,rfl,(List.append_nil s).symm⟩

theorem product_assoc {A:Type} (P Q R:Lang A) : product (product P Q) R=product P (product Q R) := by
  funext s;apply propext
  constructor
  · rintro ⟨_,c,⟨a,b,h,k,rfl⟩,l,rfl⟩
    exact ⟨a,b++c,h,⟨b,c,k,l,rfl⟩,List.append_assoc ..⟩
  · rintro ⟨a,_,h,⟨b,c,k,l,rfl⟩,rfl⟩
    exact ⟨a++b,c,⟨a,b,h,k,rfl⟩,l,(List.append_assoc ..).symm⟩

theorem product_singleton {A:Type} (x y:List A) :
    product (singleton x) (singleton y)=singleton (x++y) := by
  funext s;apply propext
  constructor
  · rintro ⟨_,_,rfl,rfl,h⟩;exact h
  · rintro rfl;exact ⟨x,y,rfl,rfl,rfl⟩

theorem fold_product {A:Type} (ls:List (Lang A)) (P Q:Lang A) :
    ls.foldl product (product P Q)=product P (ls.foldl product Q) := by
  induction ls generalizing Q with
  | nil=>rfl
  | cons x xs ih=>simp only [List.foldl_cons,product_assoc,ih]

theorem fold_concatenate {A:Type} (ls:List (Lang A)) (P:Lang A) :
    ls.foldl product P=product P (concatenate ls) := by
  simpa only [product_unit_right,concatenate] using fold_product ls P emptyWord

def imageWord {A B:Type} (f:A→List B) (P:Lang A) : Lang B :=
  fun t=>∃s,P s ∧ t=s.flatMap f

theorem image_empty {A B:Type} (f:A→List B) : imageWord f emptyWord=emptyWord := by
  funext t;apply propext
  constructor
  · rintro ⟨_,rfl,h⟩;exact h
  · rintro rfl;exact ⟨[],rfl,rfl⟩

theorem image_fail {A B:Type} (f:A→List B) : imageWord f (fun _=>False)=(fun _=>False) := by
  funext t;apply propext;constructor
  · rintro ⟨_,h,_⟩;exact h
  · exact False.elim

theorem image_product {A B:Type} (f:A→List B) (P Q:Lang A) :
    imageWord f (product P Q)=product (imageWord f P) (imageWord f Q) := by
  funext t;apply propext
  constructor
  · rintro ⟨_,⟨a,b,ha,hb,rfl⟩,rfl⟩
    exact ⟨a.flatMap f,b.flatMap f,⟨a,ha,rfl⟩,⟨b,hb,rfl⟩,List.flatMap_append ..⟩
  · rintro ⟨_,_,⟨a,ha,rfl⟩,⟨b,hb,rfl⟩,rfl⟩
    exact ⟨a++b,⟨a,b,ha,hb,rfl⟩,(List.flatMap_append ..).symm⟩

theorem image_fold {A B:Type} (f:A→List B) (ls:List (Lang A)) (P:Lang A) :
    imageWord f (ls.foldl product P)=(ls.map (imageWord f)).foldl product (imageWord f P) := by
  induction ls generalizing P with
  | nil=>rfl
  | cons x xs ih=>simp only [List.foldl_cons,List.map_cons,ih,image_product]

theorem image_concatenate {A B:Type} (f:A→List B) (ls:List (Lang A)) :
    imageWord f (concatenate ls)=concatenate (ls.map (imageWord f)) := by
  unfold concatenate;rw [image_fold,image_empty]

theorem image_alternative {A B:Type} (f:A→List B) (P Q:Lang A) (a:A) :
    imageWord f (fun s=>P s ∨ ∃tail,Q tail ∧ s=a::tail)=
      fun s=>imageWord f P s ∨ product (singleton (f a)) (imageWord f Q) s := by
  funext t;apply propext
  constructor
  · rintro ⟨s,(h|⟨tail,h,rfl⟩),rfl⟩
    · exact Or.inl ⟨s,h,rfl⟩
    · exact Or.inr ⟨f a,tail.flatMap f,rfl,⟨tail,h,rfl⟩,rfl⟩
  · rintro (⟨s,h,rfl⟩|⟨_,_,rfl,⟨tail,h,rfl⟩,rfl⟩)
    · exact ⟨s,Or.inl h,rfl⟩
    · exact ⟨a::tail,Or.inr ⟨tail,h,rfl⟩,rfl⟩

theorem Aligned.map_right {A B C:Type} {f:B→C} {R:A→C→Prop} {xs:List A} {ys:List B}
    (h:Aligned (fun x y=>R x (f y)) xs ys) : Aligned R xs (ys.map f) := by
  induction h with
  | nil=>exact .nil
  | cons a _ ih=>exact .cons a ih
end StableMSR.Recovery.TightLanguage


namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

def litStep (z:Gates×ℕ) (m:List ℕ) : Gates×ℕ :=
  let g:=z.1.push (.atom m)
  (g.push (.both z.2 z.1.size),g.size)

def sonStep (z:Gates×ℕ) (p:ℕ) : Gates×ℕ := (z.1.push (.both z.2 p),z.1.size)

theorem body_fold (g:Gates) (ms:List (List ℕ)) (ids:List ℕ) :
    body g ms ids=ids.foldl sonStep (ms.foldl litStep (g,0)) := by
  let ml:=fun (m:List ℕ) (z:Gates×ℕ)=>(pure (.yield (litStep z m)):Id (ForInStep (Gates×ℕ)))
  let sl:=fun (p:ℕ) (z:Gates×ℕ)=>(pure (.yield (sonStep z p)):Id (ForInStep (Gates×ℕ)))
  change (forIn ids (forIn ms (g,0) ml:Id (Gates×ℕ)) sl:Id (Gates×ℕ))=_
  rw [loop_eq ms _ ml litStep (fun _ _=>rfl),loop_eq ids _ sl sonStep (fun _ _=>rfl)]

theorem lit_step_correct {A:Type} (emit:List ℕ→List A) (z:Gates×ℕ) (m:List ℕ) (s:List A)
    (h:Holds emit z.1 z.2 (singleton s)) :
    Prefix z.1 (litStep z m).1 ∧ Holds emit (litStep z m).1 (litStep z m).2 (singleton (s++emit m)) := by
  have a:=Prefix.push z.1 (.atom m)
  have b:=Prefix.push (z.1.push (.atom m)) (.both z.2 z.1.size)
  have correct:=push_both (Holds.keep a h) (push_lit emit z.1 m)
  rw [←product_singleton];exact ⟨a.trans b,correct⟩

theorem masks_correct {A:Type} (emit:List ℕ→List A) (ms:List (List ℕ)) (z:Gates×ℕ) (s:List A)
    (h:Holds emit z.1 z.2 (singleton s)) :
    let out:=ms.foldl litStep z
    Prefix z.1 out.1 ∧ Holds emit out.1 out.2 (singleton (s++ms.flatMap emit)) := by
  induction ms generalizing z s with
  | nil=>simpa using And.intro (Prefix.refl _) h
  | cons m ms ih=>
    obtain ⟨later,k⟩:=lit_step_correct emit z m s h
    obtain ⟨final,correct⟩:=ih (litStep z m) (s++emit m) k
    exact ⟨later.trans final,by simpa only [List.foldl_cons,List.flatMap_cons,List.append_assoc] using correct⟩

theorem sons_correct {A:Type} (emit:List ℕ→List A) {g:Gates} {ids:List ℕ} {ls:List (Lang A)}
    (aligned:Aligned (Holds emit g) ids ls) (z:Gates×ℕ) (P:Lang A) (resident:Prefix g z.1)
    (h:Holds emit z.1 z.2 P) :
    let out:=ids.foldl sonStep z
    Prefix z.1 out.1 ∧ Holds emit out.1 out.2 (ls.foldl product P) := by
  induction aligned generalizing z P with
  | nil=>exact ⟨Prefix.refl _,h⟩
  | @cons p Q ids ls child _ ih=>
    have extend:=Prefix.push z.1 (.both z.2 p)
    have correct:=push_both h (Holds.keep resident child)
    obtain ⟨last,k⟩:=ih (sonStep z p) (product P Q) (resident.trans extend) correct
    exact ⟨extend.trans last,k⟩

theorem body_correct {A:Type} (emit:List ℕ→List A) (unit:emit []=[]) {g:Gates} (init:Prefix startGates g)
    (ms:List (List ℕ)) {ids:List ℕ} {ls:List (Lang A)} (children:Aligned (Holds emit g) ids ls) :
    let out:=body g ms ids
    Prefix g out.1 ∧ Holds emit out.1 out.2 (product (singleton (ms.flatMap emit)) (concatenate ls)) := by
  rw [body_fold]
  have zero:=Holds.keep init (initial_empty emit unit)
  obtain ⟨e,h⟩:=masks_correct emit ms (g,0) [] zero
  obtain ⟨f,k⟩:=sons_correct emit children (ms.foldl litStep (g,0)) (singleton (ms.flatMap emit)) e h
  rw [fold_concatenate] at k
  exact ⟨e.trans f,k⟩
end StableMSR.Recovery.TightLanguage


namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

/-- Emit the ordered mask word owned by a single pivot/label choice. -/
def contribution {A:Type} (d:Instance) (emit:List ℕ→List A) (letter:Letter) :=
  (d.owned letter.1 letter.2).flatMap emit

def gateSemantics {A:Type} (d:Instance) (emit:List ℕ→List A) (unit:emit []=[]) :
    Semantics (gateAlgebra d) where
  extension:=Prefix
  refl:=Prefix.refl
  trans:=Prefix.trans
  holds:=fun g p L=>Holds emit g p (imageWord (contribution d emit) L)
  keep:=fun e h=>Holds.keep e h
  fail:=by
    intro g ext
    rw [image_fail];exact Holds.keep ext (initial_fail emit)
  alt:=by
    intro g p L v x ids ls init prev cs
    have aligned:Aligned (Holds emit g) ids (ls.map (imageWord (contribution d emit))):=cs.map_right
    obtain ⟨grows,correct⟩:=body_correct emit unit init (d.owned v x) aligned
    let out:=body g (d.owned v x) ids
    have alt:=push_either (Holds.keep grows prev) correct
    refine ⟨grows.trans (Prefix.push out.1 (.either p out.2)),?_⟩
    rw [image_alternative,image_concatenate];exact alt
  finish:=by
    intro g ids ls init cs
    have aligned:Aligned (Holds emit g) ids (ls.map (imageWord (contribution d emit))):=cs.map_right
    have correct:=(body_correct emit unit init [] aligned).2
    change Holds emit _ _ (product emptyWord _) at correct
    rw [product_unit_left] at correct
    rw [image_concatenate];exact correct

/-- The actual imperative compiler recognizes the homomorphic image of the
ordered pivot/code words. The returned address is valid, including on failure. -/
theorem compiled_traces {A:Type} (d:Instance) (w:ℕ) (emit:List ℕ→List A) (unit:emit []=[]) :
    let out:=compileRegion d w
    out.2<out.1.size ∧ ∀s,Parse emit out.1 out.2 s ↔
      ∃t,traces d w t ∧ s=t.flatMap (contribution d emit) := by
  rw [source_eq,normalized]
  have h:=scan_correct (gateSemantics d emit unit) d w
  change Holds emit _ _ (imageWord (contribution d emit) (traces d w)) at h
  exact ⟨h.1,fun s=>iff_of_eq (congrFun h.2 s)⟩
end StableMSR.Recovery.TightLanguage


namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

open scoped Classical

noncomputable def maskWord (n:ℕ) (m:List ℕ) := WindowMasks.emit (Finset.univ.filter (fun i:Point n=>m.contains i.val))

theorem mask_unit (n:ℕ) : maskWord n []=[] := by simp [maskWord,WindowMasks.emit]

theorem parse_physical {n:ℕ} {g:Gates} {p:ℕ} {L:List (Cluster n)} :
    Parse (maskWord n) g p L ↔ Language n g p L := by
  constructor
  · intro h
    induction h with
    | lit hp eq=>exact .lit hp eq
    | both hp eq ha hb _ _ a b=>exact .both hp eq ha hb a b
    | left hp eq ha _ a=>exact .left hp eq ha a
    | right hp eq hb _ b=>exact .right hp eq hb b
  · intro h
    induction h with
    | lit hp eq=>exact .lit hp eq
    | both hp eq ha hb _ _ a b=>exact .both hp eq ha hb a b
    | left hp eq ha _ a=>exact .left hp eq ha a
    | right hp eq hb _ b=>exact .right hp eq hb b

theorem exact_physical_words (n:ℕ) (d:Instance) (w:ℕ) :
    let out:=compileRegion d w
    out.2<out.1.size ∧ ∀s,Language n out.1 out.2 s ↔
      ∃t,traces d w t ∧ s=t.flatMap (contribution d (maskWord n)) := by
  obtain ⟨bound,h⟩:=compiled_traces d w (maskWord n) (mask_unit n)
  exact ⟨bound,fun s=>parse_physical.symm.trans (h s)⟩
end StableMSR.Recovery.TightLanguage


open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.SingleCircuit
theorem solution (n : ℕ) (d : Instance) (w : ℕ) :
    let out := compileRegion d w
    let emit := fun m : List ℕ => WindowMasks.emit (Finset.univ.filter (fun i : Point n => m.contains i.val))
    let output := fun t : ℕ × ℕ => (d.owned t.1 t.2).flatMap emit
    out.2 < out.1.size ∧ ∀ s, Language n out.1 out.2 s ↔
      ∃ t, TightLanguage.traces d w t ∧ s = t.flatMap output := TightLanguage.exact_physical_words n d w
