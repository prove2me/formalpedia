-- Prove2me | solution 2 for StableMSR.Recovery.SingleCodes.regional_circuit_language_correct
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T20:36:45.138285+00:00
-- url     : https://prove2.me/submissions/381919e2-9452-4775-a1d1-2167955369c2

import Definitions.Def_StableMSR_DenseGlobalAssembly
import Theorems.Thm_StableMSR_Recovery_SingleSearch_deletion_piece_geometry
import Theorems.Thm_StableMSR_Recovery_SingleSearch_singleton_labelled_component_language

/-!
# Exact language of the executable regional clustering circuit

For any window region, real scale, label budget and separator width, the root
address returned by `SingleCodes.regionalCircuit` is valid. Every recognized word
lists distinct blocks and projects to a generated partition. Every generated
partition occurs as the support of a recognized word.

The theorem `TightLanguage.live_regional_circuit_correct` instantiates this
result at a mission region slot. Its graph assumptions are proved in this file.
The imported graph results describe deletion components and assignments of the
singleton search. They are established Prove2Me theorems.
-/

/-! ## The chronological table and its ordered pivot words -/

namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
def value (a : Assignment) (v : ℕ) := ((a.find? fun z=>z.1==v).map Prod.snd).getD 0
def restricted (s : List ℕ) (a : Assignment) : Assignment := s.map fun v=>(v,value a v)
def assignments (d : Instance) : List ℕ→List Assignment
  | []=>[[]]
  | v::vs=>(d.menu v).flatMap fun x=>(assignments d vs).map ((v,x)::·)
def cuts : List ℕ→ℕ→List (List ℕ)
  | [],_=>[[]]
  | _::_,0=>[[]]
  | v::vs,w+1=>cuts vs (w+1) ++ (cuts vs w).map (v::·)
def vertices (d : Instance) := (List.range d.n).filter d.active
def pieceAt (d : Instance) (allowed : List ℕ) (v : ℕ) :=
  (List.range d.n).foldl (fun seen _=>allowed.filter fun u=>seen.contains u || seen.any (fun z=>d.edge z u)) [v]
def parts (d : Instance) (allowed : List ℕ) := allowed.filterMap fun v=>
  let c:=pieceAt d allowed v
  if c.head?==some v then some c else none
def rimOf (d : Instance) (c : List ℕ) := (vertices d).filter fun v=>
  !c.contains v && c.any (fun u=>d.edge u v)
def localOK (d : Instance) (a : Assignment) := a.all fun z=>a.all fun t=>
  !(d.edge z.1 t.1) || d.test z.1 t.1 z.2 t.2

/-- The numeric dynamic program stores one value per ordered tight key. -/
abbrev Table (V:Type) := List (Key×V)

def lookup {V:Type} (tab:Table V) (c:List ℕ) (a:Assignment) : Option V :=
  (tab.find? (fun z=>z.1==(c,a))).map Prod.snd

structure Algebra (S V:Type) where
  initial : S
  fail : V
  alternative : S→V→ℕ→ℕ→List V→S×V
  finish : S→List V→S×V

def keysFor (d:Instance) (vs:List ℕ) (s:List ℕ) :=
  parts d (vs.filter (fun v=> !s.contains v))

def refs {V:Type} (d:Instance) (tab:Table V) (c:List ℕ) (v:ℕ) (a:Assignment) :=
  (parts d (c.erase v)).mapM (m:=Option) (fun t=>lookup tab t (restricted (rimOf d t) a))

def offer {S V:Type} (E:Algebra S V) (d:Instance) (tab:Table V) (c:List ℕ) (a:Assignment)
    (v x:ℕ) (b:S×V) : S×V :=
  let row:=(v,x)::a
  if localOK d row then
    match refs d tab c v row with
    | some ids=>E.alternative b.1 b.2 v x ids
    | none=>b
  else b

def collect {S V:Type} (E:Algebra S V) (d:Instance) (tab:Table V) (c:List ℕ) (a:Assignment) (g:S) :=
  c.foldl (fun b v=>(d.menu v).foldl (fun st x=>offer E d tab c a v x st) b) (g,E.fail)

def install {S V:Type} (E:Algebra S V) (d:Instance) (c:List ℕ) (a:Assignment) (st:S×Table V) :=
  let b:=collect E d st.2 c a st.1
  (b.1,((c,a),b.2)::st.2)

def visit {S V:Type} (E:Algebra S V) (d:Instance) (k:ℕ) (s c:List ℕ) (st:S×Table V) :=
  if c.length==k+1 && rimOf d c==s then
    (assignments d s).foldl (fun p a=>install E d c a p) st
  else st

def build {S V:Type} (E:Algebra S V) (d:Instance) (w:ℕ) : S×Table V :=
  let vs:=vertices d
  let ss:=cuts vs (min w d.n)
  (List.range d.n).foldl (fun p k=>ss.foldl (fun z s=>(keysFor d vs s).foldl
    (fun t c=>visit E d k s c t) z) p) (E.initial,[])

def scan {S V:Type} (E:Algebra S V) (d:Instance) (w:ℕ) : S×V :=
  let st:=build E d w
  match (parts d (vertices d)).mapM (m:=Option) (fun c=>lookup st.2 c []) with
  | some ids=>E.finish st.1 ids
  | none=>(st.1,E.fail)

abbrev Letter := ℕ×ℕ
abbrev Lang (A:Type) := List A→Prop
def emptyWord {A:Type} : Lang A := (·=[])
def product {A:Type} (p q:Lang A) : Lang A := fun s=>∃a b,p a ∧ q b ∧ s=a++b
def concatenate {A:Type} (ps:List (Lang A)) : Lang A := ps.foldl product emptyWord

def wordAlgebra : Algebra Unit (Lang Letter) where
  initial:=()
  fail:=fun _=>False
  alternative:=fun _ prior v x children=>((),fun s=>prior s ∨ ∃tail,concatenate children tail ∧ s=(v,x)::tail)
  finish:=fun _ children=>((),concatenate children)

/-- Ordered pivot/label words accepted by the tight component table. A missing
child invalidates an alternative. A missing root invalidates the whole word. -/
def traces (d:Instance) (w:ℕ) : Lang Letter := (scan wordAlgebra d w).2
end StableMSR.Recovery.TightLanguage

/-! ## Normalization of the imperative gate and table loops -/

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

/-! ## Simulation of table traversal, including failed lookups -/

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

/-! ## Earlier gate languages survive every append -/

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

/-! ## Images of word languages and the semantics of a production body -/

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

/-! ## Decoding local ball words and projecting uniquely owned blocks -/

namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

open SingleSearch WindowCuts Havens PartialDecompositions
open scoped Classical

section
variable {V X Y:Type} [Fintype V] [DecidableEq V] [DecidableEq X] [DecidableEq Y]

def relabel (f:V→X→Y) (z:V×X) : V×Y := (z.1,f z.1 z.2)

theorem relabel_labels (f:V→X→Y) (C:Finset V) (a:V→X) :
    (labels C a).image (relabel f)=labels C (fun v=>f v (a v)) := by
  classical
  simp [labels,Finset.image_image,relabel,Function.comp_def]

theorem run_empty_iff (G:SimpleGraph V) (D:V→Finset X) (T:V→V→X→X→Prop) (w m:ℕ)
    {C:Finset V} (hc:IsFlap G ∅ C) (a:V→X) (O:Finset (V×X)) :
    run G D T w m ∅ C a O ↔ one G w m ∅ C ∧ ∃f,okay G D T C f ∧ O=labels C f := by
  rw [singleton_labelled_component_language G D T w m ∅ C hc a O]
  simp

/-- Quotienting the local labels by a vertex-dependent decoder preserves and
reflects the root search, including simultaneous outputs of all components. -/
theorem root_image_iff (G:SimpleGraph V) (D:V→Finset X) (E:V→Finset Y)
    (f:V→X→Y) (onto:∀v y,y∈E v ↔ ∃c∈D v,f v c=y)
    (T:V→V→Y→Y→Prop) (w:ℕ) (a:V→X) (b:V→Y) (Q:Finset (V×Y)) :
    let U:=fun v z c k=>T v z (f v c) (f z k)
    root G E T w b Q ↔ ∃O,root G D U w a O ∧ O.image (relabel f)=Q := by
  classical
  let U:=fun v z c k=>T v z (f v c) (f z k)
  let K:=PartialDecompositions.components G ∅
  let m:=Fintype.card V
  have component (C:Finset V) (hc:C∈K) (o:Finset (V×Y)) :
      run G E T w m ∅ C b o ↔
        ∃s,run G D U w m ∅ C a s ∧ s.image (relabel f)=o := by
    have flap:=mem_components.mp hc
    rw [run_empty_iff G E T w m flap]
    constructor
    · rintro ⟨shape,p,valid,rfl⟩
      have pick (v:V) : ∃c:X,v∈C → c∈D v ∧ f v c=p v := by
        by_cases h:v∈C
        · obtain ⟨c,hc,eq⟩:=(onto v (p v)).1 (valid.1 v h)
          exact ⟨c,fun _=>⟨hc,eq⟩⟩
        · exact ⟨a v,fun hv=>False.elim (h hv)⟩
      choose code ok using pick
      have good:okay G D U C code:=by
        refine ⟨fun v hv=>(ok v hv).1,?_⟩
        intro v hv z hz edge
        change T v z (f v (code v)) (f z (code z))
        rw [(ok v hv).2,(ok z hz).2];exact valid.2 v hv z hz edge
      refine ⟨labels C code,(run_empty_iff G D U w m flap ..).2 ⟨shape,code,good,rfl⟩,?_⟩
      rw [relabel_labels];apply Finset.image_congr
      intro v hv;exact congrArg (Prod.mk v) (ok v hv).2
    · rintro ⟨s,hs,rfl⟩
      obtain ⟨shape,p,valid,rfl⟩:=(run_empty_iff G D U w m flap ..).1 hs
      refine ⟨shape,fun v=>f v (p v),⟨fun v hv=>(onto v _).2 ⟨p v,valid.1 v hv,rfl⟩,valid.2⟩,relabel_labels ..⟩
  constructor
  · rintro ⟨out,good,rfl⟩
    have chooseOut (C:Finset V) : ∃s:Finset (V×X),C∈K →
        run G D U w m ∅ C a s ∧ s.image (relabel f)=out C := by
      by_cases hc:C∈K
      · obtain ⟨s,hs⟩:=(component C hc _).1 (good C hc)
        exact ⟨s,fun _=>hs⟩
      · exact ⟨∅,fun h=>False.elim (hc h)⟩
    choose codes chosen using chooseOut
    refine ⟨K.biUnion codes,⟨codes,fun C hc=>(chosen C hc).1,rfl⟩,?_⟩
    rw [Finset.biUnion_image];exact Finset.biUnion_congr rfl (fun C hc=>(chosen C hc).2)
  · rintro ⟨O,⟨out,good,rfl⟩,rfl⟩
    refine ⟨fun C=>(out C).image (relabel f),fun C hc=>(component C hc _).2 ⟨out C,good C hc,rfl⟩,?_⟩
    exact Finset.biUnion_image
end
end StableMSR.Recovery.TightLanguage

namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

open OracleQueries WindowCSP RegionalSeeds CartesianBallRows FewBallRows SingleCodes SingleWindows
open scoped Classical

theorem mem_decode_menu (x:World) (W:Cluster x.n) (h:ℕ) (Q:Partition x.n) :
    Q∈traceMenu x h W ↔ ∃c∈SingleCodes.menu x W h,SingleCodes.decode x W h c=Q := by
  classical
  have unpair (g u:ℕ) (hg:g<h+1) :
      encode h g u%(h+1)=g ∧ encode h g u/(h+1)=u := by
    unfold encode
    constructor
    · simp [Nat.add_mod,Nat.mod_eq_of_lt hg]
    · rw [Nat.mul_comm u _,Nat.mul_add_div (by omega),Nat.div_eq_of_lt hg,Nat.add_zero]
  constructor
  · intro hQ
    obtain ⟨hit,ok⟩:=Finset.mem_filter.mp hQ
    obtain ⟨⟨g,u⟩,gu,eq⟩:=Finset.mem_image.mp hit
    obtain ⟨hg,hu⟩:=Finset.mem_product.mp gu
    obtain ⟨hm,hd⟩:=unpair g u (Finset.mem_range.mp hg)
    have dec:decode x W h (encode h g u)=Q:=by simpa only [decode,hm,hd] using eq
    refine ⟨encode h g u,List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨g,List.mem_range.mpr (Finset.mem_range.mp hg),
      List.mem_map.mpr ⟨u,List.mem_range.mpr (Finset.mem_range.mp hu),rfl⟩⟩,?_⟩,dec⟩
    simp only [dec,decide_eq_true_eq];exact ok
  · rintro ⟨c,hc,rfl⟩
    obtain ⟨hw,yes⟩:=List.mem_filter.mp hc
    obtain ⟨g,hg,vc⟩:=List.mem_flatMap.mp hw
    obtain ⟨u,hu,rfl⟩:=List.mem_map.mp vc
    have z:=unpair g u (List.mem_range.mp hg)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨(g,u),Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (List.mem_range.mp hg),Finset.mem_range.mpr (List.mem_range.mp hu)⟩,?_⟩,
      of_decide_eq_true yes⟩
    simp only [decode,z.1,z.2]

theorem mask_of_block {n:ℕ} (C:Cluster n) :
    Finset.univ.filter (fun i:Point n=>(C.toList.map Fin.val).contains i.val)=C := by
  classical
  ext i;simp only [Finset.mem_filter,Finset.mem_univ,true_and,List.contains_iff_mem,List.mem_map,Finset.mem_toList]
  exact ⟨fun ⟨a,h,e⟩=>(Fin.ext e) ▸ h,fun h=>⟨i,h,rfl⟩⟩

theorem block_output {n:ℕ} (A:Point n→Point n) (v:Point n) (P:Partition n) :
    (blockList (owned A v P)).flatMap (maskWord n)=(owned A v P).toList := by
  classical
  let U:=owned A v P
  change (U.toList.map _).flatMap (maskWord n)=U.toList
  rw [List.flatMap_map]
  have eq (C:Cluster n) (hc:C∈U.toList) : maskWord n (C.toList.map Fin.val)=[C] := by
    have hold:=(Finset.mem_filter.mp (Finset.mem_toList.mp hc)).2
    obtain ⟨j,hj,_⟩:=hold
    unfold maskWord;rw [mask_of_block];simp [WindowMasks.emit,show C.Nonempty from ⟨j,hj⟩]
  rw [List.flatMap_congr (g:=fun C=>[C]) (fun C hc=>eq C hc)]
  simp

theorem same_owner {n:ℕ} {A:Point n→Point n} {v z:Point n} {P Q:Partition n} {C:Cluster n}
    (h:C∈owned A v P) (j:C∈owned A z Q) : v=z := by
  obtain ⟨i,hi,hv,le⟩:=(Finset.mem_filter.mp h).2
  obtain ⟨b,hb,hz,le'⟩:=(Finset.mem_filter.mp j).2
  have eq:=le_antisymm (le b hb) (le' i hi)
  exact hv.symm.trans ((congrArg A eq).trans hz)

theorem union_flat {A B:Type} [DecidableEq A] [DecidableEq B] (ls:List A) (f:A→List B) :
    (ls.flatMap f).toFinset=ls.toFinset.biUnion (fun j=>(f j).toFinset) := by
  classical
  ext b;simp

theorem lookup_fin {n:ℕ} {A:Type} (f:Point n→A) (i:Point n) (a:A) :
    SingleCodes.lookup f i.val a=f i := by simp [SingleCodes.lookup,i.isLt]
end StableMSR.Recovery.TightLanguage

namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

open OracleQueries WindowCSP RegionalSeeds SingleCodes SingleWindows SingleSearch
open scoped Classical

/-- Soundness and completeness of the numeric *graph* search, with addresses
erased. All gate semantics and partition decoding are proved below this interface. -/
def NumericGraphLaw : Prop := ∀ {V:Type} [Fintype V] [DecidableEq V]
    (d:Instance) (ix:V→Fin d.n) (_:Function.Injective ix) (G:SimpleGraph V)
    (_:∀i:Fin d.n,d.active i.val=true ↔ ∃v,ix v=i)
    (_:∀v z,d.edge (ix v).val (ix z).val=true ↔ G.Adj v z) (w:ℕ),
    let dom:=fun v=>(d.menu (ix v).val).toFinset
    let test:=fun v z a b=>d.test (ix v).val (ix z).val a b=true
    let tag:=fun t:V×ℕ=>((ix t.1).val,t.2)
    let accepts:=SingleSearch.root G dom test w (fun _=>0)
    (∀t,traces d w t → ∃l:List (V×ℕ),l.map tag=t ∧ (l.map Prod.fst).Nodup ∧ accepts l.toFinset) ∧
    ∀O,accepts O → ∃l:List (V×ℕ),traces d w (l.map tag) ∧ l.toFinset=O

theorem regional_language_from_graph (graph:NumericGraphLaw) (x:World) (W:Cluster x.n) (R:ℝ) (h w:ℕ) :
    let c:=regionalCircuit x W R h w
    let gen:=generates x W R h w
    c.2<c.1.size ∧ (∀L,Language x.n c.1 c.2 L → L.Nodup ∧ gen L.toFinset) ∧
      ∀Q,gen Q → ∃L,Language x.n c.1 c.2 L ∧ L.toFinset=Q := by
  classical
  let d:=instanceOf x W R h
  let V:=Vertex x W R
  let G:=Supplement.interactionGraph x.dist R W
  let ix:V→Fin d.n:=fun v=>v.val
  let D:=fun v:V=>(d.menu (ix v).val).toFinset
  let dec:=fun (v:V) c=>decode x (window x.dist W R v) h c
  let T:=constraint x W R
  let tc:=fun (v z:V) (c k:ℕ)=>d.test (ix v).val (ix z).val c k=true
  let tag:=fun z:V×ℕ=>((ix z.1).val,z.2)
  let raw:=SingleSearch.root G D tc w (fun _=>0)
  let read:=relabel dec
  let projected:=project x W R
  have inj:Function.Injective ix:=fun _ _ e=>Subtype.ext e
  have active (i:Fin d.n) : d.active i.val=true ↔ ∃v,ix v=i := by
    have hi : i.val < x.n := i.isLt
    simp only [d,instanceOf,SingleCodes.lookup,hi,dif_pos,decide_eq_true_eq]
    constructor
    · intro member;exact ⟨⟨i,member⟩,rfl⟩
    · rintro ⟨v,rfl⟩;exact v.property
  have edge (v z:V) : d.edge (ix v).val (ix z).val=true ↔ G.Adj v z := by
    simp only [d,ix,instanceOf,lookup_fin,decide_eq_true_eq]
    change _ ↔ v.val≠z.val ∧ v.val∈_ ∧ z.val∈_ ∧ _
    simp only [v.property,z.property,true_and];rfl
  have onto (v:V) (P:Partition x.n) : P∈domains x W R h v ↔ ∃c∈D v,dec v c=P := by
    simpa only [D,d,ix,instanceOf,lookup_fin,List.mem_toFinset,dec,domains] using mem_decode_menu x (window x.dist W R v) h P
  have tests:tc=(fun v z c k=>T v z (dec v c) (dec z k)) := by
    funext v z c k;apply propext
    simp only [tc,d,ix,instanceOf,lookup_fin,decide_eq_true_eq,T,constraint,dec]
  have root_eq (Q:Finset (V×Partition x.n)) :
      SingleSearch.root G (domains x W R h) T w (fun _=>∅) Q ↔ ∃O,raw O ∧ O.image read=Q := by
    change _ ↔ ∃O,SingleSearch.root G D tc w (fun _=>0) O ∧ _
    rw [tests];exact root_image_iff G D _ dec onto T w (fun _=>0) (fun _=>∅) Q
  let F:=contribution d (maskWord x.n)
  let blocks:=fun z:V×ℕ=>owned (anchor x.dist W R) z.1.val (dec z.1 z.2)
  let out:=fun z:V×ℕ=>F (tag z)
  have each (z:V×ℕ) : out z=(blocks z).toList := by
    simpa only [out,F,contribution,tag,ix,d,instanceOf,lookup_fin,blocks,dec] using block_output (anchor x.dist W R) z.1.val (dec z.1 z.2) 
  have projection (l:List (V×ℕ)) : (l.flatMap out).toFinset=projected (l.toFinset.image read) := by
    rw [union_flat]
    change _=(l.toFinset.image read).biUnion _
    rw [Finset.image_biUnion]
    apply Finset.biUnion_congr rfl
    intro z hz;rw [each];simp [blocks,read,relabel]
  have unique (l:List (V×ℕ)) (hn:(l.map Prod.fst).Nodup) : (l.flatMap out).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun z _=>by rw [each];exact Finset.nodup_toList _,?_⟩
    rw [List.nodup_iff_pairwise_ne] at hn
    apply (List.pairwise_map.mp hn).imp
    intro i j distinct C hi hj
    rw [each] at hi hj
    exact distinct (Subtype.ext (same_owner (Finset.mem_toList.mp hi) (Finset.mem_toList.mp hj)))
  have physical:=exact_physical_words x.n d w
  obtain ⟨sound,complete⟩:=graph d ix inj G active edge w
  refine ⟨physical.1,?_,?_⟩
  · intro L hL
    obtain ⟨t,ht,rfl⟩:=(physical.2 L).1 hL
    obtain ⟨l,rfl,hn,ok⟩:=sound t ht
    change ((l.map tag).flatMap F).Nodup ∧ generates x W R h w ((l.map tag).flatMap F).toFinset
    rw [List.flatMap_map]
    exact ⟨unique l hn,l.toFinset.image read,(root_eq _).2 ⟨l.toFinset,ok,rfl⟩,(projection l).symm⟩
  · rintro Q ⟨P,hP,rfl⟩
    obtain ⟨O,hO,rfl⟩:=(root_eq P).1 hP
    obtain ⟨l,hl,rfl⟩:=complete O hO
    refine ⟨l.flatMap out,(physical.2 _).2 ⟨l.map tag,hl,?_⟩,projection l⟩
    simp only [List.flatMap_map];rfl
end StableMSR.Recovery.TightLanguage

/-! ## Numeric floods, ordered indices and canonical graph components -/

namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch
open SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
def grow (S A : Finset V) := A ∪ Finset.univ.filter (fun y=>y∉S ∧ ∃x∈A,G.Adj x y)
def flood (S : Finset V) (a : V) : ℕ→Finset V
  | 0=>{a} | i+1=>grow G S (flood S a i)
theorem mem_grow {S A : Finset V} {y : V} :
    y∈grow G S A ↔ y∈A ∨ y∉S ∧ ∃x∈A,G.Adj x y := by simp [grow]
theorem flood_step (S : Finset V) (a : V) (i : ℕ) : flood G S a i⊆flood G S a (i+1) :=
  fun _ h=>(mem_grow G).2 (Or.inl h)
theorem flood_fixed (S : Finset V) (a : V) :
    grow G S (flood G S a (Fintype.card V))=flood G S a (Fintype.card V) := by
  have aux (m : ℕ) : flood G S a (m+1)=flood G S a m ∨ m+1≤(flood G S a m).card := by
    induction m with
    | zero=>right;simp [flood]
    | succ i ih=>
      rcases ih with h|h
      · left;exact congrArg (grow G S) h
      · by_cases eq:flood G S a (i+1)=flood G S a i
        · left;exact congrArg (grow G S) eq
        · right
          have lt:=Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨flood_step G S a i,Ne.symm eq⟩)
          omega
  rcases aux (Fintype.card V) with h|h
  · exact h
  · have:=Finset.card_le_univ (flood G S a (Fintype.card V));omega
theorem flood_seed (S : Finset V) (a : V) (i : ℕ) : a∈flood G S a i := by
  induction i with
  | zero=>simp [flood]
  | succ i ih=>exact flood_step G S a i ih
theorem flood_flap (S : Finset V) (a : V) (ha:a∉S) : IsFlap G S (flood G S a (Fintype.card V)) := by
  let A:=flood G S a
  have reach (i : ℕ) (v : V) (hv:v∈A i) : ∃p:G.Walk a v, ∀z∈p.support,z∈A i := by
    induction i generalizing v with
    | zero=>
      have e:v=a:=by simpa [A,flood] using hv
      subst v
      refine ⟨.nil,?_⟩
      intro z hz
      have e:z=a:=by simpa using hz
      simpa [e] using hv
    | succ i ih=>
      rcases (mem_grow G).1 hv with h|⟨_,x,hx,adj⟩
      · obtain ⟨p,hp⟩:=ih v h
        exact ⟨p,fun z hz=>flood_step G S a i (hp z hz)⟩
      · obtain ⟨p,hp⟩:=ih x hx
        refine ⟨p.concat adj,?_⟩
        intro z hz
        rw [SimpleGraph.Walk.support_concat,List.mem_append] at hz
        rcases hz with hz|hz
        · exact flood_step G S a i (hp z hz)
        · have e:z=v:=by simpa using hz
          simpa [e] using hv
  have avoid (i : ℕ) (v : V) (hv:v∈A i) : v∉S := by
    induction i with
    | zero=>have e:v=a:=by simpa [A,flood] using hv
            simpa [e] using ha
    | succ i ih=>rcases (mem_grow G).1 hv with h|h
                 · exact ih h
                 · exact h.1
  refine ⟨⟨⟨a,flood_seed G S a _⟩,?_⟩,Finset.disjoint_left.mpr (fun _ hv hw=>avoid _ _ hw hv),?_⟩
  · intro x hx y hy
    obtain ⟨p,hp⟩:=reach _ x hx
    obtain ⟨q,hq⟩:=reach _ y hy
    refine ⟨p.reverse.append q,?_⟩
    intro z hz
    rcases (SimpleGraph.Walk.mem_support_append_iff p.reverse q).mp hz with hz|hz
    · exact hp _ (by simpa [SimpleGraph.Walk.support_reverse] using hz)
    · exact hq _ hz
  · intro x hx y hxy hy
    rw [←flood_fixed G S a]
    exact (mem_grow G).2 (Or.inr ⟨hy,x,hx,hxy⟩)

theorem flood_stable (S:Finset V) (v:V) (m:ℕ) (hm:Fintype.card V ≤ m) :
    flood G S v m=flood G S v (Fintype.card V) := by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hm
  clear hm
  induction k with
  | zero=>rfl
  | succ k ih=>change grow G S (flood G S v (Fintype.card V+k))=_;rw [ih,flood_fixed]

end StableMSR.Recovery.TightLanguage.Graph

namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

structure Presentation {V:Type} (d:Instance) (G:SimpleGraph V) where
  ix : V→Fin d.n
  injective : Function.Injective ix
  active : ∀i:Fin d.n,d.active i.val=true ↔ ∃v,ix v=i
  edges : ∀v z,d.edge (ix v).val (ix z).val=true ↔ G.Adj v z

namespace Presentation
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V} (P:Presentation d G)
def idx (v:V) := (P.ix v).val
theorem idx_injective : Function.Injective P.idx := fun _ _ h=>P.injective (Fin.ext h)
noncomputable def code (C:Finset V) : List ℕ := (C.image P.idx).sort (·≤·)
theorem code_sorted (C:Finset V) : (P.code C).Pairwise (·<·) := (C.image P.idx).sortedLT_sort.pairwise
theorem code_nodup (C:Finset V) : (P.code C).Nodup := (code_sorted P C).imp Nat.ne_of_lt
theorem mem_code {C:Finset V} {i:ℕ} : i∈P.code C ↔ ∃v∈C,P.idx v=i := by simp [code]
theorem idx_mem {C:Finset V} {v:V} : P.idx v∈P.code C ↔ v∈C := by
  rw [mem_code];exact ⟨fun ⟨y,h,e⟩=>P.idx_injective e ▸ h,fun h=>⟨v,h,rfl⟩⟩
theorem code_injective : Function.Injective P.code := by
  intro C E h;ext v;rw [←P.idx_mem, h,P.idx_mem]
theorem code_length (C:Finset V) : (P.code C).length=C.card := by
  simp [code,Finset.card_image_of_injective _ P.idx_injective]
theorem code_single (v:V) : P.code {v}=[P.idx v] := by simp [code]
theorem code_empty : P.code ∅=[] := by simp [code]

theorem code_eq {C:Finset V} {s:List ℕ} (hs:s.Pairwise (·<·))
    (covers:∀i∈s,∃v,P.idx v=i) (mem:∀v,P.idx v∈s ↔ v∈C) : s=P.code C := by
  apply hs.eq_of_mem_iff (P.code_sorted C)
  intro i;constructor
  · intro hi;obtain ⟨v,rfl⟩:=covers i hi;exact P.idx_mem.mpr ((mem v).1 hi)
  · intro hi;obtain ⟨v,hv,rfl⟩:=P.mem_code.mp hi;exact (mem v).2 hv

theorem all_code : vertices d=P.code Finset.univ := by
  apply P.code_eq (List.pairwise_lt_range.filter _)
  · intro i h
    obtain ⟨hi,ok⟩:=List.mem_filter.mp h
    obtain ⟨v,hv⟩:=(P.active ⟨i,List.mem_range.mp hi⟩).1 ok
    exact ⟨v,congrArg Fin.val hv⟩
  · intro v;simp [vertices,idx,(P.ix v).isLt,(P.active (P.ix v)).2 ⟨v,rfl⟩]

theorem code_filter (C:Finset V) (p:ℕ→Bool) :
    (P.code C).filter p=P.code (C.filter (fun v=>p (P.idx v))) := by
  apply P.code_eq ((P.code_sorted C).filter p)
  · intro i hi;obtain ⟨v,_,e⟩:=P.mem_code.mp (List.mem_filter.mp hi).1;exact ⟨v,e⟩
  · intro v;simp [P.idx_mem]

theorem code_erase (C:Finset V) (v:V) : (P.code C).erase (P.idx v)=P.code (C.erase v) := by
  apply P.code_eq ((P.code_sorted C).erase _)
  · intro i hi;obtain ⟨v,_,e⟩:=P.mem_code.mp (List.mem_of_mem_erase hi);exact ⟨v,e⟩
  · intro u
    rw [(P.code_nodup C).mem_erase_iff,Finset.mem_erase,P.idx_mem]
    simp only [P.idx_injective.ne_iff]

theorem code_comp (S:Finset V) :
    (vertices d).filter (fun i=> !(P.code S).contains i)=P.code Sᶜ := by
  rw [P.all_code,P.code_filter];congr 1;ext v;simp [P.idx_mem]

theorem rim_code (C:Finset V) : rimOf d (P.code C)=P.code (boundary G C) := by
  unfold rimOf;rw [P.all_code,P.code_filter];congr 1;ext v
  have outside : (P.code C).contains (P.idx v)=false ↔ v∉C:=by simp [P.idx_mem]
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Bool.and_eq_true,Bool.not_eq_true',outside,
    P.idx_mem,List.any_eq_true,mem_boundary]
  constructor
  · rintro ⟨outside,i,hi,he⟩
    obtain ⟨u,hu,rfl⟩:=P.mem_code.mp hi
    exact ⟨outside,u,hu,(P.edges u v).1 he⟩
  · rintro ⟨outside,u,hu,he⟩
    exact ⟨outside,P.idx u,P.idx_mem.mpr hu,(P.edges u v).2 he⟩
end Presentation
end StableMSR.Recovery.TightLanguage.Graph

namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

namespace Presentation
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V}
variable (P:Presentation d G)

theorem one_round [DecidableRel G.Adj] (U A:Finset V) (inc:A⊆U) :
    (P.code U).filter (fun i=>(P.code A).contains i || (P.code A).any (fun j=>d.edge j i)) =
      P.code (grow G Uᶜ A) := by
  rw [P.code_filter];congr 1;ext v
  have near : (∃j∈P.code A,d.edge j (P.idx v)=true) ↔ ∃u∈A,G.Adj u v := by
    constructor
    · rintro ⟨j,hj,e⟩;obtain ⟨u,hu,rfl⟩:=P.mem_code.mp hj
      exact ⟨u,hu,(P.edges u v).1 e⟩
    · rintro ⟨u,hu,e⟩;exact ⟨P.idx u,P.idx_mem.mpr hu,(P.edges u v).2 e⟩
  simp only [Finset.mem_filter,Bool.or_eq_true,List.contains_iff_mem,P.idx_mem,List.any_eq_true,near,
    mem_grow,Finset.mem_compl,not_not]
  constructor
  · rintro ⟨hu,(ha|nb)⟩
    · exact Or.inl ha
    · exact Or.inr ⟨hu,nb⟩
  · rintro (ha|⟨hu,nb⟩)
    · exact ⟨inc ha,Or.inl ha⟩
    · exact ⟨hu,Or.inr nb⟩

theorem rounds_eq [DecidableRel G.Adj] (U:Finset V) (v:V) (hv:v∈U) (m:ℕ) :
    (List.range m).foldl (fun seen _=>(P.code U).filter
      (fun i=>seen.contains i || seen.any (fun j=>d.edge j i))) [P.idx v] =
      P.code (flood G Uᶜ v m) := by
  have inside (k:ℕ) : flood G Uᶜ v k⊆U := by
    induction k with
    | zero=>simpa [flood] using hv
    | succ k ih=>
      intro x hx
      rcases (mem_grow G).mp hx with h|⟨h,_⟩
      · exact ih h
      · simpa using h
  induction m with
  | zero=>exact (P.code_single v).symm
  | succ m ih=>
    rw [List.range_succ,List.foldl_append,ih]
    exact P.one_round U _ (inside m)

theorem piece_geometry [DecidableRel G.Adj] (U:Finset V) (v:V) (hv:v∈U) :
    let C:=flood G Uᶜ v (Fintype.card V)
    pieceAt d (P.code U) (P.idx v)=P.code C ∧ IsFlap G Uᶜ C ∧ v∈C := by
  have size:Fintype.card V≤d.n:=by simpa using Fintype.card_le_of_injective P.ix P.injective
  refine ⟨?_,flood_flap G _ _ (by simpa using hv),flood_seed G _ _ _⟩
  unfold pieceAt
  rw [P.rounds_eq U v hv d.n,flood_stable G _ _ _ size]

theorem flap_unique {S C E:Finset V} (c:IsFlap G S C) (e:IsFlap G S E) {v:V}
    (hc:v∈C) (he:v∈E) : C=E := by
  have incl {C E:Finset V} (c:IsFlap G S C) (e:IsFlap G S E) (uc:v∈C) (ue:v∈E) : C⊆E := by
    intro z hz
    obtain ⟨p,hp⟩:=c.connected.2 v uc z hz
    have path {u t:V} (p:G.Walk u t) (start:u∈E) (safe:∀z∈p.support,z∉S) : t∈E := by
      induction p with
      | nil=>exact start
      | @cons a b d ab p ih=>
        apply ih (e.closed a start b ab (safe b (by simp [p.start_mem_support])))
        intro z h;exact safe z (by simp [h])
    exact path p ue (fun z h bad=>Finset.disjoint_left.mp c.avoids bad (hp _ h))
  exact Finset.Subset.antisymm (incl c e hc he) (incl e c he hc)

theorem piece_of_flap [DecidableRel G.Adj] {U C:Finset V} (hc:IsFlap G Uᶜ C) (v:V) (hv:v∈C) :
    pieceAt d (P.code U) (P.idx v)=P.code C := by
  have hu:v∈U:=by by_contra h;exact Finset.disjoint_left.mp hc.avoids (Finset.mem_compl.mpr h) hv
  obtain ⟨eq,flap,hit⟩:=P.piece_geometry U v hu
  exact eq.trans (congrArg P.code (flap_unique flap hc hit hv))

theorem parts_spec (vs s:List ℕ) : s∈parts d vs ↔
    ∃i∈vs,pieceAt d vs i=s ∧ s.head?=some i := by
  simp only [parts,List.mem_filterMap]
  constructor
  · rintro ⟨i,hi,h⟩
    split at h
    · rename_i eq;obtain rfl:=Option.some.inj h;exact ⟨i,hi,rfl,beq_iff_eq.mp eq⟩
    · contradiction
  · rintro ⟨i,hi,rfl,head⟩
    exact ⟨i,hi,by simp [head]⟩

theorem parts_distinct (vs:List ℕ) (hn:vs.Nodup) : (parts d vs).Nodup := by
  unfold parts
  apply List.Nodup.filterMap _ hn
  intro i j s hi hj
  have head (a:ℕ) (h:s∈(if (pieceAt d vs a).head? == some a then some (pieceAt d vs a) else none)) :
      s.head?=some a := by
    split at h
    · rename_i eq;have es:pieceAt d vs a=s:=Option.some.inj h;rw [←es];exact beq_iff_eq.mp eq
    · contradiction
  exact Option.some.inj ((head i hi).symm.trans (head j hj))

theorem parts_geometry (U:Finset V) (s:List ℕ) :
    s∈parts d (P.code U) ↔ ∃C:Finset V,IsFlap G Uᶜ C ∧ P.code C=s := by
  classical
  rw [parts_spec];constructor
  · rintro ⟨i,hi,rfl,_⟩
    obtain ⟨v,hv,rfl⟩:=P.mem_code.mp hi
    obtain ⟨eq,hc,_⟩:=P.piece_geometry U v hv
    exact ⟨_,hc,eq.symm⟩
  · rintro ⟨C,hc,rfl⟩
    obtain ⟨v,hv⟩:=hc.connected.1
    let vs:=P.code C
    have hn:vs≠[]:=List.ne_nil_of_mem (P.idx_mem.mpr hv)
    let i:=vs.head hn
    have head:vs.head?=some i:=List.head?_eq_some_head hn
    obtain ⟨z,hz,ez⟩:=P.mem_code.mp (List.mem_of_head? head)
    have hu:z∈U:=by by_contra h;exact Finset.disjoint_left.mp hc.avoids (Finset.mem_compl.mpr h) hz
    exact ⟨P.idx z,P.idx_mem.mpr hu,P.piece_of_flap hc z hz,ez ▸ head⟩
end Presentation
end StableMSR.Recovery.TightLanguage.Graph

namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

namespace Presentation
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V}
variable (P:Presentation d G)

def fromCode (s:List ℕ) : Finset V := Finset.univ.filter (fun v=>s.contains (P.idx v))
theorem from_code (C:Finset V) : P.fromCode (P.code C)=C := by
  ext v;simp [fromCode,P.idx_mem]

noncomputable def pieces (U:Finset V) := (parts d (P.code U)).map P.fromCode

theorem restore_piece {U:Finset V} {s:List ℕ} (hs:s∈parts d (P.code U)) : P.code (P.fromCode s)=s := by
  obtain ⟨C,_,rfl⟩:=(P.parts_geometry U s).1 hs
  rw [P.from_code]

theorem pieces_code (U:Finset V) : (P.pieces U).map P.code=parts d (P.code U) := by
  unfold pieces;rw [List.map_map]
  exact List.map_congr_left (g:=id) (fun s hs=>P.restore_piece hs) |>.trans (List.map_id ..)

theorem mem_piece {U C:Finset V} : C∈P.pieces U ↔ IsFlap G Uᶜ C := by
  unfold pieces;constructor
  · intro h;obtain ⟨s,hs,rfl⟩:=List.mem_map.mp h
    obtain ⟨C,hc,rfl⟩:=(P.parts_geometry U _).1 hs
    simpa only [P.from_code] using hc
  · intro hc
    exact List.mem_map.mpr ⟨P.code C,(P.parts_geometry U _).2 ⟨C,hc,rfl⟩,P.from_code C⟩

theorem pieces_nodup (U:Finset V) : (P.pieces U).Nodup := by
  apply List.Nodup.of_map (f:=P.code)
  rw [P.pieces_code];exact parts_distinct _ (P.code_nodup U)

theorem root_pieces : (P.pieces Finset.univ).toFinset=PartialDecompositions.components G ∅ := by
  ext C;simp [P.mem_piece,PartialDecompositions.mem_components]

theorem piece_rim_empty {C:Finset V} (hc:C∈P.pieces Finset.univ) : boundary G C=∅ := by
  have flap:IsFlap G ∅ C:=by simpa using P.mem_piece.mp hc
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨out,v,hv,edge⟩:=mem_boundary.mp hz
  exact out (flap.closed v hv z edge (Finset.notMem_empty _))

theorem different_pieces {U C E:Finset V} (hc:C∈P.pieces U) (he:E∈P.pieces U) (ne:C≠E) : Disjoint C E :=
  Finset.disjoint_left.mpr (fun _ h k=>ne (flap_unique (P.mem_piece.mp hc) (P.mem_piece.mp he) h k))

theorem children_geometry {S C:Finset V} (flap:IsFlap G S C) (v:V) (hv:v∈C) (E:Finset V) :
    E∈P.pieces (C.erase v) ↔ E∈children G (insert v S) C := by
  rw [P.mem_piece,mem_children]
  constructor
  · intro e
    have inc:E⊆C.erase v:=by
      intro z hz;by_contra bad;exact Finset.disjoint_left.mp e.avoids (Finset.mem_compl.mpr bad) hz
    refine ⟨⟨e.connected,Finset.disjoint_left.mpr ?_,?_⟩,fun _ h=>Finset.mem_of_mem_erase (inc h)⟩
    · intro z hz he
      rcases Finset.mem_insert.mp hz with rfl|hs
      · exact (Finset.mem_erase.mp (inc he)).1 rfl
      · exact Finset.disjoint_left.mp flap.avoids hs (Finset.mem_of_mem_erase (inc he))
    · intro z hz u zu hu
      have uS:u∉S:=fun hs=>hu (Finset.mem_insert_of_mem hs)
      have uC:=flap.closed z (Finset.mem_of_mem_erase (inc hz)) u zu uS
      exact e.closed z hz u zu (by simpa using Finset.mem_erase.mpr ⟨fun eq=>hu (Finset.mem_insert.mpr (Or.inl eq)),uC⟩)
  · rintro ⟨e,inc⟩
    refine ⟨e.connected,Finset.disjoint_left.mpr ?_,?_⟩
    · intro z hz he
      exact Finset.mem_compl.mp hz (Finset.mem_erase.mpr ⟨fun eq=>Finset.disjoint_left.mp e.avoids (Finset.mem_insert.mpr (Or.inl eq)) he,inc he⟩)
    · intro z hz u zu hu
      have hU:u∈C.erase v:=by simpa using hu
      apply e.closed z hz u zu
      intro t;rcases Finset.mem_insert.mp t with rfl|t
      · exact (Finset.mem_erase.mp hU).1 rfl
      · exact Finset.disjoint_left.mp flap.avoids t (Finset.mem_of_mem_erase hU)

theorem parts_children {S C:Finset V} (flap:IsFlap G S C) (v:V) (hv:v∈C) :
    (P.pieces (C.erase v)).map P.code=parts d ((P.code C).erase (P.idx v)) ∧
      (P.pieces (C.erase v)).toFinset=children G (insert v S) C := by
  refine ⟨by rw [P.code_erase,P.pieces_code],?_⟩;ext E;simp [P.children_geometry flap v hv]
end Presentation
end StableMSR.Recovery.TightLanguage.Graph

/-! ## The root language as an ordered product of component languages -/

namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

def available {A:Type} (o:Option (Lang A)) : Lang A := o.getD (fun _=>False)
def joined {A I:Type} (f:I→Option (Lang A)) (xs:List I) : Lang A :=
  match xs.mapM (m:=Option) f with
  | some ls=>concatenate ls
  | none=>fun _=>False

theorem concatenate_cons {A:Type} (L:Lang A) (ls:List (Lang A)) :
    concatenate (L::ls)=product L (concatenate ls) := by
  unfold concatenate;rw [List.foldl_cons,product_unit_left,fold_concatenate];rfl

theorem joined_cons {I A:Type} (f:I→Option (Lang A)) (i:I) (xs:List I) (s:List A) :
    joined f (i::xs) s ↔ product (available (f i)) (joined f xs) s := by
  cases ei:f i <;> cases es:xs.mapM (m:=Option) f <;>
    simp [joined,available,List.mapM_cons,ei,es,concatenate_cons,product]

theorem joined_iff {I A:Type} [DecidableEq I] (f:I→Option (Lang A)) (xs:List I) (hn:xs.Nodup) (s:List A) :
    joined f xs s ↔ ∃out:I→List A,(∀i∈xs,available (f i) (out i)) ∧ s=xs.flatMap out := by
  induction xs generalizing s with
  | nil=>
    change s=[] ↔ _
    exact ⟨fun h=>⟨fun _=>[],by simp,h⟩,fun ⟨_,_,h⟩=>h⟩
  | cons i xs ih=>
    have fresh:=(List.nodup_cons.mp hn).1
    have nodup:=(List.nodup_cons.mp hn).2
    rw [joined_cons];constructor
    · rintro ⟨x,t,hx,ht,rfl⟩
      obtain ⟨g,ok,rfl⟩:=(ih nodup t).1 ht
      let out:=Function.update g i x
      have rest (k:I) (hk:k∈xs) : out k=g k:=Function.update_of_ne (by rintro rfl;exact fresh hk) .. 
      refine ⟨out,?_,?_⟩
      · intro k hk;rcases List.mem_cons.mp hk with rfl|hk
        · simpa [out] using hx
        · rw [rest k hk];exact ok k hk
      · rw [List.flatMap_cons,show out i=x from Function.update_self ..]
        congr 1;exact List.flatMap_congr (fun k hk=>(rest k hk).symm)
    · rintro ⟨out,ok,rfl⟩
      exact ⟨out i,xs.flatMap out,ok i (by simp),(ih nodup _).2 ⟨out,fun k hk=>ok k (by simp [hk]),rfl⟩,rfl⟩

namespace Presentation
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V} (P:Presentation d G)
noncomputable def rootEntry (w:ℕ) (C:Finset V) := lookup (build wordAlgebra d w).2 (P.code C) []

theorem root_split (w:ℕ) (s:List Letter) : traces d w s ↔ ∃f:Finset V→List Letter,
    (∀C∈P.pieces Finset.univ,available (P.rootEntry w C) (f C)) ∧ s=(P.pieces Finset.univ).flatMap f := by
  rw [←joined_iff (P.rootEntry w) (P.pieces Finset.univ) (P.pieces_nodup _)]
  unfold traces scan joined rootEntry
  dsimp only
  rw [P.all_code,←P.pieces_code,List.mapM_map];simp only [Function.comp_def]
  cases h:(P.pieces Finset.univ).mapM (m:=Option) (fun C=>lookup (build wordAlgebra d w).2 (P.code C) []) <;> rfl
end Presentation
end StableMSR.Recovery.TightLanguage.Graph

namespace StableMSR.Recovery.TightLanguage.Graph
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery
def RowLaw : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V] (d : SingleCircuit.Instance) (ix : V → Fin d.n)
    (_inj : Function.Injective ix) (G : SimpleGraph V)
    (_active : ∀ i : Fin d.n, d.active i.val = true ↔ ∃ v, ix v = i)
    (_edges : ∀ v z, d.edge (ix v).val (ix z).val = true ↔ G.Adj v z)
    (w m : ℕ) (C : Finset V) (a : ℕ → ℕ)
    (_flap : Havens.IsFlap G (DecompositionSearch.boundary G C) C)
    (_space : (DecompositionSearch.boundary G C).card ≤ w) (_depth : C.card ≤ m)
    (_valid : ∀ v ∈ DecompositionSearch.boundary G C, a (ix v).val ∈ d.menu (ix v).val),
    let code := fun K : Finset V => (K.image (fun v => (ix v).val)).sort (· ≤ ·)
    let S := DecompositionSearch.boundary G C
    let key := (code S).map (fun j => (j,a j))
    let table := (TightLanguage.build TightLanguage.wordAlgebra d w).2
    let accepts := (TightLanguage.lookup table (code C) key).getD (fun _ => False)
    let dom := fun v => (d.menu (ix v).val).toFinset
    let test := fun v z c k => d.test (ix v).val (ix z).val c k = true
    let tag := fun t : V × ℕ => ((ix t.1).val,t.2)
    let runs := SingleSearch.run G dom test w m S C (fun v => a (ix v).val)
    (∀ t, accepts t → ∃ l : List (V × ℕ), l.map tag = t ∧ (l.map Prod.fst).Nodup ∧
      (l.map Prod.fst).toFinset = C ∧ runs l.toFinset) ∧
    ∀ O, runs O → ∃ l : List (V × ℕ), accepts (l.map tag) ∧ l.toFinset = O
end StableMSR.Recovery.TightLanguage.Graph

namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

theorem graph_from_rows (rows:RowLaw) : NumericGraphLaw := by
  intro V _ _ d ix inj G active edges w
  classical
  let P:Presentation d G:=⟨ix,inj,active,edges⟩
  let ks:=P.pieces Finset.univ
  let tag:=fun j:V×ℕ=>((ix j.1).val,j.2)
  let D:=fun v=>(d.menu (ix v).val).toFinset
  let test:=fun v z c k=>d.test (ix v).val (ix z).val c k=true
  let ok:=fun C=>SingleSearch.run G D test w (Fintype.card V) ∅ C (fun _=>0)
  let accept:=fun C=>available (P.rootEntry w C)
  have cm (C:Finset V) : C∈ks ↔ C∈PartialDecompositions.components G ∅ := by
    rw [←P.root_pieces];exact List.mem_toFinset.symm
  have entry (C:Finset V) (hc:C∈ks) :
      (∀t,accept C t → ∃l:List (V×ℕ),l.map tag=t ∧ (l.map Prod.fst).Nodup ∧
        (l.map Prod.fst).toFinset=C ∧ ok C l.toFinset) ∧
      ∀O,ok C O → ∃l:List (V×ℕ),accept C (l.map tag) ∧ l.toFinset=O := by
    have empty:=P.piece_rim_empty hc
    have flap:IsFlap G (boundary G C) C:=empty ▸ PartialDecompositions.mem_components.mp ((cm C).1 hc)
    have fit:(boundary G C).card≤w:=by simp [empty]
    have valid:∀v∈boundary G C,(0:ℕ)∈d.menu (ix v).val:=by simp [empty]
    have h:=rows d ix inj G active edges w (Fintype.card V) C (fun _=>0) flap fit (Finset.card_le_univ C) valid
    dsimp only at h
    simp only [empty,Finset.image_empty,Finset.sort_empty,List.map_nil] at h
    exact h
  constructor
  · intro t ht
    obtain ⟨f,hf,rfl⟩:=(P.root_split w t).1 ht
    have choices (C:Finset V) (hc:C∈ks) := (entry C hc).1 _ (hf C hc)
    let l (C:Finset V) := if hc:C∈ks then (choices C hc).choose else []
    have hl (C:Finset V) (hc:C∈ks) : (l C).map tag=f C ∧ ((l C).map Prod.fst).Nodup ∧
        ((l C).map Prod.fst).toFinset=C ∧ ok C (l C).toFinset := by
      simpa only [l,dif_pos hc] using (choices C hc).choose_spec
    refine ⟨ks.flatMap l,?_,?_,?_⟩
    · rw [List.map_flatMap];exact List.flatMap_congr (fun C h=>(hl C h).1)
    · rw [List.map_flatMap];apply List.nodup_flatMap.mpr
      refine ⟨fun C hc=>(hl C hc).2.1,?_⟩
      apply (P.pieces_nodup Finset.univ).pairwise_of_forall_ne
      intro C hc E he diff v hC hE
      have inside (C:Finset V) (hc:C∈ks) (h:v∈(l C).map Prod.fst) : v∈C := by
        rw [←(hl C hc).2.2.1];exact List.mem_toFinset.mpr h
      exact Finset.disjoint_left.mp (P.different_pieces hc he diff) (inside C hc hC) (inside E he hE)
    · refine ⟨fun C=>(l C).toFinset,fun C hc=>(hl C ((cm C).2 hc)).2.2.2,?_⟩
      rw [union_flat,show ks.toFinset=_ from P.root_pieces]
  · rintro O ⟨out,good,rfl⟩
    have choices (C:Finset V) (hc:C∈ks) := (entry C hc).2 (out C) (good C ((cm C).1 hc))
    let l (C:Finset V) := if hc:C∈ks then (choices C hc).choose else []
    have hl (C:Finset V) (hc:C∈ks) : accept C ((l C).map tag) ∧ (l C).toFinset=out C := by
      simpa only [l,dif_pos hc] using (choices C hc).choose_spec
    refine ⟨ks.flatMap l,(P.root_split w _).2 ⟨fun C=>(l C).map tag,fun C hc=>(hl C hc).1,?_⟩,?_⟩
    · rw [List.map_flatMap]
    · rw [union_flat,show ks.toFinset=_ from P.root_pieces]
      exact Finset.biUnion_congr rfl (fun C hc=>(hl C ((cm C).2 hc)).2)
end StableMSR.Recovery.TightLanguage.Graph

/-! ## The actual cut, boundary-assignment and size-layer enumeration -/

namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

theorem cuts_exact (vs:List ℕ) (w:ℕ) (s:List ℕ) :
    s∈cuts vs w ↔ s.Sublist vs ∧ s.length≤w := by
  induction vs generalizing w s with
  | nil=>cases s <;> simp [cuts]
  | cons v vs ih=>
    cases w with
    | zero=>cases s <;> simp [cuts]
    | succ w=>
      simp only [cuts,List.mem_append,List.mem_map,ih]
      constructor
      · rintro (⟨h,size⟩|⟨r,⟨h,size⟩,rfl⟩)
        · exact ⟨h.cons v,size⟩
        · exact ⟨h.cons_cons v,by simpa using size⟩
      · rintro ⟨h,size⟩
        cases h with
        | cons _ h=>exact Or.inl ⟨h,size⟩
        | cons_cons _ h=>exact Or.inr ⟨_,⟨h,by simpa using size⟩,rfl⟩

def bindCodes (s:List ℕ) (a:ℕ→ℕ) : Assignment := s.map (fun i=>(i,a i))

theorem bindings_mem (d:Instance) (s:List ℕ) (a:ℕ→ℕ) :
    bindCodes s a∈assignments d s ↔ ∀i∈s,a i∈d.menu i := by
  induction s with
  | nil=>simp [bindCodes,assignments]
  | cons i is ih=>
    simp only [bindCodes,List.map_cons,assignments,List.mem_flatMap,List.mem_map,List.cons.injEq,Prod.mk.injEq,true_and]
    constructor
    · rintro ⟨x,hx,b,hb,eq,rfl⟩;subst x
      exact List.forall_mem_cons.mpr ⟨hx,ih.mp hb⟩
    · intro h;obtain ⟨hx,ht⟩:=List.forall_mem_cons.mp h
      exact ⟨a i,hx,bindCodes is a,ih.mpr ht,rfl,rfl⟩

theorem binding_value (s:List ℕ) (a:ℕ→ℕ) (i:ℕ) (hi:i∈s) : value (bindCodes s a) i=a i := by
  induction s with
  | nil=>contradiction
  | cons j js ih=>
    by_cases eq:j=i
    · subst i;simp [value,bindCodes]
    · have rest:i∈js:=by simpa [Ne.symm eq] using hi
      simpa [value,bindCodes,List.find?_cons,eq] using ih rest

theorem restrict_binding {s t:List ℕ} (sub:∀j∈t,j∈s) (a:ℕ→ℕ) :
    restricted t (bindCodes s a)=bindCodes t a := by
  apply List.map_congr_left
  intro j hj;rw [binding_value s a j (sub j hj)]

theorem bindings_exhaust (d:Instance) (s:List ℕ) (distinct:s.Nodup) (b:Assignment) (hb:b∈assignments d s) :
    ∃a:ℕ→ℕ,b=bindCodes s a ∧ ∀i∈s,a i∈d.menu i := by
  induction s generalizing b with
  | nil=>
    have eq:b=[]:=by simpa [assignments] using hb
    subst b;exact ⟨fun _=>0,rfl,by simp⟩
  | cons i is ih=>
    obtain ⟨x,hx,hit⟩:=List.mem_flatMap.mp hb
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hit
    obtain ⟨f,rfl,valid⟩:=ih (List.nodup_cons.mp distinct).2 c hc
    let a:=Function.update f i x
    have same (j:ℕ) (h:j∈is) : a j=f j:=Function.update_of_ne (by rintro rfl;exact (List.nodup_cons.mp distinct).1 h) ..
    refine ⟨a,?_,?_⟩
    · unfold bindCodes;rw [List.map_cons,show a i=x from Function.update_self ..]
      congr 1;apply List.map_congr_left;intro j hj;rw [same j hj]
    · rw [List.forall_mem_cons];exact ⟨by simpa [a] using hx,fun j h=>same j h ▸ valid j h⟩

namespace Presentation
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V} (P:Presentation d G)

theorem good_cut (S:Finset V) (w:ℕ) (hw:S.card≤w) : P.code S∈cuts (vertices d) (min w d.n) := by
  rw [cuts_exact,P.code_length,P.all_code,Nat.le_min]
  have length:Fintype.card V≤d.n:=by simpa using Fintype.card_le_of_injective P.ix P.injective
  refine ⟨?_,hw,(Finset.card_le_univ S).trans length⟩
  apply List.sublist_of_subperm_of_pairwise _ (P.code_sorted S) (P.code_sorted Finset.univ)
  apply List.subperm_of_subset (P.code_nodup S)
  intro i hi
  obtain ⟨v,_,rfl⟩:=P.mem_code.mp hi
  exact P.idx_mem.mpr (Finset.mem_univ v)

theorem layer_contains (w:ℕ) (C:Finset V) (a:ℕ→ℕ) (hC:IsFlap G (boundary G C) C)
    (small:(boundary G C).card≤w) (valid:∀v∈boundary G C,a (P.idx v)∈d.menu (P.idx v)) :
    let S:=boundary G C
    P.code S∈cuts (vertices d) (min w d.n) ∧ P.code C∈keysFor d (vertices d) (P.code S) ∧
      rimOf d (P.code C)=P.code S ∧ bindCodes (P.code S) a∈assignments d (P.code S) := by
  refine ⟨P.good_cut _ w small,?_,P.rim_code C,(bindings_mem ..).2 ?_⟩
  · unfold keysFor;rw [P.code_comp,P.parts_geometry]
    exact ⟨C,by simpa using hC,rfl⟩
  · intro i hi;obtain ⟨v,hv,rfl⟩:=P.mem_code.mp hi;exact valid v hv
end Presentation
end StableMSR.Recovery.TightLanguage.Graph

namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

/-- The chronological list of keys installed by one component-size pass. -/
def layerKeys (d:Instance) (w k:ℕ) : List Key :=
  let vs:=vertices d
  (cuts vs (min w d.n)).flatMap fun s=>(keysFor d vs s).flatMap fun c=>
    if c.length==k+1 && rimOf d c==s then (assignments d s).map fun a=>(c,a) else []

theorem layer_mem (d:Instance) (w k:ℕ) (c:List ℕ) (a:Assignment) :
    (c,a)∈layerKeys d w k ↔ c.length=k+1 ∧ rimOf d c∈cuts (vertices d) (min w d.n) ∧
      c∈keysFor d (vertices d) (rimOf d c) ∧ a∈assignments d (rimOf d c) := by
  unfold layerKeys;simp only [List.mem_flatMap]
  constructor
  · rintro ⟨s,hs,t,ht,occ⟩
    split at occ
    · rename_i test
      simp only [Bool.and_eq_true,beq_iff_eq] at test
      obtain ⟨size,rfl⟩:=test
      obtain ⟨b,hb,eq⟩:=List.mem_map.mp occ
      cases eq;exact ⟨size,hs,ht,hb⟩
    · contradiction
  · rintro ⟨size,hs,hc,ha⟩
    exact ⟨rimOf d c,hs,c,hc,by simp [size,ha]⟩

abbrev WordTable := Table (Lang Letter)
def writeRow (d:Instance) (tab:WordTable) (k:Key) : WordTable :=
  (k,(collect wordAlgebra d tab k.1 k.2 ()).2)::tab
def sheet (d:Instance) (w m:ℕ) : WordTable :=
  (List.range m).foldl (fun tab k=>(layerKeys d w k).foldl (writeRow d) tab) []

theorem sheet_succ (d:Instance) (w m:ℕ) : sheet d w (m+1)=(layerKeys d w m).foldl (writeRow d) (sheet d w m) := by
  simp [sheet,List.range_succ,List.foldl_append]

theorem build_sheet (d:Instance) (w:ℕ) : (build wordAlgebra d w).2=sheet d w d.n := by
  let emit:=fun (p:Unit×WordTable) (k:Key)=>install wordAlgebra d k.1 k.2 p
  let layer:=fun (p:Unit×WordTable) (k:ℕ)=>(layerKeys d w k).foldl emit p
  have eq:build wordAlgebra d w=(List.range d.n).foldl layer ((),[]) := by
    unfold build;dsimp only;congr 1
    funext p k;unfold layer layerKeys
    simp only [List.foldl_flatMap]
    congr 1;funext z s;congr 1;funext t c
    unfold visit;split
    · simp only [List.foldl_map];rfl
    · rfl
  rw [eq];unfold sheet;symm
  apply List.foldl_hom (g₁:=layer) (init:=((),[])) Prod.snd
  intro z k
  apply List.foldl_hom (g₁:=emit) (init:=z) Prod.snd
  intro s key;rfl

theorem lookup_row_iff (t:WordTable) (k:Key) : (lookup t k.1 k.2).isSome ↔ k∈t.map Prod.fst := by
  induction t with
  | nil=>simp [lookup]
  | cons row rs ih=>
    by_cases e:row.1=k
    · simp [lookup,List.find?_cons,e]
    · have ne:k≠row.1:=Ne.symm e
      simpa [lookup,List.find?_cons,e,ne] using ih

theorem written_keys (d:Instance) (keys:List Key) (t:WordTable) :
    ((keys.foldl (writeRow d) t).map Prod.fst)=keys.reverse ++ t.map Prod.fst := by
  induction keys generalizing t with
  | nil=>rfl
  | cons k ks ih=>simp [List.foldl_cons,ih,writeRow,List.append_assoc]

theorem sheet_has (d:Instance) (w m:ℕ) (key:Key) :
    (lookup (sheet d w m) key.1 key.2).isSome ↔ ∃k < m,key∈layerKeys d w k := by
  rw [lookup_row_iff]
  induction m with
  | zero=>simp [sheet]
  | succ m ih=>
    rw [sheet_succ,written_keys,List.mem_append,List.mem_reverse,ih]
    constructor
    · rintro (h|⟨k,hk,h⟩)
      · exact ⟨m,Nat.lt_succ_self _,h⟩
      · exact ⟨k,Nat.lt.step hk,h⟩
    · rintro ⟨k,hk,h⟩;rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with a|rfl
      · exact Or.inr ⟨k,a,h⟩
      · exact Or.inl h

theorem has_iff (d:Instance) (w m:ℕ) (c:List ℕ) (a:Assignment) :
    (lookup (sheet d w m) c a).isSome ↔ 0<c.length ∧ c.length ≤ m ∧
      rimOf d c∈cuts (vertices d) (min w d.n) ∧ c∈keysFor d (vertices d) (rimOf d c) ∧
      a∈assignments d (rimOf d c) := by
  rw [show (lookup (sheet d w m) c a).isSome ↔ _ from sheet_has d w m (c,a)]
  constructor
  · rintro ⟨k,hk,h⟩
    obtain ⟨sz,row⟩:=(layer_mem d w k c a).1 h;exact ⟨by omega,by omega,row⟩
  · rintro ⟨h,small,row⟩
    exact ⟨c.length-1,by omega,(layer_mem ..).2 ⟨by omega,row⟩⟩

namespace Presentation
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V} (P:Presentation d G)

theorem row_present (w m:ℕ) (C:Finset V) (a:ℕ→ℕ) (flap:IsFlap G (boundary G C) C)
    (width:(boundary G C).card≤w) (depth:C.card ≤ m)
    (valid:∀v∈boundary G C,a (P.idx v)∈d.menu (P.idx v)) :
    (lookup (sheet d w m) (P.code C) (bindCodes (P.code (boundary G C)) a)).isSome := by
  obtain ⟨cut,comp,eq,good⟩:=P.layer_contains w C a flap width valid
  rw [has_iff,P.code_length,eq];exact ⟨Finset.card_pos.mpr flap.connected.1,depth,cut,comp,good⟩
end Presentation
end StableMSR.Recovery.TightLanguage.Graph

/-! ## The value of a completed row depends only on smaller rows -/

namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

theorem fold_congr_mem {A I:Type} {f g:A→I→A} (xs:List I) (a:A) (h:∀z i,i∈xs → f z i=g z i) :
    xs.foldl f a=xs.foldl g a := by
  induction xs generalizing a with
  | nil=>rfl
  | cons i is ih=>
    simp only [List.foldl_cons];rw [h a i (by simp)];exact ih _ (fun z j hj=>h z j (by simp [hj]))

theorem queries_congr {A I:Type} {f g:I→Option A} (xs:List I) (h:∀i∈xs,f i=g i) :
    xs.mapM f=xs.mapM g := by
  induction xs with
  | nil=>rfl
  | cons i is ih=>simp only [List.mapM_cons,h i (by simp),ih (fun j hj=>h j (by simp [hj]))]

theorem child_shorter (d:Instance) (nonempty:0<d.n) {c:List ℕ} {v:ℕ} (pivot:v∈c)
    {t:List ℕ} (ht:t∈parts d (c.erase v)) : t.length<c.length := by
  obtain ⟨j,_,rfl,_⟩:=Presentation.parts_spec (d:=d) (c.erase v) t |>.1 ht
  obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt nonempty)
  unfold pieceAt;rw [hk,List.range_succ,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil]
  have bound:=List.length_erase_of_mem pivot
  have cpos:=List.length_pos_of_mem pivot
  exact Nat.lt_of_le_of_lt (List.length_filter_le ..) (by omega)

def AgreeBelow (m:ℕ) (t u:WordTable) := ∀c a,c.length ≤ m → lookup t c a=lookup u c a

theorem collect_congr (d:Instance) (alive:0<d.n) (c:List ℕ) (a:Assignment) (t u:WordTable)
    (same:∀s b,s.length<c.length → lookup t s b=lookup u s b) :
    collect wordAlgebra d t c a ()=collect wordAlgebra d u c a () := by
  unfold collect;apply fold_congr_mem
  intro z v hv;apply fold_congr_mem
  intro y x _;unfold offer
  have eq:refs d t c v ((v,x)::a)=refs d u c v ((v,x)::a):=by
    apply queries_congr;intro s hs;apply same;exact child_shorter d alive hv hs
  dsimp only;rw [eq]

theorem lookup_cons (t:WordTable) (k:Key) (v:Lang Letter) (c:List ℕ) (a:Assignment) :
    lookup ((k,v)::t) c a=if k=(c,a) then some v else lookup t c a := by
  by_cases eq:k=(c,a) <;> simp [lookup,List.find?_cons,eq]

def frozen (d:Instance) (t:WordTable) (k:Key) : Key×Lang Letter :=
  (k,(collect wordAlgebra d t k.1 k.2 ()).2)

theorem frozen_layer (d:Instance) (alive:0<d.n) (k:ℕ) (old cur:WordTable) (ks:List Key)
    (sizes:∀p∈ks,p.1.length=k+1) (same:AgreeBelow k cur old) :
    ks.foldl (writeRow d) cur=(ks.map (frozen d old)).reverse ++ cur := by
  induction ks generalizing cur with
  | nil=>rfl
  | cons key ks ih=>
    have size:=sizes key (by simp)
    have v:=collect_congr d alive key.1 key.2 cur old (fun c a h=>same c a (by omega))
    have next:AgreeBelow k (writeRow d cur key) old := by
      intro c a h
      have ne:key≠(c,a):=by intro e;have l:=congrArg (fun z:Key=>z.1.length) e;dsimp only at l;omega
      unfold writeRow;rw [lookup_cons,if_neg ne];exact same c a h
    rw [List.foldl_cons,ih (writeRow d cur key) (fun p hp=>sizes p (by simp [hp])) next]
    simp [frozen,writeRow,v,List.append_assoc]

theorem lookup_frozen (d:Instance) (old cur:WordTable) (ks:List Key) (c:List ℕ) (a:Assignment) :
    lookup (ks.map (frozen d old) ++ cur) c a =
      if (c,a)∈ks then some (collect wordAlgebra d old c a ()).2 else lookup cur c a := by
  induction ks with
  | nil=>simp
  | cons key ks ih=>
    by_cases eq:key=(c,a)
    · subst key;simp [frozen,lookup_cons]
    · simp [frozen,lookup_cons,eq,Ne.symm eq,ih]

theorem layer_lookup (d:Instance) (alive:0<d.n) (w k:ℕ) (c:List ℕ) (a:Assignment) :
    lookup (sheet d w (k+1)) c a =
      if (c,a)∈layerKeys d w k then some (collect wordAlgebra d (sheet d w k) c a ()).2 else lookup (sheet d w k) c a := by
  have sizes (p:Key) (hp:p∈layerKeys d w k) : p.1.length=k+1 := (layer_mem d w k p.1 p.2).1 hp |>.1
  rw [sheet_succ,frozen_layer d alive k _ _ _ sizes (fun _ _ _=>rfl),←List.map_reverse,lookup_frozen];simp only [List.mem_reverse]

theorem sheet_stable (d:Instance) (alive:0<d.n) (w k m:ℕ) (km:k ≤ m) :
    AgreeBelow k (sheet d w m) (sheet d w k) := by
  obtain ⟨r,rfl⟩:=Nat.exists_eq_add_of_le km;clear km
  induction r with
  | zero=>exact fun _ _ _=>rfl
  | succ r ih=>
    intro c a h
    have skip:(c,a)∉layerKeys d w (k+r):=by intro hx;have:=((layer_mem ..).1 hx).1;omega
    rw [←Nat.add_assoc,layer_lookup d alive w (k+r),if_neg skip];exact ih c a h

/-- Each present entry of the final table is precisely the union of its legal
pivot productions using final child entries. Child lookups always decrease size. -/
theorem row_equation (d:Instance) (w:ℕ) (c:List ℕ) (a:Assignment)
    (registered:(lookup (build wordAlgebra d w).2 c a).isSome) :
    lookup (build wordAlgebra d w).2 c a=some (collect wordAlgebra d (build wordAlgebra d w).2 c a ()).2 := by
  rw [build_sheet] at *
  obtain ⟨pos,bound,_⟩:=(has_iff d w d.n c a).1 registered
  have alive:0<d.n:=by omega
  obtain ⟨k,hk,hit⟩:=(sheet_has d w d.n (c,a)).1 registered
  have sz:=((layer_mem ..).1 hit).1
  rw [sheet_stable d alive w (k+1) d.n hk c a (by omega),layer_lookup d alive w k,if_pos hit]
  have eq:=collect_congr d alive c a (sheet d w d.n) (sheet d w k)
    (fun s b h=>sheet_stable d alive w k d.n (Nat.le_of_lt hk) s b (by omega))
  rw [eq]
end StableMSR.Recovery.TightLanguage.Graph

namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

def production (d:Instance) (tab:WordTable) (c:List ℕ) (a:Assignment) (v x:ℕ) (s:List Letter) :=
  let b:=(v,x)::a
  localOK d b=true ∧ ∃tail,joined (fun t=>lookup tab t (restricted (rimOf d t) b))
    (parts d (c.erase v)) tail ∧ s=(v,x)::tail

theorem offer_words (d:Instance) (tab:WordTable) (c:List ℕ) (a:Assignment) (v x:ℕ) (z:Unit×Lang Letter) (s:List Letter) :
    (offer wordAlgebra d tab c a v x z).2 s ↔ z.2 s ∨ production d tab c a v x s := by
  let b:=(v,x)::a
  by_cases good:localOK d b=true
  · unfold offer production;dsimp only
    have ok:localOK d ((v,x)::a)=true:=good
    simp only [ok,if_true,true_and]
    unfold joined refs
    cases hit:(parts d (c.erase v)).mapM (m:=Option) (fun t=>lookup tab t (restricted (rimOf d t) ((v,x)::a))) <;> simp [wordAlgebra]
  · have no:localOK d ((v,x)::a)≠true:=good
    simp [offer,production,no]

theorem fold_accept {I S:Type} (f:S→I→S) (P:S→Prop) (Q:I→Prop)
    (step:∀z i,P (f z i) ↔ P z ∨ Q i) (xs:List I) (z:S) :
    P (xs.foldl f z) ↔ P z ∨ ∃i∈xs,Q i := by
  induction xs generalizing z with
  | nil=>simp
  | cons i is ih=>simp only [List.foldl_cons,ih,step,List.mem_cons];grind

theorem collect_words (d:Instance) (tab:WordTable) (c:List ℕ) (a:Assignment) (s:List Letter) :
    (collect wordAlgebra d tab c a ()).2 s ↔ ∃v∈c,∃x∈d.menu v,production d tab c a v x s := by
  let P:=fun z:Unit×Lang Letter=>z.2 s
  let Q:=production d tab c a
  let f:=fun (v:ℕ) (z:Unit×Lang Letter) (x:ℕ)=>offer wordAlgebra d tab c a v x z
  let g:=fun (z:Unit×Lang Letter) (v:ℕ)=>(d.menu v).foldl (f v) z
  have inner (z:Unit×Lang Letter) (v:ℕ) : P (g z v) ↔ P z ∨ ∃x∈d.menu v,Q v x s :=
    fold_accept (f v) P (fun x=>Q v x s) (fun z x=>offer_words ..) .. 
  have result:=fold_accept g P (fun v=>∃x∈d.menu v,Q v x s) inner c ((),wordAlgebra.fail)
  exact result.trans (Iff.of_eq (false_or _))

namespace Presentation
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V} (P:Presentation d G)

noncomputable def accepts (w:ℕ) (C:Finset V) (a:ℕ→ℕ) : Lang Letter :=
  available (lookup (build wordAlgebra d w).2 (P.code C) (bindCodes (P.code (boundary G C)) a))
def tag (z:V×ℕ) : Letter := (P.idx z.1,z.2)
def menu (v:V) := (d.menu (P.idx v)).toFinset
def test (u v:V) (a b:ℕ) := d.test (P.idx u) (P.idx v) a b=true
def decoded (a:ℕ→ℕ) (v:V) := a (P.idx v)

theorem width_of_word {w:ℕ} {C:Finset V} {a:ℕ→ℕ} {s:List Letter} (h:P.accepts w C a s) :
    (boundary G C).card≤w := by
  unfold accepts at h;rw [build_sheet] at h
  have present {o:Option (Lang Letter)} (hh:available o s) : o.isSome:=by cases o with
    | none=>exact False.elim hh
    | some _=>rfl
  have hc:=((has_iff ..).1 (present h)).2.2.1
  have len:=(cuts_exact ..).1 hc |>.2
  rw [P.rim_code,P.code_length] at len;exact len.trans (Nat.min_le_left ..)

theorem row_choices (w:ℕ) (C:Finset V) (a:ℕ→ℕ) (flap:IsFlap G (boundary G C) C)
    (width:(boundary G C).card≤w) (valid:∀v∈boundary G C,a (P.idx v)∈d.menu (P.idx v)) (s:List Letter) :
    P.accepts w C a s ↔ ∃v∈C,∃x∈d.menu (P.idx v),
      production d (build wordAlgebra d w).2 (P.code C) (bindCodes (P.code (boundary G C)) a) (P.idx v) x s := by
  have bound:C.card≤d.n:=(Finset.card_le_univ C).trans (by simpa using Fintype.card_le_of_injective P.ix P.injective)
  have ok:=P.row_present w d.n C a flap width bound valid
  rw [←build_sheet] at ok
  unfold accepts;rw [row_equation d w _ _ ok]
  change (collect wordAlgebra d _ _ _ ()).2 s ↔ _
  rw [collect_words]
  constructor
  · rintro ⟨i,hi,x,hx,h⟩;obtain ⟨v,hv,rfl⟩:=P.mem_code.mp hi;exact ⟨v,hv,x,hx,h⟩
  · rintro ⟨v,hv,x,hx,h⟩;exact ⟨P.idx v,P.idx_mem.mpr hv,x,hx,h⟩
end Presentation
end StableMSR.Recovery.TightLanguage.Graph

/-! ## Agreement of the numeric bag and the singleton graph production -/

namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

namespace Presentation
open WindowCuts
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V} (P:Presentation d G)

def newLabel (a:ℕ→ℕ) (v:V) (x:ℕ) := Function.update a (P.idx v) x

theorem decoded_new (a:ℕ→ℕ) (v:V) (x:ℕ) :
    P.decoded (P.newLabel a v x)=Function.update (P.decoded a) v x := by
  funext u;by_cases eq:u=v
  · subst u;simp [decoded,newLabel]
  · simp [decoded,newLabel,eq,P.idx_injective.ne eq,Function.update_of_ne]

theorem labelled_bag (S:Finset V) (v:V) (fresh:v∉S) (x:ℕ) (a:ℕ→ℕ) (z:Letter) :
    z∈(P.idx v,x)::bindCodes (P.code S) a ↔
    ∃u∈insert v S,(P.idx u,P.decoded (P.newLabel a v x) u)=z := by
  rw [List.mem_cons];constructor
  · rintro (rfl|hit)
    · exact ⟨v,Finset.mem_insert_self ..,by simp [decoded,newLabel]⟩
    · obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hit
      obtain ⟨u,hu,rfl⟩:=P.mem_code.mp hi
      have ne:u≠v:=fun eq=>fresh (eq ▸ hu)
      exact ⟨u,Finset.mem_insert_of_mem hu,by simp [decoded,newLabel,Function.update_of_ne (P.idx_injective.ne ne)]⟩
  · rintro ⟨u,hu,rfl⟩
    rcases Finset.mem_insert.mp hu with rfl|hu
    · left;simp [decoded,newLabel]
    · right
      have ne:u≠v:=fun eq=>fresh (eq ▸ hu)
      apply List.mem_map.mpr
      exact ⟨P.idx u,P.idx_mem.mpr hu,by simp [decoded,newLabel,Function.update_of_ne (P.idx_injective.ne ne)]⟩

theorem bag_ok (S:Finset V) (v:V) (fresh:v∉S) (x:ℕ) (hx:x∈d.menu (P.idx v))
    (a:ℕ→ℕ) (valid:∀u∈S,a (P.idx u)∈d.menu (P.idx u)) :
    localOK d ((P.idx v,x)::bindCodes (P.code S) a)=true ↔
      okay G P.menu P.test (insert v S) (P.decoded (P.newLabel a v x)) := by
  have imp (e k:Bool) : (!e || k)=true ↔ (e=true → k=true):=by cases e <;> cases k <;> decide
  simp only [localOK,List.all_eq_true,imp]
  constructor
  · intro h;constructor
    · intro u hu;rcases Finset.mem_insert.mp hu with rfl|hu
      · simpa [menu,decoded,newLabel] using hx
      · have ne:u≠v:=fun e=>fresh (e ▸ hu)
        simpa [menu,decoded,newLabel,Function.update_of_ne (P.idx_injective.ne ne)] using valid u hu
    · intro u hu y hy edge
      exact h _ ((P.labelled_bag S v fresh x a _).2 ⟨u,hu,rfl⟩) _ ((P.labelled_bag S v fresh x a _).2 ⟨y,hy,rfl⟩) ((P.edges u y).2 edge)
  · intro h z hz t ht edge
    obtain ⟨u,hu,rfl⟩:=(P.labelled_bag S v fresh x a _).1 hz
    obtain ⟨y,hy,rfl⟩:=(P.labelled_bag S v fresh x a _).1 ht
    exact h.2 u hu y hy ((P.edges u y).1 edge)

theorem restrict_new {S T:Finset V} {v:V} (inside:T⊆insert v S) (x:ℕ) (a:ℕ→ℕ) :
    restricted (P.code T) ((P.idx v,x)::bindCodes (P.code S) a)=bindCodes (P.code T) (P.newLabel a v x) := by
  apply List.map_congr_left
  intro i hi;obtain ⟨u,hu,rfl⟩:=P.mem_code.mp hi
  by_cases eq:u=v
  · subst u;simp [value,newLabel]
  · have hS:=Finset.mem_of_mem_insert_of_ne (inside hu) eq
    have ne:P.idx v≠P.idx u:=Ne.symm (P.idx_injective.ne eq)
    have bit : (P.idx v == P.idx u)=false:=by simp [ne]
    have read:=binding_value (P.code S) a (P.idx u) (P.idx_mem.mpr hS)
    simpa only [value,List.find?_cons,bit,Prod.mk.injEq,true_and,
      newLabel,Function.update_of_ne (Ne.symm ne)] using congrArg (Prod.mk (P.idx u)) read

theorem child_facts {S C:Finset V} (hc:IsFlap G S C) (v:V) (hv:v∈C) :
    let es:=P.pieces (C.erase v)
    let B:=insert v S
    es.toFinset.biUnion id=C.erase v ∧ ∀E∈es,IsFlap G (boundary G E) E ∧
      boundary G E⊆B ∧ E⊆C.erase v ∧ E.card<C.card := by
  have geo:=SingleSearch.deletion_piece_geometry G S C (insert v S) hc (Finset.subset_insert ..)
    (Finset.insert_subset (Finset.mem_union_right _ hv) Finset.subset_union_left)
  have table:=P.parts_children hc v hv
  refine ⟨?_,?_⟩
  · rw [table.2,geo.1];ext u
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_erase,not_or]
    constructor
    · rintro ⟨h,n,_⟩;exact ⟨n,h⟩
    · rintro ⟨n,h⟩;exact ⟨h,n,fun hs=>Finset.disjoint_left.mp hc.avoids hs h⟩
  · intro E he
    have entry:=(P.children_geometry hc v hv E).1 he
    have h:=geo.2.2.1 E entry
    have subset:E⊆C.erase v:=by
      intro u hu;refine Finset.mem_erase.mpr ⟨?_,(mem_children.mp entry).2 hu⟩
      rintro rfl;exact Finset.disjoint_left.mp h.2.1 hu (Finset.mem_insert_self ..)
    exact ⟨h.1,h.2.2.1,subset,(Finset.card_le_card subset).trans_lt (Finset.card_erase_lt_of_mem hv)⟩
end Presentation
end StableMSR.Recovery.TightLanguage.Graph

namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

namespace Presentation
open WindowCuts
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V} (P:Presentation d G)

theorem tail_split (w:ℕ) (C:Finset V) (a:ℕ→ℕ) (flap:IsFlap G (boundary G C) C)
    (v:V) (hv:v∈C) (x:ℕ) (tail:List Letter) :
    let tab:=(build wordAlgebra d w).2
    let b:=(P.idx v,x)::bindCodes (P.code (boundary G C)) a
    joined (fun t=>lookup tab t (restricted (rimOf d t) b)) (parts d ((P.code C).erase (P.idx v))) tail ↔
      ∃f:Finset V→List Letter,(∀E∈P.pieces (C.erase v),P.accepts w E (P.newLabel a v x) (f E)) ∧
        tail=(P.pieces (C.erase v)).flatMap f := by
  let es:=P.pieces (C.erase v)
  let tab:=(build wordAlgebra d w).2
  let b:=(P.idx v,x)::bindCodes (P.code (boundary G C)) a
  let ask:=fun t=>lookup tab t (restricted (rimOf d t) b)
  let row:=fun E=>lookup tab (P.code E) (bindCodes (P.code (boundary G E)) (P.newLabel a v x))
  have eq:(parts d ((P.code C).erase (P.idx v))).mapM (m:=Option) ask=es.mapM row := by
    rw [←(P.parts_children flap v hv).1,List.mapM_map]
    apply queries_congr;intro E he
    change lookup tab (P.code E) (restricted (rimOf d (P.code E)) b)=_
    rw [P.rim_code,P.restrict_new ((P.child_facts flap v hv).2 E he).2.1]
  change joined ask _ tail ↔ _
  have same:joined ask (parts d ((P.code C).erase (P.idx v)))=joined row es:=by unfold joined;rw [eq]
  rw [same];exact joined_iff row es (P.pieces_nodup _) tail

theorem step_words (w:ℕ) (C:Finset V) (a:ℕ→ℕ) (flap:IsFlap G (boundary G C) C)
    (width:(boundary G C).card≤w) (valid:∀u∈boundary G C,a (P.idx u)∈d.menu (P.idx u)) (s:List Letter) :
    P.accepts w C a s ↔ ∃v∈C,∃x∈d.menu (P.idx v),
      okay G P.menu P.test (insert v (boundary G C)) (P.decoded (P.newLabel a v x)) ∧
      ∃f:Finset V→List Letter,(∀E∈P.pieces (C.erase v),P.accepts w E (P.newLabel a v x) (f E)) ∧
      s=(P.idx v,x)::(P.pieces (C.erase v)).flatMap f := by
  rw [P.row_choices w C a flap width valid]
  have each (v:V) (hv:v∈C) (x:ℕ) (hx:x∈d.menu (P.idx v)) :
      production d (build wordAlgebra d w).2 (P.code C) (bindCodes (P.code (boundary G C)) a) (P.idx v) x s ↔
      okay G P.menu P.test (insert v (boundary G C)) (P.decoded (P.newLabel a v x)) ∧
      ∃f:Finset V→List Letter,(∀E∈P.pieces (C.erase v),P.accepts w E (P.newLabel a v x) (f E)) ∧
      s=(P.idx v,x)::(P.pieces (C.erase v)).flatMap f := by
    have fresh:v∉boundary G C:=fun hs=>Finset.disjoint_left.mp flap.avoids hs hv
    unfold production;dsimp only
    rw [P.bag_ok _ v fresh x hx a valid]
    apply and_congr_right;intro _
    constructor
    · rintro ⟨tail,h,rfl⟩;obtain ⟨f,hf,rfl⟩:=(P.tail_split w C a flap v hv x tail).1 h
      exact ⟨f,hf,rfl⟩
    · rintro ⟨f,hf,rfl⟩;exact ⟨_,(P.tail_split w C a flap v hv x _).2 ⟨f,hf,rfl⟩,rfl⟩
  constructor
  · rintro ⟨v,hv,x,hx,h⟩;exact ⟨v,hv,x,hx,(each v hv x hx).1 h⟩
  · rintro ⟨v,hv,x,hx,h⟩;exact ⟨v,hv,x,hx,(each v hv x hx).2 h⟩

theorem assemble_support {S C:Finset V} (flap:IsFlap G S C) (v:V) (hv:v∈C) (x:ℕ)
    (l:Finset V→List (V×ℕ)) (each:∀E∈P.pieces (C.erase v),
      ((l E).map Prod.fst).Nodup ∧ ((l E).map Prod.fst).toFinset=E) :
    let all:=((v,x)::(P.pieces (C.erase v)).flatMap l).map Prod.fst
    all.Nodup ∧ all.toFinset=C := by
  classical
  let es:=P.pieces (C.erase v)
  let g:=fun E=>(l E).map Prod.fst
  have flat:((v,x)::es.flatMap l).map Prod.fst=v::es.flatMap g:=by simp [List.map_flatMap,g]
  rw [flat]
  have geom:=P.child_facts flap v hv
  have inside (E:Finset V) (he:E∈es) (u:V) (hu:u∈g E) : u∈E:=by rw [←(each E he).2];exact List.mem_toFinset.mpr hu
  constructor
  · rw [List.nodup_cons];constructor
    · intro h;obtain ⟨E,he,hv'⟩:=List.mem_flatMap.mp h
      exact (Finset.mem_erase.mp ((geom.2 E he).2.2.1 (inside E he v hv'))).1 rfl
    · apply List.nodup_flatMap.mpr
      refine ⟨fun E he=>(each E he).1,(P.pieces_nodup _).pairwise_of_forall_ne ?_⟩
      intro E he F hf diff u hE hF
      exact Finset.disjoint_left.mp (P.different_pieces he hf diff) (inside E he u hE) (inside F hf u hF)
  · rw [List.toFinset_cons,union_flat]
    have eq:es.toFinset.biUnion (fun E=>(g E).toFinset)=es.toFinset.biUnion id:=
      Finset.biUnion_congr rfl (fun E he=>(each E (List.mem_toFinset.mp he)).2)
    rw [eq,geom.1,Finset.insert_erase hv]
end Presentation
end StableMSR.Recovery.TightLanguage.Graph

/-! ## Soundness and completeness by induction on search depth -/

namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

namespace Presentation
open WindowCuts SingleSearch
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V} (P:Presentation d G)

def RowMeaning (w m:ℕ) (C:Finset V) (a:ℕ→ℕ) :=
  let runs:=run G P.menu P.test w m (boundary G C) C (P.decoded a)
  (∀t,P.accepts w C a t → ∃l:List (V×ℕ),l.map P.tag=t ∧ (l.map Prod.fst).Nodup ∧
    (l.map Prod.fst).toFinset=C ∧ runs l.toFinset) ∧
  ∀O,runs O → ∃l:List (V×ℕ),P.accepts w C a (l.map P.tag) ∧ l.toFinset=O

theorem exact_row (w m:ℕ) (C:Finset V) (a:ℕ→ℕ) (flap:IsFlap G (boundary G C) C)
    (width:(boundary G C).card≤w) (depth:C.card ≤ m) (valid:∀v∈boundary G C,a (P.idx v)∈d.menu (P.idx v)) :
    P.RowMeaning w m C a := by
  classical
  induction m generalizing C a with
  | zero=>have positive:=Finset.card_pos.mpr flap.connected.1;omega
  | succ m ih=>
    let S:=boundary G C
    have step:=P.step_words w C a flap width valid
    constructor
    · intro t ht
      obtain ⟨v,hv,x,hx,ok,f,hf,rfl⟩:=(step t).1 ht
      let es:=P.pieces (C.erase v)
      let b:=P.newLabel a v x
      have facts:=P.child_facts flap v hv
      have components:=P.parts_children flap v hv |>.2
      have cm (E:Finset V) : E∈es ↔ E∈children G (insert v S) C := by
        rw [←components];exact List.mem_toFinset.symm
      have child (E:Finset V) (he:E∈es) : P.RowMeaning w m E b := by
        obtain ⟨tight,rim,_,lt⟩:=facts.2 E he
        apply ih E b tight (P.width_of_word (hf E he)) (by omega)
        intro z hz;exact List.mem_toFinset.mp (ok.1 z (rim hz))
      have choices (E:Finset V) (he:E∈es) := (child E he).1 (f E) (hf E he)
      let l (E:Finset V) := if he:E∈es then (choices E he).choose else []
      have hl (E:Finset V) (he:E∈es) :
          (l E).map P.tag=f E ∧ ((l E).map Prod.fst).Nodup ∧ ((l E).map Prod.fst).toFinset=E ∧
          run G P.menu P.test w m (boundary G E) E (P.decoded b) (l E).toFinset := by
        simpa only [l,dif_pos he] using (choices E he).choose_spec
      have support:=P.assemble_support flap v hv x l (fun E he=>⟨(hl E he).2.1,(hl E he).2.2.1⟩)
      refine ⟨(v,x)::es.flatMap l,?_,support.1,support.2,?_⟩
      · simp only [List.map_cons,List.map_flatMap]
        exact congrArg (List.cons (P.idx v,x)) (List.flatMap_congr (fun E he=>(hl E he).1))
      · refine ⟨width,v,hv,x,?_,fun E=>(l E).toFinset,?_,?_⟩
        · rw [←P.decoded_new];exact ok
        · intro E hE;have he:=(cm E).2 hE
          rw [←P.decoded_new];exact ⟨P.width_of_word (hf E he),(hl E he).2.2.2⟩
        · rw [List.toFinset_cons,union_flat,show es.toFinset=_ from components]
    · rintro O ⟨_,v,hv,x,good,out,childrenOK,rfl⟩
      let es:=P.pieces (C.erase v)
      let b:=P.newLabel a v x
      have facts:=P.child_facts flap v hv
      have components:=P.parts_children flap v hv |>.2
      have cm (E:Finset V) : E∈es ↔ E∈children G (insert v S) C := by
        rw [←components];exact List.mem_toFinset.symm
      have ok:okay G P.menu P.test (insert v S) (P.decoded b):=by rw [P.decoded_new];exact good
      have hx:x∈d.menu (P.idx v):=by
        have validx:=ok.1 v (Finset.mem_insert_self ..)
        simpa [b,menu,decoded,newLabel] using validx
      have choices (E:Finset V) (he:E∈es) :
          ∃l:List (V×ℕ),P.accepts w E b (l.map P.tag) ∧ l.toFinset=out E := by
        obtain ⟨tight,rim,_,lt⟩:=facts.2 E he
        obtain ⟨small,runs⟩:=childrenOK E ((cm E).1 he)
        have dom:∀z∈boundary G E,b (P.idx z)∈d.menu (P.idx z):=
          fun z hz=>List.mem_toFinset.mp (ok.1 z (rim hz))
        apply (ih E b tight small (by omega) dom).2 (out E)
        rw [P.decoded_new];exact runs
      let l (E:Finset V) := if he:E∈es then (choices E he).choose else []
      have hl (E:Finset V) (he:E∈es) : P.accepts w E b ((l E).map P.tag) ∧ (l E).toFinset=out E := by
        simpa only [l,dif_pos he] using (choices E he).choose_spec
      refine ⟨(v,x)::es.flatMap l,(step _).2 ⟨v,hv,x,hx,ok,fun E=>(l E).map P.tag,
        fun E he=>(hl E he).1,?_⟩,?_⟩
      · simp only [List.map_cons,List.map_flatMap];rfl
      · rw [List.toFinset_cons,union_flat,show es.toFinset=_ from components]
        congr 1;exact Finset.biUnion_congr rfl (fun E h=>(hl E ((cm E).2 h)).2)
end Presentation

theorem table_rows_correct : RowLaw := by
  intro V _ _ d ix inj G active edges w m C a flap width depth valid
  let P:Presentation d G:=⟨ix,inj,active,edges⟩
  exact P.exact_row w m C a flap width depth valid

theorem numeric_graph_correct : NumericGraphLaw := graph_from_rows table_rows_correct
end StableMSR.Recovery.TightLanguage.Graph

/-! ## The regional clustering theorem -/

namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

open OracleQueries SingleCodes SingleWindows

/-- The regional circuit computes the singleton window grammar for every window
region and every real scale. Each recognized word lists its owned blocks once. -/
theorem regional_language (x:World) (W:Cluster x.n) (R:ℝ) (h w:ℕ) :
    let c:=regionalCircuit x W R h w
    let gen:=generates x W R h w
    c.2<c.1.size ∧ (∀L,Language x.n c.1 c.2 L → L.Nodup ∧ gen L.toFinset) ∧
      ∀Q,gen Q → ∃L,Language x.n c.1 c.2 L ∧ L.toFinset=Q :=
  regional_language_from_graph Graph.numeric_graph_correct x W R h w

/-- The mission's live regional circuit conclusion, without a graph hypothesis. -/
theorem live_regional_circuit_correct (x:World) (h w u i:ℕ) : SingleRAM.LiveCircuitCorrect x h w u i :=
  regional_language x (WindowProfiles.piece x u i) (WindowCSP.scale x u) h w
end StableMSR.Recovery.TightLanguage


open StableMSR.Recovery StableMSR.Recovery.OracleQueries
theorem solution (x : World) (h w u i : ℕ) : SingleRAM.LiveCircuitCorrect x h w u i :=
  TightLanguage.live_regional_circuit_correct x h w u i
