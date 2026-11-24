-- Prove2me | solution 1 for StableMSR.Recovery.SingleRAM.global_assembly_resource_bound
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T22:31:57.449834+00:00
-- url     : https://prove2.me/submissions/bad0baa9-56df-499f-971f-6c222025b9d1

import Definitions.Def_StableMSR_DenseGlobalAssembly
set_option linter.all false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
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

namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
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

end StableMSR.Recovery.TightLanguage

namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false

theorem fold_gain {S I : Type} (size : S → ℕ) (xs : List I) (step : S → I → S) (z : S) (C : ℕ)
    (h : ∀ p i, i ∈ xs → size (step p i) ≤ size p + C) :
    size (xs.foldl step z) ≤ size z + xs.length * C := by
  induction xs generalizing z with
  | nil => simp
  | cons i xs ih =>
    simp only [List.foldl_cons,List.length_cons,Nat.succ_mul]
    have a := h z i (by simp)
    have b := ih (step z i) (fun p j hj => h p j (by simp [hj]))
    omega

theorem flat_length {I O : Type} (xs : List I) (f : I → List O) (B : ℕ)
    (h : ∀ i, i ∈ xs → (f i).length ≤ B) : (xs.flatMap f).length ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
    have a := h i (by simp)
    have b := ih (fun j hj => h j (by simp [hj]))
    omega

theorem body_bound (g : Gates) (ms : List (List ℕ)) (vs : List ℕ) :
    (body g ms vs).1.size ≤ g.size + 2*ms.length + vs.length := by
  rw [body_fold]
  have a := fold_gain (fun z : Gates×ℕ => z.1.size) ms litStep (g,0) 2
    (fun p i _ => by simp [litStep])
  have b := fold_gain (fun z : Gates×ℕ => z.1.size) vs sonStep (ms.foldl litStep (g,0)) 1
    (fun p i _ => by simp [sonStep])
  dsimp only at a b
  omega

theorem some_length {I O : Type} (f : I → Option O) (xs : List I) (ys : List O)
    (h : xs.mapM f = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => simpa [List.mapM_nil] using congrArg (fun q : Option (List O) => (q.getD []).length) h.symm
  | cons i xs ih =>
    rw [List.mapM_cons] at h
    cases a : f i with
    | none => simp [a] at h
    | some v =>
      cases b : xs.mapM f with
      | none => simp [a,b] at h
      | some vs =>
        simp [a,b] at h
        subst ys
        simp [ih _ b]

theorem assignments_bound (d : Instance) (K : ℕ) (hK : ∀ v, (d.menu v).length ≤ K) (s : List ℕ) :
    (assignments d s).length ≤ K^s.length := by
  induction s with
  | nil => simp [assignments]
  | cons v s ih =>
    unfold assignments
    apply Nat.le_trans (flat_length _ _ (K^s.length) (fun x _ => by simpa using ih))
    simpa [Nat.pow_succ,Nat.mul_comm] using Nat.mul_le_mul_right (K^s.length) (hK v)

theorem cut_size (vs : List ℕ) (w : ℕ) (s : List ℕ) (h : s ∈ cuts vs w) : s.length ≤ w := by
  induction vs generalizing w s with
  | nil => simp [cuts] at h; simp [h]
  | cons v vs ih =>
    cases w with
    | zero => simp [cuts] at h; simp [h]
    | succ w =>
      rw [cuts,List.mem_append] at h
      rcases h with h | h
      · exact ih _ _ h
      · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
        simpa using ih _ _ ht

theorem cuts_count (vs : List ℕ) (w : ℕ) : (cuts vs w).length ≤ (vs.length+1)^w := by
  induction vs generalizing w with
  | nil => simp [cuts]
  | cons v vs ih =>
    cases w with
    | zero => simp [cuts]
    | succ w =>
      rw [cuts,List.length_append,List.length_map,List.length_cons]
      calc
        _ ≤ (vs.length+1)^(w+1) + (vs.length+1)^w := Nat.add_le_add (ih _) (ih _)
        _ = (vs.length+1)^w * (vs.length+1+1) := by simp only [Nat.pow_succ,Nat.mul_succ]
        _ ≤ _ := by rw [Nat.pow_succ]; exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)

theorem parts_count (d : Instance) (allowed : List ℕ) : (parts d allowed).length ≤ allowed.length :=
  List.length_filterMap_le .. 

theorem refs_count (d : Instance) {V : Type} (tab : Table V) (c : List ℕ) (v : ℕ) (a : Assignment)
    (ids : List V) (h : refs d tab c v a = some ids) : ids.length ≤ c.length := by
  rw [some_length _ _ _ h]
  exact Nat.le_trans (parts_count d _) List.length_erase_le

end StableMSR.Recovery.TightLanguage


namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxHeartbeats 700000

def gateEnvelope (N M B w : ℕ) := 2+N*((N+1)^w*(N*M^w)*((N*M)*(2*B+N+2)))+N

theorem offer_bound (d : Instance) (B : ℕ) (hB : ∀ v x, (d.owned v x).length ≤ B)
    (tab : Table ℕ) (c : List ℕ) (a : Assignment) (v x : ℕ) (p : Gates × ℕ) :
    (offer (gateAlgebra d) d tab c a v x p).1.size ≤ p.1.size + (2*B+c.length+2) := by
  unfold offer
  dsimp only
  split
  · split
    next ids eq =>
      change (Array.push (body p.1 (d.owned v x) ids).1 _).size ≤ _
      rw [Array.size_push]
      have h := body_bound p.1 (d.owned v x) ids
      have k := refs_count _ _ _ _ _ _ eq
      have b := hB v x
      omega
    next => omega
  · omega

theorem collect_bound (d : Instance) (K B : ℕ) (hK : ∀ v, (d.menu v).length ≤ K)
    (hB : ∀ v x, (d.owned v x).length ≤ B) (tab : Table ℕ) (c : List ℕ) (a : Assignment)
    (g : Gates) (hc : c.length ≤ d.n) :
    (collect (gateAlgebra d) d tab c a g).1.size ≤ g.size + (d.n*K)*(2*B+d.n+2) := by
  let C := 2*B+d.n+2
  unfold collect
  have outer := fold_gain (fun p : Gates×ℕ => p.1.size) c
    (fun p v => (d.menu v).foldl (fun st x => offer (gateAlgebra d) d tab c a v x st) p)
    (g,(gateAlgebra d).fail) (K*C) (by
      intro p v _
      apply Nat.le_trans (fold_gain (fun q : Gates×ℕ => q.1.size) _ _ _ C ?_)
      · exact Nat.add_le_add_left (Nat.mul_le_mul_right C (hK v)) _
      · intro st x _
        have e := offer_bound d B hB tab c a v x st
        dsimp only [C] at *
        omega)
  apply Nat.le_trans outer
  dsimp only
  rw [←Nat.mul_assoc]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right C (Nat.mul_le_mul_right K hc)) _

theorem visit_bound (d : Instance) (K B w : ℕ) (h0 : 0<K) (hK : ∀ v, (d.menu v).length ≤ K)
    (hB : ∀ v x, (d.owned v x).length ≤ B) (k : ℕ) (s c : List ℕ)
    (p : Gates × Table ℕ) (hk : k < d.n) (hs : s.length ≤ w) :
    (visit (gateAlgebra d) d k s c p).1.size ≤ p.1.size + K^w*((d.n*K)*(2*B+d.n+2)) := by
  unfold visit
  split
  next e =>
    have e' : c.length=k+1 := by
      simp only [Bool.and_eq_true,beq_iff_eq] at e
      exact e.1
    have hb := fold_gain (fun t : Gates×Table ℕ => t.1.size) (assignments d s)
      (fun t a => install (gateAlgebra d) d c a t) p ((d.n*K)*(2*B+d.n+2))
      (fun t a _ => collect_bound d K B hK hB t.2 c a t.1 (by omega))
    exact Nat.le_trans hb (Nat.add_le_add_left (Nat.mul_le_mul_right _
      (Nat.le_trans (assignments_bound d K hK s) (Nat.pow_le_pow_right h0 hs))) _)
  next => omega

theorem table_count (d : Instance) (w K B : ℕ) (h0 : 0<K) (hK : ∀ v, (d.menu v).length ≤ K)
    (hB : ∀ v x, (d.owned v x).length ≤ B) :
    (build (gateAlgebra d) d w).1.size ≤ 2+d.n*((d.n+1)^w*(d.n*K^w)*((d.n*K)*(2*B+d.n+2))) := by
  let vs := vertices d
  let seps := cuts vs (min w d.n)
  let C := (d.n*K)*(2*B+d.n+2)
  let V := K^w*C
  have hv : vs.length ≤ d.n := by
    exact Nat.le_trans (List.length_filter_le ..) (by simp)
  have hs : seps.length ≤ (d.n+1)^w := Nat.le_trans (cuts_count vs _) (Nat.le_trans
    (Nat.pow_le_pow_left (by omega : vs.length+1 ≤ d.n+1) _) (Nat.pow_le_pow_right (by omega) (Nat.min_le_left ..)))
  have hkey (s : List ℕ) : (keysFor d vs s).length ≤ d.n := Nat.le_trans
    (parts_count d _) (Nat.le_trans (List.length_filter_le ..) hv)
  have per (p : Gates×Table ℕ) (k : ℕ) (hk : k∈List.range d.n) (s : List ℕ) (hmem : s∈seps) :
      ((keysFor d vs s).foldl (fun t c => visit (gateAlgebra d) d k s c t) p).1.size ≤ p.1.size+d.n*V := by
    apply Nat.le_trans (fold_gain (fun t : Gates×Table ℕ => t.1.size) _ _ _ V
      (fun t c _ => visit_bound d K B w h0 hK hB k s c t (List.mem_range.mp hk)
        (Nat.le_trans (cut_size vs _ s hmem) (Nat.min_le_left ..))))
    exact Nat.add_le_add_left (Nat.mul_le_mul_right V (hkey s)) _
  let step := fun (p : Gates×Table ℕ) (k : ℕ) => seps.foldl (fun z s =>
    (keysFor d vs s).foldl (fun t c => visit (gateAlgebra d) d k s c t) z) p
  have mid (p : Gates×Table ℕ) (k : ℕ) (hk : k∈List.range d.n) :
      (step p k).1.size ≤ p.1.size+(d.n+1)^w*(d.n*V) := by
    apply Nat.le_trans (fold_gain (fun t : Gates×Table ℕ => t.1.size) _ _ _ (d.n*V)
      (fun t s ht => per t k hk s ht))
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hs) _
  have top := fold_gain (fun t : Gates×Table ℕ => t.1.size) (List.range d.n) step
    ((gateAlgebra d).initial,[]) ((d.n+1)^w*(d.n*V)) mid
  change ((List.range d.n).foldl step ((gateAlgebra d).initial,[])).1.size ≤ _
  have base : (gateAlgebra d).initial.size=2 := rfl
  simpa only [base,V,C,List.length_range,Nat.mul_assoc] using top

theorem circuit_count (d : Instance) (w K B : ℕ) (h0 : 0<K) (hK : ∀ v, (d.menu v).length ≤ K)
    (hB : ∀ v x, (d.owned v x).length ≤ B) :
    (compileRegion d w).1.size ≤ gateEnvelope d.n K B w := by
  rw [source_eq,normalized]
  let st := build (gateAlgebra d) d w
  have ht := table_count d w K B h0 hK hB
  change st.1.size ≤ _ at ht
  have hp : (parts d (vertices d)).length ≤ d.n := Nat.le_trans (parts_count d _)
    (Nat.le_trans (List.length_filter_le ..) (by simp))
  unfold scan
  dsimp only
  rw [← show st = build (gateAlgebra d) d w from rfl]
  split
  next ids eq =>
    have he := some_length _ _ _ eq
    have hb := body_bound st.1 [] ids
    change (body st.1 [] ids).1.size ≤ _
    simp only [List.length_nil,Nat.mul_zero,Nat.add_zero] at hb
    unfold gateEnvelope
    omega
  next =>
    unfold gateEnvelope
    dsimp only
    omega

end StableMSR.Recovery.TightLanguage


namespace StableMSR.Recovery.TightLanguage
open OracleQueries SingleCircuit SingleCodes
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

def menuLimit (n h : ℕ) := (h+1)*n^(2*(h+1))

theorem integer_gate_count (x : World) (W : Cluster x.n) (R : ℝ) (h w : ℕ) (hn : 1 ≤ x.n) :
    (regionalCircuit x W R h w).1.size ≤ gateEnvelope x.n (menuLimit x.n h) x.n w := by
  let K := menuLimit x.n h
  have pos : 0<K := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  have words : (SingleCodes.words x.n h).length ≤ K := by
    apply (flat_length _ _ (CartesianBallRows.rows x.n (h+1)) ?_).trans
    · simp [K,menuLimit,CartesianBallRows.rows]
    · intro a ha; simp
  apply circuit_count _ _ K x.n pos
  · intro v
    simp only [SingleCodes.instanceOf,SingleCodes.lookup]
    split
    · exact (List.length_filter_le ..).trans words
    · simp
  · intro v a
    simp only [SingleCodes.instanceOf,SingleCodes.lookup]
    split
    · simp only [blockList,List.length_map,Finset.length_toList]
      apply (Finset.card_filter_le ..).trans
      apply Finset.card_image_le.trans
      simpa using (Finset.card_le_univ (WindowCSP.window x.dist W R ⟨v,by assumption⟩))
    · simp


theorem envelope_power (n h w : ℕ) (hn:2≤n) :
    gateEnvelope n (menuLimit n h) n w ≤ n^(15*((h+1)*(w+1))) := by
  let p:=(h+1)*(w+1)
  let A:=n^p
  have h1:1≤h+1:=by omega
  have w1:1≤w+1:=by omega
  have hw:h+1≤p:=Nat.le_mul_of_pos_right _ w1
  have wp:w≤p:=by have e:=Nat.le_mul_of_pos_left (w+1) h1;omega
  have pp:1≤p:=h1.trans hw
  have na:n≤A:=by simpa [A] using (Nat.pow_le_pow_right (show 1≤n by omega) pp)
  have aa:2≤A:=hn.trans na
  have k: menuLimit n h≤n^(3*(h+1)) := by
    have hh:h+1≤n^(h+1):=(Nat.le_of_lt (Nat.lt_two_pow_self (n:=h+1))).trans (Nat.pow_le_pow_left hn _)
    calc _ ≤ n^(h+1)*n^(2*(h+1)) := Nat.mul_le_mul_right _ hh
         _ = _ := by rw [←pow_add];congr 1;omega
  have kw:(menuLimit n h)^w≤A^3 := by
    apply (Nat.pow_le_pow_left k w).trans
    rw [←pow_mul,show A^3=n^(p*3) from (pow_mul ..).symm]
    apply Nat.pow_le_pow_right (by omega)
    dsimp [p];nlinarith
  have k0:menuLimit n h≤A^3:=by
    apply k.trans
    rw [show A^3=n^(p*3) from (pow_mul ..).symm]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have nw:(n+1)^w≤A^2 := by
    have plus:n+1≤n^2:=by nlinarith [Nat.mul_le_mul_right n hn]
    apply (Nat.pow_le_pow_left plus w).trans
    rw [←pow_mul,show A^2=n^(p*2) from (pow_mul ..).symm]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have three:2*n+n+2≤A^3 := by
    have sq:2*A≤A*A:=Nat.mul_le_mul_right A aa
    have cube:2*(A*A)≤A*(A*A):=Nat.mul_le_mul_right _ aa
    nlinarith
  have big:n*((n+1)^w*(n*(menuLimit n h)^w)*((n*menuLimit n h)*(2*n+n+2)))≤A^14 := by
    calc _ ≤ A*(A^2*(A*A^3)*((A*A^3)*A^3)) := Nat.mul_le_mul na (Nat.mul_le_mul
              (Nat.mul_le_mul nw (Nat.mul_le_mul na kw)) (Nat.mul_le_mul (Nat.mul_le_mul na k0) three))
         _ = _ := by ring
  have rest:2+n≤A^14 := by
    apply (show 2+n≤A^2 by nlinarith [Nat.mul_le_mul_right A aa]).trans
    exact Nat.pow_le_pow_right (by omega) (by decide)
  change 2+_+n≤_
  calc _ ≤ A^14+A^14 := by omega
       _ = 2*A^14 := by omega
       _ ≤ A*A^14 := Nat.mul_le_mul_right _ aa
       _ = A^15 := by ring
       _ = n^(15*p) := by rw [show A^15=n^(p*15) from (pow_mul ..).symm,Nat.mul_comm p]
theorem uniform_live_gate_bound (x : World) (u i : ℕ) (e : ℚ) (he:0<e) (hl:e<1) (hn:2≤x.n) :
    (regionalCircuit x (WindowProfiles.piece x u i) (WindowCSP.scale x u) (WindowCSP.budget (e:ℝ)) (widthBound (e:ℝ))).1.size≤x.n^(75*parameterEnvelope (e:ℝ)) := by
  have realPos:0<(e:ℝ):=by exact_mod_cast he
  have realLt:(e:ℝ)<1:=by exact_mod_cast hl
  have ow:1≤ownerBound (e:ℝ) := by
    unfold ownerBound
    apply Nat.le_floor
    push_cast
    exact (le_div_iff₀ realPos).2 (by linarith)
  apply (integer_gate_count x _ _ _ _ (by omega)).trans
  apply (envelope_power _ _ _ hn).trans
  apply Nat.pow_le_pow_right (by omega)
  have b:WindowCSP.budget (e:ℝ)+1≤5*ownerBound (e:ℝ):=by unfold WindowCSP.budget;omega
  have c:=Nat.mul_le_mul_right (widthBound (e:ℝ)+1) b
  unfold parameterEnvelope
  nlinarith
end StableMSR.Recovery.TightLanguage

namespace StableMSR.Recovery.SingleRAM
open OracleQueries WindowCSP WindowProfiles
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem raw_gate_count (x : World) (h w R M : ℕ)
    (per : ∀ u i, (SingleCodes.regionalCircuit x (WindowProfiles.piece x u i) (scale x u) h w).1.size ≤ M) :
    (rawAssembly x h w R).gates.size ≤ 2+R*M := by
  have step (a : Assembly) (r : ℕ) : (appendRegion x h w r a).gates.size ≤ a.gates.size+M := by
    unfold appendRegion
    dsimp only
    split
    · split
      · simp only [Array.size_append,Array.size_map]
        exact Nat.add_le_add_left (per _ _) _
      · exact Nat.le_add_right _ _
    · exact Nat.le_add_right _ _
  have g := TightLanguage.fold_gain (fun a : Assembly => a.gates.size) (List.range R)
    (fun a r => appendRegion x h w r a) emptyAssembly M (fun a r _ => step a r)
  simpa only [rawAssembly,List.length_range,show emptyAssembly.gates.size=2 by rfl] using g

theorem global_assembly_resource_bound (x : World) (e : ℚ)
    (he : 0 < e) (hl : e < 1) (hn : 2 ≤ x.n) :
    let G := (globalAssembly x (budget (e:ℝ)) (widthBound (e:ℝ))).gates.size
    let A := x.n^(75*parameterEnvelope (e:ℝ))
    G ≤ 2+x.rows*x.n*A ∧
    2+5*(1+3*G*x.n*x.n) ≤ 52*x.cap^4*A ∧
    82+42*G+7*(G*x.n) ≤ 256*x.cap^3*A := by
  let h:=budget (e:ℝ)
  let w:=widthBound (e:ℝ)
  let A:=x.n^(75*parameterEnvelope (e:ℝ))
  let R:=x.rows*x.n
  let G:=(globalAssembly x h w).gates.size
  let cp:=x.cap
  have pos:1≤A:=Nat.pow_pos (by omega)
  have raw : (rawAssembly x h w R).gates.size ≤ 2+R*A :=
    raw_gate_count _ _ _ _ _ (fun u i => TightLanguage.uniform_live_gate_bound x u i e he hl hn)
  have pad : (R+2)/3 ≤ 2+R*A := by
    have lt := Nat.le_mul_of_pos_right R pos
    omega
  have bg : G ≤ 2+R*A := by
    change (padAssembly (rawAssembly x h w R) R).gates.size ≤ _
    simp only [padAssembly,Array.size_append,Array.size_replicate]
    omega
  have hp:1≤cp:=by dsimp [cp,World.cap];omega
  have nx:x.n≤cp:=by dsimp [cp,World.cap];omega
  have sx:x.rows≤cp:=by dsimp [cp,World.cap];omega
  have p1 (t : ℕ) : 1≤cp^t*A:=Nat.mul_pos (Nat.pow_pos hp) pos
  have p2:x.n*x.n≤cp^4*A:=by
    calc x.n*x.n ≤ cp*cp := Nat.mul_le_mul nx nx
         _ = cp^2 := by ring
         _ ≤ cp^4 := Nat.pow_le_pow_right hp (by decide)
         _ ≤ _ := Nat.le_mul_of_pos_right _ pos
  have p3:R*x.n*x.n*A≤cp^4*A:=by
    apply Nat.mul_le_mul_right
    calc R*x.n*x.n ≤ cp*cp*cp*cp := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul sx nx) nx) nx
         _ = _ := by ring
  have n3:x.n≤cp^3*A:=by
    calc x.n ≤ cp^1 := by simpa using nx
         _ ≤ cp^3 := Nat.pow_le_pow_right hp (by decide)
         _ ≤ _ := Nat.le_mul_of_pos_right _ pos
  have r3:R*x.n*A ≤ cp^3*A := by
    apply Nat.mul_le_mul_right
    calc R*x.n ≤ cp*cp*cp := Nat.mul_le_mul (Nat.mul_le_mul sx nx) nx
         _ = _ := by ring
  have gg:G*x.n≤2*x.n+R*x.n*A:=by
    calc _ ≤ (2+R*A)*x.n := Nat.mul_le_mul_right _ bg
         _ = _ := by ring
  have g0:G≤G*x.n:=Nat.le_mul_of_pos_right _ (by omega)
  refine ⟨bg,?_,?_⟩
  · change 2+5*(1+3*G*x.n*x.n)≤52*cp^4*A
    calc _ ≤ 2+5*(1+3*(2+R*A)*x.n*x.n) := by gcongr
         _ = 7+30*(x.n*x.n)+15*(R*x.n*x.n*A) := by ring
         _ ≤ 52*(cp^4*A) := by have := p1 4;omega
         _ = _ := by ring
  · change 82+42*G+7*(G*x.n)≤256*cp^3*A
    rw [Nat.mul_assoc 256]
    have := p1 3
    omega

end StableMSR.Recovery.SingleRAM

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 15000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleCodes
open StableMSR.Recovery.WindowProfiles (piece keys)
open StableMSR.Recovery.SingleWindows
open StableMSR.Recovery.SingleRAM
theorem solution (x : World) (e : ℚ)
    (he : 0 < e) (hl : e < 1) (hn : 2 ≤ x.n) :
    let G := (globalAssembly x (budget (e:ℝ)) (widthBound (e:ℝ))).gates.size
    let A := x.n^(75*parameterEnvelope (e:ℝ))
    G ≤ 2+x.rows*x.n*A ∧
    2+5*(1+3*G*x.n*x.n) ≤ 52*x.cap^4*A ∧
    82+42*G+7*(G*x.n) ≤ 256*x.cap^3*A := StableMSR.Recovery.SingleRAM.global_assembly_resource_bound x e he hl hn
