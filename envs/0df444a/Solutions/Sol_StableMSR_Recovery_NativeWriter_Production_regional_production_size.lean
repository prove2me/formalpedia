-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.regional_production_size
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T23:14:35.474835+00:00
-- url     : https://prove2.me/submissions/6b9ca584-26a2-4a50-be11-30cbf519a1c2

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_ordered_production_replay
import Definitions.Def_StableMSR_RegionalProductionTable
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
namespace StableMSR.Recovery.NativeWriter.Production
open SingleCircuit SingleCodes TightLanguage OracleQueries WindowCSP Relative
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem count_events (s : State) (es : List Event) :
    s.gates.size+es.length≤(es.foldl step s).gates.size+es.count .save := by
  induction es generalizing s with
  | nil=>simp
  | cons e es ih=>
    have h:=ih (step s e)
    cases e <;> simp [step,litStep,sonStep,List.count_cons] at h ⊢ <;> omega

theorem invariant_fold {A B : Type} (J : A→Prop) (xs : List B) (f : A→B→A)
    (h : ∀a b,J a→J (f a b)) (a : A) (ok : J a) : J (xs.foldl f a) := by
  induction xs generalizing a with
  | nil=>exact ok
  | cons b xs ih=>exact ih (f a b) (h a b ok)

theorem unsaved (d : Instance) (w:ℕ) : Event.save ∉ (build (chartAlgebra d) d w).1 := by
  let J:=fun p:List Event×Table ℕ=>Event.save∉p.1
  let K:=fun p:List Event×ℕ=>Event.save∉p.1
  change J _
  unfold build
  apply invariant_fold J _ _ _ _ (by simp [J,chartAlgebra])
  intro p k hp;apply invariant_fold J _ _ _ _ hp
  intro p s hp;apply invariant_fold J _ _ _ _ hp
  intro p c hp;unfold visit;split
  · apply invariant_fold J _ _ _ _ hp
    intro p a hp
    change K (collect (chartAlgebra d) d p.2 c a p.1)
    unfold collect;apply invariant_fold K _ _ _ _ hp
    intro q v hq;apply invariant_fold K _ _ _ _ hq
    intro z x hz
    dsimp only [K,offer];split
    · split
      · simpa [K,chartAlgebra] using hz
      · exact hz
    · exact hz
  · exact hp

theorem chart_saves (d : Instance) (w:ℕ) : (chart d w).1.count .save≤1 := by
  let t:=build (chartAlgebra d) d w
  have h:t.1.count .save=0:=List.count_eq_zero.mpr (unsaved d w)
  unfold chart scan;dsimp only
  generalize hh:(parts d (vertices d)).mapM (m:=Option) (fun c=>TightLanguage.lookup (build (chartAlgebra d) d w).2 c [])=R
  cases R
  case some ids=>
    have hc:(ids.map Event.child).count .save=0 := List.count_eq_zero.mpr (by simp)
    change ((t.1++ids.map Event.child)++[Event.save]).count Event.save≤1
    simp [h,hc]
  case none=>exact Nat.le_trans (Nat.le_of_eq h) (by decide)

theorem chart_length (d : Instance) (w:ℕ) : (chart d w).1.length≤(compileRegion d w).1.size := by
  have sz:=count_events initial (chart d w).1
  have eq:=congrArg (fun p:Gates×ℕ=>p.1.size) (ordered_production_replay d w)
  change (play (chart d w).1).gates.size=(compileRegion d w).1.size at eq
  change 2+(chart d w).1.length≤(play (chart d w).1).gates.size+_ at sz
  have h:=chart_saves d w
  omega

theorem script_exact (x : World) (h w r : ℕ) : (regionalScript x h w r).packet=Relative.packet x h w r := by
  unfold regionalScript Relative.packet;dsimp only
  split
  · split
    · unfold Script.packet
      simp only [Int.natCast_nonneg,not_lt.mpr,if_false,Int.toNat_natCast]
      let d:=instanceOf x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) h
      have eq:=ordered_production_replay d w
      change Packet.mk (result (chart d w)).1 ((result (chart d w)).2:ℤ)=
        Packet.mk (compileRegion d w).1 ((compileRegion d w).2:ℤ)
      rw [eq]
    · rfl
  · rfl

theorem script_length (x : World) (e : ℚ) (r:ℕ) (he:0<e) (hl:e<1) (hn:2≤x.n) :
    (regionalScript x (budget (e:ℝ)) (widthBound (e:ℝ)) r).events.length≤x.n^(75*parameterEnvelope (e:ℝ)) := by
  unfold regionalScript;dsimp only
  split
  · split
    · exact (chart_length _ _).trans (TightLanguage.uniform_live_gate_bound x _ _ e he hl hn)
    · exact Nat.zero_le _
  · exact Nat.zero_le _

end StableMSR.Recovery.NativeWriter.Production
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit
theorem solution (x : World) (e : ℚ) (r:ℕ)
    (he:0<e) (hl:e<1) (hn:2≤x.n) :
    let h:=budget (e:ℝ)
    let w:=widthBound (e:ℝ)
    let t:=regionalScript x h w r
    t.packet=Relative.packet x h w r ∧ t.events.length≤x.n^(75*parameterEnvelope (e:ℝ)) := ⟨script_exact x _ _ r,script_length x e r he hl hn⟩
