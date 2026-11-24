-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.unfiltered_scan_is_exact
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T23:39:48.645798+00:00
-- url     : https://prove2.me/submissions/059dac8b-2486-4b53-a635-5c6d45c42014

import Definitions.Def_StableMSR_UnfilteredSeparatorCandidates
set_option linter.all false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates
open SingleCircuit TightLanguage
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 16000

def readKey (t:Table ℕ) (k:Key) := TightLanguage.lookup t k.1 k.2
def aligned (enc:Key→ℕ) (t:Table ℕ) (d:ℕ→Option ℕ) := ∀k,d (enc k)=readKey t k

theorem read_insert (enc:Key→ℕ) (inj:Function.Injective enc) (k:Key) (v:ℕ) (t:Table ℕ) (d:ℕ→Option ℕ)
    (h:aligned enc t d) : aligned enc ((k,v)::t) (Function.update d (enc k) (some v)) := by
  rintro ⟨c,a⟩
  by_cases eq:k=(c,a)
  · subst k;simp [readKey,TightLanguage.lookup]
  · have ne:enc (c,a)≠enc k:=fun z=>eq (inj z).symm
    simpa [readKey,TightLanguage.lookup,List.find?_cons,eq,Function.update_of_ne ne] using h (c,a)

theorem lits_fold (ms:List (List ℕ)) (s:Work) :
    (ms.map Instr.lit).foldl step s={s with stage:=s.stage++ms.map Event.mask} := by
  induction ms generalizing s with
  | nil=>simp
  | cons m ms ih=>simp [ih,step,List.append_assoc]

theorem need_fold (ks:List ℕ) (s:Work) :
    (ks.map Instr.need).foldl step s={s with
      stage:=s.stage++ks.map (fun k=>Event.child ((s.dict k).getD 0)),
      ok:=s.ok && ks.all (fun k=>(s.dict k).isSome)} := by
  induction ks generalizing s with
  | nil=>simp
  | cons k ks ih=>simp [ih,step,List.append_assoc,Bool.and_assoc]

theorem option_rows {A:Type} (ks:List A) (f:A→Option ℕ) :
    ks.mapM f=(if ks.all (fun k=>(f k).isSome) then some (ks.map (fun k=>(f k).getD 0)) else none) := by
  induction ks with
  | nil=>rfl
  | cons k ks ih=>cases h:f k <;> cases a:ks.all (fun k=>(f k).isSome) <;> simp [List.mapM_cons,ih,h,a]

theorem refs_list (enc:Key→ℕ) (d:Instance) (tab:Table ℕ) (f:ℕ→Option ℕ)
    (c:List ℕ) (v:ℕ) (row:Assignment) (h:aligned enc tab f) :
    refs d tab c v row=(children d c v row).mapM (fun k=>f (enc k)) := by
  unfold aligned at h
  simp [children,List.mapM_map,Function.comp_def,h,readKey,refs]

def fresh (es:List Event) (v ex:ℕ) (table:ℕ→Option ℕ) : Work := ⟨es,[],true,v,ex,table⟩

theorem trial_run (enc:Key→ℕ) (d:Instance) (tab:Table ℕ) (f:ℕ→Option ℕ) (ex:ℕ) (syn:aligned enc tab f)
    (c:List ℕ) (a:Assignment) (v x:ℕ) (p:List Event×ℕ) :
    (trial enc d c a v x).foldl step (fresh p.1 p.2 ex f)=
    let z:=offer (chartAlgebra d) d tab c a v x p
    fresh z.1 z.2 ex f := by
  let ks:=children d c v ((v,x)::a)
  let available:=fun k:Key=>(f (enc k)).isSome
  have rr:=refs_list enc d tab f c v ((v,x)::a) syn
  rw [option_rows] at rr
  change refs d tab c v ((v,x)::a)=(if ks.all available then _ else _) at rr
  unfold trial offer
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
  rw [show (children d c v ((v,x)::a)).map (fun k=>Instr.need (enc k))=(ks.map enc).map Instr.need by simp [ks,List.map_map,Function.comp_def]]
  change step (((ks.map enc).map Instr.need).foldl step (((d.owned v x).map Instr.lit).foldl step (fresh p.1 p.2 ex f))) (.close (localOK d ((v,x)::a)))=_
  rw [lits_fold,need_fold]
  cases ok:localOK d ((v,x)::a) <;> cases al:ks.all available <;>
    simp [fresh,step,buffer,chartAlgebra,ok,rr,al,List.map_map,Function.comp_def,available,List.append_assoc] at *
  exact ⟨rfl,rfl⟩

theorem collect_run (enc:Key→ℕ) (d:Instance) (tab:Table ℕ) (f:ℕ→Option ℕ) (ex:ℕ) (syn:aligned enc tab f)
    (c:List ℕ) (a:Assignment) (es:List Event) :
    (c.flatMap (fun v=>(d.menu v).flatMap (trial enc d c a v))).foldl step (fresh es 0 ex f)=
      let z:=collect (chartAlgebra d) d tab c a es
      fresh z.1 z.2 ex f := by
  unfold collect;rw [List.foldl_flatMap]
  have eq (xs:List ℕ) (p:List Event×ℕ) :
     xs.foldl (fun s v=>((d.menu v).flatMap (trial enc d c a v)).foldl step s) (fresh p.1 p.2 ex f)=
       let z:=xs.foldl (fun q v=>(d.menu v).foldl (fun b x=>offer (chartAlgebra d) d tab c a v x b) q) p
       fresh z.1 z.2 ex f := by
    induction xs generalizing p with
    | nil=>rfl
    | cons v xs ih=>
      have menu (ys:List ℕ) (p:List Event×ℕ) :
          (ys.flatMap (trial enc d c a v)).foldl step (fresh p.1 p.2 ex f)=
          let z:=ys.foldl (fun b x=>offer (chartAlgebra d) d tab c a v x b) p
          fresh z.1 z.2 ex f := by
        induction ys generalizing p with
        | nil=>rfl
        | cons y ys im=>simp only [List.flatMap_cons,List.foldl_append,List.foldl_cons,trial_run enc d tab f ex syn,im]
      simp only [List.foldl_cons,menu,ih]
  exact eq c (es,0)

def Rows (enc:Key→ℕ) (s:Work) (p:List Event×Table ℕ) :=
  s=fresh p.1 0 0 s.dict ∧ aligned enc p.2 s.dict

theorem entry_run (enc:Key→ℕ) (inj:Function.Injective enc) (d:Instance) (c:List ℕ) (a:Assignment)
    (s:Work) (p:List Event×Table ℕ) (h:Rows enc s p) :
    Rows enc ((entry enc d c a).foldl step s) (install (chartAlgebra d) d c a p) := by
  obtain ⟨clean,ok⟩:=h
  unfold entry install
  rw [List.foldl_append,clean,collect_run enc d p.2 s.dict 0 ok]
  exact ⟨rfl,read_insert enc inj _ _ _ _ ok⟩

theorem fold_pair {A B I:Type} (R:A→B→Prop) (u:A→I→A) (v:B→I→B)
    (s:List I) (x:A) (y:B) (h:R x y) (next:∀x y i,R x y→R (u x i) (v y i)) :
    R (s.foldl u x) (s.foldl v y) := by
  induction s generalizing x y with
  | nil=>exact h
  | cons i is ih=>exact ih _ _ (next _ _ _ h)

theorem rows_run (enc:Key→ℕ) (inj:Function.Injective enc) (d:Instance) (w:ℕ) :
    Rows enc ((rowTape enc d w).foldl step start) (build (chartAlgebra d) d w) := by
  unfold rowTape build;dsimp only
  simp only [List.foldl_flatMap]
  apply fold_pair _ _ _ _ _ _ ⟨rfl,fun _=>rfl⟩
  intro x y k h
  apply fold_pair _ _ _ _ _ _ h
  intro x y s h
  apply fold_pair _ _ _ _ _ _ h
  intro x y c h
  unfold visitTape visit;split
  · rw [List.foldl_flatMap];apply fold_pair _ _ _ _ _ _ h
    intro x y a ha;exact entry_run enc inj d c a x y ha
  · exact h

theorem candidate_exact (enc:Key→ℕ) (inj:Function.Injective enc) (d:Instance) (w:ℕ) :
    eval (tape enc d w)=⟨(chart d w).1,((chart d w).2:ℤ)⟩ := by
  let t:=(rowTape enc d w).foldl step start
  let b:=build (chartAlgebra d) d w
  let cs:=parts d (vertices d)
  obtain ⟨clean,ok⟩:=rows_run enc inj d w
  change t=fresh b.1 0 0 t.dict at clean
  have lt:(cs.mapM (fun c=>TightLanguage.lookup b.2 c []))=
      (if cs.all (fun c=>(t.dict (enc (c,[]))).isSome) then some (cs.map (fun c=>(t.dict (enc (c,[]))).getD 0)) else none):=by
    have h (c:List ℕ) : TightLanguage.lookup b.2 c []=t.dict (enc (c,[])) := (ok (c,[])).symm
    simp_rw [h];apply option_rows
  unfold eval tape chart scan;dsimp only
  rw [List.foldl_append,List.foldl_append]
  rw [show (parts d (vertices d)).map (fun c=>Instr.need (enc (c,[])))=(cs.map (fun c=>enc (c,[]))).map Instr.need by simp [cs,List.map_map,Function.comp_def]]
  change (let u:=step (((cs.map (fun c=>enc (c,[]))).map Instr.need).foldl step t) .finish; Script.mk u.done (u.exit:ℤ))=_
  rw [need_fold]
  generalize hk:cs.all (fun c=>(t.dict (enc (c,[]))).isSome)=haveAll at lt
  cases haveAll <;> simp at lt
  all_goals
    have yes:t.stage=[]:=congrArg Work.stage clean
    have nice:t.ok=true:=congrArg Work.ok clean
    have initial:t.done=b.1:=congrArg Work.done clean
    simp only [←show cs=parts d (vertices d) from rfl,←show b=build (chartAlgebra d) d w from rfl,lt]
    simp [step,buffer,yes,nice,initial,chartAlgebra,List.map_map,Function.comp_def,hk,List.append_assoc]

end StableMSR.Recovery.NativeWriter.Production.Candidates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates
theorem solution (enc:Key→ℕ)
    (inj:Function.Injective enc) (d:Instance) (w:ℕ) :
    Candidates.eval (tape enc d w)=⟨(chart d w).1,((chart d w).2:ℤ)⟩ := candidate_exact enc inj d w
