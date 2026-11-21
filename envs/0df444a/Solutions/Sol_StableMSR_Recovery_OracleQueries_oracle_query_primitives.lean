-- Prove2me | solution 1 for StableMSR.Recovery.OracleQueries.oracle_query_primitives
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T20:32:12.372838+00:00
-- url     : https://prove2.me/submissions/1f76174f-a1f8-440a-8b63-6cdeeef183a8

import Definitions.Def_StableMSR_OracleQueries
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open Polynomial
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
private lemma axSmall (a : Axis) : a.reg < 3 := by cases a <;> decide
private lemma keepReady {x : World} {b : ℕ} {s t : Store} (hb : 3 ≤ b) (h : Keeps b s t) (r : Ready x s) : Ready x t :=
  ⟨fun a=>(h.1 _ (lt_of_lt_of_le (axSmall a) hb)).1.trans (r.1 a),fun i=>by rw [h.2];exact r.2 i⟩
private lemma keepTrans {b : ℕ} {u v t : Store} (h : Keeps b u v) (k : Keeps b v t) : Keeps b u t :=
  ⟨fun i hi=>⟨(k.1 i hi).1.trans (h.1 i hi).1,(k.1 i hi).2.trans (h.1 i hi).2⟩,k.2.trans h.2⟩
private lemma keepDown {b c : ℕ} {s t : Store} (h : Keeps c s t) (le : b ≤ c) : Keeps b s t :=
  ⟨fun i hi=>h.1 i (lt_of_lt_of_le hi le),h.2⟩
private def pair (i j : Op) : Cmd := .seq (.atom i) (.atom j)
private lemma writePair (x : World) (s : Store) (b : ℕ) (a : Op) (z : ℤ)
    (ea : (a.eval x.dist s)={s with ptrs:=Function.update s.ptrs b z}) :
    ∃t, Executes x.dist (pair a (.realConst b 0)) s t 2 ∧ Keeps b s t ∧ (t.ptrs b,t.regs b)=iv z := by
  refine ⟨_,.seq (.atom _ _) (.atom _ _),⟨?_,by change (a.eval x.dist s).imem=s.imem;rw [ea]⟩,?_⟩
  · intro i hi;simp only [ea];simp [Op.eval,Function.update_of_ne (ne_of_lt hi)]
  · simp only [ea];simp [Op.eval,iv]
private noncomputable def primCmd (p : Prim) (b : ℕ) : Cmd :=
  match p with
  | .add => pair (.pointerAdd b b (b+1)) (.realAdd b b (b+1))
  | .query => pair (.distance b b (b+1)) (.pointerConst b 0)
  | .read => .seq (.atom (.pointerConst (b+1) 0)) (.seq
      (.ite (.pointerLE (b+1) b) .skip (.atom (.pointerConst b 0))) (pair (.integerLoad b b) (.realConst b 0)))
  | .ile => .ite (.pointerLE b (b+1)) (pair (.pointerConst b 1) (.realConst b 0)) (pair (.pointerConst b 0) (.realConst b 0))
  | .rle => .seq (.atom (.realSub b b (b+1))) (.ite (.realNonpos b) (pair (.pointerConst b 1) (.realConst b 0)) (pair (.pointerConst b 0) (.realConst b 0)))
private lemma primRun (x : World) (b : ℕ) (p : Prim) (s : Store) (mem : ∀i : ℕ,s.imem (i:ℤ)=x.mem i) :
    ∃t z,Executes x.dist (primCmd p b) s t z ∧ Keeps b s t ∧
      (t.ptrs b,t.regs b)=p.val x (s.ptrs b,s.regs b) (s.ptrs (b+1),s.regs (b+1)) ∧ z ≤ 8 := by
  have wr (s' : Store) (j : ℤ) := writePair x s' b (.pointerConst b j) j rfl
  cases p with
  | add =>
    refine ⟨_,_,Executes.seq (.atom _ _) (.atom _ _),⟨?_,rfl⟩,?_,by decide⟩
    · intro i hi;simp [Op.eval,Function.update_of_ne (ne_of_lt hi)]
    · simp [Op.eval,Prim.val]
  | query =>
    refine ⟨_,_,Executes.seq (.atom _ _) (.atom _ _),⟨?_,rfl⟩,?_,by decide⟩
    · intro i hi;simp [Op.eval,Function.update_of_ne (ne_of_lt hi)]
    · simp [Op.eval,Prim.val,rv]
  | ile =>
    by_cases h : s.ptrs b ≤ s.ptrs (b+1)
    · obtain ⟨t,ex,k,v⟩ := wr s 1
      exact ⟨t,_,.ite_true h ex,k,by simpa [Prim.val,flag,h] using v,by decide⟩
    · obtain ⟨t,ex,k,v⟩ := wr s 0
      exact ⟨t,_,.ite_false h ex,k,by simpa [Prim.val,flag,h] using v,by decide⟩
  | rle =>
    let u := (Op.realSub b b (b+1)).eval x.dist s
    have ku : Keeps b s u := ⟨fun i hi=>by simp [u,Op.eval,Function.update_of_ne (ne_of_lt hi)],rfl⟩
    have test : (Cond.realNonpos b).test u ↔ s.regs b ≤ s.regs (b+1) := by simp [Cond.test,u,Op.eval]
    by_cases h : s.regs b ≤ s.regs (b+1)
    · obtain ⟨t,ex,k,v⟩ := wr u 1
      exact ⟨t,_,.seq (.atom _ _) (.ite_true (test.mpr h) ex),keepTrans ku k,by simpa [Prim.val,flag,h] using v,by decide⟩
    · obtain ⟨t,ex,k,v⟩ := wr u 0
      exact ⟨t,_,.seq (.atom _ _) (.ite_false (mt test.mp h) ex),keepTrans ku k,by simpa [Prim.val,flag,h] using v,by decide⟩
  | read =>
    let u := (Op.pointerConst (b+1) 0).eval x.dist s
    have ku : Keeps b s u := ⟨fun i hi=>by simp [u,Op.eval,Function.update_of_ne (by omega : i ≠ b+1)],rfl⟩
    have test : (Cond.pointerLE (b+1) b).test u ↔ 0 ≤ s.ptrs b := by simp [Cond.test,u,Op.eval]
    have tail (w : Store) (pw : w.ptrs b=(s.ptrs b).toNat) (kw : Keeps b s w) :
        ∃ t,Executes x.dist (pair (.integerLoad b b) (.realConst b 0)) w t 2 ∧ Keeps b s t ∧
          (t.ptrs b,t.regs b)=iv (x.mem (s.ptrs b).toNat) := by
      obtain ⟨t,ex,k,v⟩ := writePair x w b (.integerLoad b b) (w.imem (w.ptrs b)) rfl
      exact ⟨t,ex,keepTrans kw k,by simpa only [kw.2,pw,mem] using v⟩
    by_cases h : 0 ≤ s.ptrs b
    · obtain ⟨t,ex,k,v⟩ := tail u (by simp [u,Op.eval,Int.toNat_of_nonneg h]) ku
      exact ⟨t,_,.seq (.atom _ _) (.seq (.ite_true (test.mpr h) (.skip _)) ex),k,v,by decide⟩
    · let w := (Op.pointerConst b 0).eval x.dist u
      have kw : Keeps b u w := ⟨fun i hi=>by simp [w,Op.eval,Function.update_of_ne (ne_of_lt hi)],rfl⟩
      obtain ⟨t,ex,k,v⟩ := tail w (by simp [w,Op.eval,Int.toNat_of_nonpos (by omega : s.ptrs b ≤ 0)]) (keepTrans ku kw)
      exact ⟨t,_,.seq (.atom _ _) (.seq (.ite_false (mt test.mp h) (.atom _ _)) ex),k,v,by decide⟩

theorem solution : (∀z : ℤ,Engine (fun _ _=>iv z)) ∧
    (∀i : ℕ,Engine (fun _ ρ=>iv (ρ i))) ∧ (∀a : Axis, Engine (fun x _=>iv (x.size a))) ∧
    (∀ (v : Prim) (f g : Term),Engine f → Engine g → Engine (fun x ρ=>v.val x (f x ρ) (g x ρ))) ∧
    (∀f g h : Term,Engine f → Engine g → Engine h →
      Engine (fun x ρ=>if 1 ≤ (f x ρ).1 then g x ρ else h x ρ)) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro z
    refine ⟨C 2,fun b src hb hsrc=>⟨pair (.pointerConst b z) (.realConst b 0),?_⟩⟩
    intro x s ρ _ _
    obtain ⟨t,ex,k,v⟩ := writePair x s b (.pointerConst b z) z rfl
    exact ⟨t,2,ex,k,v,by simp⟩
  · intro i
    refine ⟨C 2,fun b src hb hsrc=>⟨pair (.pointerCopy b (src i)) (.realConst b 0),?_⟩⟩
    intro x s ρ _ hr
    obtain ⟨t,ex,k,v⟩ := writePair x s b (.pointerCopy b (src i)) _ rfl
    exact ⟨t,2,ex,k,by simpa only [hr] using v,by simp⟩
  · intro a
    refine ⟨C 2,fun b src hb hsrc=>⟨pair (.pointerCopy b a.reg) (.realConst b 0),?_⟩⟩
    intro x s ρ hr _
    obtain ⟨t,ex,k,v⟩ := writePair x s b (.pointerCopy b a.reg) _ rfl
    exact ⟨t,2,ex,k,by simpa only [hr.1] using v,by simp⟩
  · rintro p f g ⟨a,ha⟩ ⟨c,hc⟩
    refine ⟨a+c+C 8,?_⟩
    intro b src hb hs
    obtain ⟨F,ef⟩ := ha b src hb hs
    obtain ⟨G,eg⟩ := hc (b+1) src (by omega) (fun i=>(hs i).trans (Nat.lt_succ_self _))
    refine ⟨.seq F (.seq G (primCmd p b)),?_⟩
    intro x s ρ rs rr
    obtain ⟨u,i,ei,ki,vi,ti⟩ := ef x s ρ rs rr
    obtain ⟨v,j,ej,kj,vj,tj⟩ := eg x u ρ (keepReady hb ki rs) (fun i=>(ki.1 _ (hs i)).1.trans (rr i))
    obtain ⟨t,l,el,kl,vl,tl⟩ := primRun x b p v (fun i=>by rw [kj.2,ki.2];exact rs.2 i)
    have eq : (v.ptrs b,v.regs b)=f x ρ := (Prod.ext (kj.1 b (by omega)).1 (kj.1 b (by omega)).2).trans vi
    exact ⟨t,_,.seq ei (.seq ej el),keepTrans ki (keepTrans (keepDown kj (by omega)) kl),
      by simpa only [eq,vj] using vl,by simp only [eval_add,eval_C];omega⟩
  · rintro f g h ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩
    refine ⟨a+b+c+C 4,?_⟩
    intro j src hj hs
    obtain ⟨F,ef⟩ := ha j src hj hs
    obtain ⟨G,eg⟩ := hb j src hj hs
    obtain ⟨H,eh⟩ := hc j src hj hs
    let one := Op.pointerConst (j+1) 1
    let cond := Cond.pointerLE (j+1) j
    refine ⟨.seq F (.seq (.atom one) (.ite cond G H)),?_⟩
    intro x s ρ rs rr
    obtain ⟨u,i,ei,ki,vi,ti⟩ := ef x s ρ rs rr
    let v := one.eval x.dist u
    have kv : Keeps j u v := ⟨fun l hl=>by simp [v,one,Op.eval,Function.update_of_ne (by omega : l ≠ j+1)],rfl⟩
    have kk := keepTrans ki kv
    have test : cond.test v ↔ 1 ≤ (f x ρ).1 := by
      have hi : u.ptrs j=(f x ρ).1 := congrArg Prod.fst vi
      simp [cond,v,one,Op.eval,Cond.test,hi]
    have rr' (l : ℕ) := (kk.1 _ (hs l)).1.trans (rr l)
    by_cases pos : 1 ≤ (f x ρ).1
    · obtain ⟨t,l,el,kl,vl,tl⟩ := eg x v ρ (keepReady hj kk rs) rr'
      exact ⟨t,_,.seq ei (.seq (.atom _ _) (.ite_true (test.mpr pos) el)),keepTrans kk kl,
        by simpa [pos] using vl,by simp only [eval_add,eval_C];omega⟩
    · obtain ⟨t,l,el,kl,vl,tl⟩ := eh x v ρ (keepReady hj kk rs) rr'
      exact ⟨t,_,.seq ei (.seq (.atom _ _) (.ite_false (mt test.mp pos) el)),keepTrans kk kl,
        by simpa [pos] using vl,by simp only [eval_add,eval_C];omega⟩
