-- Prove2me | solution 1 for PandoraKnapsack.Skipping.ArrayRAM.prepare_array_exec
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:54:59.828332+00:00
-- url     : https://prove2.me/submissions/b5f862a4-8334-4395-bc34-07dccc6b79d4

import Definitions.Def_PandoraKnapsack_Skipping_PrepareRAM
import Definitions.Def_PandoraKnapsack_Skipping_DyadicPlan

namespace PandoraKnapsack.Skipping.ArrayRAM

variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

theorem forN_inv {idx : ℕ} {bound : N} {body : C} {s : Store} {M : ℕ}
    (Inv : ℕ → Store → Prop) (h0 : Inv 0 s)
    (hs : ∀ j, j < bound.eval s → ∀ u, Inv j u →
      ∃ v k, Exec I ω body (u.setN idx j) v k ∧ k ≤ M ∧ Inv (j+1) v) :
    ∃ v k, Exec I ω (.forN idx bound body) s (v.setN idx (bound.eval s)) k ∧
      k ≤ bound.work+4+5*(bound.eval s)+(bound.eval s)*M ∧ Inv (bound.eval s) v := by
  classical
  let L := bound.eval s
  have nextExists (j : ℕ) (u : Store) : ∃ v k, j < L ∧ Inv j u →
      Exec I ω body (u.setN idx j) v k ∧ k ≤ M ∧ Inv (j+1) v := by
    by_cases h : j < L ∧ Inv j u
    · obtain ⟨v,k,hv⟩ := hs j h.1 u h.2
      exact ⟨v,k,fun _ => hv⟩
    · exact ⟨u,0,fun a => (h a).elim⟩
  choose next price hnext using nextExists
  let states : ℕ → Store := Nat.rec s (fun j u => next j u)
  have good : ∀ j, j ≤ L → Inv j (states j) := by
    intro j
    induction j with
    | zero => exact fun _ => h0
    | succ j ih =>
      intro hj
      exact (hnext j (states j) ⟨by omega,ih (by omega)⟩).2.2
  have h := Exec.forN (I := I) (ω := ω) idx bound body states (fun j => price j (states j))
    (fun j hj => (hnext j (states j) ⟨hj,good j (by exact Nat.le_of_lt hj)⟩).1)
  refine ⟨states L,_,h,?_,good L le_rfl⟩
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _j ∈ Finset.range L, M := Finset.sum_le_sum fun j hj =>
      (hnext j (states j) ⟨Finset.mem_range.mp hj, good j (Nat.le_of_lt (Finset.mem_range.mp hj))⟩).2.1
    _ = _ := by simp [L]

end PandoraKnapsack.Skipping.ArrayRAM

namespace PandoraKnapsack.Skipping.ArrayRAM

inductive Slot
  | nat (reg : ℕ)
  | real (reg : ℕ)
  | table (key : Fin 16)
  | out
  | draws
deriving DecidableEq

def Slot.Val : Slot → Type
  | .nat _ | .draws => ℕ
  | .real _ => ℝ
  | .table _ | .out => ℕ → ℝ

def Store.read (s : Store) : (l : Slot) → l.Val
  | .nat r => s.ns r
  | .real r => s.rs r
  | .table t => s.tab t
  | .out => s.out
  | .draws => s.draws

def writes (c : C) (l : Slot) : Prop := match c with
  | .skip => False
  | .seq a b | .itePos _ a b => writes a l ∨ writes b l
  | .whilePos _ a => writes a l
  | .forN i _ a => l = .nat i ∨ writes a l
  | .letN i _ => l = .nat i
  | .letR r _ | .value r _ | .cost r _ _ | .cdf r _ _ _ | .truncMean r _ _ _ => l = .real r
  | .put t _ _ => l = .table t
  | .out _ _ => l = .out
  | .uniform r => l = .draws ∨ l = .real r

theorem read_setN (s : Store) (r a : ℕ) (l : Slot) (h : l ≠ .nat r) :
    (s.setN r a).read l = s.read l := by
  cases l <;> simp_all [Store.setN,Store.read,Function.update_of_ne] <;> rfl

theorem read_setR (s : Store) (r : ℕ) (a : ℝ) (l : Slot) (h : l ≠ .real r) :
    (s.setR r a).read l = s.read l := by
  cases l <;> simp_all [Store.setR,Store.read,Function.update_of_ne] <;> rfl

theorem read_put (s : Store) (t : Fin 16) (i : ℕ) (a : ℝ) (l : Slot) (h : l ≠ .table t) :
    (s.put t i a).read l = s.read l := by
  cases l <;> simp_all [Store.put,Store.read,Function.update_of_ne] <;> rfl

theorem Exec.frame {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}
    {c : C} {s v : Store} {k : ℕ} (e : Exec I ω c s v k) (l : Slot) (h : ¬ writes c l) :
    v.read l = s.read l := by
  induction e with
  | skip => rfl
  | seq _ _ ha hb =>
    exact (hb (fun hh => h (Or.inr hh))).trans (ha (fun hh => h (Or.inl hh)))
  | ite_true _ _ ih => exact ih (fun hh => h (Or.inl hh))
  | ite_false _ _ ih => exact ih (fun hh => h (Or.inr hh))
  | while_false => rfl
  | while_true _ _ _ ia ib => exact (ib h).trans (ia h)
  | forN i b body ss ks _ ih =>
    have hi : l ≠ .nat i := fun he => h (Or.inl he)
    rw [read_setN _ _ _ _ hi]
    have H (j : ℕ) (hj : j ≤ b.eval (ss 0)) : (ss j).read l = (ss 0).read l := by
      induction j with
      | zero => rfl
      | succ k hk =>
        exact (ih k (by omega) (fun hh => h (Or.inr hh))).trans
          ((read_setN _ _ _ _ hi).trans (hk (by omega)))
    exact H _ le_rfl
  | put => exact read_put _ _ _ _ _ h
  | letN => exact read_setN _ _ _ _ h
  | letR | value | cost | cdf | truncMean => exact read_setR _ _ _ _ h
  | out =>
    cases l <;> simp_all [writes,Store.writeOut,Store.read] <;> rfl
  | uniform =>
    cases l <;> simp_all [writes,Store.setR,Store.read,Function.update_of_ne] <;> rfl

def Frame (allow : List Slot) (s v : Store) : Prop :=
  ∀ key, key ∉ allow → v.read key = s.read key

theorem Frame.refl (allow : List Slot) (s : Store) : Frame allow s s := fun _ _ => rfl

theorem Frame.trans {s u v : Store} {allow : List Slot} (f : Frame allow s u) (g : Frame allow u v) :
    Frame allow s v := fun key hk => (g key hk).trans (f key hk)

theorem Frame.setN {s u : Store} {allow : List Slot} (f : Frame allow s u) (i val : ℕ) (h : .nat i ∈ allow) :
    Frame allow s (u.setN i val) := fun key hk =>
  (read_setN u i val key (fun he => hk (he ▸ h))).trans (f key hk)

theorem Frame.setR {s u : Store} {allow : List Slot} (f : Frame allow s u) (i : ℕ) (val : ℝ) (h : .real i ∈ allow) :
    Frame allow s (u.setR i val) := fun key hk =>
  (read_setR u i val key (fun he => hk (he ▸ h))).trans (f key hk)

theorem Frame.put {s u : Store} {allow : List Slot} (f : Frame allow s u) (t : Fin 16) (i : ℕ) (val : ℝ)
    (h : .table t ∈ allow) : Frame allow s (u.put t i val) := fun key hk =>
  (read_put u t i val key (fun he => hk (he ▸ h))).trans (f key hk)

theorem Exec.toFrame {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}
    {c : C} {s v : Store} {k : ℕ} (e : Exec I ω c s v k)
    {xs : List Slot} (h : ∀ l, writes c l → l ∈ xs) : Frame xs s v :=
  fun l hn => e.frame l (fun hw => hn (h l hw))

end PandoraKnapsack.Skipping.ArrayRAM

namespace PandoraKnapsack.Skipping.ArrayRAM

variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

/-- Agreement with the input on all slots outside the command's write set. -/
def Kept (c : C) (s v : Store) := ∀ l, ¬writes c l → v.read l = s.read l

def foldRange {α : Type*} (f : ℕ → α → α) (x : α) : ℕ → α
  | 0 => x
  | k+1 => f k (foldRange f x k)

theorem Exec.observeFor {α : Type*} {idx : ℕ} {b : N} {body : C} {s v : Store} {k : ℕ}
    (he : Exec I ω (.forN idx b body) s v k) (obs : Store → α) (f : ℕ → α → α)
    (hi : ∀ u j, obs (u.setN idx j) = obs u)
    (hstep : ∀ j, j < b.eval s → ∀ u z l,
      Kept (.forN idx b body) s u → u.ns idx = j → Exec I ω body u z l →
      obs z = f j (obs u)) :
    obs v = foldRange f (obs s) (b.eval s) := by
  cases he with
  | forN _ _ _ ss ks es =>
    let L := b.eval (ss 0)
    have kept (j) (hj : j ≤ L) : Kept (.forN idx b body) (ss 0) (ss j) := by
      induction j with
      | zero => exact fun _ _ => rfl
      | succ j ih =>
        intro l hl
        exact ((es j (by omega)).frame l (fun h => hl (Or.inr h))).trans
          ((read_setN _ _ _ l (fun h => hl (Or.inl h))).trans (ih (by omega) l hl))
    have track (j) (hj : j ≤ L) : obs (ss j) = foldRange f (obs (ss 0)) j := by
      induction j with
      | zero => rfl
      | succ j ih =>
        have hij : j < L := by omega
        have haux : Kept (.forN idx b body) (ss 0) ((ss j).setN idx j) :=
          fun l hl => (read_setN _ _ _ l (fun h => hl (Or.inl h))).trans (kept j hij.le l hl)
        rw [hstep j hij _ _ _ haux (by simp [Store.setN]) (es j hij), hi, ih hij.le]
        rfl
    exact (hi _ _).trans (track L le_rfl)

theorem foldRange_hit {α : Type*} (p : Prop) [Decidable p] (i : ℕ) (x val : α) (L : ℕ) :
    foldRange (fun j a => if p ∧ j=i then val else a) x L =
      if p ∧ i<L then val else x := by
  induction L with
  | zero => simp [foldRange]
  | succ j ih =>
    rw [foldRange,ih]
    by_cases hp : p
    · simp only [hp, true_and]; split_ifs <;> first | rfl | omega
    · simp [hp]

theorem Exec.forN_hit {α : Type*} {idx : ℕ} {b : N} {body : C} {s v : Store} {k : ℕ}
    (he : Exec I ω (.forN idx b body) s v k) (obs : Store → α) (val : α)
    (p : Prop) [Decidable p] (i : ℕ) (hr : i < b.eval s)
    (hi : ∀ u j, obs (u.setN idx j) = obs u)
    (hstep : ∀ j, j < b.eval s → ∀ u z l,
      Kept (.forN idx b body) s u → u.ns idx = j → Exec I ω body u z l →
      obs z = if p ∧ j=i then val else obs u) :
    obs v = if p then val else obs s := by
  rw [he.observeFor obs _ hi hstep, foldRange_hit]
  simp [hr]


structure Axis where
  reg : ℕ
  bound : ℕ
  target : ℕ

def nest (body : C) : List Axis → C
  | [] => body
  | a :: as => .forN a.reg (.var a.bound) (nest body as)

def Fresh (body : C) : List Axis → Prop
  | [] => True
  | a :: as => ¬writes (nest body as) (.nat a.reg) ∧ Fresh body as

private theorem kept_trans_for {s u z : Store} {c : C} {i : ℕ} {b : N}
    (h : Kept (.forN i b c) s u) (k : Kept c u z) : Kept (.forN i b c) s z :=
  fun l hl => (k l (fun hc => hl (Or.inr hc))).trans (h l hl)

theorem Exec.nest_hit {α : Type*} {body : C} {s v : Store} {k : ℕ} (ds : List Axis)
    (he : Exec I ω (nest body ds) s v k) (obs : Store → α) (val : α)
    (p : Prop) [Decidable p]
    (hobs : ∀ u i j, obs (u.setN i j) = obs u) (hfresh : Fresh body ds)
    (hbnd : ∀ a ∈ ds, ¬writes (nest body ds) (.nat a.bound))
    (hstep : ∀ u z l, Kept (nest body ds) s u →
      (∀ a ∈ ds, u.ns a.reg < s.ns a.bound) → Exec I ω body u z l →
      obs z = if p ∧ (∀ a ∈ ds, u.ns a.reg = a.target) then val else obs u) :
    obs v = if p ∧ (∀ a ∈ ds, a.target < s.ns a.bound) then val else obs s := by
  classical
  induction ds generalizing s v k p with
  | nil => simpa using hstep s v k (fun _ _ => rfl) (by simp) he
  | cons a ds ih =>
    let active := ∀ e ∈ ds, e.target < s.ns e.bound
    have h := he.observeFor obs (fun j old => if (p ∧ active) ∧ j = a.target then val else old)
      (fun u j => hobs u a.reg j) (by
        intro j hj u z l hu hidx hrun
        have eqB (e : Axis) (he : e ∈ a::ds) : u.ns e.bound = s.ns e.bound :=
          hu (.nat e.bound) (hbnd e he)
        have inner := ih hrun (p ∧ j=a.target) hfresh.2
          (fun e hm hw => hbnd e (by simp [hm]) (Or.inr hw)) (by
            intro w z' l' hw hdom hz
            have hidx' : w.ns a.reg = j := (hw (.nat a.reg) hfresh.1).trans hidx
            rw [hstep _ _ _ (kept_trans_for hu hw) (by
              intro e he
              rcases List.mem_cons.mp he with rfl | hm
              · exact hidx' ▸ hj
              · exact (hdom e hm).trans_le (eqB e (by simp [hm])).le) hz]
            simp only [List.forall_mem_cons,hidx']
            simp only [and_assoc])
        rw [inner]
        have hr : (∀ e ∈ ds, e.target < u.ns e.bound) ↔ active := by
          dsimp [active]
          constructor <;> intro hh e hm <;> simpa [eqB e (by simp [hm])] using hh e hm
        simp only [hr]
        split_ifs <;> tauto)
    rw [h,foldRange_hit]
    change (if (p ∧ active) ∧ a.target < s.ns a.bound then val else obs s) = _
    simp only [List.forall_mem_cons]
    dsimp [active]
    split_ifs <;> tauto

end PandoraKnapsack.Skipping.ArrayRAM

namespace PandoraKnapsack.Skipping.ArrayRAM.Bounded
noncomputable section

variable {n m T : ℕ}

def iter (f : ℕ → Store → Store) (s : Store) : ℕ → Store
  | 0 => s
  | k+1 => f k (iter f s k)

def loop (idx len : ℕ) (body : Store → Store) (s : Store) : Store :=
  (iter (fun k a => body (a.setN idx k)) s len).setN idx len

def eval (I : Instance n m T) (ω : ℕ → ℝ) : C → Store → Store
  | .skip, s => s
  | .seq a b, s => eval I ω b (eval I ω a s)
  | .letN r a, s => s.setN r (a.eval s)
  | .letR r a, s => s.setR r (a.eval s)
  | .put t i a, s => s.put t (i.eval s) (a.eval s)
  | .out i a, s => s.writeOut (i.eval s) (a.eval s)
  | .itePos e a b, s => if 0 < e.eval s then eval I ω a s else eval I ω b s
  | .forN idx bound body, s => loop idx (bound.eval s) (eval I ω body) s
  | .whilePos _ _, s => s
  | .value dst i, s => s.setR dst (valueAt I (i.eval s))
  | .cost dst i j, s => s.setR dst (pairAt n m (i.eval s) (j.eval s) I.cost)
  | .cdf dst i j e, s => s.setR dst (pairAt n m (i.eval s) (j.eval s) (fun a b => Skipping.cdf I a b (e.eval s)))
  | .truncMean dst i j e, s => s.setR dst (pairAt n m (i.eval s) (j.eval s) (fun a b => Skipping.truncMean I a b (e.eval s)))
  | .uniform dst, s => {s.setR dst (ω s.draws) with draws := s.draws+1}

def NoWhile : C → Prop
  | .whilePos _ _ => False
  | .seq a b | .itePos _ a b => NoWhile a ∧ NoWhile b
  | .forN _ _ b => NoWhile b
  | _ => True

theorem eval_eq {I : Instance n m T} {ω : ℕ → ℝ} {c : C} {s v : Store} {k : ℕ}
    (h : Exec I ω c s v k) (hc : NoWhile c) : eval I ω c s = v := by
  induction h with
  | seq _ _ ia ib => exact (congrArg _ (ia hc.1)).trans (ib hc.2)
  | ite_true hp _ ih => simpa only [eval,if_pos hp] using ih hc.1
  | ite_false hp _ ih => simpa only [eval,if_neg (not_lt.mpr hp)] using ih hc.2
  | while_true | while_false => exact hc.elim
  | forN i b body ss ks hs ih =>
    have he (j) (hj : j ≤ b.eval (ss 0)) : iter (fun k u => eval I ω body (u.setN i k)) (ss 0) j = ss j := by
      induction j with
      | zero => rfl
      | succ j e => rw [iter,e (by omega)]; exact ih j (by omega) hc
    exact congrArg (fun z => z.setN i (b.eval (ss 0))) (he _ le_rfl)
  | _ => rfl

def num (U : ℕ) : N → ℕ
  | .lit k => k
  | .var _ => U
  | .add a b => num U a + num U b
  | .mul a b => num U a * num U b

def rwCost (U : ℕ) : R → ℕ
  | .lit _ | .var _ => 1
  | .nat a => a.work
  | .get t i => i.work + 4 + (5 * tableOffset t (num U i) + 5)
  | .add a b | .sub a b | .mul a b | .div a b => rwCost U a + rwCost U b + 1

def cost (U : ℕ) : C → ℕ
  | .skip => 0
  | .seq a b => cost U a + cost U b
  | .letN _ a => a.work+1
  | .letR _ e => rwCost U e+1
  | .put t i e => i.work+4+rwCost U e+(5*tableOffset t (num U i)+5)
  | .out i e => i.work+rwCost U e+(5*num U i+5)
  | .itePos e a b => rwCost U e+2+cost U a+cost U b
  | .forN _ b c => b.work+4+5*num U b + num U b*cost U c
  | .whilePos _ _ => 0
  | .value _ i => i.work+(5*num U i+4)+1
  | .cost _ i j => i.work+(5*num U i+4)+(j.work+(5*num U j+4))+1
  | .cdf _ i j e | .truncMean _ i j e =>
    i.work+(5*num U i+4)+(j.work+(5*num U j+4))+rwCost U e+1
  | .uniform _ => 1

def Safe (U : ℕ) : C → Prop
  | .whilePos _ _ => False
  | .letN _ a => num U a ≤ U
  | .seq a b | .itePos _ a b => Safe U a ∧ Safe U b
  | .forN _ b c => num U b ≤ U ∧ Safe U c
  | _ => True

def Good (U : ℕ) (s : Store) := ∀ i, s.ns i ≤ U

private lemma num_le {s : Store} {U : ℕ} (hs : Good U s) (a : N) : a.eval s ≤ num U a := by
  induction a with
  | lit => rfl
  | var => exact hs _
  | add a b ia ib => exact Nat.add_le_add ia ib
  | mul a b ia ib => exact Nat.mul_le_mul ia ib

private lemma rw_le {s : Store} {U : ℕ} (hs : Good U s) (e : R) : e.work s ≤ rwCost U e := by
  induction e with
  | lit | var | nat => rfl
  | get t i => simp only [R.work,rwCost,tableOffset]; gcongr; exact num_le hs _
  | add a b ia ib | sub a b ia ib | mul a b ia ib | div a b ia ib =>
    exact Nat.add_le_add_right (Nat.add_le_add ia ib) 1

private lemma setGood {s : Store} {U j : ℕ} (hs : Good U s) (i : ℕ) (h : j ≤ U) :
    Good U (s.setN i j) := by
  intro k
  simp only [Store.setN, Function.update_apply]
  split_ifs <;> first | exact h | exact hs _

theorem execute (I : Instance n m T) (ω : ℕ → ℝ) (U : ℕ) (c : C) (s : Store)
    (h : Safe U c) (hs : Good U s) :
    ∃ k, Exec I ω c s (eval I ω c s) k ∧ k ≤ cost U c ∧ Good U (eval I ω c s) := by
  induction c generalizing s with
  | skip => exact ⟨_,.skip _,le_rfl,hs⟩
  | seq a b ia ib =>
    obtain ⟨k,ha,hk,hu⟩ := ia s h.1 hs
    obtain ⟨l,hb,hl,hv⟩ := ib _ h.2 hu
    exact ⟨_,.seq ha hb,Nat.add_le_add hk hl,hv⟩
  | letN r a => exact ⟨_,.letN ..,le_rfl,setGood hs r ((num_le hs a).trans h)⟩
  | letR r e => exact ⟨_,.letR ..,Nat.add_le_add_right (rw_le hs e) _,hs⟩
  | uniform r => exact ⟨_,.uniform ..,le_rfl,hs⟩
  | value r i => refine ⟨_,.value ..,?_,hs⟩; simp only [cost,indexWork]; gcongr; exact num_le hs _
  | cost r i j => refine ⟨_,.cost ..,?_,hs⟩; simp only [cost,indexWork]; gcongr <;> exact num_le hs _
  | cdf r i j e => refine ⟨_,.cdf ..,?_,hs⟩; simp only [cost,indexWork]; gcongr <;> first | exact num_le hs _ | exact rw_le hs _
  | truncMean r i j e => refine ⟨_,.truncMean ..,?_,hs⟩; simp only [cost,indexWork]; gcongr <;> first | exact num_le hs _ | exact rw_le hs _
  | out i e => refine ⟨_,.out ..,?_,hs⟩; simp only [cost]; gcongr <;> first | exact num_le hs _ | exact rw_le hs _
  | put t i e => refine ⟨_,.put ..,?_,hs⟩; simp only [cost,tableOffset]; gcongr <;> first | exact num_le hs _ | exact rw_le hs _
  | itePos e a b ia ib =>
    have he := rw_le hs e
    by_cases hp : 0 < e.eval s
    · obtain ⟨k,hk,hc,hv⟩ := ia s h.1 hs
      simp only [eval,if_pos hp,cost]
      exact ⟨_,.ite_true hp hk,by omega,hv⟩
    · obtain ⟨k,hk,hc,hv⟩ := ib s h.2 hs
      simp only [eval,if_neg hp,cost]
      exact ⟨_,.ite_false (le_of_not_gt hp) hk,by omega,hv⟩
  | whilePos => exact False.elim h
  | forN i b body ih =>
    let states := iter (fun j u => eval I ω body (u.setN i j)) s
    have hb := num_le hs b
    have h0 : Good U (states 0) := hs
    obtain ⟨v,k,he,hk,hv⟩ := forN_inv (I := I) (ω := ω) (idx := i) (bound := b) (body := body)
      (s := s) (M := cost U body) (fun j u => u = states j ∧ Good U u) ⟨rfl,h0⟩ (by
        intro j hj u hu
        obtain ⟨rfl,hg⟩ := hu
        obtain ⟨k,he,hk,hv⟩ := ih _ h.2 (setGood hg i (hj.le.trans (hb.trans h.1)))
        exact ⟨_,_,he,hk,rfl,hv⟩)
    obtain ⟨rfl,hg⟩ := hv
    refine ⟨k,he,hk.trans ?_,setGood hg i (hb.trans h.1)⟩
    simp only [cost]
    gcongr

end
end PandoraKnapsack.Skipping.ArrayRAM.Bounded

namespace PandoraKnapsack.Skipping.ArrayRAM.Prepare

variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

structure Header (n m T : ℕ) (s : Store) : Prop where
  items : s.ns 0 = n
  choices : s.ns 1 = m
  labels : s.ns 2 = labelCount T
  cols : s.ns 3 = columnCount n m T
  rows : s.ns 4 = timeRows n T
  capacity : s.rs 0 = T
  grid : ∀ k : Fin (labelCount T), s.tab 0 k.val = timeLabel k

def headerSlots : List Slot := [.nat 0,.nat 1,.nat 2,.nat 3,.nat 4,.real 0,.table 0]

theorem Header.kept {s u : Store} {c : C} (h : Header n m T s) (hk : Kept c s u)
    (hn : ∀ l ∈ headerSlots, ¬writes c l) : Header n m T u := by
  have eq (l : Slot) (hl : l ∈ headerSlots) := hk l (hn l hl)
  constructor
  · exact (eq (.nat 0) (by decide)).trans h.items
  · exact (eq (.nat 1) (by decide)).trans h.choices
  · exact (eq (.nat 2) (by decide)).trans h.labels
  · exact (eq (.nat 3) (by decide)).trans h.cols
  · exact (eq (.nat 4) (by decide)).trans h.rows
  · exact (eq (.real 0) (by decide)).trans h.capacity
  · intro k
    exact (congrFun (eq (.table 0) (by decide)) k.val).trans (h.grid k)

/-- Arithmetic indexing used in every buffer row. -/
theorem flatCol (i : Fin n) (j : Fin m) (h : Fin (labelCount T)) :
    ((columns n m T (i,j,h)).val) = (i.val*m+j.val)*labelCount T+h.val := by
  change (h.val + labelCount T*j.val) + (m*labelCount T)*i.val = _
  ring

private lemma valueAt_fin (I : Instance n m T) (i : Fin n) : valueAt I i.val = I.value i := by
  simp [valueAt,ptrIndex,i.isLt]

private lemma pairAt_fin (i : Fin n) (j : Fin m) (f : Fin n → Fin m → ℝ) :
    pairAt n m i.val j.val f = f i j := by simp [pairAt,ptrIndex,i.isLt,j.isLt]

private def axes (i j h : ℕ) : List Axis := [⟨5,0,i⟩,⟨6,1,j⟩,⟨7,2,h⟩]

theorem weights_correct {s v : Store} {cost : ℕ} (ex : Exec I ω weights s v cost)
    (g : Header n m T s) (col : Fin (columnCount n m T)) : v.tab 1 col.val = columnWeight I col := by
  classical
  obtain ⟨⟨i,j,h⟩,rfl⟩ := (columns n m T).surjective col
  let c := columns n m T (i,j,h)
  have he : Exec I ω (nest weightBody (axes i.val j.val h.val)) s v cost := ex
  have hres := he.nest_hit (obs := fun u => u.tab 1 c.val) (val := columnWeight I c)
    (p := True) (ds := axes i.val j.val h.val)
    (fun _ _ _ => rfl) (by simp [axes]; simp +decide [axes,headerSlots,nest,Fresh,writes, itemEntry,timeEntry,weightBody,weights,itemMatrix,timeMatrix]) (by intro a ha; simp [axes] at ha; rcases ha with rfl|rfl|rfl <;> simp +decide [axes,headerSlots,nest,Fresh,writes, itemEntry,timeEntry,weightBody,weights,itemMatrix,timeMatrix]) (by
      intro u z k hk hd hz
      have gu := g.kept hk (by intro l hl; simp [headerSlots] at hl; rcases hl with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [axes]; all_goals simp +decide [axes,headerSlots,nest,Fresh,writes, itemEntry,timeEntry,weightBody,weights,itemMatrix,timeMatrix])
      simp only [axes,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff, implies_true, and_true] at hd ⊢
      obtain ⟨hi,hj,hh⟩ := hd
      let a : Fin n := ⟨u.ns 5,hi.trans_eq g.items⟩
      let b : Fin m := ⟨u.ns 6,hj.trans_eq g.choices⟩
      let d : Fin (labelCount T) := ⟨u.ns 7,hh.trans_eq g.labels⟩
      let c' := columns n m T (a,b,d)
      have addr : colAddr.eval u = c'.val := by
        rw [flatCol]
        change (u.ns 5 * u.ns 1 + u.ns 6)*u.ns 2+u.ns 7 = _
        rw [gu.choices,gu.labels]
      have hw : columnWeight I c' = I.value a * cdf I a b ((T:ℝ)-(timeLabel d:ℝ)) - I.cost a b := by simp [columnWeight,c',effWeight]
      have hc : (Bounded.eval I ω weightBody u).tab 1 c.val =
          if c.val = c'.val then columnWeight I c' else u.tab 1 c.val := by
        change ((u.setR 3 (valueAt I a.val)).setR 4 (pairAt n m a.val b.val I.cost) |>.setR 5
          (pairAt n m a.val b.val (fun x y => cdf I x y (u.rs 0 - u.tab 0 d.val))) |>.put 1
          (colAddr.eval u) (valueAt I a.val * pairAt n m a.val b.val (fun x y => cdf I x y (u.rs 0 - u.tab 0 d.val)) -
           pairAt n m a.val b.val I.cost)).tab 1 c.val = _
        simp only [Store.put,Function.update_self,Store.setR,Function.update_apply,addr,gu.capacity,gu.grid d,
          pairAt_fin,valueAt_fin,hw]
      rw [← Bounded.eval_eq hz (by simp [weightBody,Bounded.NoWhile]),hc]
      have eqv : c.val = c'.val ↔ u.ns 5=i.val ∧ u.ns 6=j.val ∧ u.ns 7=h.val := by
        change _ ↔ a.val=i.val ∧ b.val=j.val ∧ d.val=h.val
        simp [c,c',← Fin.ext_iff, eq_comm (a := i), eq_comm (a := j), eq_comm (a := h)]
      by_cases heq : c.val = c'.val
      · have ceq : c = c' := Fin.ext heq
        simp [eqv.mp heq,ceq]
      · simp [heq,show ¬(u.ns 5=i.val ∧ u.ns 6=j.val ∧ u.ns 7=h.val) from mt eqv.mpr heq])
  simpa [axes,g.items,g.choices,g.labels,i.isLt,j.isLt,h.isLt,c] using hres


private theorem flatAddress_eq {D : ℕ} (a b : ℕ) (c d : Fin D) :
    a*D+c.val = b*D+d.val ↔ a=b ∧ c=d := by
  constructor
  · intro h
    have hdiv := congrArg (fun z => z / D) h
    have pos := Nat.zero_lt_of_lt c.isLt
    simp only [Nat.mul_comm a D,Nat.mul_comm b D,Nat.mul_add_div pos,
      Nat.div_eq_of_lt c.isLt,Nat.div_eq_of_lt d.isLt,Nat.add_zero] at hdiv
    exact ⟨hdiv,Fin.ext (by subst b; omega)⟩
  · rintro ⟨rfl,rfl⟩
    rfl

private def axes4 (b i j h r : ℕ) : List Axis :=
  [⟨5,0,i⟩,⟨6,1,j⟩,⟨7,2,h⟩,⟨8,b,r⟩]

private theorem matrixSweep {s v : Store} {body : C} {k : ℕ} (b offset row : ℕ)
    (i : Fin n) (j : Fin m) (h : Fin (labelCount T)) (hd : Header n m T s)
    (hreg : b=0 ∨ b=2)
    (F : Fin n → Fin m → Fin (labelCount T) → ℕ → ℝ)
    (he : Exec I ω (nest body (axes4 b i.val j.val h.val (row-offset))) s v k)
    (hkeep : ∀ l ∈ headerSlots, ¬writes body l)
    (hregkeep : ∀ q, ¬writes body (.nat q))
    (hstep : ∀ (u z : Store) (p : ℕ), Header n m T u →
      ∀ (a : Fin n) (e : Fin m) (f : Fin (labelCount T)),
      u.ns 5 = a.val → u.ns 6 = e.val → u.ns 7 = f.val → u.ns 8 < u.ns b →
      Exec I ω body u z p → ∀ idx,
      z.tab 2 idx = if idx = (offset+u.ns 8)*columnCount n m T+(columns n m T (a,e,f)).val then
        F a e f (u.ns 8) else u.tab 2 idx) :
    let adr := row*columnCount n m T + (columns n m T (i,j,h)).val
    v.tab 2 adr = if offset ≤ row ∧ row-offset < s.ns b then F i j h (row-offset) else s.tab 2 adr := by
  classical
  let adr := row*columnCount n m T + (columns n m T (i,j,h)).val
  have hk0 : ∀ l ∈ headerSlots, ¬writes (nest body (axes4 b i j h (row-offset))) l := by
    intro l hl
    have hc := hkeep l hl
    simp [headerSlots] at hl
    rcases hl with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [nest,axes4,writes,hc]
  have hh := he.nest_hit (obs := fun u => u.tab 2 adr) (val := F i j h (row-offset))
    (p := offset ≤ row) (ds := axes4 b i j h (row-offset)) (fun _ _ _ => rfl)
    (by simp [axes4,Fresh,nest,writes,hregkeep])
    (by intro a ha; rcases hreg with rfl|rfl <;> simp [axes4] at ha <;>
        rcases ha with rfl|rfl|rfl|rfl <;> simp [nest,axes4,writes,hregkeep]) (by
      intro u z l hk dom hz
      have g := hd.kept hk hk0
      simp only [axes4,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true] at dom ⊢
      rcases dom with ⟨ha,he,hf,hq⟩
      let a : Fin n := ⟨u.ns 5,ha.trans_eq hd.items⟩
      let e : Fin m := ⟨u.ns 6,he.trans_eq hd.choices⟩
      let f : Fin (labelCount T) := ⟨u.ns 7,hf.trans_eq hd.labels⟩
      have eqb : u.ns b = s.ns b := by
        rcases hreg with rfl|rfl
        · exact hk (.nat 0) (hk0 (.nat 0) (by decide))
        · exact hk (.nat 2) (hk0 (.nat 2) (by decide))
      rw [hstep u z l g a e f rfl rfl rfl (by simpa only [eqb] using hq) hz adr]
      simp only [adr,flatAddress_eq,Equiv.apply_eq_iff_eq,Prod.mk.injEq] 
      change (if row=offset+u.ns 8 ∧ i=a ∧ j=e ∧ h=f then _ else _) = _
      by_cases H : row=offset+u.ns 8 ∧ i=a ∧ j=e ∧ h=f
      · rcases H with ⟨rfl,rfl,rfl,rfl⟩
        simp [a,e,f]
      · rw [if_neg H,if_neg]
        rintro ⟨lo,ha',he',hf',hq'⟩
        exact H ⟨by omega, Fin.ext ha'.symm, Fin.ext he'.symm, Fin.ext hf'.symm⟩)
  simpa only [adr,axes4,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true,
    hd.items,hd.choices,hd.labels,i.isLt,j.isLt,h.isLt,true_and] using hh

private theorem colAddr_spec (u : Store) (g : Header n m T u)
    (a : Fin n) (b : Fin m) (d : Fin (labelCount T)) (hi : u.ns 5 = a.val) (hj : u.ns 6 = b.val)
    (hh : u.ns 7 = d.val) : colAddr.eval u = (columns n m T (a,b,d)).val := by
  rw [flatCol]
  change (u.ns 5 * u.ns 1 + u.ns 6)*u.ns 2 + u.ns 7 = _
  rw [hi,hj,hh,g.choices,g.labels]



private theorem integer_guard (x y : ℕ) :
    0 < 1 - ((x:ℝ) - y)*((x:ℝ)-y) ↔ x = y := by
  by_cases he : x = y
  · simp [he]
  · rcases lt_or_gt_of_ne he with h | h
    · have h' : (x:ℝ)+1 ≤ y := by exact_mod_cast (show x+1 ≤ y by omega)
      have := mul_nonneg (show 0 ≤ (y:ℝ)-x-1 by linarith) (show 0 ≤ (y:ℝ)-x+1 by linarith)
      constructor <;> intro hh <;> first | nlinarith | contradiction
    · have h' : (y:ℝ)+1 ≤ x := by exact_mod_cast (show y+1 ≤ x by omega)
      have := mul_nonneg (show 0 ≤ (x:ℝ)-y-1 by linarith) (show 0 ≤ (x:ℝ)-y+1 by linarith)
      constructor <;> intro hh <;> first | nlinarith | contradiction

private theorem itemSweep {s v : Store} {p : ℕ} (ex : Exec I ω itemMatrix s v p)
    (hd : Header n m T s) (row : ℕ) (i : Fin n) (j : Fin m) (h : Fin (labelCount T)) :
    let adr := row*columnCount n m T + (columns n m T (i,j,h)).val
    v.tab 2 adr = if row<n then (if row=i.val then 1 else 0) else s.tab 2 adr := by
  have hsum := matrixSweep 0 0 row i j h hd (Or.inl rfl)
    (fun a _ _ r => if r = a.val then 1 else 0)
    (body := itemEntry) ex
    (by intro l hl; simp [headerSlots] at hl; rcases hl with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp +decide [axes,headerSlots,nest,Fresh,writes, itemEntry,timeEntry,weightBody,weights,itemMatrix,timeMatrix])
    (by intro q; simp [writes,itemEntry]) (by
      intro u z k g a b f ha hb hf hr hz idx
      have haddr := colAddr_spec u g a b f ha hb hf
      rw [← Bounded.eval_eq hz (by simp [itemEntry,Bounded.NoWhile])]
      let c := colAddr.eval u
      let ad := u.ns 8 * u.ns 3 + c
      change (if 0 < ((1:ℕ):ℝ) - ((u.ns 8:ℝ)-u.ns 5)*((u.ns 8:ℝ)-u.ns 5) then
        u.put 2 ad ((1:ℕ):ℝ) else u.put 2 ad ((0:ℕ):ℝ)).tab 2 idx = _
      simp only [Nat.cast_one, Nat.cast_zero, integer_guard,ha,ad,c,g.cols,haddr,zero_add]
      split_ifs <;> simp_all [Store.put,Function.update_apply])
  simpa [hd.items] using hsum

private noncomputable def timeCoef (I : Instance n m T) (a : Fin n) (b : Fin m)
    (f : Fin (labelCount T)) (r : ℕ) : ℝ :=
  if hr : r < labelCount T then
    let τ := timeLabel (T := T) ⟨r,hr⟩
    if timeLabel f ≤ τ then mu I a b τ / (2*(τ:ℝ)) else 0
  else 0

private theorem timeSweep {s v : Store} {p : ℕ} (ex : Exec I ω timeMatrix s v p)
    (hd : Header n m T s) (row : ℕ) (i : Fin n) (j : Fin m) (h : Fin (labelCount T)) :
    let adr := row*columnCount n m T + (columns n m T (i,j,h)).val
    v.tab 2 adr = if n ≤ row ∧ row-n < labelCount T then timeCoef I i j h (row-n) else s.tab 2 adr := by
  have hsum := matrixSweep 2 n row i j h hd (Or.inr rfl) (timeCoef I) (body := timeEntry) ex
    (by intro l hl; simp [headerSlots] at hl; rcases hl with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp +decide [axes,headerSlots,nest,Fresh,writes, itemEntry,timeEntry,weightBody,weights,itemMatrix,timeMatrix])
    (by intro q; simp [writes,timeEntry]) (by
      intro u z k g a b f ha hb hf hr hz idx
      have haddr := colAddr_spec u g a b f ha hb hf
      have hdom : u.ns 8 < labelCount T := hr.trans_eq g.labels
      let r : Fin (labelCount T) := ⟨u.ns 8,hdom⟩
      have ht : u.tab 0 (u.ns 7) = (timeLabel f : ℝ) := hf ▸ g.grid f
      have hτ : u.tab 0 (u.ns 8) = (timeLabel r : ℝ) := g.grid r
      rw [← Bounded.eval_eq hz (by simp [timeEntry,Bounded.NoWhile])]
      let ad := (u.ns 0 + u.ns 8)*u.ns 3 + colAddr.eval u
      let e := pairAt n m (u.ns 5) (u.ns 6) (fun x y => Skipping.truncMean I x y (u.tab 0 (u.ns 8)))
      change (if 0 < u.tab 0 (u.ns 7) - u.tab 0 (u.ns 8) then u.put 2 ad ((0:ℕ):ℝ)
        else (u.setR 6 e).put 2 ad (e / (((2:ℕ):ℝ)*u.tab 0 (u.ns 8)))).tab 2 idx = _
      have he : e = mu I a b (timeLabel r) := by
        simp only [e,ha,hb,hτ,pairAt_fin,mu]
      simp only [ad,g.items,g.cols,haddr,ht,hτ,Nat.cast_zero,Nat.cast_ofNat,he,timeCoef,dif_pos hdom]
      by_cases H : timeLabel f ≤ timeLabel r
      · have hn : ¬0 < (timeLabel f : ℝ) - timeLabel r := by exact not_lt.mpr (sub_nonpos_of_le (by exact_mod_cast H))
        dsimp only [r] at H hn ⊢
        rw [if_neg hn, if_pos H]
        simp [Store.put,Store.setR,Function.update_apply]
      · have hp : 0 < (timeLabel f : ℝ) - timeLabel r := sub_pos.mpr (by exact_mod_cast Nat.lt_of_not_ge H)
        dsimp only [r] at H hp ⊢
        rw [if_pos hp, if_neg H]
        simp [Store.put,Function.update_apply])
  simpa [hd.labels] using hsum

theorem matrix_correct {s v : Store} {k : ℕ} (ex : Exec I ω matrix s v k) (hd : Header n m T s)
    (row : Fin (timeRows n T)) (col : Fin (columnCount n m T)) :
    v.tab 2 (row.val*columnCount n m T+col.val) = packingRows I row col := by
  unfold matrix at ex
  cases ex with
  | @seq _ _ _ u _ _ _ ei et =>
    have hu := hd.kept (c := itemMatrix) (s := s) (u := u) (fun l hl => ei.frame l hl) (by
      intro l hl
      simp [headerSlots] at hl
      rcases hl with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp +decide [axes,headerSlots,nest,Fresh,writes, itemEntry,timeEntry,weightBody,weights,itemMatrix,timeMatrix])
    obtain ⟨⟨i,j,h⟩,rfl⟩ := (columns n m T).surjective col
    obtain ⟨r,rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin (labelCount T) ≃ Fin (timeRows n T)).surjective row
    cases r with
    | inl a =>
      have he := itemSweep ei hd a.val i j h
      have ht := timeSweep et hu a.val i j h
      have hf : ¬ n ≤ a.val := Nat.not_le.mpr a.isLt
      simp [hf,a.isLt] at ht he
      simpa [packingRows,Fin.ext_iff] using ht.trans he
    | inr r =>
      have ht := timeSweep et hu (n+r.val) i j h
      simp [r.isLt] at ht
      by_cases hz : timeLabel r = 0 <;> simpa [packingRows,timeCoef,r.isLt,hz] using ht

end PandoraKnapsack.Skipping.ArrayRAM.Prepare

namespace PandoraKnapsack.Skipping.ArrayRAM.Prepare
noncomputable section
variable {n m T : ℕ} (I : Instance n m T) (ω : ℕ → ℝ)

theorem labelCount_eq_size (T : ℕ) : labelCount T = T.size + 1 := by
  by_cases h : T = 0
  · simp [labelCount,h]
  · have lo := Nat.lt_size.mpr (Nat.pow_log_le_self 2 h)
    have hi := Nat.size_le.mpr (Nat.lt_pow_succ_log_self (b := 2) (by decide) T)
    simp only [labelCount,if_neg h]
    omega

private def labelNat (i : ℕ) : ℕ := if i=0 then 0 else 2^(i-1)
private def loopBody : C :=
  .seq (.put 0 (.var 2) (.var 1)) <| .seq (.letN 2 (.var 2 + 1)) (.letR 1 (.var 1 + .var 1))
private def guard : R := (.var 0 + R.lit 1) - .var 1
private def Inv (T q : ℕ) (s : Store) :=
  s.ns 2 = q+1 ∧ s.rs 0 = T ∧ s.rs 1 = (2:ℝ)^q ∧ ∀ j ≤ q, s.tab 0 j = labelNat j

private theorem loopExec (q : ℕ) (s : Store) (hq : q ≤ T.size) (h : Inv T q s) :
    ∃ v k, Exec I ω (.whilePos guard loopBody) s v k ∧
      k ≤ 10 + (T.size-q)*(200*(T.size+2)) ∧ Inv T T.size v := by
  rcases eq_or_lt_of_le hq with he | hl
  · subst q
    refine ⟨s,_,.while_false ?_,?_,h⟩
    · have hT : (T:ℝ)+1 ≤ (2:ℝ)^T.size := by exact_mod_cast Nat.lt_size_self T
      change s.rs 0 + 1 - s.rs 1 ≤ 0
      rw [h.2.1,h.2.2.1]
      linarith
    · change 5+1 ≤ _
      omega
  · let a := s.put 0 (s.ns 2) (s.rs 1)
    let b := a.setN 2 (a.ns 2 + 1)
    let v := b.setR 1 (b.rs 1 + b.rs 1)
    have hb := Exec.seq (I := I) (ω := ω) (Exec.put s 0 (.var 2) (.var 1))
      (Exec.seq (Exec.letN a 2 (.var 2 + 1)) (Exec.letR b 1 (.var 1 + .var 1)))
    have hInv : Inv T (q+1) v := by
      rcases h with ⟨hn,ht,hp,hm⟩
      refine ⟨?_,?_,?_,?_⟩
      · simp [v,b,a,Store.setR,Store.setN,Store.put,hn]
      · simpa [v,b,a,Store.setR,Store.setN,Store.put,Function.update_of_ne] using ht
      · simp [v,b,a,Store.setR,Store.setN,Store.put,hp,pow_succ]; ring
      · intro j hj
        by_cases hj' : j=q+1
        · subst j
          simp [v,b,a,Store.setR,Store.setN,Store.put,hn,hp,labelNat]
        · simpa [v,b,a,Store.setR,Store.setN,Store.put,hn,Function.update_of_ne hj'] using hm j (by omega)
    obtain ⟨z,k,hz,hk,hInv'⟩ := loopExec (q+1) v hl hInv
    have hg : 0 < guard.eval s := by
      have hT : (2:ℝ)^q ≤ (T:ℝ) := by exact_mod_cast Nat.lt_size.mp hl
      change 0 < s.rs 0 + 1 - s.rs 1
      rw [h.2.1,h.2.2.1]
      linarith
    refine ⟨z,_,.while_true hg hb hz,?_,hInv'⟩
    change 5+1+((1+4+1+(5*(1+16*(s.ns 2)+0)+5))+(3+1+(3+1)))+1+k ≤ _
    rw [h.1]
    have heq : T.size-q = (T.size-(q+1)) + 1 := by omega
    rw [heq, Nat.add_mul, Nat.one_mul]
    omega
termination_by T.size-q

theorem labels_exec (s : Store) (ht : s.rs 0 = T) :
    ∃ v k, Exec I ω labels s v k ∧ k ≤ 100+T.size*(200*(T.size+2)) ∧
      v.ns 2 = labelCount T ∧ ∀ j : Fin (labelCount T), v.tab 0 j.val = timeLabel j := by
  let a := s.setN 2 1
  let b := a.put 0 0 0
  let c := b.setR 1 1
  have h : Inv T 0 c := by
    refine ⟨?_,?_,?_,?_⟩
    · simp [a,b,c,Store.setN,Store.setR,Store.put]
    · simpa [a,b,c,Store.setN,Store.setR,Store.put,Function.update_of_ne] using ht
    · simp [a,b,c,Store.setN,Store.setR,Store.put]
    · intro j hj
      have : j=0 := by omega
      simp [a,b,c,Store.setN,Store.setR,Store.put,this,labelNat]
  obtain ⟨v,k,hr,hk,hi⟩ := loopExec I ω 0 c (Nat.zero_le _) h
  refine ⟨v,_,.seq (.letN ..) (.seq (.put a 0 0 (.lit 0)) (.seq (.letR b 1 (.lit 1)) hr)),?_,?_,?_⟩
  · change 2 + ((1+4+1+(5*1+5))+(2+k)) ≤ _
    simp only [Nat.sub_zero] at hk
    omega
  · exact hi.1.trans (labelCount_eq_size T).symm
  · intro j
    have ht := j.isLt
    have hc := labelCount_eq_size T
    exact hi.2.2.2 _ (by omega)

end
end PandoraKnapsack.Skipping.ArrayRAM.Prepare

namespace PandoraKnapsack.Skipping.ArrayRAM.Prepare
variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

private theorem maxBody_correct {s v : Store} {k : ℕ} (h : Exec I ω maxBody s v k) :
    v.rs 2 = max (s.rs 2) (s.tab 1 ((s.ns 5*s.ns 1+s.ns 6)*s.ns 2)) := by
  unfold maxBody at h
  cases h with
  | ite_true hp e =>
    cases e
    change 0 < s.tab 1 ((s.ns 5*s.ns 1+s.ns 6)*s.ns 2) - s.rs 2 at hp
    rw [max_eq_right (by linarith)]
    simp [Store.setR,R.eval,N.eval]
  | ite_false hp e =>
    cases e
    change s.tab 1 ((s.ns 5*s.ns 1+s.ns 6)*s.ns 2) - s.rs 2 ≤ 0 at hp
    rw [max_eq_left (by linarith)]

private theorem scan_le_iff (B seed : ℝ) (P : ℕ → Prop) (F : ℕ → ℝ → ℝ)
    (hF : ∀ j v, F j v ≤ B ↔ v ≤ B ∧ P j) (L : ℕ) :
    foldRange F seed L ≤ B ↔ seed ≤ B ∧ ∀ j < L, P j := by
  induction L with
  | zero => simp [foldRange]
  | succ L ih =>
    rw [foldRange,hF,ih]
    constructor
    · rintro ⟨⟨ha,hb⟩,hc⟩
      refine ⟨ha,fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
      · exact hb j h
      · exact hc
    · rintro ⟨ha,hb⟩
      exact ⟨⟨ha,fun j hj => hb j (by omega)⟩,hb L (by omega)⟩

private theorem fold_max_eq (w : ℕ → ℕ → ℝ)
    (hw : ∀ (i : Fin n) (j : Fin m), w i j = effWeight I i j 0) :
    foldRange (fun i a => foldRange (fun j v => max v (w i j)) a m) 0 n = maxWeight I := by
  let M := foldRange (fun i a => foldRange (fun j v => max v (w i j)) a m) 0 n
  have hm (B : ℝ) : M ≤ B ↔ 0 ≤ B ∧ ∀ (i : Fin n) (j : Fin m), effWeight I i j 0 ≤ B := by
    have h := scan_le_iff B 0 (fun i => ∀ j < m, w i j ≤ B) _ (fun i a =>
      scan_le_iff B a (fun j => w i j ≤ B) _ (fun j v => max_le_iff) m) n
    rw [show M = _ by rfl,h]
    constructor
    · rintro ⟨h0,h⟩
      exact ⟨h0, fun i j => hw i j ▸ h i i.isLt j j.isLt⟩
    · rintro ⟨h0,h⟩
      exact ⟨h0,fun i hi j hj => (hw ⟨i,hi⟩ ⟨j,hj⟩).symm ▸ h ⟨i,hi⟩ ⟨j,hj⟩⟩
  have hmax (B : ℝ) : maxWeight I ≤ B ↔ 0 ≤ B ∧ ∀ (i : Fin n) (j : Fin m), effWeight I i j 0 ≤ B := by
    classical
    simp [maxWeight,Finset.max'_le_iff]
    grind
  exact le_antisymm ((hm _).2 ((hmax _).1 le_rfl)) ((hmax _).2 ((hm _).1 le_rfl))

theorem maximum_correct {s v : Store} {k : ℕ} (h : Exec I ω maximum s v k)
    (hn : s.ns 0 = n) (hm : s.ns 1 = m) (hK : s.ns 2 = labelCount T)
    (hw : ∀ col : Fin (columnCount n m T), s.tab 1 col.val = columnWeight I col) :
    v.rs 2 = maxWeight I := by
  let w (i j : ℕ) := s.tab 1 ((i*m+j)*labelCount T)
  have hW (i : Fin n) (j : Fin m) : w i j = effWeight I i j 0 := by
    let z : Fin (labelCount T) := ⟨0,by unfold labelCount; split <;> omega⟩
    let c := columns n m T (i,j,z)
    have hc : c.val = (i.val*m+j.val)*labelCount T := by
      change 0 + labelCount T * ↑j + (m*labelCount T)*↑i = _
      ring
    have h := hw c
    rw [hc] at h
    simpa [w,c,z,columnWeight,timeLabel] using h
  unfold maximum at h
  cases h with
  | seq e0 outer =>
    cases e0
    let F (i : ℕ) (a : ℝ) := foldRange (fun j v => max v (w i j)) a m
    have ho := outer.observeFor (fun u => u.rs 2) F (fun _ _ => rfl) (by
      intro i hi u z l hu h5 inner
      have hu1 : u.ns 1 = m := (hu (.nat 1) (by simp [writes,maxBody])).trans hm
      have hu2 : u.ns 2 = labelCount T := (hu (.nat 2) (by simp [writes,maxBody])).trans hK
      have hut : u.tab 1 = s.tab 1 := hu (.table 1) (by simp [writes,maxBody])
      have hi := inner.observeFor (fun u => u.rs 2) (fun j v => max v (w i j)) (fun _ _ => rfl) (by
        intro j hj u' z' l' hu' h6 ex
        have h1 : u'.ns 1 = m := (hu' (.nat 1) (by simp [writes,maxBody])).trans hu1
        have h2 : u'.ns 2 = labelCount T := (hu' (.nat 2) (by simp [writes,maxBody])).trans hu2
        have h5' : u'.ns 5 = i := (hu' (.nat 5) (by simp [writes,maxBody])).trans h5
        have ht : u'.tab 1 = s.tab 1 := (hu' (.table 1) (by simp [writes,maxBody])).trans hut
        simpa [h1,h2,h5',h6,ht,w] using maxBody_correct ex)
      simpa [F,N.eval,hu1] using hi)
    change v.rs 2 = foldRange F ((s.setR 2 (R.eval s (.lit ((0 : ℕ) : ℝ)))).rs 2) (s.ns 0) at ho
    simp only [R.eval,Nat.cast_zero] at ho
    rw [ho,hn]
    simpa [Store.setR,F] using fold_max_eq w hW

theorem profits_correct {s v : Store} {k : ℕ} (h : Exec I ω profits s v k)
    (hD : s.ns 3 = columnCount n m T) (hM : s.rs 2 = maxWeight I)
    (hw : ∀ col : Fin (columnCount n m T), s.tab 1 col.val = columnWeight I col)
    (col : Fin (columnCount n m T)) : v.tab 3 col.val = packingProfits I col := by
  unfold profits at h
  have he := h.forN_hit (fun u => u.tab 3 col.val) (packingProfits I col) True col.val
    (by change col.val < s.ns 3; rw [hD]; exact col.isLt) (fun _ _ => rfl) (by
      intro j hj u z l hu hidx hstep
      have hut : u.tab 1 = s.tab 1 := hu (.table 1) (by simp [writes])
      have hum : u.rs 2 = maxWeight I := (hu (.real 2) (by simp [writes])).trans hM
      cases hstep with
      | ite_true hp ep =>
        cases ep
        change 0 < u.tab 1 (u.ns 9) at hp
        by_cases heq : j = col.val
        · rw [hidx,heq,hut,hw] at hp
          change Function.update (u.tab 3) (u.ns 9) (u.tab 1 (u.ns 9) / u.rs 2) col.val = _
          simp [hidx,heq,hut,hw,hum,packingProfits,max_eq_right hp.le]
          exact fun h => Or.inr h
        · change Function.update (u.tab 3) (u.ns 9) _ col.val = _
          simp [hidx,Function.update_of_ne (Ne.symm heq),heq]
      | ite_false hp ep =>
        cases ep
        change u.tab 1 (u.ns 9) ≤ 0 at hp
        by_cases heq : j = col.val
        · rw [hidx,heq,hut,hw] at hp
          change Function.update (u.tab 3) (u.ns 9) (R.eval u (.lit ((0 : ℕ) : ℝ))) col.val = _
          simp [R.eval,hidx,heq,packingProfits,max_eq_left hp]
        · change Function.update (u.tab 3) (u.ns 9) _ col.val = _
          simp [hidx,Function.update_of_ne (Ne.symm heq),heq])
  simpa using he

end PandoraKnapsack.Skipping.ArrayRAM.Prepare

namespace PandoraKnapsack.Skipping.ArrayRAM.Bounded

/-- A dimension-only bound in the same power form as the mission's budget.
The base is at least two, so constants are absorbed without a leading coefficient. -/
def Poly (f : ℕ → ℕ) : Prop := ∃ k : ℕ, ∀ z : ℕ, 2 ≤ z → f z ≤ z^k

lemma poly_id : Poly (fun z => z) := ⟨1,fun _ _ => by simp⟩

lemma poly_const (a : ℕ) : Poly (fun _ => a) := by
  refine ⟨a,fun z hz => ?_⟩
  exact (Nat.le_of_lt (Nat.lt_two_pow_self)).trans (Nat.pow_le_pow_left hz _)

lemma poly_mul {f g : ℕ → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun z => f z * g z) := by
  obtain ⟨i,hi⟩ := hf
  obtain ⟨j,hj⟩ := hg
  exact ⟨i+j,fun z hz => (Nat.mul_le_mul (hi z hz) (hj z hz)).trans_eq (pow_add ..).symm⟩

lemma poly_add {f g : ℕ → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun z => f z + g z) := by
  obtain ⟨i,hi⟩ := hf
  obtain ⟨j,hj⟩ := hg
  refine ⟨max i j + 1,fun z hz => ?_⟩
  have h1 := (hi z hz).trans (Nat.pow_le_pow_right (by omega : 0 < z) (le_max_left i j))
  have h2 := (hj z hz).trans (Nat.pow_le_pow_right (by omega : 0 < z) (le_max_right i j))
  calc
    _ ≤ z^(max i j) + z^(max i j) := Nat.add_le_add h1 h2
    _ = z^(max i j) * 2 := by omega
    _ ≤ _ := by rw [pow_succ]; exact Nat.mul_le_mul_left _ hz

theorem num_poly (a : N) : Poly (fun z => num z a) := by
  induction a <;> dsimp [num] <;> (repeat' first | assumption | exact poly_id | exact poly_const _ | apply poly_add | apply poly_mul)

theorem rwCost_poly (e : R) : Poly (fun z => rwCost z e) := by
  induction e with
  | get t a => have := num_poly a; dsimp [rwCost,tableOffset]; (repeat' first | assumption | exact poly_id | exact poly_const _ | apply poly_add | apply poly_mul)
  | _ => dsimp [rwCost]; (repeat' first | assumption | exact poly_id | exact poly_const _ | apply poly_add | apply poly_mul)

theorem cost_poly (c : C) : Poly (fun z => cost z c) := by
  induction c with
  | seq | skip | letN | whilePos | uniform => dsimp [cost]; (repeat' first | assumption | exact poly_id | exact poly_const _ | apply poly_add | apply poly_mul)
  | forN i b c ih => have := num_poly b; dsimp [cost]; (repeat' first | assumption | exact poly_id | exact poly_const _ | apply poly_add | apply poly_mul)
  | value r i => have := num_poly i; dsimp [cost]; (repeat' first | assumption | exact poly_id | exact poly_const _ | apply poly_add | apply poly_mul)
  | cost r i j => have := num_poly i; have := num_poly j; dsimp [cost]; (repeat' first | assumption | exact poly_id | exact poly_const _ | apply poly_add | apply poly_mul)
  | letR r e => have := rwCost_poly e; dsimp [cost]; (repeat' first | assumption | exact poly_id | exact poly_const _ | apply poly_add | apply poly_mul)
  | itePos e a b ia ib => have := rwCost_poly e; dsimp [cost]; (repeat' first | assumption | exact poly_id | exact poly_const _ | apply poly_add | apply poly_mul)
  | out i e => have := num_poly i; have := rwCost_poly e; dsimp [cost]; (repeat' first | assumption | exact poly_id | exact poly_const _ | apply poly_add | apply poly_mul)
  | put t i e => have := num_poly i; have := rwCost_poly e; dsimp [cost,tableOffset]; (repeat' first | assumption | exact poly_id | exact poly_const _ | apply poly_add | apply poly_mul)
  | cdf r i j e | truncMean r i j e =>
    have := num_poly i; have := num_poly j; have := rwCost_poly e; dsimp [cost]; (repeat' first | assumption | exact poly_id | exact poly_const _ | apply poly_add | apply poly_mul)

end PandoraKnapsack.Skipping.ArrayRAM.Bounded

namespace PandoraKnapsack.Skipping.ArrayRAM.Prepare
noncomputable section
variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

structure Tables (I : Instance n m T) (s : Store) extends Header n m T s where
  weights : ∀ col : Fin (columnCount n m T), s.tab 1 col.val = columnWeight I col
  matrix : ∀ row : Fin (timeRows n T), ∀ col : Fin (columnCount n m T),
    s.tab 2 (row.val*columnCount n m T+col.val) = packingRows I row col
  profits : ∀ col : Fin (columnCount n m T), s.tab 3 col.val = packingProfits I col
  draws : s.draws = 0

private def rest : C := .seq weights (.seq maximum (.seq profits matrix))


private theorem rest_correct {s v : Store} {k : ℕ} (ex : Exec I ω rest s v k)
    (hd : Header n m T s) (h0 : s.draws = 0) : Tables I v := by
  have hv0 : v.draws = 0 := (ex.frame .draws (by simp +decide [writes,labels,dimensions,weights,weightBody, maximum,maxBody,profits,matrix,itemMatrix,timeMatrix,itemEntry,timeEntry,rest,code])).trans h0
  unfold rest at ex
  cases ex with
  | @seq _ _ _ a _ _ _ ew e =>
    cases e with
    | @seq _ _ _ b _ _ _ em e =>
      cases e with
      | @seq _ _ _ c _ _ _ ep et =>
        have ha := hd.kept (c := weights) (u := a) ew.frame (by (intro q hq; simp [headerSlots] at hq; rcases hq with ha|ha|ha|ha|ha|ha|ha <;> subst q <;> simp +decide [writes,labels,dimensions,weights,weightBody, maximum,maxBody,profits,matrix,itemMatrix,timeMatrix,itemEntry,timeEntry,rest,code]))
        have hb := ha.kept (c := maximum) (u := b) em.frame (by (intro q hq; simp [headerSlots] at hq; rcases hq with ha|ha|ha|ha|ha|ha|ha <;> subst q <;> simp +decide [writes,labels,dimensions,weights,weightBody, maximum,maxBody,profits,matrix,itemMatrix,timeMatrix,itemEntry,timeEntry,rest,code]))
        have hc := hb.kept (c := profits) (u := c) ep.frame (by (intro q hq; simp [headerSlots] at hq; rcases hq with ha|ha|ha|ha|ha|ha|ha <;> subst q <;> simp +decide [writes,labels,dimensions,weights,weightBody, maximum,maxBody,profits,matrix,itemMatrix,timeMatrix,itemEntry,timeEntry,rest,code]))
        have hv := hc.kept (c := matrix) (u := v) et.frame (by (intro q hq; simp [headerSlots] at hq; rcases hq with ha|ha|ha|ha|ha|ha|ha <;> subst q <;> simp +decide [writes,labels,dimensions,weights,weightBody, maximum,maxBody,profits,matrix,itemMatrix,timeMatrix,itemEntry,timeEntry,rest,code]))
        have wa := weights_correct ew hd
        have wb (col : Fin (columnCount n m T)) : b.tab 1 col.val = columnWeight I col :=
          (congrFun (em.frame (.table 1) (by simp +decide [writes,labels,dimensions,weights,weightBody, maximum,maxBody,profits,matrix,itemMatrix,timeMatrix,itemEntry,timeEntry,rest,code])) col.val).trans (wa col)
        have mx := maximum_correct em ha.items ha.choices ha.labels wa
        have ps := profits_correct ep hb.cols mx wb
        refine ⟨hv,?_,matrix_correct et hc,?_,hv0⟩
        · intro col
          exact (congrFun (et.frame (.table 1) (by simp +decide [writes,labels,dimensions,weights,weightBody, maximum,maxBody,profits,matrix,itemMatrix,timeMatrix,itemEntry,timeEntry,rest,code])) _).trans
            ((congrFun (ep.frame (.table 1) (by simp +decide [writes,labels,dimensions,weights,weightBody, maximum,maxBody,profits,matrix,itemMatrix,timeMatrix,itemEntry,timeEntry,rest,code])) _).trans (wb col))
        · intro col
          exact (congrFun (et.frame (.table 3) (by simp +decide [writes,labels,dimensions,weights,weightBody, maximum,maxBody,profits,matrix,itemMatrix,timeMatrix,itemEntry,timeEntry,rest,code])) _).trans (ps col)

private lemma rest_safe (U : ℕ) : Bounded.Safe U rest := by
  simp [rest,weights,maximum,maxBody,profits,matrix,itemMatrix,timeMatrix,itemEntry,timeEntry,
    weightBody,Bounded.Safe,Bounded.num]

lemma dims_bounds (n m T : ℕ) :
    let S := inputSize n m T + 2
    n ≤ S ∧ m ≤ S ∧ labelCount T ≤ S ∧ columnCount n m T ≤ S^3 ∧ timeRows n T ≤ S := by
  dsimp only
  have hn : n ≤ inputSize n m T + 2 := by unfold inputSize; omega
  have hm : m ≤ inputSize n m T + 2 := by unfold inputSize; omega
  have ht : labelCount T ≤ inputSize n m T + 2 := by rw [labelCount_eq_size]; unfold inputSize; omega
  refine ⟨hn,hm,ht,?_,?_⟩
  · unfold columnCount
    have := Nat.mul_le_mul hn (Nat.mul_le_mul hm ht)
    simpa [pow_succ,Nat.mul_assoc] using this
  · unfold timeRows inputSize
    rw [labelCount_eq_size]
    omega

theorem prepare_exec : ∃ e : ℕ, ∀ (n m T : ℕ) (I : Instance n m T) (ω : ℕ → ℝ),
    ∃ v k, Exec I ω code (initial n m T) v k ∧ k ≤ (inputSize n m T + 2)^e ∧ Tables I v := by
  obtain ⟨p,hp⟩ := Bounded.cost_poly rest
  have hpow : Bounded.Poly (fun S => S^(3*p)) := ⟨3*p,fun _ _ => le_rfl⟩
  have hpall : Bounded.Poly (fun S => (100 + S*(200*(S+2))) + (20 + S^(3*p))) := by
    exact Bounded.poly_add (Bounded.poly_add (Bounded.poly_const 100)
      (Bounded.poly_mul Bounded.poly_id (Bounded.poly_mul (Bounded.poly_const 200)
        (Bounded.poly_add Bounded.poly_id (Bounded.poly_const 2))))) (Bounded.poly_add (Bounded.poly_const 20) hpow)
  obtain ⟨e,he⟩ := hpall
  refine ⟨e,?_⟩
  intro n m T I ω
  let S := inputSize n m T + 2
  let U := S^3
  have hS : 2 ≤ S := by dsimp [S]; omega
  have hSU : S ≤ U := Nat.le_self_pow (by decide) S
  have hU : 2 ≤ U := hS.trans hSU
  have hb := dims_bounds n m T
  obtain ⟨s,l,el,hl,hK,hL⟩ := labels_exec I ω (initial n m T) (by simp [initial])
  have hn : s.ns 0=n := (el.frame (.nat 0) (by simp +decide [writes,labels,dimensions,weights,weightBody, maximum,maxBody,profits,matrix,itemMatrix,timeMatrix,itemEntry,timeEntry,rest,code])).trans (by rfl)
  have hm : s.ns 1=m := (el.frame (.nat 1) (by simp +decide [writes,labels,dimensions,weights,weightBody, maximum,maxBody,profits,matrix,itemMatrix,timeMatrix,itemEntry,timeEntry,rest,code])).trans (by rfl)
  have ht : s.rs 0 = T := (el.frame (.real 0) (by simp +decide [writes,labels,dimensions,weights,weightBody, maximum,maxBody,profits,matrix,itemMatrix,timeMatrix,itemEntry,timeEntry,rest,code])).trans (by rfl)
  let a := s.setN 3 (s.ns 0 * (s.ns 1 * s.ns 2))
  let b := a.setN 4 (a.ns 0 + a.ns 2)
  have ed : Exec I ω dimensions s b 10 := by
    exact Exec.seq (.letN s 3 (.var 0 * (.var 1 * .var 2))) (.letN a 4 (.var 0 + .var 2))
  have hd : Header n m T b := by
    constructor <;> simp [b,a,Store.setN,Function.update_of_ne,hn,hm,hK,ht,hL,columnCount,timeRows]
  have hg : Bounded.Good U b := by
    intro i
    rcases eq_or_ne i 0 with rfl | h0
    · rw [hd.items]; exact hb.1.trans hSU
    rcases eq_or_ne i 1 with rfl | h1
    · rw [hd.choices]; exact hb.2.1.trans hSU
    rcases eq_or_ne i 2 with rfl | h2
    · rw [hd.labels]; exact hb.2.2.1.trans hSU
    rcases eq_or_ne i 3 with rfl | h3
    · rw [hd.cols]; exact hb.2.2.2.1
    rcases eq_or_ne i 4 with rfl | h4
    · rw [hd.rows]; exact hb.2.2.2.2.trans hSU
    have hs : s.ns i = (initial n m T).ns i := el.frame (.nat i) (by
      simp [labels,writes,h2])
    simp [b,a,Store.setN,Function.update_of_ne,h3,h4,hs,initial,h0,h1]
  have hz : b.draws=0 := el.frame .draws (by simp +decide [writes,labels,dimensions,weights,weightBody, maximum,maxBody,profits,matrix,itemMatrix,timeMatrix,itemEntry,timeEntry,rest,code])
  obtain ⟨k,er,hr,_⟩ := Bounded.execute I ω U rest b (rest_safe U) hg
  refine ⟨_,_,.seq el (.seq ed er),?_,rest_correct er hd hz⟩
  apply le_trans _ (he S hS)
  have hs : T.size ≤ S := by dsimp [S,inputSize]; omega
  have hl' := hl.trans (Nat.add_le_add_left (Nat.mul_le_mul hs (Nat.mul_le_mul_left 200 (Nat.add_le_add_right hs 2))) 100)
  have hr' := hr.trans (hp U hU)
  have powEq : U^p = S^(3*p) := (pow_mul S 3 p).symm
  rw [powEq] at hr'
  change l+(10+k) ≤ (100 + S*(200*(S+2))) + (20+S^(3*p))
  exact Nat.add_le_add hl' (Nat.add_le_add (by decide) hr')

end
end PandoraKnapsack.Skipping.ArrayRAM.Prepare

open PandoraKnapsack.Skipping PandoraKnapsack.Skipping.ArrayRAM

theorem solution : ∃ e : ℕ, ∀ (n m T : ℕ) (I : Instance n m T) (ω : ℕ → ℝ),
    ∃ (v : Store) (k : ℕ), Exec I ω Prepare.code (initial n m T) v k ∧
      k ≤ (inputSize n m T + 2)^e ∧ v.ns 0 = n ∧ v.ns 1 = m ∧
      v.ns 2 = labelCount T ∧ v.ns 3 = columnCount n m T ∧ v.ns 4 = timeRows n T ∧
      v.rs 0 = T ∧ (∀ h : Fin (labelCount T), v.tab 0 h.val = timeLabel h) ∧
      (∀ col : Fin (columnCount n m T), v.tab 1 col.val = columnWeight I col) ∧
      (∀ row : Fin (timeRows n T), ∀ col : Fin (columnCount n m T),
        v.tab 2 (row.val*columnCount n m T+col.val) = packingRows I row col) ∧
      (∀ col : Fin (columnCount n m T), v.tab 3 col.val = packingProfits I col) ∧ v.draws = 0 := by
  obtain ⟨e,he⟩ := Prepare.prepare_exec
  refine ⟨e,?_⟩
  intro n m T I ω
  obtain ⟨v,k,ex,hk,h⟩ := he n m T I ω
  exact ⟨v,k,ex,hk,h.items,h.choices,h.labels,h.cols,h.rows,h.capacity,h.grid,
    h.weights,h.matrix,h.profits,h.draws⟩
