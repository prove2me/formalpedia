-- Prove2me | solution 1 for PandoraKnapsack.Skipping.ArrayRAM.packing_array_exec
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:54:49.148421+00:00
-- url     : https://prove2.me/submissions/7d2db535-d86c-40ee-9d35-12fa66d1958a

import Definitions.Def_PandoraKnapsack_Skipping_PackingRAM
import Definitions.Def_PandoraKnapsack_NormalizedPacking

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

namespace PandoraKnapsack.Skipping.ArrayRAM.Packing
open PandoraPacking

variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

@[simp] theorem re_num (s : Store) (k : ℕ) : (OfNat.ofNat k : R).eval s = (k : ℝ) := rfl
@[simp] theorem re_0 (s : Store) : R.eval s 0 = 0 := by change ((0:ℕ):ℝ) = 0; norm_num
@[simp] theorem re_1 (s : Store) : R.eval s 1 = 1 := by change ((1:ℕ):ℝ) = 1; norm_num
@[simp] theorem re_8 (s : Store) : R.eval s 8 = 8 := by change ((8:ℕ):ℝ) = 8; norm_num
@[simp] theorem re_9 (s : Store) : R.eval s 9 = 9 := by change ((9:ℕ):ℝ) = 9; norm_num
@[simp] theorem re_add (s : Store) (a b : R) : (a+b).eval s = a.eval s+b.eval s := rfl
@[simp] theorem re_sub (s : Store) (a b : R) : (a-b).eval s = a.eval s-b.eval s := rfl
@[simp] theorem re_mul (s : Store) (a b : R) : (a*b).eval s = a.eval s*b.eval s := rfl
@[simp] theorem re_div (s : Store) (a b : R) : (a/b).eval s = a.eval s/b.eval s := rfl
@[simp] theorem re_var (s : Store) (k : ℕ) : (R.var k).eval s = s.rs k := rfl
@[simp] theorem re_nat (s : Store) (a : N) : (R.nat a).eval s = (a.eval s : ℝ) := rfl
@[simp] theorem re_get (s : Store) (t : Fin 16) (a : N) : (R.get t a).eval s = s.tab t (a.eval s) := rfl

abbrev Runs (I : Instance n m T) (ω : ℕ → ℝ) (code : C) (s : Store) (M : ℕ)
    (Post : Store → Prop) : Prop :=
  ∃ v k, Exec I ω code s v k ∧ k ≤ M ∧ Post v

abbrev vec (s : Store) (t : Fin 16) (d : ℕ) : Vec d := fun j => s.tab t j.val

def Expr {d : ℕ} (s : Store) (allow : List Slot) (e : R) (f : Vec d) (B : ℕ) : Prop :=
  ∀ u, Frame allow s u → ∀ j : Fin d, u.ns 25 = j.val → e.eval u = f j ∧ e.work u ≤ B

def partialDot {d : ℕ} (f : Vec d) (z : ℕ) := ∑ j ∈ Finset.range z, if h : j < d then f ⟨j,h⟩ else 0

@[simp] theorem prefix_zero {d : ℕ} (f : Vec d) : partialDot f 0 = 0 := by simp [partialDot]

theorem prefix_succ {d z : ℕ} (f : Vec d) (h : z < d) :
    partialDot f (z+1) = partialDot f z + f ⟨z,h⟩ := by simp [partialDot,Finset.sum_range_succ,h]

theorem prefix_all {d : ℕ} (f : Vec d) : partialDot f d = ∑ j, f j := by
  rw [partialDot, ← Fin.sum_univ_eq_sum_range]
  simp

def arithBudget (d r : ℕ) := 500*(d+1)*(r+1)+500

def accessBudget (d : ℕ) := 110*(d+1)

def dotBudget (d B : ℕ) := 10 + 5*d + d*(2*B+5)

def dotSlots : List Slot := [.nat 25,.real 28]

theorem exec_dot {d B : ℕ} (s : Store) (hd : s.ns 3 = d) (a b : R) (f g : Vec d)
    (ha : Expr s dotSlots a f B) (hb : Expr s dotSlots b g B) :
    Runs I ω (scalarProduct a b) s (dotBudget d B) (fun u => u.rs 28 = dot f g) := by
  let start := s.setR 28 0
  let Inv (j : ℕ) (u : Store) := Frame dotSlots s u ∧ u.rs 28 = partialDot (fun q => f q * g q) j
  have hz : Inv 0 start := ⟨(Frame.refl _ s).setR 28 0 (by decide),by simp [start, Store.setR]⟩
  have hn : dReg.eval start = d := hd
  have step (j : ℕ) (hj : j < dReg.eval start) (u : Store) (hu : Inv j u) :
      ∃ v k, Exec I ω (.letR 28 (.var 28 + a*b)) (u.setN 25 j) v k ∧
          k ≤ 2*B+5 ∧ Inv (j+1) v := by
    let t := u.setN 25 j
    let jj : Fin d := ⟨j,hn ▸ hj⟩
    have hf : Frame dotSlots s t := hu.1.setN 25 j (by decide)
    have hcol : t.ns 25 = jj.val := by simp [t,Store.setN,jj]
    obtain ⟨hea,hwa⟩ := ha t hf jj hcol
    obtain ⟨heb,hwb⟩ := hb t hf jj hcol
    refine ⟨_,_,Exec.letR (I := I) (ω := ω) t 28 (.var 28 + a*b),?_,
      hf.setR _ _ (by decide), ?_⟩
    · change 1+(a.work t+b.work t+1)+1+1 ≤ _
      omega
    · change (Function.update t.rs 28 (t.rs 28 + a.eval t * b.eval t)) 28 = _
      rw [Function.update_self, hea, heb, prefix_succ _ jj.isLt]
      exact congrArg (· + f jj*g jj) hu.2
  obtain ⟨v,k,hv,hk,_,hr⟩ := forN_inv (I := I) (ω := ω) Inv hz step
  have first : Exec I ω (.letR 28 0) s start 2 := by
    have h := Exec.letR (I := I) (ω := ω) s 28 (0:R)
    rwa [re_0] at h
  refine ⟨_,_,Exec.seq first hv, ?_, ?_⟩
  · change 1+1+k ≤ _
    change k ≤ 1+4+5*(dReg.eval start)+(dReg.eval start)*(2*B+5) at hk
    rw [hn] at hk
    dsimp [dotBudget]
    omega
  · change v.rs 28 = _
    rwa [hn, prefix_all] at hr

theorem expr_atCol {d B : ℕ} (s : Store) (t : Fin 16) (allow : List Slot)
    (ht : .table t ∉ allow) (hB : accessBudget d ≤ B) :
    Expr s allow (atCol t) (vec s t d) B := by
  intro u hu j hj
  constructor
  · change u.tab t (u.ns 25) = s.tab t j.val
    rw [hj]
    exact congrFun (hu (.table t) ht) j.val
  · change 1+4+(5*tableOffset t (u.ns 25)+5) ≤ B
    rw [hj]
    apply le_trans _ hB
    unfold tableOffset accessBudget
    have := t.isLt
    have := j.isLt
    omega

theorem work_access_le (d r : ℕ) : accessBudget d ≤ arithBudget d r := by
  unfold accessBudget arithBudget
  nlinarith [Nat.zero_le (d*r)]

def loopBudget (d per : ℕ) := 5+5*d+d*per

/-- Execute a pointwise column update. The loop exposes the partly written array to
the next body call and preserves all later coordinates. -/
theorem exec_vec_loop {d B : ℕ} (s : Store) (hd : s.ns 3 = d) (t : Fin 16) (f : Vec d)
    (body : C) (allow : List Slot) (hidx : .nat 25 ∈ allow)
    (hb : ∀ j : Fin d, ∀ u, Frame allow s u → u.ns 25 = j.val →
      u.tab t j.val = s.tab t j.val →
      Runs I ω body u B (fun v => Frame allow u v ∧ v.tab t = Function.update (u.tab t) j.val (f j))) :
    Runs I ω (columnsLoop body) s (loopBudget d B) (fun u => Frame allow s u ∧ vec u t d = f) := by
  let Inv (k : ℕ) (u : Store) := Frame allow s u ∧
    ∀ j : Fin d, u.tab t j.val = if j.val < k then f j else s.tab t j.val
  have hz : Inv 0 s := ⟨Frame.refl _ _,fun j => by simp⟩
  have step (j : ℕ) (hj : j < dReg.eval s) (u : Store) (hu : Inv j u) :
      ∃ v k, Exec I ω body (u.setN 25 j) v k ∧ k ≤ B ∧ Inv (j+1) v := by
    let jj : Fin d := ⟨j,hd ▸ hj⟩
    have hnext := hu.1.setN 25 j hidx
    obtain ⟨v,k,hv,hk,hf,hm⟩ := hb jj _ hnext (by simp [Store.setN,jj]) (by simpa [jj,Store.setN] using hu.2 jj)
    refine ⟨v,k,hv,hk,hnext.trans hf,fun z => ?_⟩
    rw [hm]
    by_cases h : z = jj
    · subst z
      simp [jj]
    · have he : z.val ≠ j := fun hh => h (Fin.ext hh)
      rw [Function.update_of_ne he]
      change u.tab t z.val = _
      rw [hu.2 z]
      split_ifs <;> first | rfl | omega
  obtain ⟨v,k,hv,hk,hinv⟩ := forN_inv (I := I) (ω := ω) Inv hz step
  refine ⟨_,k,hv,?_,hinv.1.setN _ _ hidx,?_⟩
  · change k ≤ 1+4+5*(s.ns 3)+(s.ns 3)*B at hk
    simpa [loopBudget,hd] using hk
  · funext j
    change v.tab t j.val = _
    simpa only [show dReg.eval s = d from hd,if_pos j.isLt] using hinv.2 j

def fillSlots (t : Fin 16) : List Slot := [.nat 25,.table t]

def putBudget (d B : ℕ) := accessBudget d + B + 4

theorem exec_fill {d B : ℕ} (s : Store) (hd : s.ns 3 = d) (t : Fin 16) (e : R) (f : Vec d)
    (he : ∀ j : Fin d, ∀ u, Frame (fillSlots t) s u → u.ns 25 = j.val →
      u.tab t j.val = s.tab t j.val → e.eval u = f j ∧ e.work u ≤ B) :
    Runs I ω (fill t e) s (loopBudget d (putBudget d B)) (fun u => vec u t d = f) := by
  apply Exists.imp ?_ (exec_vec_loop (I := I) (ω := ω) (B := putBudget d B) s hd t f
      (.put t colReg e) (fillSlots t) (by simp [fillSlots]) ?_)
  · intro v hv
    obtain ⟨k,hv,hk,_,hz⟩ := hv
    exact ⟨k,hv,hk,hz⟩
  · intro j u hu hj hcell
    obtain ⟨hr,hb⟩ := he j u hu hj hcell
    refine ⟨_,_,Exec.put (I := I) (ω := ω) u t colReg e,?_,
      (Frame.refl _ u).put _ _ _ (by simp [fillSlots]),?_⟩
    · change 1+4+e.work u+(5*tableOffset t (u.ns 25)+5) ≤ _
      unfold putBudget accessBudget tableOffset
      rw [hj]
      have := j.isLt
      have := t.isLt
      omega
    · simp [Store.put,N.eval,hj,hr]

def updateSlots : List Slot := [.nat 25,.table 5,.real 29]

def updateBudget (d B : ℕ) := loopBudget d (4*accessBudget d + 2*B + 40)

private theorem exec_clip_write {d : ℕ} (t : Store) (j : Fin d) (hj : t.ns 25 = j.val) :
    Runs I ω (.itePos (.var 29 - 1) (.put 5 colReg 1)
      (.itePos (.var 29) (.put 5 colReg (.var 29)) (.put 5 colReg 0))) t
      (accessBudget d + 18) (fun v => Frame updateSlots t v ∧
        v.tab 5 = Function.update (t.tab 5) j.val (clip (t.rs 29))) := by
  have price (e : R) (he : e.work t = 1) :
      colReg.work+4+e.work t+(5*tableOffset 5 (colReg.eval t)+5) ≤ accessBudget d + 1 := by
    change 1+4+e.work t+(5*tableOffset 5 (t.ns 25)+5) ≤ _
    simp only [he,hj,tableOffset,accessBudget]
    have := j.isLt
    omega
  have spec (e : R) (h : e.eval t = clip (t.rs 29)) :
      Frame updateSlots t (t.put 5 (colReg.eval t) (e.eval t)) ∧
        (t.put 5 (colReg.eval t) (e.eval t)).tab 5 =
          Function.update (t.tab 5) j.val (clip (t.rs 29)) :=
    ⟨(Frame.refl _ t).put 5 _ _ (by decide),by simp [Store.put,N.eval,hj,h]⟩
  by_cases h1 : 1 < t.rs 29
  · refine ⟨_,_,Exec.ite_true (e := .var 29-1) (by simp; linarith)
      (Exec.put t 5 colReg 1),?_, spec 1 ?_⟩
    · change 3+1+_+1 ≤ _
      have := price 1 rfl
      omega
    · simp [clip,min_eq_left h1.le]
  · have h1' : t.rs 29 ≤ 1 := le_of_not_gt h1
    by_cases h0 : 0 < t.rs 29
    · refine ⟨_,_,Exec.ite_false (e := .var 29-1) (by simp; linarith)
        (Exec.ite_true (e := .var 29) h0 (Exec.put t 5 colReg (.var 29))),?_,spec (.var 29) ?_⟩
      · change 3+1+(1+1+_+1) ≤ _
        have := price (.var 29) rfl
        omega
      · simp [clip,min_eq_right h1',max_eq_right h0.le]
    · refine ⟨_,_,Exec.ite_false (e := .var 29-1) (by simp; linarith)
        (Exec.ite_false (e := .var 29) (le_of_not_gt h0) (Exec.put t 5 colReg 0)),?_,spec 0 ?_⟩
      · change 3+1+(1+1+_) ≤ _
        have := price 0 rfl
        omega
      · simp [clip,min_eq_right h1',max_eq_left (le_of_not_gt h0)]

theorem exec_update {d B : ℕ} (s : Store) (hd : s.ns 3 = d) (a : R) (f : Vec d)
    (hrate : s.rs 25 = rate d) (ha : Expr s updateSlots a f B) :
    Runs I ω (projectedUpdate a) s (updateBudget d B)
      (fun v => vec v 5 d = update f (vec s 5 d)) := by
  obtain ⟨v,k,hv,hk,_,hZ⟩ := exec_vec_loop (I := I) (ω := ω)
    (B := 4*accessBudget d+2*B+40) s hd 5 (update f (vec s 5 d))
    (.seq (.letR 29 (atCol 5 - .var 25*a))
      (.itePos (.var 29-1) (.put 5 colReg 1)
       (.itePos (.var 29) (.put 5 colReg (.var 29)) (.put 5 colReg 0)))) updateSlots (by decide) (by
      intro j u hF hj hcell
      obtain ⟨hea,hwa⟩ := ha u hF j hj
      let q : R := atCol 5 - .var 25*a
      let t := u.setR 29 (q.eval u)
      have hrate' : u.rs 25 = rate d := (hF (.real 25) (by decide)).trans hrate
      have zval : t.rs 29 = vec s 5 d j - rate d * f j := by
        simp [t,q,Store.setR,atCol,N.eval,hj,hcell,hrate',hea,vec]
      obtain ⟨v,l,ev,hl,hframe,hnew⟩ := exec_clip_write (I := I) (ω := ω) t j (by exact hj)
      refine ⟨v,_,Exec.seq (Exec.letR u 29 q) ev,?_,
        ((Frame.refl _ u).setR 29 _ (by decide)).trans hframe,?_⟩
      · have hb := (expr_atCol u 5 [] (by decide) (le_refl (accessBudget d)) u (Frame.refl _ _) j hj).2
        change (atCol 5).work u + (1 + a.work u + 1) + 1 + 1 + l ≤ _
        omega
      · rw [zval] at hnew
        exact hnew)
  exact ⟨v,k,hv,hk,hZ⟩

end PandoraKnapsack.Skipping.ArrayRAM.Packing

namespace PandoraKnapsack.Skipping.ArrayRAM.Packing
open PandoraPacking
noncomputable section
variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

def rowSlots : List Slot := [.nat 25, .real 27, .real 28, .real 29, .table 5]

theorem enlarge {s u : Store} {xs ys : List Slot} (hf : Frame xs s u)
    (h : xs ⊆ ys) : Frame ys s u := fun key hk => hf key (fun h' => hk (h h'))

theorem expr_shrink {d B : ℕ} {s u : Store} {xs ys : List Slot} {a : R} {f : Vec d}
    (e : Expr s ys a f B) (hu : Frame ys s u) (h : xs ⊆ ys) :
    Expr u xs a f B := fun t ht => e t (hu.trans (enlarge ht h))

theorem packing_dot_frame {s u : Store} {k : ℕ} {a b : R}
    (h : Exec I ω (scalarProduct a b) s u k) : Frame dotSlots s u := by
  apply h.toFrame
  intro l
  simp [scalarProduct,columnsLoop,writes,dotSlots]
  tauto

def checkBudget (d B : ℕ) := dotBudget d B + updateBudget d B + B + 20

structure Checked {d : ℕ} (s v : Store) (a x : Vec d) (bound : ℝ) : Prop where
  data : vec v 5 d = if bound + 1/8 < dot a x then update a x else x
  flag : v.rs 27 = if bound + 1/8 < dot a x then 1 else s.rs 27

theorem exec_check {d B : ℕ} (s : Store) (hd : s.ns 3 = d) (a E : R) (f : Vec d) (bound : ℝ)
    (br : accessBudget d ≤ B) (hrate : s.rs 25 = rate d)
    (ha : Expr s rowSlots a f B)
    (hE : ∀ u, Frame dotSlots s u → E.eval u = bound ∧ E.work u ≤ B) :
    Runs I ω (checkRow a E) s (checkBudget d B) (fun v => Checked s v f (vec s 5 d) bound) := by
  have hdots : dotSlots ⊆ rowSlots := by decide
  obtain ⟨u,k,eu,hk,hacc⟩ := exec_dot (I := I) (ω := ω) s hd a (atCol 5) f (vec s 5 d)
    (expr_shrink ha (Frame.refl _ _) hdots) (expr_atCol s 5 dotSlots (by decide) br)
  have hframe := packing_dot_frame eu
  have hframe' := enlarge hframe hdots
  have htab : vec u 5 d = vec s 5 d := funext fun j => congrFun (hframe (.table 5) (by decide)) j.val
  obtain ⟨hev,hew⟩ := hE u hframe
  let test : R := .var 28-E-(1/8:R)
  have eval : test.eval u = dot f (vec s 5 d) - bound - 1/8 := by simp [test,hacc,hev]
  have price : test.work u ≤ B+7 := by change 1 + E.work u + 1 + (1+1+1) + 1 ≤ _; omega
  by_cases hh : bound+1/8 < dot f (vec s 5 d)
  · have hd' : u.ns 3 = d := (hframe (.nat 3) (by decide)).trans hd
    have hr' : u.rs 25 = rate d := (hframe (.real 25) (by decide)).trans hrate
    obtain ⟨v,l,ev,hl,hz⟩ := exec_update (I := I) (ω := ω) u hd' a f hr'
      (expr_shrink ha hframe' (by decide : updateSlots ⊆ rowSlots))
    let ef := Exec.letR (I := I) (ω := ω) v 27 (1:R)
    refine ⟨_,_,Exec.seq eu (Exec.ite_true (e := test) (by rw [eval];linarith)
      (Exec.seq ev ef)),?_, ?_⟩
    · change k+(test.work u+1+(l+2)+1) ≤ _
      dsimp [checkBudget]
      omega
    · constructor
      · rw [if_pos hh]
        exact hz.trans (congrArg (update f) htab)
      · rw [if_pos hh]
        simp [Store.setR]
  · refine ⟨_,_,Exec.seq eu (Exec.ite_false (e := test) (by rw [eval];linarith) (Exec.skip u)),?_,?_⟩
    · dsimp [checkBudget]
      omega
    · exact ⟨(if_neg hh).symm ▸ htab,(if_neg hh).symm ▸ hframe (.real 27) (by decide)⟩

structure Inputs {r d : ℕ} (s : Store) (A : Matrix r d) (c : Vec d) : Prop where
  d_eq : s.ns 3 = d
  r_eq : s.ns 4 = r
  coeff : ∀ i : Fin r, ∀ j : Fin d, s.tab 2 (i.val*d+j.val) = A i j
  profit : vec s 3 d = c

def inputSlots : List Slot := [.nat 25,.nat 26,.nat 27,.nat 28,.real 25,.real 26,.real 27,
  .real 28,.real 29,.real 30,.table 4,.table 5]

theorem Inputs.transport {r d : ℕ} {s u : Store} {A : Matrix r d} {c : Vec d}
    (h : Inputs s A c) (f : Frame inputSlots s u) : Inputs u A c :=
  ⟨(f (.nat 3) (by decide)).trans h.d_eq,(f (.nat 4) (by decide)).trans h.r_eq,
    fun i j => (congrFun (f (.table 2) (by decide)) _).trans (h.coeff i j),
    (funext fun j : Fin d => congrFun (f (.table 3) (by decide)) j.val).trans h.profit⟩

private theorem coeff_row {r d : ℕ} {s : Store} {A : Matrix r d} {c : Vec d} (hin : Inputs s A c)
    (i : Fin r) (hi : s.ns 26 = i.val) :
    Expr s rowSlots matrixCoeff (A i) (arithBudget d r) := by
  intro u hu j hj
  have hrow : u.ns 26 = i.val := (hu (.nat 26) (by decide)).trans hi
  have hd : u.ns 3 = d := (hu (.nat 3) (by decide)).trans hin.d_eq
  constructor
  · change u.tab 2 (u.ns 26*u.ns 3+u.ns 25) = A i j
    rw [hrow,hd,hj]
    exact (congrFun (hu (.table 2) (by decide)) _).trans (hin.coeff i j)
  · change 5+4+(5*tableOffset 2 (u.ns 26*u.ns 3+u.ns 25)+5) ≤ _
    rw [hrow,hd,hj]
    unfold tableOffset arithBudget
    have hr := Nat.mul_le_mul_right d i.isLt.le
    have hc := j.isLt
    norm_num
    nlinarith

private theorem profit_row {r d : ℕ} {s : Store} {A : Matrix r d} {c : Vec d} (hin : Inputs s A c) :
    Expr s rowSlots (0-atCol 3) (fun j => -c j) (arithBudget d r) := by
  intro u hu j hj
  have ⟨e,w⟩ := expr_atCol s 3 rowSlots (by decide) (le_refl (accessBudget d)) u hu j hj
  constructor
  · simp only [re_sub,re_0,e,zero_sub,neg_inj]
    exact congrFun hin.profit j
  · change 1+(atCol 3).work u+1 ≤ _
    have hh : accessBudget d+2 ≤ arithBudget d r := by
      unfold accessBudget arithBudget
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
      omega
    omega

def scanSlots : List Slot := [.nat 25,.nat 26,.real 27,.real 28,.real 29,.table 5]

private theorem row_frame {s u : Store} {k : ℕ} {a E : R}
    (h : Exec I ω (checkRow a E) s u k) : Frame rowSlots s u :=
  h.toFrame (by
    intro l hw
    simp [checkRow, projectedUpdate, scalarProduct, columnsLoop, writes, rowSlots] at hw ⊢
    tauto)

def firstBad {r d : ℕ} (A : Matrix r d) (c : Vec d) (g : ℝ) (x : Vec d) (k : ℕ) : Option (Row d) :=
  badRow ((rowsFor A c g).take (k+1)) x

private theorem firstBad_zero {r d : ℕ} (A : Matrix r d) (c : Vec d) (g : ℝ) (x : Vec d) :
    firstBad A c g x 0 =
      if -g+1/8 < dot (fun j => -c j) x then some ⟨(fun j => -c j),-g⟩ else none := by
  simp [firstBad,badRow,rowsFor,List.find?_cons]
  split_ifs with hh <;> simp [hh]

private theorem firstBad_succ {r d : ℕ} (A : Matrix r d) (c : Vec d) (g : ℝ) (x : Vec d)
    {k : ℕ} (hk : k < r) :
    firstBad A c g x (k+1) =
      (firstBad A c g x k).or (if 1+1/8 < dot (A ⟨k,hk⟩) x then some ⟨A ⟨k,hk⟩,1⟩ else none) := by
  have hs : k+1 < (rowsFor A c g).length := by simpa [rowsFor] using hk
  rw [firstBad, List.take_succ_eq_append_getElem hs]
  unfold badRow
  rw [List.find?_append]
  congr 1
  simp [rowsFor,List.find?_cons]
  split_ifs with hh <;> simp [hh]

private theorem firstBad_all {r d : ℕ} (A : Matrix r d) (c : Vec d) (g : ℝ) (x : Vec d) :
    firstBad A c g x r = badRow (rowsFor A c g) x := by
  rw [firstBad, List.take_of_length_le]
  simp [rowsFor]

def resultVec {d : ℕ} (x : Vec d) (o : Option (Row d)) : Vec d :=
  match o with | none => x | some q => update q.coeff x

def badFlag {d : ℕ} (o : Option (Row d)) : ℝ := if o.isSome then 1 else 0

def scanBudget (r d : ℕ) :=
  25 + checkBudget d (arithBudget d r) +
    loopBudget r (checkBudget d (arithBudget d r) + 4)

theorem exec_scan {r d : ℕ} (s : Store) (A : Matrix r d) (c : Vec d) (guess : ℕ)
    (hin : Inputs s A c) (hg : s.ns 27 = guess) (hrate : s.rs 25 = rate d)
    (hs0 : s.rs 26 = 0) :
    Runs I ω oneScan s (scanBudget r d) (fun v =>
      let o := badRow (rowsFor A c ((guess:ℝ)/8)) (vec s 5 d)
      vec v 5 d = resultVec (vec s 5 d) o ∧ v.rs 26 = if o.isNone then 1 else 0) := by
  let B := arithBudget d r
  let g := (guess:ℝ)/8
  let x := vec s 5 d
  let start := s.setR 27 0
  have hstart : Frame scanSlots s start := (Frame.refl _ _).setR 27 0 (by decide)
  have hin' := hin.transport (enlarge hstart (by decide : scanSlots ⊆ inputSlots))
  have payoff : Expr start rowSlots (0-atCol 3) (fun j => -c j) B := profit_row hin'
  have first : Exec I ω (.letR 27 0) s start 2 := by
    have hh := Exec.letR (I := I) (ω := ω) s 27 (0:R)
    rwa [re_0] at hh
  obtain ⟨u,k,eu,hk,hu⟩ := exec_check (I := I) (ω := ω) start hin'.d_eq _ (0-.nat guessReg/8) _ (-g)
    (work_access_le d r) (by exact hrate) payoff (by
      intro t ht
      have ho : t.ns 27 = guess := (ht (.nat 27) (by decide)).trans hg
      exact ⟨by simp [g,guessReg,N.eval,ho],by change 1+(1+1+1)+1 ≤ _; dsimp [B,arithBudget]; omega⟩)
  let Inv (p : ℕ) (t : Store) := Frame scanSlots s t ∧
    vec t 5 d = resultVec x (firstBad A c g x p) ∧ t.rs 27 = badFlag (firstBad A c g x p)
  have fu := hstart.trans (enlarge (row_frame eu) (by decide : rowSlots ⊆ scanSlots))
  have hbase : Inv 0 u := by
    refine ⟨fu, ?_, ?_⟩
    · rw [firstBad_zero]
      change vec u 5 d = resultVec x (if _ then _ else _)
      have h := hu.data
      change vec u 5 d = (if -g+1/8 < dot (fun j => -c j) x then _ else _) at h
      split_ifs at h ⊢ <;> exact h
    · rw [firstBad_zero]
      have h := hu.flag
      have hzero : start.rs 27 = 0 := by simp [start,Store.setR]
      change u.rs 27 = (if -g+1/8 < dot (fun j => -c j) x then 1 else start.rs 27) at h
      rw [hzero] at h
      split_ifs at h ⊢ <;> exact h
  have hr : rReg.eval u = r := (fu (.nat 4) (by decide)).trans hin.r_eq
  let body := C.itePos (.var 27) .skip (checkRow matrixCoeff 1)
  have step (p : ℕ) (hp : p < rReg.eval u) (t : Store) (ht : Inv p t) :
      ∃ v l, Exec I ω body (t.setN 26 p) v l ∧ l ≤ checkBudget d B + 4 ∧ Inv (p+1) v := by
    let j : Fin r := ⟨p,hr ▸ hp⟩
    let t' := t.setN 26 p
    have ft : Frame scanSlots s t' := ht.1.setN 26 p (by decide)
    have inp := hin.transport (enlarge ft (by decide : scanSlots ⊆ inputSlots))
    cases ho : firstBad A c g x p with
    | some q =>
      have htflag : t'.rs 27 = 1 := by simpa [ho,badFlag,t',Store.setN] using ht.2.2
      have hh : firstBad A c g x (p+1) = some q := by rw [firstBad_succ _ _ _ _ j.isLt,ho]; rfl
      refine ⟨t',_,Exec.ite_true (e := .var 27) (by change 0 < t'.rs 27;rw [htflag];norm_num)
        (Exec.skip _),by change 1+1+0+1 ≤ _;omega,ft,?_,?_⟩
      · simpa only [ho,hh,t',Store.setN,vec] using ht.2.1
      · rw [hh]
        exact htflag
    | none =>
      have hvec : vec t' 5 d = x := by simpa only [ho,resultVec,t',vec,Store.setN] using ht.2.1
      have htflag : t'.rs 27 = 0 := by simpa [ho,badFlag,t',Store.setN] using ht.2.2
      obtain ⟨v,l,ev,hl,hv⟩ := exec_check (I := I) (ω := ω) t' inp.d_eq _ 1 (A j) 1
        (work_access_le d r) ((ft (.real 25) (by decide)).trans hrate)
        (coeff_row inp j (by simp [t',Store.setN,j])) (fun w _ =>
          ⟨re_1 w,by change 1 ≤ arithBudget d r; dsimp [arithBudget];omega⟩)
      refine ⟨v,_,Exec.ite_false (e := .var 27) (by change t'.rs 27 ≤ 0;rw [htflag]) ev,
        by change 1+1+l ≤ _;dsimp only [B];omega, ft.trans (enlarge (row_frame ev) (by decide : rowSlots ⊆ scanSlots)),?_,?_⟩
      · rw [firstBad_succ _ _ _ _ j.isLt,ho]
        have h := hv.data
        rw [hvec] at h
        split_ifs at h ⊢ <;> exact h
      · rw [firstBad_succ _ _ _ _ j.isLt,ho]
        have h := hv.flag
        rw [hvec,htflag] at h
        split_ifs at h ⊢ <;> exact h
  obtain ⟨v,l,ev,hl,hv⟩ := forN_inv (I := I) (ω := ω) Inv hbase step
  let v' := v.setN 26 (rReg.eval u)
  have fv : Frame scanSlots s v' := hv.1.setN _ _ (by decide)
  let o := badRow (rowsFor A c g) x
  have hvV : vec v' 5 d = resultVec x o := by
    simpa only [v',Store.setN,vec,o,hr, firstBad_all] using hv.2.1
  have hvF : v'.rs 27 = badFlag o := by simpa only [v',Store.setN,o,hr, firstBad_all] using hv.2.2
  have finish :
      Runs I ω (.itePos (.var 27) .skip (.letR 26 1)) v' 4 (fun w =>
        vec w 5 d = resultVec x o ∧ w.rs 26 = if o.isNone then 1 else 0) := by
    cases ho : o with
    | some q =>
      have hf : v'.rs 27 = 1 := by simpa [ho,badFlag] using hvF
      refine ⟨_,_,Exec.ite_true (e := .var 27) (by simpa only [re_var,hf] using (zero_lt_one : (0:ℝ)<1))
        (Exec.skip _),by change 3 ≤ 4;decide,?_,?_⟩
      · simpa only [ho] using hvV
      · exact (fv (.real 26) (by decide)).trans hs0
    | none =>
      have hf : v'.rs 27 = 0 := by simpa [ho,badFlag] using hvF
      refine ⟨_,_,Exec.ite_false (e := .var 27) (by simp only [re_var,hf,le_refl])
        (Exec.letR _ 26 1),by change 4 ≤ 4;decide,?_,?_⟩
      · simpa only [ho,vec,Store.setR] using hvV
      · simp [Store.setR]
  obtain ⟨w,a,ea,ha,hw⟩ := finish
  refine ⟨w,_,Exec.seq first (Exec.seq eu (Exec.seq ev ea)),?_,hw⟩
  change l ≤ 1+4+5*(rReg.eval u)+(rReg.eval u)*(checkBudget d B+4) at hl
  rw [hr] at hl
  dsimp only [scanBudget,loopBudget,B] at *
  omega

end
end PandoraKnapsack.Skipping.ArrayRAM.Packing

namespace PandoraKnapsack.Skipping.ArrayRAM.Packing
open PandoraPacking
noncomputable section
variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

def projectSlots : List Slot := [.nat 25,.nat 26,.nat 28,.real 26,.real 27,.real 28,.real 29,.table 5]

def trialSlots : List Slot := [.nat 25,.nat 26,.nat 28,.real 26,.real 27,.real 28,.real 29,.real 30,.table 4,.table 5]

private theorem project_frame {s u : Store} {k : ℕ} (h : Exec I ω oneScan s u k) :
    Frame projectSlots s u := h.toFrame (by
  intro l hw
  simp [oneScan,checkRow,projectedUpdate,scalarProduct,columnsLoop,writes,projectSlots] at hw ⊢
  tauto)

private theorem fuel_eval (s : Store) (d : ℕ) (hd : s.ns 3 = d) : fuelExpr.eval s = fuelBound d := by
  change 64*(s.ns 3+1)*(s.ns 3+1)+1 = _
  rw [hd]
  simp only [fuelBound,pow_two,Nat.mul_assoc]

def iterBudget (r d : ℕ) :=
  fuelExpr.work+4+5*(fuelBound d)+(fuelBound d)*(scanBudget r d+3)

private theorem run_iters {r d : ℕ} (s : Store) (A : Matrix r d) (c : Vec d) (guess : ℕ)
    (hin : Inputs s A c) (hg : s.ns 27 = guess) (hrate : s.rs 25 = rate d) (hs : s.rs 26 = 0) :
    Runs I ω (.forN 28 fuelExpr (.itePos (.var 26) .skip oneScan)) s (iterBudget r d)
      (fun u => (if 0 < u.rs 26 then some (vec u 5 d) else none) =
        iterate (rowsFor A c ((guess:ℝ)/8)) (fuelBound d) (vec s 5 d)) := by
  let F := fuelBound d
  let rows := rowsFor A c ((guess:ℝ)/8)
  let res := iterate rows F (vec s 5 d)
  let Inv (p : ℕ) (u : Store) := Frame projectSlots s u ∧ (u.rs 26 = 0 ∨ u.rs 26 = 1) ∧
    (if 0 < u.rs 26 then some (vec u 5 d) else iterate rows (F-p) (vec u 5 d)) = res
  have hz : Inv 0 s := ⟨Frame.refl _ _,Or.inl hs, by simp [hs,res]⟩
  have hF := fuel_eval s d hin.d_eq
  have step (p : ℕ) (hp : p < fuelExpr.eval s) (u : Store) (hu : Inv p u) :
      ∃ v l, Exec I ω (.itePos (.var 26) .skip oneScan) (u.setN 28 p) v l ∧
        l ≤ scanBudget r d + 3 ∧ Inv (p+1) v := by
    let u' := u.setN 28 p
    have fu : Frame projectSlots s u' := hu.1.setN 28 p (by decide)
    have inp := hin.transport (enlarge fu (by decide : projectSlots ⊆ inputSlots))
    have remain : F-p = (F-(p+1))+1 := by change fuelBound d - p = _;rw [hF] at hp;dsimp [F];omega
    rcases hu.2.1 with hzero | hone
    · obtain ⟨v,l,ev,hl,hvec,hflag⟩ := exec_scan (I := I) (ω := ω) u' A c guess inp
        ((fu (.nat 27) (by decide)).trans hg) ((fu (.real 25) (by decide)).trans hrate) (by exact hzero)
      have hpre := hu.2.2
      rw [if_neg (by rw [hzero];linarith),remain,iterate] at hpre
      let o := badRow rows (vec u 5 d)
      change vec v 5 d = resultVec (vec u 5 d) o at hvec
      change v.rs 26 = if o.isNone then 1 else 0 at hflag
      refine ⟨v,_,Exec.ite_false (e := .var 26) (by change u.rs 26 ≤ 0;rw [hzero]) ev,
        by change 1+1+l ≤ _;omega,fu.trans (project_frame ev),?_⟩
      cases hoe : o with
      | none =>
        rw [show badRow rows (vec u 5 d) = none from hoe] at hpre
        have hv0 : v.rs 26 = 1 := by simpa [hoe] using hflag
        have hv : vec v 5 d = vec u 5 d := by simpa [hoe,resultVec] using hvec
        exact ⟨Or.inr hv0,by simpa only [hv0,if_pos (zero_lt_one : (0:ℝ)<1),hv,hoe] using hpre⟩
      | some q =>
        rw [show badRow rows (vec u 5 d) = some q from hoe] at hpre
        have hv0 : v.rs 26 = 0 := by simpa [hoe] using hflag
        have hv : vec v 5 d = update q.coeff (vec u 5 d) := by simpa [hoe,resultVec] using hvec
        exact ⟨Or.inl hv0,by simpa only [hv0,lt_irrefl,if_false,hv,hoe] using hpre⟩
    · have hpos : 0 < u.rs 26 := by rw [hone];norm_num
      refine ⟨u',_,Exec.ite_true (e := .var 26) hpos (Exec.skip _),by change 3 ≤ _;omega,
        fu,Or.inr hone,?_⟩
      have hpre := hu.2.2
      rw [if_pos hpos] at hpre
      change (if 0 < u.rs 26 then some (vec u 5 d) else _) = res
      rw [if_pos hpos];exact hpre
  obtain ⟨v,k,ev,hk,hv⟩ := forN_inv (I := I) (ω := ω) Inv hz step
  refine ⟨_,_,ev,?_,?_⟩
  · simpa only [hF,iterBudget] using hk
  · change (if 0 < v.rs 26 then some (vec v 5 d) else none) = res
    simpa only [hF,F,Nat.sub_self,iterate] using hv.2.2

private theorem exec_zero {d : ℕ} (s : Store) (hd : s.ns 3 = d) (t : Fin 16) :
    Runs I ω (fill t 0) s (loopBudget d (putBudget d 1)) (fun u => vec u t d = 0) :=
  exec_fill s hd t 0 0 (fun _ u _ _ _ => ⟨re_0 u,le_rfl⟩)

private theorem exec_scale (s : Store) {d : ℕ} (hd : s.ns 3 = d) :
    Runs I ω (fill 5 ((8/9:R)*atCol 5)) s (loopBudget d (putBudget d (accessBudget d+4)))
      (fun u => vec u 5 d = scale (vec s 5 d)) := by
  apply exec_fill
  · exact hd
  · intro j u _ hj hcell
    constructor
    · simp [atCol,N.eval,hj,hcell,scale,vec]
    · have hw := (expr_atCol u 5 [] (by decide) (le_refl (accessBudget d)) u (Frame.refl _ _) j hj).2
      change 3+(atCol 5).work u+1 ≤ _
      omega

private theorem exec_copy (s : Store) {d : ℕ} (hd : s.ns 3 = d) :
    Runs I ω (fill 4 (atCol 5)) s (loopBudget d (putBudget d (accessBudget d)))
      (fun u => vec u 4 d = vec s 5 d) :=
  exec_fill s hd 4 _ _ (fun j u hf hj _ =>
    expr_atCol s 5 (fillSlots 4) (by decide) (le_refl (accessBudget d)) u hf j hj)

private def chooseVecCode := C.seq (scalarProduct (atCol 3) (atCol 4)) <|
  .seq (.letR 30 (.var 28)) <|
  .seq (scalarProduct (atCol 3) (atCol 5)) <|
  .itePos (.var 28 - .var 30) (fill 4 (atCol 5)) .skip

def chooseBudget (d : ℕ) :=
  2*dotBudget d (accessBudget d)+loopBudget d (putBudget d (accessBudget d))+12

private theorem choose_result {r d : ℕ} (s : Store) {A : Matrix r d} {c : Vec d} (hin : Inputs s A c) :
    Runs I ω chooseVecCode s (chooseBudget d) (fun w => vec w 4 d = better c (vec s 4 d) (vec s 5 d)) := by
  let x := vec s 4 d
  let y := vec s 5 d
  obtain ⟨u,k,eu,hk,hu⟩ := exec_dot (I := I) (ω := ω) s hin.d_eq _ _ _ _
    (expr_atCol s 3 dotSlots (by decide) (le_refl (accessBudget d)))
    (expr_atCol s 4 dotSlots (by decide) (le_refl (accessBudget d)))
  change u.rs 28 = dot (vec s 3 d) x at hu
  rw [hin.profit] at hu
  let t := u.setR 30 (u.rs 28)
  have hsave : Exec I ω (.letR 30 (.var 28)) u t 2 := Exec.letR u 30 (.var 28)
  have f1 := packing_dot_frame eu
  let slots : List Slot := [.nat 25,.real 28,.real 30]
  have ft : Frame slots s t := (enlarge f1 (by decide : dotSlots ⊆ slots)).setR 30 _ (by decide)
  have hdt : t.ns 3 = d := (ft (.nat 3) (by decide)).trans hin.d_eq
  have ct : vec t 3 d = c := (funext fun j : Fin d => congrFun (ft (.table 3) (by decide)) j.val).trans hin.profit
  have yt : vec t 5 d = y := funext fun j => congrFun (ft (.table 5) (by decide)) j.val
  obtain ⟨v,l,ev,hl,hv⟩ := exec_dot (I := I) (ω := ω) t hdt _ _ _ _
    (expr_atCol t 3 dotSlots (by decide) (le_refl (accessBudget d)))
    (expr_atCol t 5 dotSlots (by decide) (le_refl (accessBudget d)))
  rw [ct,yt] at hv
  have f2 := packing_dot_frame ev
  have fv := ft.trans (enlarge f2 (by decide : dotSlots ⊆ slots))
  have oldVal : v.rs 30 = dot c x := (f2 (.real 30) (by decide)).trans (by
    change t.rs 30 = dot c x
    simpa [t,Store.setR] using hu)
  have newVal : (.var 28 - .var 30 : R).eval v = dot c y - dot c x := by rw [re_sub,re_var,re_var,hv,oldVal]
  by_cases hcmp : dot c x < dot c y
  · obtain ⟨w,a,ew,ha,hw⟩ := exec_copy (I := I) (ω := ω) v ((fv (.nat 3) (by decide)).trans hin.d_eq)
    refine ⟨w,_,Exec.seq eu (Exec.seq hsave (Exec.seq ev
      (Exec.ite_true (e := .var 28-.var 30) (by rw [newVal];linarith) ew))),?_,?_⟩
    · change k+(2+(l+(3+1+a+1))) ≤ _
      dsimp [chooseBudget];omega
    · change vec w 4 d = better c x y
      rw [better,if_pos hcmp,hw]
      exact funext fun j => congrFun (fv (.table 5) (by decide)) j.val
  · refine ⟨v,_,Exec.seq eu (Exec.seq hsave (Exec.seq ev
      (Exec.ite_false (e := .var 28-.var 30) (by rw [newVal];linarith) (Exec.skip v)))),?_,?_⟩
    · change k+(2+(l+(3+1+0))) ≤ _
      dsimp [chooseBudget];omega
    · rw [better,if_neg hcmp]
      exact funext fun j => congrFun (fv (.table 4) (by decide)) j.val

def trialBudget (r d : ℕ) :=
  2*loopBudget d (putBudget d 1)+iterBudget r d+loopBudget d (putBudget d (accessBudget d+4))+chooseBudget d+12

theorem exec_guess {r d : ℕ} (s : Store) (A : Matrix r d) (c : Vec d) (guess : ℕ)
    (hin : Inputs s A c) (hg : s.ns 27 = guess) (hrate : s.rs 25 = rate d) :
    Runs I ω tryGuess s (trialBudget r d) (fun w => vec w 4 d = better c (vec s 4 d) (trial A c guess)) := by
  obtain ⟨u,k,eu,hk,hu⟩ := exec_zero (I := I) (ω := ω) s hin.d_eq 5
  let t := u.setR 26 0
  have reset : Exec I ω (.letR 26 0) u t 2 := by
    have hh := Exec.letR (I := I) (ω := ω) u 26 (0:R)
    rwa [re_0] at hh
  have f0 : Frame projectSlots s u := eu.toFrame (by
    intro key hw; simp [fill,columnsLoop,writes,projectSlots] at hw ⊢; tauto)
  have ft : Frame projectSlots s t := f0.setR 26 _ (by decide)
  have inT := hin.transport (enlarge ft (by decide : projectSlots ⊆ inputSlots))
  obtain ⟨v,l,ev,hl,hv⟩ := run_iters (I := I) (ω := ω) t A c guess inT
    ((ft (.nat 27) (by decide)).trans hg) ((ft (.real 25) (by decide)).trans hrate) (by simp [t,Store.setR])
  have f1 : Frame projectSlots t v := ev.toFrame (by
    intro key hw
    simp [oneScan,checkRow,projectedUpdate,scalarProduct,columnsLoop,writes,projectSlots] at hw ⊢
    tauto)
  have fv := ft.trans f1
  have hdv : v.ns 3 = d := (fv (.nat 3) (by decide)).trans hin.d_eq
  change (if 0 < v.rs 26 then some (vec v 5 d) else none) =
    iterate (rowsFor A c ((guess:ℝ)/8)) (fuelBound d) (vec u 5 d) at hv
  rw [hu] at hv
  let finish := C.itePos (.var 26) (fill 5 ((8/9:R)*atCol 5)) (fill 5 0)
  have fin : Runs I ω finish v (loopBudget d (putBudget d (accessBudget d+4)) + loopBudget d (putBudget d 1)+3)
      (fun w => vec w 5 d = trial A c guess) := by
    by_cases hh : 0 < v.rs 26
    · obtain ⟨w,k,ew,hk,hw⟩ := exec_scale (I := I) (ω := ω) v hdv
      refine ⟨w,_,Exec.ite_true (e := .var 26) hh ew,by change 1+1+k+1 ≤ _;omega,?_⟩
      rw [if_pos hh] at hv
      simpa only [trial,← hv] using hw
    · obtain ⟨w,k,ew,hk,hw⟩ := exec_zero (I := I) (ω := ω) v hdv 5
      refine ⟨w,_,Exec.ite_false (e := .var 26) (le_of_not_gt hh) ew,by change 1+1+k ≤ _;omega,?_⟩
      rw [if_neg hh] at hv
      simpa only [trial,← hv] using hw
  obtain ⟨w,a,ew,ha,hw⟩ := fin
  have f2 : Frame projectSlots v w := ew.toFrame (by
    intro key hm; simp [finish,fill,columnsLoop,writes,projectSlots] at hm ⊢;tauto)
  have fw := fv.trans f2
  obtain ⟨z,b,ez,hb,hz⟩ := choose_result (I := I) (ω := ω) w
    (hin.transport (enlarge fw (by decide : projectSlots ⊆ inputSlots)))
  refine ⟨z,_,Exec.seq eu (Exec.seq reset (Exec.seq ev (Exec.seq ew ez))),?_,?_⟩
  · dsimp [trialBudget];omega
  · change vec z 4 d = better c (vec s 4 d) (trial A c guess)
    rw [hz,hw]
    exact congrArg (fun x => better c x (trial A c guess)) (funext fun j : Fin d =>
      congrFun (fw (.table 4) (by decide)) j.val)

def solveBudget (r d : ℕ) :=
  loopBudget d (putBudget d 1) + 20 + (8*dReg+1).work + 4 + 5*(8*d+1) + (8*d+1)*trialBudget r d

private def footprint : C → List Slot
  | .skip => []
  | .seq a b | .itePos _ a b => footprint a ++ footprint b
  | .whilePos _ a => footprint a
  | .forN i _ a => .nat i :: footprint a
  | .letN r _ => [.nat r]
  | .letR r _ | .value r _ | .cost r _ _ | .cdf r _ _ _ | .truncMean r _ _ _ => [.real r]
  | .put t _ _ => [.table t]
  | .out .. => [.out]
  | .uniform r => [.draws,.real r]

private theorem writes_iff (c : C) (l : Slot) : writes c l ↔ l ∈ footprint c := by
  induction c <;> simp_all [footprint,writes]

private theorem trialFrame {s v : Store} {k : ℕ} (h : Exec I ω tryGuess s v k) :
    Frame trialSlots s v := h.toFrame (fun l hw =>
  (by decide : footprint tryGuess ⊆ trialSlots) ((writes_iff _ _).mp hw))

theorem exec_packing {r d : ℕ} (s : Store) (A : Matrix r d) (c : Vec d) (hin : Inputs s A c) :
    Runs I ω packingCode s (solveBudget r d) (fun w => vec w 4 d = solve A c ∧ Frame inputSlots s w) := by
  obtain ⟨u,k,eu,hk,hu⟩ := exec_zero (I := I) (ω := ω) s hin.d_eq 4
  have f0 : Frame inputSlots s u := eu.toFrame (by
    intro l hw
    simp [fill,columnsLoop,writes,inputSlots] at hw ⊢
    tauto)
  let eta : R := 1/(8*.nat (dReg+1))
  let t := u.setR 25 (eta.eval u)
  have eset := Exec.letR (I := I) (ω := ω) u 25 eta
  have ft : Frame inputSlots s t := f0.setR 25 _ (by decide)
  have hd : u.ns 3 = d := (f0 (.nat 3) (by decide)).trans hin.d_eq
  have he : t.rs 25 = rate d := by
    simp only [t,Store.setR,Function.update_self,eta,re_div,re_1,re_mul,re_8,re_nat]
    change 1/(8*(↑(u.ns 3+1):ℝ)) = rate d
    rw [hd];rfl
  let inv (guess : ℕ) (v : Store) := Frame inputSlots s v ∧ vec v 4 d = search A c guess ∧ v.rs 25 = rate d
  have h0 : inv 0 t := ⟨ft,by exact hu,he⟩
  have hL : (8*dReg+1).eval t = 8*d+1 := by change 8*u.ns 3+1 = _;rw [hd]
  have step (p : ℕ) (_ : p < (8*dReg+1).eval t) (v : Store) (hv : inv p v) :
      ∃ w l, Exec I ω tryGuess (v.setN 27 p) w l ∧ l ≤ trialBudget r d ∧ inv (p+1) w := by
    let v' := v.setN 27 p
    have fv : Frame inputSlots s v' := hv.1.setN 27 p (by decide)
    obtain ⟨w,l,ew,hl,hw⟩ := exec_guess (I := I) (ω := ω) v' A c p (hin.transport fv)
      (by simp [v',Store.setN]) (by exact hv.2.2)
    have f1 := trialFrame ew
    refine ⟨w,l,ew,hl,fv.trans (enlarge f1 (by decide : trialSlots ⊆ inputSlots)),?_,?_⟩
    · exact hw.trans (congrArg (fun x => better c x (trial A c p)) hv.2.1)
    · exact (f1 (.real 25) (by decide)).trans hv.2.2
  obtain ⟨v,l,ev,hl,hv⟩ := forN_inv (I := I) (ω := ω) inv h0 step
  refine ⟨_,_,Exec.seq eu (Exec.seq eset ev),?_,?_,hv.1.setN _ _ (by decide)⟩
  · have heta : eta.work u + 1 ≤ 20 := by change 1+(1+3+1)+1+1 ≤ 20; decide
    rw [hL] at hl
    dsimp [solveBudget];omega
  · change vec v 4 d = solve A c
    simpa only [hL,solve] using hv.2.1

end
end PandoraKnapsack.Skipping.ArrayRAM.Packing

namespace PandoraKnapsack.Skipping.ArrayRAM.Packing

private def PolyBound (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ k, ∀ r d, f r d ≤ (r+d+2)^k

private theorem pc (a : ℕ) : PolyBound (fun _ _ => a) := by
  refine ⟨a,fun r d => Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by omega) _)⟩

private theorem pr : PolyBound (fun r _ => r) := ⟨1, fun r d => by simp;omega⟩
private theorem pd : PolyBound (fun _ d => d) := ⟨1, fun r d => by simp;omega⟩

private theorem pm {f g : ℕ → ℕ → ℕ} (a : PolyBound f) (b : PolyBound g) :
    PolyBound (fun r d => f r d * g r d) := by
  obtain ⟨k,hk⟩ := a
  obtain ⟨l,hl⟩ := b
  exact ⟨k+l,fun r d => by rw [pow_add];exact Nat.mul_le_mul (hk _ _) (hl _ _)⟩

private theorem pa {f g : ℕ → ℕ → ℕ} (a : PolyBound f) (b : PolyBound g) :
    PolyBound (fun r d => f r d + g r d) := by
  obtain ⟨k,hk⟩ := a
  obtain ⟨l,hl⟩ := b
  refine ⟨max k l+1,fun r d => ?_⟩
  let U := r+d+2
  have hu : 0 < U := by dsimp [U];omega
  have h1 := (hk r d).trans (Nat.pow_le_pow_right hu (le_max_left k l))
  have h2 := (hl r d).trans (Nat.pow_le_pow_right hu (le_max_right k l))
  change f r d + g r d ≤ U^(max k l+1)
  rw [pow_succ]
  calc
    _ ≤ U^max k l + U^max k l := Nat.add_le_add h1 h2
    _ = U^max k l * 2 := by omega
    _ ≤ _ := Nat.mul_le_mul_left _ (by dsimp [U];omega)

private inductive CostExpr
  | lit (a : ℕ) | row | col | add (a b : CostExpr) | mul (a b : CostExpr) | sq (a : CostExpr)
private instance (a : ℕ) : OfNat CostExpr a := ⟨.lit a⟩
private instance : Add CostExpr := ⟨.add⟩
private instance : Mul CostExpr := ⟨.mul⟩

private def CostExpr.val : CostExpr → ℕ → ℕ → ℕ
  | .lit a,_,_ => a
  | .row,r,_ => r
  | .col,_,d => d
  | .add a b,r,d => a.val r d+b.val r d
  | .mul a b,r,d => a.val r d*b.val r d
  | .sq a,r,d => (a.val r d)^2

private theorem CostExpr.poly (q : CostExpr) : PolyBound q.val := by
  induction q with
  | lit k => exact pc k
  | row => exact pr
  | col => exact pd
  | add a b ha hb => exact pa ha hb
  | mul a b ha hb => exact pm ha hb
  | sq a ha => simpa only [CostExpr.val,pow_two] using pm ha ha

private def fullCost : CostExpr :=
  let r := CostExpr.row
  let d := CostExpr.col
  let access := 110*(d+1)
  let arith := 500*(d+1)*(r+1)+500
  let dot (b : CostExpr) := 10+5*d+d*(2*b+5)
  let loop (n per : CostExpr) := 5+5*n+n*per
  let put (b : CostExpr) := access+b+4
  let update := loop d (4*access+2*arith+40)
  let check := dot arith+update+arith+20
  let scan := 25+check+loop r (check+4)
  let fuel := 64*(d+1).sq+1
  let iters := CostExpr.lit fuelExpr.work+4+5*fuel+fuel*(scan+3)
  let choose := 2*dot access+loop d (put access)+12
  let trial := 2*loop d (put 1)+iters+loop d (put (access+4))+choose+12
  loop d (put 1)+20+CostExpr.lit (8*dReg+1).work+4+5*(8*d+1)+(8*d+1)*trial

theorem packing_budget_polynomial : ∃ k, ∀ r d, solveBudget r d ≤ (r+d+2)^k := by
  obtain ⟨k,hk⟩ := fullCost.poly
  exact ⟨k,fun r d => (hk r d : fullCost.val r d ≤ _)⟩

end PandoraKnapsack.Skipping.ArrayRAM.Packing

open PandoraKnapsack.Skipping PandoraKnapsack.Skipping.ArrayRAM
open PandoraKnapsack.Skipping.ArrayRAM.Packing

theorem solution :
    ∃ e : ℕ, ∀ {r d n m T : ℕ} (I : Instance n m T) (ω : ℕ → ℝ) (s : Store)
      (A : PandoraPacking.Matrix r d) (c : PandoraPacking.Vec d),
      s.ns 3 = d → s.ns 4 = r →
      (∀ i : Fin r, ∀ j : Fin d, s.tab 2 (i.val * d + j.val) = A i j) →
      (∀ j : Fin d, s.tab 3 j.val = c j) →
      ∃ v k, Exec I ω packingCode s v k ∧ k ≤ (r+d+2)^e ∧
        (∀ j : Fin d, v.tab 4 j.val = PandoraPacking.solve A c j) ∧
        (∀ j < 25, v.ns j = s.ns j) ∧ (∀ j < 25, v.rs j = s.rs j) ∧
        (∀ t : Fin 16, t ≠ 4 → t ≠ 5 → v.tab t = s.tab t) ∧
        v.out = s.out ∧ v.draws = s.draws  := by
  obtain ⟨e,he⟩ := packing_budget_polynomial
  refine ⟨e,?_⟩
  intro r d n m T I ω s A c hd hr fa fc
  obtain ⟨v,k,hv,hk,value,frame⟩ := exec_packing (I := I) (ω := ω) s A c
    ⟨hd,hr,fa,funext fc⟩
  refine ⟨v,k,hv,hk.trans (he r d),fun j => congrFun value j,?_,?_,?_,
    frame .out (by decide),frame .draws (by decide)⟩
  · intro j hj
    exact frame (.nat j) (by simp [inputSlots]; omega)
  · intro j hj
    exact frame (.real j) (by simp [inputSlots]; omega)
  · intro t h4 h5
    exact frame (.table t) (by simp [inputSlots,h4,h5])
