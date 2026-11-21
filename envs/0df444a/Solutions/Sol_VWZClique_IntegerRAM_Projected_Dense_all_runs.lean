-- Prove2me | solution 1 for VWZClique.IntegerRAM.Projected.Dense.all_runs
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T14:08:42.26302+00:00
-- url     : https://prove2.me/submissions/67450dab-7d4c-4318-8891-ce722f100653

import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_VWZClique_Contraction
import Definitions.Def_VWZClique_Count
import Definitions.Def_VWZClique_FoldedSum
import Definitions.Def_VWZClique_NativeCliqueCompiler
import Definitions.Def_VWZClique_NativeProjectionContract
import Definitions.Def_VWZClique_Operators
import Definitions.Def_VWZClique_Weighted
import Mathlib
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring
import Theorems.Thm_VWZClique_IntegerRAM_Projected_SquareCaller_square_run

/- NativeFoldBits -/
section
namespace VWZClique.IntegerRAM.FoldBits
open Structured

def Capacity (W M : ℕ) := (M:ℤ) < (2:ℤ)^(W-1)
theorem Capacity.fits {W M : ℕ} (cap : Capacity W M) {j : ℤ} (lo : -(M:ℤ) ≤ j) (hi : j ≤ M) : Fits W j := by
  unfold Capacity at cap
  exact ⟨by change -(2:ℤ)^(W-1) ≤ j; omega,hi.trans_lt cap⟩

def bit (b : Bool) : ℕ := if b then 1 else 0

def encode : List Bool → ℕ
  | [] => 0
  | b :: bs => bit b * 2^bs.length + encode bs

theorem encode_lt (bs : List Bool) : encode bs < 2^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs h => cases b <;> simp [encode,bit,pow_succ] <;> omega

def write (m : Memory) : Atom → Memory
  | .one d => update m d 1
  | .add d i j => update m d (m i + m j)
  | .sub d i j => update m d (m i - m j)
  | .mul d i j => update m d (m i * m j)
  | .load d i => update m d (m (m i))
  | .store i j => update m (m i) (m j)

def safe (W : ℕ) (m : Memory) : Atom → Prop
  | .load _ i | .store i _ => Fits W (m i)
  | _ => True

def Safe (W : ℕ) (m : Memory) : List Atom → Prop
  | [] => True
  | h :: t => safe W m h ∧ Safe W (write m h) t

theorem code_runs (W : ℕ) (xs : List Atom) (m : Memory) (hf : Safe W m xs) :
    Runs W (code xs) m xs.length (xs.foldl write m) := by
  induction xs generalizing m with
  | nil => exact .skip m
  | cons h xs ih =>
    have step : Step W h m (write m h) := by
      cases h with
      | one => exact .one ..
      | add => exact .add ..
      | sub => exact .sub ..
      | mul => exact .mul ..
      | load => exact .load _ _ _ hf.1
      | store => exact .store _ _ _ hf.1
    simpa only [code,List.foldl_cons,List.length_cons,Nat.add_comm 1] using
      Runs.seq (Runs.atom step) (ih (write m h) hf.2)

end VWZClique.IntegerRAM.FoldBits
end

/- NativeProjectionBatchStep -/
section
namespace VWZClique.IntegerRAM.Projected.Batch
open Structured FoldBits

def privateCell (j : ℕ) := j=353 ∨ j=354 ∨ j=355 ∨ j=357 ∨ 360≤j ∧ j≤366
def locked (j : ℤ) := j=0 ∨ j=labels ∨ j=labelCount ∨ clock≤j ∧ j ≤ slab
instance (j : ℤ) : Decidable (locked j) := inferInstanceAs (Decidable (_ ∨ _))
def unchanged (m x : Memory) := ∀ j : ℕ, ¬privateCell j → x j=m j
def linear (n p r c : ℕ) := (p*n+r)*n+c

structure Ctl (n a base i p r c : ℕ) (m : Memory) : Prop where
  side : m 0=n
  base : m labels=base
  size : m labelCount=a
  phase : m slab=p
  row : m rowReg=r
  col : m colReg=c
  time : m clock=i
  total : m limit=((a*n*n:ℕ):ℤ)
  one : m unit=1

theorem Ctl.stable {n a base i p r c : ℕ} {m x : Memory} (h : Ctl n a base i p r c m)
    (fr : ∀ j, locked j → x j=m j) : Ctl n a base i p r c x := by
  rcases h with ⟨u,v,w,p,r,c,i,t,o⟩
  constructor <;> rw [fr _ (by decide)] <;> assumption

theorem headers_run {W M n a b i p r c : ℕ} (room : Graph.Division.Room W M)
    (space : b+p≤M) (m : Memory) (h : Ctl n a b i p r c m) :
    ∃ x, Runs W (code headers) m 5 x ∧ x 353=m ((b+p:ℕ):ℤ) ∧ x 354=r ∧ x 355=c ∧ x 357=p ∧
      unchanged m x ∧ ∀ j : ℤ, locked j → x j=m j := by
  let x := headers.foldl write m
  have b0 : m 358=b := h.base
  have p0 : m 366=p := h.phase
  have r0 : m 361=r := h.row
  have c0 : m 362=c := h.col
  have one : m 363=1 := h.one
  have fit : Fits W ((b:ℤ)+p) := room.fits (by omega) (by omega)
  have safeH : Safe W m headers := by simpa [headers,Safe,safe,write,update,carryTest,labels,slab,b0,p0] using fit
  refine ⟨x,code_runs _ _ _ safeH,?_,?_,?_,?_,?_,?_⟩
  all_goals try intro j hj
  all_goals try dsimp [privateCell,locked,labels,labelCount,clock,slab] at hj
  all_goals simp [x,headers,write,update,carryTest,labels,slab,rowReg,colReg,unit,b0,p0,r0,c0,one] <;> first | omega | (split_ifs <;> omega)

set_option maxHeartbeats 800000 in
theorem carry_runs {W M n a b i p r c : ℕ} (cap : Graph.Division.Room W M) (space : n≤M) (hn : 0<n)
    (m : Memory) (h : Ctl n a b i p r c m) (rr : r<n) (cc : c<n) :
    ∃ t≤9, ∃ x p' r' c', Runs W carry m t x ∧ Ctl n a b i p' r' c' x ∧
      r'<n ∧ c'<n ∧ linear n p' r' c'=linear n p r c+1 ∧ unchanged m x := by
  let x := plusCol.foldl write m
  have first : Runs W (code plusCol) m 2 x := code_runs _ _ _ (by simp [plusCol,Safe,safe])
  obtain ⟨nn,bb,aa,pp,rv,cv,ii,tt,one⟩ := h
  dsimp [labels,labelCount,slab,rowReg,colReg,clock,limit,unit] at nn bb aa pp rv cv ii tt one
  have test₁ : x carryTest=(c:ℤ)+1-n := by simp [x,plusCol,write,update,carryTest,colReg,unit,cv,one,nn]
  have fit₁ : Fits W (x carryTest) := by rw [test₁];apply cap.fits <;> omega
  by_cases noc : c+1<n
  · refine ⟨3,by decide,x,p,r,c+1,.seq first (.guard_skip fit₁ (by rw [test₁];omega)),?_,rr,noc,by simp [linear,Nat.add_assoc],?_⟩
    · constructor <;> simp [x,plusCol,write,update,carryTest,colReg,unit,clock,slab,rowReg,limit,labels,labelCount, *]
    · intro j hj;dsimp [privateCell] at hj
      simp [x,plusCol,write,update,carryTest,colReg] <;> first | omega | (split_ifs <;> omega)
  · let y := wrapCol.foldl write x
    have did : c+1=n := by omega
    have second : Runs W (code wrapCol) x 3 y := code_runs _ _ _ (by simp [wrapCol,Safe,safe])
    have test₂ : y carryTest=(r:ℤ)+1-n := by
      simp [y,x,wrapCol,plusCol,write,update,carryTest,colReg,rowReg,unit,rv,one,nn]
    have fit₂ : Fits W (y carryTest) := by rw [test₂];apply cap.fits <;> omega
    by_cases nor : r+1<n
    · refine ⟨7,by decide,y,p,r+1,0,.seq first (.guard_take fit₁ (by rw [test₁];omega)
        (.seq second (.guard_skip fit₂ (by rw [test₂];omega)))),?_,nor,hn,?_,?_⟩
      · constructor <;> simp [y,x,wrapCol,plusCol,write,update,carryTest,colReg,rowReg,unit,clock,slab,limit,labels,labelCount, *]
      · dsimp [linear];nlinarith only [did]
      · intro j hj;dsimp [privateCell] at hj
        simp [x,y,plusCol,wrapCol,write,update,carryTest,rowReg,colReg] <;> first | omega | (split_ifs <;> omega)
    · let z := wrapRow.foldl write y
      have red : r+1=n := by omega
      have third : Runs W (code wrapRow) y 2 z := code_runs _ _ _ (by simp [wrapRow,Safe,safe])
      refine ⟨9,by decide,z,p+1,0,0,.seq first (.guard_take fit₁ (by rw [test₁];omega)
        (.seq second (.guard_take fit₂ (by rw [test₂];omega) third))),?_,hn,hn,?_,?_⟩
      · constructor <;> simp [z,y,x,wrapRow,wrapCol,plusCol,write,update,carryTest,colReg,rowReg,unit,clock,slab,limit,labels,labelCount, *]
      · dsimp [linear];nlinarith only [did,red,congrArg (·*n) red]
      · intro j hj;dsimp [privateCell] at hj
        simp [x,y,z,plusCol,wrapCol,wrapRow,write,update,carryTest,rowReg,colReg,slab] <;> first | omega | (split_ifs <;> omega)

end VWZClique.IntegerRAM.Projected.Batch
end

/- NativeProjectionBatch -/
section
namespace VWZClique.IntegerRAM.Projected.Batch
open Structured FoldBits

theorem init_runs {W n a b : ℕ} (m : Memory) (side : m 0=n) (count : m labelCount=a) (base : m labels=b) :
    ∃ x, Runs W (code init) m 8 x ∧ Ctl n a b 0 0 0 0 x ∧
      x carryTest=((a*n*n:ℕ):ℤ)-1 ∧ unchanged m x := by
  let x := init.foldl write m
  have cnt : m 359=a := count
  have bse : m 358=b := base
  refine ⟨x,code_runs _ _ _ (by simp [init,Safe,safe]),?_,?_,?_⟩
  · constructor <;> simp [x,init,write,update,unit,clock,slab,rowReg,colReg,carryTest,test,limit,labelCount,labels,side,cnt,bse]
  · simp [x,init,write,update,unit,clock,slab,rowReg,colReg,carryTest,test,limit,labelCount,side,cnt]
  · intro j hj;dsimp [privateCell] at hj
    simp [x,init,write,update,unit,clock,slab,rowReg,colReg,carryTest,test,limit] <;> split_ifs <;> omega

/-- Enumerate the retained labels and both short axes in row-major order.
Every job receives the actual stored label ID, its compact index and the two
coordinate words. Its private negative registers may all be overwritten. -/
theorem grid_runs {W M n a b B : ℕ} (hn : 0<n) (cap : Graph.Division.Room W M)
    (nfit : n≤M) (space : b+a≤M) (timeFit : a*n*n≤M)
    (job : Command) (I : ℕ→Memory→Prop)
    (transport : ∀ i x y, unchanged x y → I i x → I i y)
    (ids : Fin a→ℤ) (table : ∀ i x, I i x → ∀ p : Fin a, x ((b+p.val:ℕ):ℤ)=ids p)
    (m : Memory) (dim : m 0=n) (count : m labelCount=a) (base : m labels=b) (start : I 0 m)
    (step : ∀ (p : Fin a) (r c : Fin n) (x : Memory), I (linear n p.val r.val c.val) x →
      x 353=ids p → x 354=r.val → x 355=c.val → x 357=p.val →
      ∃ t≤B, ∃ y, Runs W job x t y ∧ I (linear n p.val r.val c.val+1) y ∧
        ∀ j : ℤ, locked j → y j=x j) :
    ∃ t≤9+(a*n*n)*(B+17), ∃ o, Runs W (grid job) m t o ∧ I (a*n*n) o := by
  obtain ⟨s,initR,sc,cmp,unch⟩ := init_runs (W:=W) m dim count base
  have i0 := transport 0 m s unch start
  let N := a*n*n
  have cmpFits : Fits W (s carryTest) := by rw [cmp];apply cap.fits <;> omega
  by_cases zero : N=0
  · have small : s carryTest<0 := by change a*n*n=0 at zero;rw [cmp,zero];norm_num
    refine ⟨9,by omega,s,.seq initR (.guard_skip cmpFits small),?_⟩
    change I N s;simpa only [zero] using i0
  · let J := fun (q : ℕ) (x : Memory) => I q x ∧ ∃ p r c : ℕ, Ctl n a b q p r c x ∧
      r<n ∧ c<n ∧ linear n p r c=q
    have initial : J 0 s := ⟨i0,0,0,0,sc,hn,hn,by simp [linear]⟩
    have action (q : ℕ) (hq : q<N) (x : Memory) (pre : J q x) :
        ∃ t≤B+14, ∃ y, Runs W (visit job) x t y ∧ y clock=q ∧ y unit=1 ∧ y limit=(N:ℤ) ∧
          J (q+1) (nextMemory y clock test q N) := by
      obtain ⟨ii,p,r,c,ctl,hr,hc,lin⟩ := pre
      have hp : p<a := by
        by_contra! no
        have lower : a*n*n≤(p*n+r)*n := Nat.mul_le_mul_right n ((Nat.mul_le_mul_right n no).trans (Nat.le_add_right (p*n) r))
        change q<a*n*n at hq;dsimp [linear] at lin;omega
      let pp : Fin a := ⟨p,hp⟩
      let rr : Fin n := ⟨r,hr⟩
      let cc : Fin n := ⟨c,hc⟩
      obtain ⟨u,setupH,idVal,rVal,cVal,pVal,fixed,raw⟩ := headers_run cap (by omega : b+p≤M) x ctl
      have iU := transport q x u fixed ii
      obtain ⟨h,charge,v,go,after,keep⟩ := step pp rr cc u (lin ▸ iU) (idVal.trans (table q x ii pp)) rVal cVal pVal
      have cv := (ctl.stable raw).stable keep
      obtain ⟨tt,bb,y,p',r',c',inc,post,rr',cc',adv,frame⟩ := carry_runs cap nfit hn v cv hr hc
      have after₁ : I (q+1) y := transport _ v y frame (lin ▸ after)
      have tickKeep : unchanged y (nextMemory y clock test q N) := by
        intro j notP
        dsimp [privateCell] at notP
        simp [nextMemory,update,clock,test] <;> split_ifs <;> omega
      have tick (j : ℤ) (hj : j≠clock) (jt : j≠test) : nextMemory y clock test q N j=y j := by
        simp [nextMemory,update,hj,jt]
      have conv : Ctl n a b (q+1) p' r' c' (nextMemory y clock test q N) := by
        obtain ⟨nn,base,sz,ph,row,col,clk,tm,unit⟩ := post
        constructor
        all_goals first | rw [tick _ (by decide) (by decide)];assumption | simp [nextMemory,update,clock,test]
      exact ⟨_,by omega,y,.seq setupH (.seq go inc),post.time,post.one,post.total,
        transport _ y _ tickKeep after₁,p',r',c',conv,rr',cc',adv.trans (congrArg (·+1) lin)⟩
    have capN : N≤M := timeFit
    obtain ⟨t,ht,o,run,endSt⟩ := repeatN_runs (W:=W) (B:=B+14) (by omega : 0<N) _
      (by decide : limit≠clock) J (fun q hq => cap.fits (by omega) (by omega))
      action initial
    have good : ¬s carryTest<0 := by rw [cmp];dsimp [N] at zero;omega
    have time : 8+(1+t)≤9+(a*n*n)*(B+17) := by
      rw [show 8+(1+t)=9+t by omega,show B+17=B+14+3 by omega]
      exact Nat.add_le_add_left ht 9
    exact ⟨_,time,o,.seq initR (.guard_take cmpFits good run),endSt.1⟩

end VWZClique.IntegerRAM.Projected.Batch
end

/- NativeProjectionGrid -/
section
namespace VWZClique.IntegerRAM.Projected.Grid
open Structured Batch

abbrev Site (a n : ℕ) := Fin a × Fin n × Fin n

def serial {a n : ℕ} (v : Site a n) := Batch.linear n v.1.val v.2.1.val v.2.2.val

theorem serial_lt {a n : ℕ} (v : Site a n) : serial v<a*n*n := by
  have row := v.2.1.isLt
  have col := v.2.2.isLt
  have slab := Nat.mul_le_mul_right n v.1.isLt
  rw [Nat.succ_mul] at slab
  have hl : v.1.val*n+v.2.1.val<a*n := by omega
  have hw := Nat.mul_le_mul_right n hl
  rw [Nat.succ_mul] at hw
  unfold serial Batch.linear; omega

theorem serial_inj {a n : ℕ} : Function.Injective (@serial a n) := by
  rintro ⟨p,r,c⟩ ⟨q,s,d⟩ h
  change (p.val*n+r.val)*n+c.val=(q.val*n+s.val)*n+d.val at h
  have hcd : c.val=d.val := by simpa [Nat.add_mod,Nat.mod_eq_of_lt c.isLt,Nat.mod_eq_of_lt d.isLt] using congrArg (·%n) h
  have hn : 0<n := Nat.zero_lt_of_lt c.isLt
  have hpr : p.val*n+r.val=q.val*n+s.val := Nat.eq_of_mul_eq_mul_right hn (by omega)
  have hrs : r.val=s.val := by simpa [Nat.add_mod,Nat.mod_eq_of_lt r.isLt,Nat.mod_eq_of_lt s.isLt] using congrArg (·%n) hpr
  have hpq : p.val=q.val := Nat.eq_of_mul_eq_mul_right hn (by omega)
  exact Prod.ext (Fin.ext hpq) (Prod.ext (Fin.ext hrs) (Fin.ext hcd))

/-- Run a fixed job on each stored label and pair of short indices. Job-specific
read-only data and any future inputs are threaded through `S`. The native loop
accumulates the actual output words of every earlier job. -/
theorem collect {W M n a b B : ℕ} {α : Type*} (hn : 0<n) (cap : Graph.Division.Room W M)
    (nfit : n≤M) (space : b+a≤M) (clockFit : a*n*n≤M)
    (job : Command) (S : ℕ → Memory → Prop) (ids : Fin a → ℤ)
    (dest : Site a n → α → ℕ) (value : Site a n → α → ℤ)
    (stable : ∀ i x y, unchanged x y → S i x → S i y)
    (away : ∀ v k, ¬privateCell (dest v k))
    (labels : ∀ i x, S i x → ∀ p : Fin a, x ((b+p.val:ℕ):ℤ)=ids p)
    (m : Memory) (dim : m 0=n) (count : m Batch.labelCount=a) (base : m Batch.labels=b) (initial : S 0 m)
    (step : ∀ (v : Site a n) (x : Memory), S (serial v) x →
      x 353=ids v.1 → x 354=v.2.1.val → x 355=v.2.2.val → x 357=v.1.val →
      ∃ t≤B, ∃ y, Runs W job x t y ∧ S (serial v+1) y ∧ (∀ k, y (dest v k)=value v k) ∧
        (∀ u, serial u<serial v → ∀ k, y (dest u k)=x (dest u k)) ∧
        ∀ j : ℤ, locked j → y j=x j) :
    ∃ t≤9+(a*n*n)*(B+17), ∃ o, Runs W (grid job) m t o ∧ S (a*n*n) o ∧
      ∀ v k, o (dest v k)=value v k := by
  let I := fun i x => S i x ∧ ∀ v, serial v < i → ∀ k, x (dest v k)=value v k
  obtain ⟨t,ht,o,run,st,vals⟩ := grid_runs hn cap nfit space clockFit job I
    (fun i x y frame h => ⟨stable i x y frame h.1,fun v hv k => (frame _ (away v k)).trans (h.2 v hv k)⟩)
    ids (fun i x h => labels i x h.1) m dim count base ⟨initial,fun v hv => by omega⟩ (by
      intro p r c x pre id rr cc pp
      let v : Site a n := (p,r,c)
      obtain ⟨t,ht,y,run,after,values,fixed,lock⟩ := step v x pre.1 id rr cc pp
      refine ⟨t,ht,y,run,⟨after,?_⟩,lock⟩
      intro u hu k
      change serial u<serial v+1 at hu
      by_cases eq : serial u=serial v
      · exact (serial_inj eq) ▸ values k
      · have lt : serial u<serial v := by omega
        exact (fixed u lt k).trans (pre.2 u lt k))
  exact ⟨t,ht,o,run,st,fun v k => vals v (serial_lt v) k⟩

end VWZClique.IntegerRAM.Projected.Grid
end

/- NativeSquareExpr -/
section
namespace VWZClique.IntegerRAM.SquareCode
open Structured

def Expr.val (m : Memory) : Expr → ℤ
  | .zero => 0
  | .one => 1
  | .reg r => m r
  | .read a => m (a.val m)
  | .add a b => a.val m + b.val m
  | .sub a b => a.val m - b.val m
  | .mul a b => a.val m * b.val m

def Expr.safe (d : ℤ) (W : ℕ) (m : Memory) : Expr → Prop
  | .zero | .one => True
  | .reg r => d < r
  | .read a => a.safe d W m ∧ d < a.val m ∧ Fits W (a.val m)
  | .add a b | .sub a b | .mul a b => a.safe d W m ∧ b.safe d W m

theorem carry {d D : ℤ} (hd : D ≤ d) {W : ℕ} {m p : Memory}
    (agree : ∀ i, d < i → p i=m i) (x : Expr) (hx : x.safe d W m) :
    x.val p=x.val m ∧ x.safe D W p := by
  induction x with
  | zero => exact ⟨rfl,True.intro⟩
  | one => exact ⟨rfl,True.intro⟩
  | reg i => exact ⟨agree _ hx,Int.lt_of_le_of_lt hd hx⟩
  | read x ih =>
    obtain ⟨v,s⟩ := ih hx.1
    exact ⟨(congrArg p v).trans (agree _ hx.2.1),s,v ▸ Int.lt_of_le_of_lt hd hx.2.1,v ▸ hx.2.2⟩
  | add a b ia ib | sub a b ia ib | mul a b ia ib =>
    obtain ⟨va,sa⟩ := ia hx.1
    obtain ⟨vb,sb⟩ := ib hx.2
    exact ⟨by simp only [Expr.val,va,vb],sa,sb⟩

def Result (W : ℕ) (m : Memory) (d : ℤ) (x : Expr) : Prop :=
  ∃ out : Memory, Runs W (x.code d) m x.steps out ∧ out d=x.val m ∧ ∀ i, d < i → out i=m i

private theorem joinOp {W : ℕ} {m : Memory} {d : ℤ} (a b x : Expr) (op : Atom) (f : ℤ → ℤ → ℤ)
    (hc : x.code d=binary (a.code d) (b.code (d-1)) op) (ht : x.steps=a.steps+(b.steps+1))
    (hv : x.val m=f (a.val m) (b.val m))
    (action : ∀ p : Memory, Step W op p (update p d (f (p d) (p (d-1)))))
    (ha : Result W m d a) (hb : b.safe d W m)
    (rhs : ∀ p d', b.safe d' W p → Result W p d' b) : Result W m d x := by
  obtain ⟨u,hu,ua,uf⟩ := ha
  obtain ⟨v₀,b₀⟩ := carry (show d-1 ≤ d by omega) uf b hb
  obtain ⟨v,hv',vb,vf⟩ := rhs u _ b₀
  refine ⟨update v d (f (v d) (v (d-1))),?_,?_,?_⟩
  · rw [hc,ht]; exact Runs.seq hu (Runs.seq hv' (Runs.atom (action v)))
  · simp [update,vf d (by omega),ua,vb,v₀,hv]
  · intro i hi
    rw [update,if_neg (by omega),vf _ (by omega),uf _ hi]

theorem Expr.run (x : Expr) {W : ℕ} (m : Memory) (d : ℤ) (hx : x.safe d W m) :
    Result W m d x := by
  induction x generalizing m d with
  | one =>
    exact ⟨_,.atom (.one _ _),by simp [update,val],fun i hi => if_neg (by omega)⟩
  | zero =>
    exact ⟨_,.atom (.sub _ _ _ _),by simp [update,Expr.val],fun i hi => if_neg (by omega)⟩
  | reg i =>
    let p := update m d (m d-m d)
    refine ⟨_,Runs.seq (.atom (.sub _ _ _ _)) (.atom (.add p d d i)),?_,?_⟩
    · have diff : i≠d := by change d < i at hx; omega
      simp [p,update,Expr.val,diff]
    · intro j hj
      simp only [p,update,if_neg (by omega : j≠d)]
  | read a ih =>
    obtain ⟨p,hp,pv,pf⟩ := ih m d hx.1
    have fit : Fits W (p d) := pv ▸ hx.2.2
    refine ⟨_,Runs.seq hp (.atom (.load p d d fit)),?_,?_⟩
    · simp [update,pv,pf _ hx.2.1,Expr.val]
    · intro i hi
      simp only [update,if_neg ((by omega : i≠d)),pf _ hi]
  | add a b ia ib => exact joinOp a b _ _ (·+·) rfl rfl rfl (fun p => .add p _ _ _) (ia _ _ hx.1) hx.2 ib
  | sub a b ia ib => exact joinOp a b _ _ (·-·) rfl rfl rfl (fun p => .sub p _ _ _) (ia _ _ hx.1) hx.2 ib
  | mul a b ia ib => exact joinOp a b _ _ (·*·) rfl rfl rfl (fun p => .mul p _ _ _) (ia _ _ hx.1) hx.2 ib

@[simp] theorem Expr.num_val (m : Memory) (n : ℕ) : (num n).val m=n := by
  induction n <;> simp_all [num,val]

@[simp] theorem Expr.num_safe (m : Memory) (d : ℤ) (W n : ℕ) : (num n).safe d W m := by
  induction n <;> simp_all [num,safe]

theorem write_run {W : ℕ} (m : Memory) (d : ℤ) (a x : Expr)
    (ha : a.safe d W m) (hx : x.safe d W m) (hf : Fits W (a.val m)) :
    ∃ out, Runs W (write d a x) m (a.steps+(x.steps+1)) out ∧
      ∀ i, d < i → out i = if i=a.val m then x.val m else m i := by
  obtain ⟨p,hp,pa,pf⟩ := a.run m d ha
  obtain ⟨v,s⟩ := carry (show d-1 ≤ d by omega) pf x hx
  obtain ⟨q,hq,qx,qf⟩ := x.run p (d-1) s
  have qa := (qf d (by omega)).trans pa
  refine ⟨_,Runs.seq hp (Runs.seq hq (.atom (.store q _ _ (qa ▸ hf)))),?_⟩
  intro i hi
  simp [update,qa,qx,v,qf i (by omega),pf i hi]

end VWZClique.IntegerRAM.SquareCode
end

/- NativeSquareGrid -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured

abbrev Heap := ℕ → ℤ
def heap (m : IntegerRAM.Memory) : Heap := fun a => m a
def regs (i : ℤ) (m p : IntegerRAM.Memory) := ∀ z, (i < z ∨ floor < z ∧ z <  -8) → z < 0 → p z=m z

def foldRange (f : ℕ → Heap → Heap) : ℕ → Heap → Heap
  | 0,H => H
  | q+1,H => f q (foldRange f q H)

/-- A counted native loop, with persistent data modeled by a pure update to
nonnegative cells. The outer loop counters are preserved. -/
theorem loop_run {W N B : ℕ} {i lim : ℤ} (hi : -6 ≤ i) (hi' : i ≤ -4)
    (hl : i < lim) (hl' : lim < 0) (hn : 0 < N) (m : IntegerRAM.Memory) (bound : m lim=N)
    (guardFit : ∀ q : ℕ, q ≤ N → Fits W ((q:ℤ)-N))
    (body : Command) (f : ℕ → Heap → Heap)
    (step : ∀ q < N, ∀ x : IntegerRAM.Memory, regs i m x → x i=q → x (-7)=1 →
      ∃ t, t ≤ B ∧ ∃ out, Runs W body x t out ∧ heap out=f q (heap x) ∧ regs (i-1) x out ∧ out (-7)=1) :
    ∃ t, t ≤ 2+N*(B+3) ∧ ∃ out, Runs W (loop i lim body) m t out ∧ heap out=foldRange f N (heap m) ∧
      regs i m out ∧ out (-7)=1 := by
  let I (q : ℕ) (x : IntegerRAM.Memory) := x i=q ∧ x (-7)=1 ∧ regs i m x ∧ heap x=foldRange f q (heap m)
  let s := update m (-7) 1
  let init := update s i (s i-s i)
  have ini : I 0 init := by
    refine ⟨by simp [init,update],by simp [init,s,update,if_neg (by omega : (-7:ℤ)≠i)],?_,?_⟩
    · intro z h₁ h₂
      unfold floor at h₁
      simp only [init,s,update,if_neg (by omega : z≠i),if_neg (by omega : z≠ -7)]
    · funext z
      change init z = m z
      simp only [init,s,update,if_neg (by omega : (z:ℤ)≠i),if_neg (by omega : (z:ℤ)≠ -7)]
  have advance (q : ℕ) (hq : q < N) (x : IntegerRAM.Memory) (inv : I q x) :
      ∃ t, t ≤ B ∧ ∃ o, Runs W body x t o ∧ o i=q ∧ o (-7)=1 ∧ o lim=N ∧
        I (q+1) (nextMemory o i (-8) q N) := by
    obtain ⟨idx,one,ctx,data⟩ := inv
    obtain ⟨t,ht,o,run,dat,keep,unit⟩ := step q hq x ctx idx one
    have oi := (keep i (by omega) (by omega)).trans idx
    have ol := (keep lim (by omega) hl').trans ((ctx lim (Or.inl hl) hl').trans bound)
    refine ⟨t,ht,o,run,oi,unit,ol,?_,?_,?_,?_⟩
    · simp [nextMemory,update,if_neg (by omega : i≠ -8)]
    · simp [nextMemory,update,if_neg (by omega : (-7:ℤ)≠i),unit]
    · intro z hz hz'
      unfold floor at hz
      simp only [nextMemory,update,if_neg (by omega : z≠ -8),if_neg (by omega : z≠i)]
      exact (keep z (by rcases hz with h|h; exact Or.inl (by omega); exact Or.inr h) hz').trans (ctx z hz hz')
    · funext z
      change (nextMemory o i (-8) q N) z = _
      simp only [nextMemory,update,if_neg (by omega : (z:ℤ)≠ -8),if_neg (by omega : (z:ℤ)≠i)]
      exact congrFun (dat.trans (congrArg (f q) data)) z
  obtain ⟨t,ht,o,run,last⟩ := repeatN_runs hn body (by omega : lim≠i) I guardFit advance ini
  exact ⟨1+(1+t),by omega,o,Runs.seq (.atom (.one m (-7))) (Runs.seq (.atom (.sub s i i i)) run),
    last.2.2.2,last.2.2.1,last.2.1⟩

def gridFold (f : ℕ → ℕ → ℕ → Heap → Heap) (N side : ℕ) (H : Heap) :=
  foldRange (fun p => foldRange (fun u => foldRange (fun v => f p u v) side) side) N H

theorem grid_run {W N D B : ℕ} (hn : 0 < N) (hd : 0 < D) (m : IntegerRAM.Memory)
    (limN : m (-2)=N) (limD : m (-3)=D)
    (guardN : ∀ j : ℕ, j ≤ N → Fits W ((j:ℤ)-N)) (guardD : ∀ j : ℕ, j ≤ D → Fits W ((j:ℤ)-D))
    (body : Command) (f : ℕ → ℕ → ℕ → Heap → Heap)
    (cell : ∀ p < N, ∀ u < D, ∀ v < D, ∀ x : IntegerRAM.Memory, regs (-4) m x →
      x (-4)=p → x (-5)=u → x (-6)=v → x (-7)=1 →
      ∃ t, t ≤ B ∧ ∃ out, Runs W body x t out ∧ heap out=f p u v (heap x) ∧
        regs (-7) x out ∧ out (-7)=1) :
    ∃ t, t ≤ gridCost N D B ∧ ∃ out, Runs W (grid body) m t out ∧
      heap out=gridFold f N D (heap m) ∧ regs (-4) m out ∧ out (-7)=1 := by
  apply loop_run (by decide) (by decide) (by decide) (by decide) hn m limN guardN
  intro p hp a ma pa _
  have da := (ma (-3) (by decide) (by decide)).trans limD
  apply loop_run (by decide) (by decide) (by decide) (by decide) hd a da guardD
  intro u hu b ab ub _
  have db := (ab (-3) (by decide) (by decide)).trans da
  apply loop_run (by decide) (by decide) (by decide) (by decide) hd b db guardD
  intro v hv x bx vx unit
  apply cell p hp u hu v hv x _ _ _ vx unit
  · intro z h1 h2
    exact (bx z (by rcases h1 with h|h; exact Or.inl (by omega); exact Or.inr h) h2).trans
      ((ab z (by rcases h1 with h|h; exact Or.inl (by omega); exact Or.inr h) h2).trans (ma z h1 h2))
  · exact (bx _ (by decide) (by decide)).trans ((ab _ (by decide) (by decide)).trans pa)
  · exact (bx _ (by decide) (by decide)).trans ub

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareScatter -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout

abbrev Position := ℕ × ℕ × ℕ
def points (N D : ℕ) : List Position :=
  (List.range N).flatMap fun p => (List.range D).flatMap fun u => (List.range D).map fun v => (p,u,v)

theorem points_mem (N D : ℕ) (a : Position) :
    a ∈ points N D ↔ a.1 < N ∧ a.2.1 < D ∧ a.2.2 < D := by
  rcases a with ⟨p,u,v⟩
  simp [points] <;> grind

private theorem foldRange_list (n : ℕ) (f : ℕ → Heap → Heap) (H : Heap) :
    foldRange f n H = (List.range n).foldl (fun a i => f i a) H := by
  induction n with
  | zero => rfl
  | succ n ih => simp [foldRange,List.range_succ,ih]

theorem gridFold_list (f : ℕ → ℕ → ℕ → Heap → Heap) (N D : ℕ) (H : Heap) :
    gridFold f N D H = (points N D).foldl (fun a i => f i.1 i.2.1 i.2.2 a) H := by
  simp only [gridFold,foldRange_list,points,List.foldl_flatMap,List.foldl_map]

def scatter (dst : Position → ℕ) (value : Position → Heap → ℤ) (a : Position) (H : Heap) :
    Heap := fun z => if z=dst a then value a H else H z

/-- A loop of disjoint single-cell writes over a source area disjoint from all
destinations. This applies to every down- and up-pass of the square scheme. -/
theorem scatter_result (l : List Position) (H : Heap) (dst : Position → ℕ)
    (value : Position → Heap → ℤ) (source : ℕ → Prop)
    (apart : ∀ a ∈ l, ¬ source (dst a))
    (reads : ∀ a ∈ l, ∀ x y : Heap, (∀ z, source z → x z=y z) → value a x=value a y)
    (injective : ∀ a ∈ l, ∀ b ∈ l, dst a=dst b → a=b) :
    let result := l.foldl (fun cur a => scatter dst value a cur) H
    (∀ a ∈ l, result (dst a)=value a H) ∧
    ∀ z, (∀ a ∈ l, z≠dst a) → result z=H z := by
  induction l generalizing H with
  | nil => simp
  | cons a l ih =>
    have mem (b : Position) (hb : b∈l) : b∈a::l := List.mem_cons_of_mem _ hb
    let H' := scatter dst value a H
    have init (z : ℕ) (hz : source z) : H' z=H z := by
      apply if_neg
      intro he
      exact apart a (by simp) (he ▸ hz)
    obtain ⟨hit,miss⟩ := ih H' (fun b hb => apart b (mem b hb))
      (fun b hb => reads b (mem b hb))
      (fun b hb c hc => injective b (mem b hb) c (mem c hc))
    dsimp only
    constructor
    · intro b hb
      rcases List.mem_cons.mp hb with eq|rest
      · subst b
        by_cases found : a∈l
        · exact (hit a found).trans (reads a (by simp) _ _ init)
        · have avoid (c : Position) (hc : c∈l) : dst a≠dst c := fun he =>
            found ((injective a (by simp) c (mem c hc) he) ▸ hc)
          exact (miss _ avoid).trans (by simp [H',scatter])
      · exact (hit b rest).trans (reads b (mem b rest) _ _ init)
    · intro z avoid
      exact (miss _ (fun b hb => avoid b (mem _ hb))).trans (if_neg (avoid a (by simp)))

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareControl -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured

theorem assign_run {W : ℕ} (m : IntegerRAM.Memory) {reg : ℤ} (hr : floor < reg) (e : Expr)
    (safe : e.safe floor W m) :
    ∃ out, Runs W (assign reg e) m (e.steps+2) out ∧ ∀ z, floor < z →
      out z=if z=reg then e.val m else m z := by
  obtain ⟨p,run,res,fr⟩ := e.run m floor safe
  let q := update p reg (p reg-p reg)
  refine ⟨_,Runs.seq run (Runs.seq (.atom (.sub p reg reg reg)) (.atom (.add q reg reg floor))),?_⟩
  intro z hz
  have dif : floor≠reg := by omega
  by_cases h : z=reg
  · subst z; simp [q,update,dif,res]
  · simp only [update,if_neg h,q,fr _ hz]

-- A negative remainder is the loop guard, so an exact positive multiple
-- performs precisely q subtraction rounds.

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeProjectionScatter -/
section
namespace VWZClique.IntegerRAM.Projected.Scatter
open Structured SquareCode SquareCode.Layout

def offset (dst sr sc r c : ℕ) := dst+r*sr+c*sc
def readAt (start n r c : ℕ) := start+r*n+c

def cost (n : ℕ) := gridCost 1 n (destination.steps+(source.steps+1))

structure Ready (n start dst sr sc : ℕ) (m : Memory) : Prop where
  once : m (-2)=1
  width : m (-3)=n
  dest : m anchor=dst
  rows : m rowStride=sr
  cols : m colStride=sc
  input : m src=start

theorem strided {W n start dst sr sc : ℕ} (hn : 0<n) (m : Memory) (h : Ready n start dst sr sc m)
    (guard : ∀ i : ℕ, i≤n → Fits W ((i:ℤ)-n)) (one : ∀ i : ℕ, i≤1 → Fits W ((i:ℤ)-1))
    (fit : ∀ r<n, ∀ c<n, Fits W (offset dst sr sc r c) ∧ Fits W (readAt start n r c))
    (apart : ∀ r<n, ∀ c<n, ∀ i<n, ∀ j<n, offset dst sr sc r c≠readAt start n i j)
    (inj : ∀ r<n, ∀ c<n, ∀ i<n, ∀ j<n, offset dst sr sc r c=offset dst sr sc i j → r=i ∧ c=j) :
    ∃ t o, t≤cost n ∧ Runs W run m t o ∧
      (∀ r<n, ∀ c<n, o (offset dst sr sc r c)=m (readAt start n r c)) ∧
      ∀ z : ℕ, (∀ r<n, ∀ c<n, z≠offset dst sr sc r c) → o z=m z := by
  let target (p : Position) := offset dst sr sc p.2.1 p.2.2
  let val (p : Position) (H : Heap) := H (readAt start n p.2.1 p.2.2)
  let effect (p r c : ℕ) := scatter target val (p,r,c)
  let touched (z : ℕ) := ∃ i<n, ∃ j<n, z=readAt start n i j
  let B := destination.steps+(source.steps+1)
  have step (p : ℕ) (_ : p<1) (r : ℕ) (hr : r<n) (c : ℕ) (hc : c<n) (x : Memory)
      (reg : regs (-4) m x) (_ : x (-4)=p) (xr : x (-5)=r) (xc : x (-6)=c) (unit : x (-7)=1) :
      ∃ t, t≤B ∧ ∃ y, Runs W cell x t y ∧ heap y=effect p r c (heap x) ∧ regs (-7) x y ∧ y (-7)=1 := by
    have xs := (reg src (by decide) (by decide)).trans h.input
    have xd := (reg anchor (by decide) (by decide)).trans h.dest
    have xa := (reg rowStride (by decide) (by decide)).trans h.rows
    have xb := (reg colStride (by decide) (by decide)).trans h.cols
    have xn := (reg (-3) (by decide) (by decide)).trans h.width
    have destEq : destination.val x=offset dst sr sc r c := by
      simp [destination,Expr.val,row,col,xd,xa,xb,xr,xc,offset,Nat.cast_add,Nat.cast_mul]
    have srcEq : inputAddress.val x=readAt start n r c := by
      simp [inputAddress,Expr.val,side,row,col,xs,xn,xr,xc,readAt,Nat.cast_add,Nat.cast_mul]
    have sa : destination.safe floor W x := by simp [destination,Expr.safe,row,col,anchor,rowStride,colStride,floor]
    have sb : inputAddress.safe floor W x := by simp [inputAddress,Expr.safe,row,col,side,src,floor]
    have sc' : source.safe floor W x := ⟨sb,by rw [srcEq];dsimp [floor];omega,srcEq ▸ (fit r hr c hc).2⟩
    obtain ⟨y,act,fr⟩ := write_run x floor destination source sa sc' (destEq ▸ (fit r hr c hc).1)
    have valEq : source.val x = x (readAt start n r c) := by simp only [source,Expr.val,srcEq]
    refine ⟨B,le_rfl,y,act,?_,?_,?_⟩
    · funext z
      simpa [heap,effect,scatter,target,val,destEq,valEq] using fr (z:ℤ) (by dsimp [floor];omega)
    · intro z lo neg
      rw [fr z (by dsimp [floor] at *; omega),destEq,if_neg (by omega)]
    · rw [fr _ (by decide),destEq,if_neg (by omega),unit]
  obtain ⟨t,time,o,exec,res,_,_⟩ := grid_run (by decide : 0<1) hn m h.once h.width one guard cell effect step
  have no : ∀ a∈points 1 n, ¬touched (target a) := by
    rintro ⟨p,r,c⟩ h ⟨i,hi,j,hj,eq⟩
    obtain ⟨_,hr,hc⟩ := (points_mem ..).mp h
    exact apart r hr c hc i hi j hj eq
  have same : ∀ a∈points 1 n, ∀ H J : Heap, (∀ z,touched z → H z=J z) → val a H=val a J := by
    intro p hp x y fr
    obtain ⟨_,hr,hc⟩ := (points_mem ..).mp hp
    exact fr _ ⟨_,hr,_,hc,rfl⟩
  have uniq : ∀ a∈points 1 n, ∀ b∈points 1 n, target a=target b → a=b := by
    rintro ⟨p,r,c⟩ h ⟨q,i,j⟩ h' eq
    obtain ⟨hp,hr,hc⟩ := (points_mem ..).mp h
    obtain ⟨hq,hi,hj⟩ := (points_mem ..).mp h'
    obtain ⟨rfl,rfl⟩ := inj r hr c hc i hi j hj eq
    congr 1
    omega
  have proof := scatter_result (points 1 n) (heap m) target val touched no same uniq
  rw [gridFold_list] at res
  refine ⟨t,o,time,exec,?_,?_⟩
  · intro r hr c hc
    have ok : (0,r,c) ∈ points 1 n := (points_mem ..).mpr ⟨by exact Nat.zero_lt_one,hr,hc⟩
    exact (congrFun res (target (0,r,c))).trans (proof.1 _ ok)
  · intro z avoid
    exact (congrFun res z).trans (proof.2 z (fun p hp =>
      avoid _ ((points_mem ..).mp hp).2.1 _ ((points_mem ..).mp hp).2.2))

end VWZClique.IntegerRAM.Projected.Scatter
end

/- NativeProjectionScatterLayout -/
section
namespace VWZClique.IntegerRAM.Projected.Scatter
open Structured SquareCode SquareCode.Layout

structure Slice where
  n : ℕ
  src : ℕ
  dst : ℕ
  j : ℕ
  count : ℕ
  x : ℕ
  y : ℕ
  pair : ℕ

def Slice.start (s : Slice) : Channel → ℕ
  | .middle => s.dst+(s.j*s.n)*(s.n*(s.n*s.n))+(s.x*s.n+s.y)*s.n
  | .right => s.dst+((s.x*s.n+s.y)*s.n)*(s.count*s.n)+s.j*s.n
  | .left => s.dst+(s.j*s.n*s.n)*(s.n*s.n)+s.pair

def Slice.rstep (s : Slice) : Channel → ℕ
  | .middle | .left => s.n*(s.n*s.n)
  | .right => 1

def Slice.cstep (s : Slice) : Channel → ℕ
  | .middle => 1
  | .right => s.count*s.n
  | .left => s.n*s.n

def Slice.target (s : Slice) (b : Channel) := offset (s.start b) (s.rstep b) (s.cstep b)

theorem Slice.target_middle (s : Slice) (r c : ℕ) : s.target .middle r c =
    s.dst+(s.j*s.n+r)*s.n^3 + ((s.x*s.n+s.y)*s.n+c) := by
  dsimp [target,offset,start,rstep,cstep]; ring

theorem Slice.target_right (s : Slice) (r c : ℕ) : s.target .right r c =
    s.dst+((s.x*s.n+s.y)*s.n+c)*(s.count*s.n)+(s.j*s.n+r) := by
  dsimp [target,offset,start,rstep,cstep]; ring

theorem Slice.target_left (s : Slice) (r c : ℕ) : s.target .left r c =
    s.dst+((s.j*s.n+r)*s.n+c)*s.n^2+s.pair := by
  dsimp [target,offset,start,rstep,cstep]; ring

private theorem in_order {n high low u v u' v' : ℕ} (step : n*low≤high) (lo : 0<low)
    (hv : v<n) (hv' : v'<n) (eq : u*high+v*low=u'*high+v'*low) : u=u' ∧ v=v' := by
  have ord {r i c j : ℕ} (ri : r< i) (cn : c<n) :
      r*high+c*low< i*high+j*low := by
    have lt := Nat.mul_lt_mul_of_pos_right cn lo
    have le := Nat.mul_le_mul_right high ri
    rw [Nat.succ_mul] at le
    omega
  have same : u=u' := by
    by_contra ne
    rcases lt_or_gt_of_ne ne with a|a
    · exact (ord (j:=v') a hv).ne eq
    · exact (ord (j:=v) a hv').ne eq.symm
  obtain rfl := same
  refine ⟨rfl,Nat.eq_of_mul_eq_mul_right lo (by omega)⟩

theorem Slice.injective (s : Slice) (n : 0<s.n) (a : 0<s.count) (b : Channel)
    (r c i j : Fin s.n) (eq : s.target b r c=s.target b i j) : r=i ∧ c=j := by
  have leading : s.n≤ s.n*(s.n*s.n) := Nat.le_mul_of_pos_right _ (by positivity)
  change _+r.val*s.rstep b+c.val*s.cstep b=_+i.val*s.rstep b+j.val*s.cstep b at eq
  have pair : r.val*s.rstep b+c.val*s.cstep b=i.val*s.rstep b+j.val*s.cstep b := by omega
  cases b with
  | left =>
    obtain ⟨h,g⟩ := in_order (by rfl : s.n*(s.n*s.n)≤ s.n*(s.n*s.n)) (by positivity : 0<s.n*s.n) c.isLt j.isLt pair
    exact ⟨Fin.ext h,Fin.ext g⟩
  | middle =>
    obtain ⟨h,g⟩ := in_order (by simpa only [Slice.rstep,Nat.mul_one] using leading) (by decide : 0<1) c.isLt j.isLt pair
    exact ⟨Fin.ext h,Fin.ext g⟩
  | right =>
    have bound : s.n*1≤ s.count*s.n := by rw [Nat.mul_one]; exact Nat.le_mul_of_pos_left _ a
    have swapped : c.val*(s.count*s.n)+r.val*1=j.val*(s.count*s.n)+i.val*1 := by
      simpa only [Slice.rstep,Slice.cstep,Nat.add_comm] using pair
    obtain ⟨g,h⟩ := in_order bound (by decide : 0<1) r.isLt i.isLt swapped
    exact ⟨Fin.ext h,Fin.ext g⟩

def Slice.control (s : Slice) (m : Memory) :=
  m 0=s.n ∧ m sourceBase=s.src ∧ m targetBase=s.dst ∧ m labelID=s.j ∧
  m labels=s.count ∧ m remoteX=s.x ∧ m remoteY=s.y ∧ m pairCode=s.pair

open FoldBits (code Safe safe)

theorem prepare_runs {W : ℕ} {s : Slice} (b : Channel) (m : Memory) (init : s.control m) :
    ∃ f o, f≤16 ∧ Runs W (prepare b) m f o ∧ Ready s.n s.src (s.start b) (s.rstep b) (s.cstep b) o ∧
      ∀ z : ℕ, o z=m z := by
  obtain ⟨N,S,D,L,C,X,Y,P⟩ := init
  let ops := initOps++arrange b
  let out := ops.foldl FoldBits.write m
  refine ⟨ops.length,out,?_,FoldBits.code_runs W ops m ?_,?_,?_⟩
  · cases b <;> decide
  · cases b <;> simp [ops,initOps,arrange,Safe,safe]
  · cases b <;> constructor <;>
      simp [out,ops,initOps,arrange,FoldBits.write,update,src,anchor,rowStride,colStride,
        sourceBase,targetBase,labelID,labels,remoteX,remoteY,pairCode,
        Slice.start,Slice.rstep,Slice.cstep,N,S,D,L,C,X,Y,P,Nat.cast_add,Nat.cast_mul] at * <;> ring
  · intro z
    cases b <;> simp (disch := omega) [out,ops,initOps,arrange,FoldBits.write,update,src,anchor,rowStride,colStride]

theorem copy_slice {W : ℕ} (s : Slice) (b : Channel) (hn : 0<s.n) (hj : s.j<s.count)
    (m : Memory) (ctrl : s.control m)
    (guard : ∀ i : Fin (s.n+1), Fits W ((i.val:ℤ)-s.n))
    (one : ∀ i:ℕ, i≤1 → Fits W ((i:ℤ)-1))
    (fit : ∀ r c : Fin s.n, Fits W (s.target b r c) ∧ Fits W (readAt s.src s.n r c))
    (apart : ∀ r c i j : Fin s.n, s.target b r c≠readAt s.src s.n i j) :
    ∃ f o, f≤16+cost s.n ∧ Runs W (command b) m f o ∧
      (∀ r c : Fin s.n, o (s.target b r c)=m (readAt s.src s.n r c)) ∧
      ∀ z : ℕ, (∀ r c : Fin s.n, z≠s.target b r c) → o z=m z := by
  obtain ⟨t,v,ht,first,ready,keep⟩ := prepare_runs b m ctrl
  obtain ⟨u,o,hu,run,data,fr⟩ := strided hn v ready (fun i hi => guard ⟨i,by omega⟩) one
    (fun r hr c hc => fit ⟨r,hr⟩ ⟨c,hc⟩)
    (fun r hr c hc i hi j hj' => apart ⟨r,hr⟩ ⟨c,hc⟩ ⟨i,hi⟩ ⟨j,hj'⟩)
    (fun r hr c hc i hi j hj' e => by
      obtain ⟨eq,eq'⟩ := s.injective hn (by omega) b ⟨r,hr⟩ ⟨c,hc⟩ ⟨i,hi⟩ ⟨j,hj'⟩ e
      exact ⟨congrArg Fin.val eq,congrArg Fin.val eq'⟩)
  exact ⟨_,o,Nat.add_le_add ht hu,.seq first run,fun r c => (data _ r.isLt _ c.isLt).trans (keep _),
    fun z hz => (fr _ (fun r hr c hc => hz ⟨r,hr⟩ ⟨c,hc⟩)).trans (keep _)⟩

theorem cost_le {n : ℕ} (pos : 0<n) : 16+cost n≤128*n^2 := by
  have nn : n≤n*n := Nat.le_mul_of_pos_right _ pos
  simp only [cost,gridCost,destination,source,inputAddress,row,col,side,Expr.steps]
  nlinarith

end VWZClique.IntegerRAM.Projected.Scatter
end

/- WordButterfly -/
section
/-! A fixed native signed-word program for one product-basis digit.
    Four contiguous input stripes are streamed into one contiguous output array.
    Each output quartet has the order 00, 11, 01+10, 01−10. -/

namespace VWZClique.IntegerRAM.Butterfly
open Structured TrulySubcubicAPSP

namespace Reg
end Reg

def effect (m : Memory) : Atom → Memory
  | .one d => update m d 1
  | .add d a b => update m d (m a + m b)
  | .sub d a b => update m d (m a - m b)
  | .mul d a b => update m d (m a * m b)
  | .load d p => update m d (m (m p))
  | .store p s => update m (m p) (m s)

def safe (W : ℕ) (m : Memory) : Atom → Prop
  | .load _ p | .store p _ => Fits W (m p)
  | _ => True

def safeLine (W : ℕ) (m : Memory) : List Atom → Prop
  | [] => True
  | a :: as => safe W m a ∧ safeLine W (effect m a) as

theorem line_runs {W : ℕ} (as : List Atom) (m : Memory) (h : safeLine W m as) :
    Runs W (line as) m as.length (as.foldl effect m) := by
  induction as generalizing m with
  | nil => exact .skip _
  | cons a as ih =>
    have ha : Step W a m (effect m a) := by
      have hh := h.1
      cases a with
      | one => exact .one ..
      | add => exact .add ..
      | sub => exact .sub ..
      | mul => exact .mul ..
      | load => exact .load _ _ _ hh
      | store => exact .store _ _ _ hh
    rw [List.length_cons,Nat.add_comm]
    exact .seq (.atom ha) (ih _ h.2)

/-- The fixed register inputs and the live loop cursors. -/
structure Parameters (m : Memory) (b d s : ℕ) : Prop where
  src : m Reg.srcBase = b
  dst : m Reg.dstBase = d
  stride : m Reg.stride = s

structure Cursor (m : Memory) (b d s j : ℕ) : Prop where
  p0 : m Reg.p0 = (b+j:ℕ)
  p1 : m Reg.p1 = (b+s+j:ℕ)
  p2 : m Reg.p2 = (b+2*s+j:ℕ)
  p3 : m Reg.p3 = (b+3*s+j:ℕ)
  dest : m Reg.dest = (d+4*j:ℕ)
  one : m Reg.one = 1
  count : m Reg.count = (j:ℤ)-s

def quartet (z : Fin 4) (a b u v : ℤ) : ℤ :=
  if z = 0 then a else if z = 1 then b else if z = 2 then u+v else u-v

/-- An integral butterfly is exactly multiplication by the paper's four rational rows. -/
theorem quartet_oneBit (z : Fin 4) (w : Bool × Bool → ℤ) :
    (quartet z (w (false,false)) (w (true,true)) (w (false,true)) (w (true,false)) : ℚ) =
      ∑ t : Bool × Bool, oneBit z t.1 t.2 * (w t : ℚ) := by
  rw [Fintype.sum_prod_type]
  fin_cases z <;> simp [quartet,oneBit] <;> ring

def sample (m : Memory) (b s j : ℕ) (z : Fin 4) : ℤ :=
  quartet z (m (b+j:ℕ)) (m (b+s+j:ℕ)) (m (b+2*s+j:ℕ)) (m (b+3*s+j:ℕ))

/-- Nonnegative indices in each used interval fit as signed words. The same bound
    also covers the negative trip counter. Endpoints are exclusive. -/
def Room (W b d s : ℕ) : Prop := max b d + 4*s ≤ 2^(W-1)

theorem fits_nat {W x : ℕ} (h : x < 2^(W-1)) : Fits W x := by
  constructor
  · exact le_trans (neg_nonpos.mpr (by positivity) : -(2:ℤ)^(W-1) ≤ 0) (by positivity)
  · exact_mod_cast h

theorem fits_count {W b d s i : ℕ} (h : Room W b d s) (hi : i ≤ s) :
    Fits W ((i:ℤ)-s) := by
  have hn : s ≤ 2^(W-1) := by unfold Room at h; omega
  have hh : (s:ℤ) ≤ (2:ℤ)^(W-1) := by exact_mod_cast hn
  have hk : (0:ℤ) < 2^(W-1) := by positivity
  constructor <;> omega

theorem fits_src {W b d s i : ℕ} (h : Room W b d s) (hi : i < b+4*s) :
    Fits W i := by
  apply fits_nat
  have := Nat.le_max_left b d
  unfold Room at h
  omega

theorem fits_dst {W b d s i : ℕ} (h : Room W b d s) (hi : i < d+4*s) :
    Fits W i := by
  apply fits_nat
  have := Nat.le_max_right b d
  unfold Room at h
  omega

/-- Scratch cells used by a stage lie strictly above the outer loop registers. -/
def Retains (m n : Memory) : Prop := ∀ a : ℤ, a ≤ Reg.srcBase → n a = m a

theorem Retains.params {m n : Memory} {b d s : ℕ} (h : Retains m n)
    (p : Parameters m b d s) : Parameters n b d s := by
  exact ⟨(h _ (by decide)).trans p.src,(h _ (by decide)).trans p.dst,
    (h _ (by decide)).trans p.stride⟩

theorem Retains.trans {m n q : Memory} (h : Retains m n) (k : Retains n q) :
    Retains m q := fun a ha => (k a ha).trans (h a ha)

set_option maxHeartbeats 1600000

theorem prepare_run {W b d s : ℕ} (m : Memory) (p : Parameters m b d s) :
    ∃ n, Runs W (line prepare) m 8 n ∧ Cursor n b d s 0 ∧
      Parameters n b d s ∧ n Reg.stages = m Reg.stages ∧ ∀ a : ℕ, n a = m a := by
  refine ⟨_,line_runs prepare m (by simp [prepare,safeLine,safe]),?_,?_,?_,?_⟩
  · constructor <;>
      simp [prepare,List.foldl,effect,update,Reg.p0,Reg.p1,Reg.p2,Reg.p3,Reg.dest,
        Reg.srcBase,Reg.dstBase,Reg.stride,Reg.one,Reg.zero,Reg.count] at * <;>
      try { have h₀ := p.src; have h₁ := p.dst; have h₂ := p.stride
            dsimp [Reg.srcBase,Reg.dstBase,Reg.stride] at h₀ h₁ h₂
            rw [h₀,h₂] <;> ring } <;>
      try { exact p.src } <;> try { exact p.dst } <;>
      try { rw [show m (-15) = (s:ℤ) from p.stride] }
  · constructor <;> first | exact p.src | exact p.dst | exact p.stride
  · rfl
  · intro a
    simp (disch := omega) [prepare,effect,update,Reg.p0,Reg.p1,Reg.p2,Reg.p3,
      Reg.dest,Reg.srcBase,Reg.dstBase,Reg.stride,Reg.one,Reg.zero,Reg.count]

attribute [local simp] Reg.p0 Reg.p1 Reg.p2 Reg.p3 Reg.dest Reg.x0 Reg.x1 Reg.x2 Reg.x3
  Reg.sum Reg.diff Reg.count Reg.srcBase Reg.dstBase Reg.stride Reg.one Reg.zero Reg.stages Reg.swap

@[local simp] private theorem update_same (m : Memory) (a v : ℤ) : update m a v a = v :=
  if_pos rfl

private theorem update_other (m : Memory) (i v a : ℤ) (ne : a ≠ i) : update m i v a = m a :=
  if_neg ne

private theorem read_run {W b d s j : ℕ} (m : Memory) (c : Cursor m b d s j)
    (hr : Room W b d s) (hj : j<s) :
    ∃ r, Runs W (line readInputs) m 6 r ∧ Cursor r b d s j ∧ Retains m r ∧
      (∀ a : ℕ, r a = m a) ∧ r Reg.x0 = m (b+j:ℕ) ∧ r Reg.x1 = m (b+s+j:ℕ) ∧
      r Reg.sum = m (b+2*s+j:ℕ) + m (b+3*s+j:ℕ) ∧
      r Reg.diff = m (b+2*s+j:ℕ) - m (b+3*s+j:ℕ) := by
  obtain ⟨p0,p1,p2,p3,pd,one,count⟩ := c
  simp only [Reg.p0,Reg.p1,Reg.p2,Reg.p3,Reg.dest,Reg.one,Reg.count] at *
  have h0 := fits_src hr (i := b+j) (by omega)
  have h1 := fits_src hr (i := b+s+j) (by omega)
  have h2 := fits_src hr (i := b+2*s+j) (by omega)
  have h3 := fits_src hr (i := b+3*s+j) (by omega)
  let r := readInputs.foldl effect m
  refine ⟨r,line_runs readInputs m ?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [readInputs,safeLine,safe,effect,update,Reg.x0,Reg.x1,Reg.x2,Reg.x3,
      Reg.p0,Reg.p1,Reg.p2,Reg.p3] 
    simpa [p0,p1,p2,p3] using And.intro h0 ⟨h1,h2,h3⟩
  · exact ⟨p0,p1,p2,p3,pd,one,count⟩
  · intro a ha
    simp only [Reg.srcBase] at ha
    simp (disch := omega) [r,readInputs,effect,update_other]
  · intro a
    simp (disch := omega) [r,readInputs,effect,update_other]
  all_goals simp (disch := omega) [r,readInputs,effect,update_other,p0,p1,p2,p3]

private def put (m : Memory) (p : ℕ) (v : ℤ) : Memory :=
  update (update m p v) Reg.dest ((p+1:ℕ):ℤ)

private theorem put_reg (m : Memory) (p : ℕ) (v a : ℤ)
    (ha : a < 0) (hn : a ≠ Reg.dest) : put m p v a = m a := by
  rw [put,update_other _ _ _ _ hn,update_other _ _ _ _ (by omega)]

@[simp] private theorem put_ptr (m : Memory) (p : ℕ) (v : ℤ) :
    put m p v Reg.dest = ((p+1:ℕ):ℤ) := by simp [put,update]

@[simp] private theorem put_cell (m : Memory) (p a : ℕ) (v : ℤ) :
    put m p v a = if a=p then v else m a := by
  simp (disch := omega) [put,update]

private theorem write_one {W p : ℕ} (m : Memory) (r : ℤ) (hp : m Reg.dest=p)
    (ho : m Reg.one=1) (hf : Fits W p) :
    Runs W (writeOne r) m 2 (put m p (m r)) := by
  have hs : safeLine W m [.store Reg.dest r,.add Reg.dest Reg.dest Reg.one] := by
    simp only [safeLine,safe,hp,hf,true_and]
  have hh := line_runs _ _ hs
  have hneg : Reg.dest ≠ (p:ℤ) := by dsimp [Reg.dest]; omega
  have hone : Reg.one ≠ (p:ℤ) := by dsimp [Reg.one]; omega
  simpa only [writeOne,List.length_cons,List.length_nil,List.foldl_cons,List.foldl_nil,effect,hp,update,if_neg hneg,
    if_neg hone,ho,Nat.cast_add,Nat.cast_one,put] using hh

private def fourWrites (m : Memory) (p : ℕ) : Memory :=
  put (put (put (put m p (m Reg.x0)) (p+1) (m Reg.x1)) (p+2) (m Reg.sum))
    (p+3) (m Reg.diff)

private theorem writes_run {W p : ℕ} (m : Memory) (hp : m Reg.dest=p) (ho : m Reg.one=1)
    (hf : ∀ i < 4, Fits W ((p+i:ℕ):ℤ)) : Runs W writeOutputs m 8 (fourWrites m p) := by
  have h0 := write_one m Reg.x0 hp ho (by simpa using hf 0 (by decide))
  let a := put m p (m Reg.x0)
  let b := put a (p+1) (m Reg.x1)
  let c := put b (p+2) (m Reg.sum)
  have h1 : Runs W (writeOne Reg.x1) a 2 b := by
    simpa (disch := decide) [a,b,put_reg] using write_one a Reg.x1 (put_ptr ..)
      ((put_reg _ _ _ _ (by decide) (by decide)).trans ho) (hf 1 (by decide))
  have h2 : Runs W (writeOne Reg.sum) b 2 c := by
    have h := write_one b Reg.sum (put_ptr ..) (by simp (disch := decide) [a,b,put_reg,ho])
      (hf 2 (by decide))
    simpa (disch := decide) [a,b,c,put_reg] using h
  have h3 : Runs W (writeOne Reg.diff) c 2 (fourWrites m p) := by
    have h := write_one c Reg.diff (put_ptr ..) (by simp (disch := decide) [a,b,c,put_reg,ho])
      (hf 3 (by decide))
    simpa (disch := decide) [a,b,c,fourWrites,put_reg] using h
  exact .seq h0 (.seq h1 (.seq h2 h3))

private theorem body_run {W b d s j : ℕ} (m : Memory) (c : Cursor m b d s j)
    (hr : Room W b d s) (hj : j<s) :
    ∃ q, Runs W body m 19 q ∧ Cursor q b d s (j+1) ∧ Retains m q ∧
      (∀ z : Fin 4, q (d+4*j+z:ℕ) = sample m b s j z) ∧
      ∀ a : ℕ, a < d+4*j ∨ d+4*(j+1) ≤ a → q a=m a := by
  obtain ⟨r,hread,rc,rret,rcells,x0,x1,plus,minus⟩ := read_run m c hr hj
  let p := d+4*j
  let n := fourWrites r p
  let q := advance.foldl effect n
  have hw := writes_run (p:=p) r rc.dest rc.one
    (fun i hi => fits_dst hr (i:=p+i) (by dsimp [p]; omega))
  have hnext := line_runs advance n (W:=W) (by simp [advance,safeLine,safe])
  refine ⟨q,.seq hread (.seq hw hnext),?_,?_,?_,?_⟩
  · obtain ⟨p0,p1,p2,p3,pd,one,count⟩ := rc
    simp only [Reg.p0,Reg.p1,Reg.p2,Reg.p3,Reg.dest,Reg.one,Reg.count] at *
    constructor <;>
      simp (disch := decide) [q,n,fourWrites,advance,effect,update,put_reg,p0,p1,p2,p3,
        one,count,p,Nat.cast_add,Nat.cast_mul] <;> ring
  · intro a ha
    have hh := rret a ha
    simp only [Reg.srcBase] at ha
    have get (u : Memory) (k : ℕ) (v : ℤ) : put u k v a = u a :=
      put_reg _ _ _ _ (by omega) (by dsimp [Reg.dest]; omega)
    simp (disch := omega) [q,n,fourWrites,advance,effect,update_other,get,hh]
  · intro z
    have ac (a : ℕ) : q a = n a := by
      simp (disch := omega) [q,advance,effect,update_other]
    rw [ac]
    simp only [n,fourWrites,put_cell]
    fin_cases z <;>
      simp [p,sample,quartet,x0,x1,plus,minus]
  · intro a ha
    have ac : q a = n a := by
      simp (disch := omega) [q,advance,effect,update_other]
    rw [ac]
    simp only [n,fourWrites,put_cell,p,if_neg (by omega : a ≠ d+4*j+3),
      if_neg (by omega : a ≠ d+4*j+2),if_neg (by omega : a ≠ d+4*j+1),
      if_neg (by omega : a ≠ d+4*j),rcells]

/-- Disjoint source and destination arrays of length four times the stripe length. -/
def Apart (b d s : ℕ) : Prop := b+4*s ≤ d ∨ d+4*s ≤ b

private theorem sweep_run {W b d s : ℕ} (left : ℕ) (j : ℕ) (m : Memory)
    (endAt : j+(left+1)=s) (c : Cursor m b d s j) (hr : Room W b d s)
    (ha : Apart b d s) :
    ∃ q, Runs W sweep m (20*(left+1)) q ∧ Retains m q ∧
      (∀ k, j≤k → k<s → ∀ z : Fin 4, q (d+4*k+z:ℕ) = sample m b s k z) ∧
      ∀ a : ℕ, a<d+4*j ∨ d+4*s≤a → q a=m a := by
  induction left generalizing m j with
  | zero =>
    obtain ⟨q,act,cc,ret,val,frame⟩ := body_run m c hr (by omega)
    have hc : q Reg.count = 0 := by rw [cc.count]; push_cast; omega
    have hf : Fits W (q Reg.count) := cc.count ▸ fits_count hr (by omega)
    refine ⟨q,.loop_done act hf (by rw [hc]; omega),ret,?_,?_⟩
    · intro k hj hk z
      have : k=j := by omega
      simpa [this] using val z
    · intro a h
      exact frame _ (by omega)
  | succ left ih =>
    obtain ⟨r,act,cc,ret,val,frame⟩ := body_run m c hr (by omega)
    obtain ⟨q,more,ret',val',frame'⟩ := ih (j+1) r (by omega) cc
    have hf : Fits W (r Reg.count) := cc.count ▸ fits_count hr (by omega)
    have hn : r Reg.count < 0 := by rw [cc.count]; push_cast; omega
    have reread (k : ℕ) (hk : k<s) (z : Fin 4) :
        sample r b s k z = sample m b s k z := by
      unfold Apart at ha
      simp only [sample,frame (b+k) (by omega),frame (b+s+k) (by omega),
        frame (b+2*s+k) (by omega),frame (b+3*s+k) (by omega)]
    refine ⟨q,?_,ret.trans ret',?_,?_⟩
    · rw [show 20*(left+1+1) = 19+1+20*(left+1) by omega]
      exact .loop_again act hf hn more
    · intro k hj hk z
      by_cases he : k=j
      · subst k
        rw [frame' _ (Or.inl (by have := z.isLt; omega)),val]
      · exact (val' _ (by omega) hk z).trans (reread k hk z)
    · intro a h
      exact (frame' a (by omega)).trans (frame a (by omega))

/-- For arbitrary array bases and positive stripe length the fixed command computes
    all four one-bit basis coefficients in every column. It runs 20 instructions
    per column, including the loop branch, with eight setup instructions. -/
theorem stage_run {W b d s : ℕ} (m : Memory) (p : Parameters m b d s)
    (hs : 0<s) (hr : Room W b d s) (ha : Apart b d s) :
    ∃ q, Runs W stage m (8+20*s) q ∧ Parameters q b d s ∧
      q Reg.stages=m Reg.stages ∧
      (∀ j<s, ∀ z : Fin 4, q (d+4*j+z:ℕ) = sample m b s j z) ∧
      ∀ a : ℕ, a<d ∨ d+4*s≤a → q a=m a := by
  obtain ⟨r,hprep,c,pr,outer,cells⟩ := prepare_run (W:=W) m p
  obtain ⟨left,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  obtain ⟨q,hloop,ret,val,frame⟩ := sweep_run left 0 r (by omega) c hr ha
  refine ⟨q,.seq hprep hloop,ret.params pr,(ret _ (by decide)).trans outer,?_,?_⟩
  · intro j hj z
    simpa only [sample,cells] using val j (Nat.zero_le _) hj z
  · intro a hh
    exact (frame a (by simpa using hh)).trans (cells a)

end VWZClique.IntegerRAM.Butterfly
end

/- WordButterflyTransform -/
section
/-! A uniform native program for all bit lengths. A stage moves the leading raw
    digit to a transformed trailing digit. After all stages the trailing labels
    are in their original order. -/

namespace VWZClique.IntegerRAM.Butterfly
open Structured TrulySubcubicAPSP

def digit : Bool → Bool → Fin 4
  | false,false => 0
  | true,true => 1
  | false,true => 2
  | true,false => 3

/-- Big-endian base-four address of a tensor coordinate. -/
def address : (L : ℕ) → BasisLabel L → ℕ
  | 0, _ => 0
  | L+1, a => (a 0 : ℕ)*4^L + address L (fun i => a i.succ)

def pairAddress {L : ℕ} (x : PairBits L) := address L (fun i => digit (x.1 i) (x.2 i))

theorem address_lt (L : ℕ) (j : BasisLabel L) : address L j < 4^L := by
  induction L with
  | zero => decide +revert
  | succ L ih =>
    have h := ih (fun i => j i.succ)
    have a := (j 0).isLt
    rw [address,pow_succ]
    calc
      _ < ((j 0:ℕ)+1)*4^L := by rw [Nat.add_mul,one_mul]; omega
      _ ≤ 4^L*4 := by rw [mul_comm]; exact Nat.mul_le_mul_left _ a

def prepend {L : ℕ} (t : Bool × Bool) (x : PairBits L) : PairBits (L+1) :=
  (Fin.cons t.1 x.1,Fin.cons t.2 x.2)

theorem pairAddress_prepend {L : ℕ} (t : Bool × Bool) (x : PairBits L) :
    pairAddress (prepend t x) = (digit t.1 t.2 : ℕ)*4^L + pairAddress x := by
  simp [pairAddress,address,prepend]

private def split (L : ℕ) : ((Bool × Bool) × PairBits L) ≃ PairBits (L+1) where
  toFun t := prepend t.1 t.2
  invFun x := ((x.1 0,x.2 0),(fun i => x.1 i.succ,fun i => x.2 i.succ))
  left_inv := by intro t; simp [prepend]
  right_inv := by
    intro x
    apply Prod.ext <;> funext i <;> refine Fin.cases ?_ (fun i => ?_) i <;> rfl

private theorem entry_prepend {L : ℕ} (j : BasisLabel (L+1)) (t : Bool × Bool) (x : PairBits L) :
    basisEntry j (prepend t x) = oneBit (j 0) t.1 t.2 * basisEntry (fun i => j i.succ) x := by
  simp [basisEntry,Fin.prod_univ_succ,prepend]

/-- Sum the first raw digit against its prescribed basis row. -/
def foldDigit {L : ℕ} (w : PairBits (L+1) → ℤ) (z : Fin 4) (t : PairBits L) : ℤ :=
  quartet z (w (prepend (false,false) t)) (w (prepend (true,true) t))
    (w (prepend (false,true) t)) (w (prepend (true,false) t))

def transformed : (L : ℕ) → (PairBits L → ℤ) → BasisLabel L → ℤ
  | 0,w,_ => w (Fin.elim0,Fin.elim0)
  | L+1,w,j => transformed L (foldDigit w (j 0)) (fun i => j i.succ)

theorem transformed_spec (L : ℕ) (w : PairBits L → ℤ) (j : BasisLabel L) :
    (transformed L w j : ℚ) = ∑ x, basisEntry j x*(w x : ℚ) := by
  classical
  induction L with
  | zero =>
    let z : PairBits 0 := (Fin.elim0,Fin.elim0)
    rw [Finset.sum_eq_single z (fun a _ h => (h (Subsingleton.elim _ _)).elim) (by simp)]
    simp [transformed,basisEntry,z]
  | succ L ih =>
    rw [transformed,ih]
    calc
      _ = ∑ x : PairBits L, ∑ t : Bool × Bool, basisEntry (fun i => j i.succ) x *
            (oneBit (j 0) t.1 t.2 * (w (prepend t x) : ℚ)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.mul_sum]
        exact congrArg (fun a : ℚ => basisEntry (fun i => j i.succ) x * a)
          (quartet_oneBit (j 0) (fun t => w (prepend t x)))
      _ = _ := by
        conv_rhs => rw [← (split L).sum_comp,Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro x _
        change _ = basisEntry j (prepend t x) * (w (prepend t x) : ℚ)
        rw [entry_prepend]
        ring

def finalBase : ℕ → ℕ → ℕ → ℕ
  | 0,b,_ => b
  | l+1,b,d => finalBase l d b

private theorem swap_run {W b d s : ℕ} (m : Memory) (p : Parameters m b d s) :
    ∃ q, Runs W (line swapBuffers) m 6 q ∧ Parameters q d b s ∧
      q Reg.stages=m Reg.stages+1 ∧ ∀ a : ℕ, q a=m a := by
  obtain ⟨src,dst,stride⟩ := p
  refine ⟨_,line_runs swapBuffers m (by simp [swapBuffers,safeLine,safe]),?_,?_,?_⟩
  · constructor <;>
      simp_all [swapBuffers,effect,update,Reg.srcBase,Reg.dstBase,Reg.swap,
        Reg.zero,Reg.one,Reg.stages,Reg.stride]
  · simp [swapBuffers,effect,update,Reg.srcBase,Reg.dstBase,Reg.swap,
      Reg.zero,Reg.one,Reg.stages]
  · intro a
    simp [swapBuffers,effect,update,Reg.srcBase,Reg.dstBase,Reg.swap,
      Reg.zero,Reg.one,Reg.stages]

private theorem prelude_run {W b d s l : ℕ} (m : Memory) (p : Parameters m b d s)
    (count : m Reg.stages = l) :
    ∃ q, Runs W (line butterflySetupAtoms) m 4 q ∧ Parameters q b d s ∧
      q Reg.stages=-(l:ℤ) ∧ q Reg.swap=(l:ℤ)-1 ∧ ∀ a : ℕ, q a=m a := by
  refine ⟨_,line_runs butterflySetupAtoms m (by simp [butterflySetupAtoms,safeLine,safe]),?_,?_,?_,?_⟩
  · exact ⟨p.src,p.dst,p.stride⟩
  · simp [butterflySetupAtoms,effect,update,Reg.zero,Reg.one,Reg.swap,Reg.stages] at count ⊢
    exact count
  · simp [butterflySetupAtoms,effect,update,Reg.zero,Reg.one,Reg.swap,Reg.stages] at count ⊢
    exact count
  · intro a
    simp [butterflySetupAtoms,effect,update,Reg.zero,Reg.one,Reg.swap,Reg.stages]

private theorem after_digit {b d s n B : ℕ} {m q : Memory} {A : Type}
    (slot : A → ℕ) (hslt : ∀ a,slot a<B) (w : A → PairBits (n+1) → ℤ)
    (dataIn : ∀ a x, m (b+pairAddress x*B+slot a:ℕ)=w a x)
    (size : s=4^n*B)
    (dataOut : ∀ j<s, ∀ z : Fin 4, q (d+4*j+z:ℕ)=sample m b s j z) :
    ∀ (a : A) (z : Fin 4) (x : PairBits n),
      q (d+pairAddress x*(4*B)+(4*slot a+z):ℕ) = foldDigit (w a) z x := by
  intro a z x
  let idx := pairAddress x*B+slot a
  have bound : idx<s := by
    have less : pairAddress x < 4^n := address_lt n _
    calc
      _ < (pairAddress x+1)*B := by rw [Nat.add_mul,one_mul]; dsimp [idx]; have := hslt a; omega
      _ ≤ s := size ▸ Nat.mul_le_mul_right B less
  have write := dataOut idx bound z
  rw [show d+pairAddress x*(4*B)+(4*slot a+z) = d+4*idx+z by dsimp [idx]; ring,write]
  have fetch (t : Bool × Bool) :
      m (b+(digit t.1 t.2:ℕ)*s+idx:ℕ) = w a (prepend t x) := by
    rw [← dataIn]
    congr 1
    norm_cast
    rw [pairAddress_prepend,size]
    dsimp [idx]
    ring
  have f0 : m (b+idx:ℕ)=w a (prepend (false,false) x) := by
    simpa [digit] using fetch (false,false)
  have f1 : m (b+s+idx:ℕ)=w a (prepend (true,true) x) := by
    simpa [digit] using fetch (true,true)
  have f2 : m (b+2*s+idx:ℕ)=w a (prepend (false,true) x) := by
    simpa [digit] using fetch (false,true)
  have f3 : m (b+3*s+idx:ℕ)=w a (prepend (true,false) x) := by
    simpa [digit] using fetch (true,false)
  simp only [sample,foldDigit,f0,f1,f2,f3]

private def layers : ℕ → Command
  | 0 => .skip
  | _+1 => allStages

theorem fits_minus {W n : ℕ} (h : n≤2^(W-1)) : Fits W (-(n:ℤ)) := by
  have hh : (n:ℤ) ≤ (2:ℤ)^(W-1) := by exact_mod_cast h
  have hpos : (0:ℤ) < 2^(W-1) := by positivity
  constructor <;> omega

private theorem join_layers {W n s : ℕ} {m r q : Memory}
    (act : Runs W iteration m (14+20*s) r) (count : r Reg.stages = -(n:ℤ))
    (hf : Fits W (r Reg.stages)) (more : Runs W (layers n) r (n*(15+20*s)) q) :
    Runs W (layers (n+1)) m ((n+1)*(15+20*s)) q := by
  cases n with
  | zero =>
    simp only [layers,zero_mul] at more
    cases more
    simpa only [layers,allStages,one_mul,zero_add,show 14+20*s+1=15+20*s by omega] using
      (Runs.loop_done (reg:=Reg.stages) act hf (by rw [count]; simp))
  | succ n =>
    rw [show (n+1+1)*(15+20*s)=14+20*s+1+(n+1)*(15+20*s) by ring]
    exact Runs.loop_again (s:=14+20*s) act hf (by rw [count]; push_cast; omega) more

/-- The invariant carries every previously processed prefix as a trailing batch
    index. Both array bases are swapped after each stage. -/
private theorem run_layers (l : ℕ) {W b d s B : ℕ} (m : Memory) (A : Type)
    (slot : A → ℕ) (hslt : ∀ a,slot a<B) (w : A → PairBits l → ℤ)
    (dataIn : ∀ a x, m (b+pairAddress x*B+slot a:ℕ)=w a x)
    (p : Parameters m b d s) (cnt : m Reg.stages = -(l:ℤ)) (hs : 0<s)
    (size : 0<l → 4*s=4^l*B) (hlen : l≤2^(W-1)) (room : Room W b d s) (apart : Apart b d s) :
    ∃ q, Runs W (layers l) m (l*(15+20*s)) q ∧
      (∀ a j, q (finalBase l b d+slot a*4^l+address l j:ℕ)=transformed l (w a) j) ∧
      ∀ i : ℕ, (i < b ∨ b + 4*s ≤ i) → (i < d ∨ d + 4*s ≤ i) → q i=m i := by
  induction l generalizing b d B m A with
  | zero =>
    rw [zero_mul]
    refine ⟨m,.skip _,?_,fun _ _ _ => rfl⟩
    intro a j
    simpa [finalBase,pairAddress,address,transformed] using dataIn a (Fin.elim0,Fin.elim0)
  | succ n ih =>
    have ss : s=4^n*B := by
      apply Nat.eq_of_mul_eq_mul_left (by decide : 0<4)
      exact (size (by omega)).trans (by rw [pow_succ]; ring)
    obtain ⟨r,st,pr,cs,out,frame⟩ := stage_run m p hs room apart
    obtain ⟨u,sw,pu,cu,cells⟩ := swap_run (W:=W) r pr
    have nu : u Reg.stages = -(n:ℤ) := by rw [cu,cs,cnt]; push_cast; ring
    let nextSlot (a : A × Fin 4) := 4*slot a.1+(a.2:ℕ)
    have bnd (a : A × Fin 4) : nextSlot a < 4*B := by
      dsimp [nextSlot]; have := hslt a.1; have := a.2.isLt; omega
    have ent (a : A × Fin 4) (x : PairBits n) :
        u (d+pairAddress x*(4*B)+nextSlot a:ℕ) = foldDigit (w a.1) a.2 x := by
      rw [cells]
      exact after_digit slot hslt w dataIn ss out a.1 a.2 x
    obtain ⟨q,more,values,untouched⟩ := ih (b:=d) (d:=b) (B:=4*B) u (A × Fin 4)
      nextSlot bnd (fun a => foldDigit (w a.1) a.2) ent pu nu
      (fun _ => by rw [ss]; ring) (by omega)
      (by unfold Room at room ⊢; rw [max_comm]; exact room) (Or.symm apart)
    have act : Runs W iteration m (14+20*s) u := by
      rw [show 14+20*s=(8+20*s)+6 by omega]
      exact .seq st sw
    refine ⟨q,join_layers act nu (nu ▸ fits_minus (by omega)) more,?_,?_⟩
    · intro a j
      have v := values (a,j 0) (fun i => j i.succ)
      rw [transformed]
      apply Eq.trans _ v
      congr 1
      norm_cast
      dsimp [finalBase,address,nextSlot]
      rw [pow_succ]
      ring
    · intro i hb hd
      exact (untouched i hd hb).trans ((cells i).trans (frame i hd))

theorem length_le_stride (l : ℕ) : l ≤ 4^(l-1) := by
  cases l with
  | zero => simp
  | succ n =>
    simp only [Nat.add_one_sub_one]
    induction n with
    | zero => decide
    | succ n ih => rw [pow_succ]; omega

/-- One fixed program computes every coefficient of the full product transform.
    Inputs use the address convention above, and the output array alternates with
    the parity of the number of digits. -/
theorem full_run {W b d l : ℕ} (m : Memory) (w : PairBits l → ℤ)
    (p : Parameters m b d (4^(l-1))) (cnt : m Reg.stages=l)
    (hin : ∀ x, m (b+pairAddress x:ℕ) = w x)
    (room : Room W b d (4^(l-1))) (apart : Apart b d (4^(l-1))) :
    ∃ q, Runs W full m (5+l*(15+20*4^(l-1))) q ∧
      (∀ j, q (finalBase l b d+address l j:ℕ)=transformed l w j) ∧
      ∀ i : ℕ, (i < b ∨ b + 4*4^(l-1) ≤ i) → (i < d ∨ d + 4*4^(l-1) ≤ i) → q i=m i := by
  obtain ⟨r,pre,pr,nr,guard,cells⟩ := prelude_run (W:=W) m p cnt
  have hlen : l ≤ 2^(W-1) := by
    have := length_le_stride l; unfold Room at room; omega
  have gf : Fits W (r Reg.swap) := by
    have hpos : (0:ℤ) < 2^(W-1) := by positivity
    have hh : (l:ℤ) ≤ (2:ℤ)^(W-1) := by exact_mod_cast hlen
    rw [guard]; constructor <;> omega
  have ins (_ : Unit) (x : PairBits l) :
      r (b+pairAddress x*1+0:ℕ) = w x := by simp only [mul_one,add_zero,cells,hin]
  obtain ⟨q,run,val,frame⟩ := run_layers l (B:=1) r Unit (fun _ => 0) (fun _ => by decide)
    (fun _ => w) ins pr nr (by positivity)
    (fun hp => by cases l with
                  | zero => omega
                  | succ l => simp [pow_succ,Nat.mul_comm]) hlen room apart
  refine ⟨q,?_,fun j => by simpa using val () j,fun i hb hd => (frame i hb hd).trans (cells i)⟩
  cases l with
  | zero =>
    simp only [layers,zero_mul] at run
    cases run
    simp only [zero_mul,add_zero]
    exact Runs.seq (s:=4) (t:=1) pre (.guard_skip gf (by rw [guard]; simp))
  | succ l =>
    rw [show 5+(l+1)*(15+20*4^(l+1-1))=4+(1+(l+1)*(15+20*4^(l+1-1))) by omega]
    exact .seq pre (.guard_take gf (by rw [guard]; push_cast; omega) run)

end VWZClique.IntegerRAM.Butterfly
end

/- WordButterflyLayout -/
section
/-! Explicit reversible indexing of all input pairs and output labels. -/

namespace VWZClique.IntegerRAM.Butterfly
open Structured TrulySubcubicAPSP

theorem labelIndex_val (l : ℕ) (j : BasisLabel l) : (labelIndex l j : ℕ)=address l j := by
  induction l with
  | zero => exact Fin.eq_zero (labelIndex 0 j) |> congrArg Fin.val
  | succ n ih =>
    change (labelIndex n (fun i => j i.succ):ℕ)+4^n*(j 0:ℕ) =
      (j 0:ℕ)*4^n+address n (fun i => j i.succ)
    rw [ih]
    ring

private def bitsOfDigit (i : Fin 4) : Bool × Bool :=
  if i=0 then (false,false) else if i=1 then (true,true)
  else if i=2 then (false,true) else (true,false)

private theorem bits_digit (s t : Bool) : bitsOfDigit (digit s t)=(s,t) := by
  cases s <;> cases t <;> decide

private def digitLabels (l : ℕ) : PairBits l ≃ BasisLabel l where
  toFun x i := digit (x.1 i) (x.2 i)
  invFun j := (fun i => (bitsOfDigit (j i)).1,fun i => (bitsOfDigit (j i)).2)
  left_inv := by intro x; simp [bits_digit]
  right_inv := by
    intro j
    funext i
    change digit (bitsOfDigit (j i)).1 (bitsOfDigit (j i)).2 = j i
    generalize j i = a
    fin_cases a <;> decide

/-- The corresponding computable bijection for pairs of raw bit vectors. -/
def pairIndex (l : ℕ) : PairBits l ≃ Fin (4^l) := (digitLabels l).trans (labelIndex l)

theorem pairIndex_val {l : ℕ} (x : PairBits l) : (pairIndex l x:ℕ)=pairAddress x :=
  labelIndex_val l _

theorem finalBase_parity (l b d : ℕ) : finalBase l b d=if Even l then b else d := by
  induction l generalizing b d with
  | zero => simp [finalBase]
  | succ n ih => simp only [finalBase,ih,Nat.even_add_one,ite_not]

end VWZClique.IntegerRAM.Butterfly
end

/- NativeProjectionPlacement -/
section
namespace VWZClique.IntegerRAM.Projected.Placement
open Grid UniformFolds Scatter

def remote {L : ℕ} (r c : Fin (2^L)) : PairBits L := ((wordIndex L).symm r,(wordIndex L).symm c)

def packed {a b : ℕ} (x : Fin a) (y : Fin b) : Fin (a*b) := finProdFinEquiv (x,y)

theorem packed_val {a b : ℕ} (x : Fin a) (y : Fin b) : (packed x y).val=x.val*b+y.val := by
  change y.val+b*x.val=_;ring

private theorem unpack {a b} {x x' : Fin a} {y y' : Fin b} (h : packed x y=packed x' y') :
    x=x' ∧ y=y' := by
  have h' := finProdFinEquiv.injective h
  exact ⟨congrArg Prod.fst h',congrArg Prod.snd h'⟩

def pairCode {L} (x y : Fin (2^L)) : Fin ((2^L)^2) := Fin.cast
  (by rw [←pow_mul,Nat.mul_comm,pow_mul];rfl : (4:ℕ)^L=(2^L)^2) (Butterfly.pairIndex L (remote x y))

theorem pairCode_val {L} (x y : Fin (2^L)) : (pairCode x y).val=Butterfly.pairAddress (remote x y) :=
  Butterfly.pairIndex_val _

private theorem pair_inj {L} {x y x' y' : Fin (2^L)} (eq : pairCode x y=pairCode x' y') : x=x' ∧ y=y' := by
  have p0 := congrArg Fin.val eq
  have p := (Butterfly.pairIndex L).injective (show Butterfly.pairIndex L (remote x y) = Butterfly.pairIndex L (remote x' y') from Fin.ext p0)
  exact ⟨(wordIndex L).symm.injective (congrArg Prod.fst p),(wordIndex L).symm.injective (congrArg Prod.snd p)⟩

def lo3 {n : ℕ} (x y z : Fin n) : Fin (n^3) := Fin.cast (by ring) (packed (packed x y) z)

theorem lo3_val {n} (x y z : Fin n) : (lo3 x y z).val=(x.val*n+y.val)*n+z.val := by
  simp only [lo3,Fin.val_cast,packed_val]

private theorem lo3_inj {n} {x y z x' y' z' : Fin n} (eq : lo3 x y z=lo3 x' y' z') :
    x=x' ∧ y=y' ∧ z=z' := by
  have h0 := congrArg Fin.val eq
  obtain ⟨h,c⟩ := unpack (show packed (packed x y) z=packed (packed x' y') z' from Fin.ext h0)
  obtain ⟨a,b⟩ := unpack h
  exact ⟨a,b,c⟩

def location {a L : ℕ} (ch : Channel) (v : Site a (2^L)) (k : Fin (2^L) × Fin (2^L)) : ℕ :=
  match ch with
  | .middle => (packed (packed v.1 k.1) (lo3 v.2.1 v.2.2 k.2)).val
  | .right => (packed (lo3 v.2.1 v.2.2 k.2) (packed v.1 k.1)).val
  | .left => (packed (packed (packed v.1 k.1) k.2) (pairCode v.2.1 v.2.2)).val

theorem location_lt {a L : ℕ} (ch : Channel) (v : Site a (2^L)) (k : Fin (2^L) × Fin (2^L)) :
    location ch v k<a*(2^L)^4 := by
  cases ch with
  | middle => exact (packed _ _).isLt.trans_eq (by ring)
  | right => exact (packed _ _).isLt.trans_eq (by ring)
  | left => exact (packed _ _).isLt.trans_eq (by ring)

theorem different {a L} (ch : Channel) {v u : Site a (2^L)} {k j : Fin (2^L) × Fin (2^L)}
    (eq : location ch v k=location ch u j) : v=u := by
  cases ch with
  | middle =>
    have e := unpack (Fin.ext eq)
    exact Prod.ext (unpack e.1).1 (Prod.ext (lo3_inj e.2).1 (lo3_inj e.2).2.1)
  | right =>
    have e := unpack (Fin.ext eq)
    exact Prod.ext (unpack e.2).1 (Prod.ext (lo3_inj e.1).1 (lo3_inj e.1).2.1)
  | left =>
    have e := unpack (Fin.ext eq)
    exact Prod.ext (unpack (unpack e.1).1).1 (Prod.ext (pair_inj e.2).1 (pair_inj e.2).2)

end VWZClique.IntegerRAM.Projected.Placement
end

/- NativeProjectionLeftGather -/
section
namespace VWZClique.IntegerRAM.Projected.LeftGather
open Structured SquareCode SquareCode.Layout

structure Ready (num C R S D n : ℕ) (d : ℤ) (m : Memory) : Prop where
  count : m limit=num
  codes : m LeftGather.codes=C
  scales : m coeff=R
  vals : m inputBase=S
  dst : m dest=D
  stride : m LeftGather.stride=n
  scalar : m rowScalar=d

theorem Ready.retain {num C R S D n : ℕ} {d : ℤ} {m o : Memory}
    (h : Ready num C R S D n d m) (fix : ∀ r, (-25:ℤ)≤r → r≤ -20 ∨ r=limit → o r=m r) :
    Ready num C R S D n d o :=
  ⟨(fix _ (by decide) (Or.inr rfl)).trans h.count,(fix _ (by decide) (Or.inl (by decide))).trans h.codes,
    (fix _ (by decide) (Or.inl (by decide))).trans h.scales,(fix _ (by decide) (Or.inl (by decide))).trans h.vals,
    (fix _ (by decide) (Or.inl (by decide))).trans h.dst,(fix _ (by decide) (Or.inl (by decide))).trans h.stride,
    (fix _ (by decide) (Or.inl (by decide))).trans h.scalar⟩

def loc (d n i : ℕ) := d+i*n

theorem gather {W num C R S D n : ℕ} {d : ℤ} (pos : 0<num) (hn : 0<n)
    (code : Fin num→ℕ) (coef value : Fin num→ℤ) (m : Memory)
    (ready : Ready num C R S D n d m)
    (src : ∀ i : Fin num, m (C+i.val:ℕ)=code i ∧ m (R+i.val:ℕ)=coef i ∧ m (S+code i:ℕ)=value i)
    (apart : ∀ i j : Fin num, loc D n j.val≠C+i.val ∧ loc D n j.val≠R+i.val ∧ loc D n j.val≠S+code i)
    (guard : ∀ i : ℕ, i≤num → Fits W ((i:ℤ)-num))
    (fits : ∀ i : Fin num, Fits W ((C+i.val:ℕ):ℤ) ∧ Fits W ((R+i.val:ℕ):ℤ) ∧
      Fits W ((S+code i:ℕ):ℤ) ∧ Fits W ((loc D n i.val:ℕ):ℤ)) :
    ∃ t o, t≤2+num*(address.steps+(val.steps+1)+3) ∧ Runs W run m t o ∧
      (∀ i : Fin num, o (loc D n i.val) = d*coef i*value i) ∧
      ∀ z : ℕ, (∀ i : Fin num, z≠loc D n i.val) → o z=m z := by
  let Scope (q : ℕ) (x : Memory) := Ready num C R S D n d x ∧ x index=q ∧ x unit=1 ∧
    (∀ i : Fin num, i.val<q → x (loc D n i.val)=d*coef i*value i) ∧
    ∀ z : ℕ, (∀ i : Fin num, i.val<q → z≠loc D n i.val) → x z=m z
  let u := update m unit 1
  let v := update u index (u index-u index)
  have init : Scope 0 v :=
    ⟨ready.retain (by intro r lo hi; simp [v,u,update,show r≠index by dsimp [index,limit] at *;omega,
      show r≠unit by dsimp [unit,limit] at *;omega]),by simp [v,update],by simp [v,u,update,index,unit],
      by omega,fun z _ => by simp [v,u,update,index,unit]⟩
  let B := address.steps+(val.steps+1)
  have step (q : ℕ) (hq : q<num) (x : Memory) (hx : Scope q x) :
      ∃ t≤B, ∃ y, Runs W body x t y ∧ y index=q ∧ y unit=1 ∧ y limit=num ∧
        Scope (q+1) (nextMemory y index flag q num) := by
    obtain ⟨ctrl,Q,U,data,frame⟩ := hx
    let i : Fin num := ⟨q,hq⟩
    have tab := src i
    have cval : x (C+q:ℕ)=code i := (frame _ (fun j _ => Ne.symm (apart i j).1)).trans tab.1
    have rval : x (R+q:ℕ)=coef i := (frame _ (fun j _ => Ne.symm (apart i j).2.1)).trans tab.2.1
    have sval : x (S+code i:ℕ)=value i := (frame _ (fun j _ => Ne.symm (apart i j).2.2)).trans tab.2.2
    have hin (r : ℤ) (p : ℕ) (h : x r=(p:ℤ)) : (entry r).val x = x (p+q:ℕ) := by simp [entry,Expr.val,h,Q,Nat.cast_add]
    have stone (r : ℤ) (lo : floor<r) (p : ℕ) (h : x r=(p:ℤ)) (fit : Fits W ((p+q:ℕ):ℤ)) : (entry r).safe floor W x := by
      refine ⟨⟨lo,by exact (by decide : floor < index)⟩,?_,?_⟩
      · simp [Expr.val,h,Q,floor];omega
      · simpa [Expr.val,h,Q,Nat.cast_add] using fit
    have xc := (hin codes C ctrl.codes).trans cval
    have xr := (hin coeff R ctrl.scales).trans rval
    have xs : source.val x=value i := by
      change x (x inputBase+(entry codes).val x)=_
      rw [ctrl.vals,xc,←Nat.cast_add]
      exact sval
    have go : address.val x=loc D n q := by simp [address,Expr.val,ctrl.dst,ctrl.stride,Q,loc,Nat.cast_add,Nat.cast_mul]
    have expr : val.val x=d*coef i*value i := by simp [val,Expr.val,ctrl.scalar,xr,xs]
    have safe' : source.safe floor W x := by
      refine ⟨⟨by exact (by decide : floor < inputBase),stone codes (by decide) C ctrl.codes (fits i).1⟩,?_,?_⟩
      · simp [Expr.val,xc,ctrl.vals,floor];omega
      · simpa [Expr.val,xc,ctrl.vals,Nat.cast_add] using (fits i).2.2.1
    obtain ⟨y,run,atCell⟩ := write_run x floor address val (by simp [address,Expr.safe,floor,dest,index,stride])
      ⟨⟨by exact (by decide : floor < rowScalar),stone coeff (by decide) R ctrl.scales (fits i).2.1⟩,safe'⟩ (go ▸ (fits i).2.2.2)
    have fixed (r : ℤ) (lo : floor<r) (neg : r<0) : y r=x r := by rw [atCell r lo,go,if_neg (by omega)]
    have cell (z : ℕ) := atCell (z:ℤ) (by dsimp [floor];omega)
    have old (z : ℕ) : nextMemory y index flag q num z=y z := by simp [nextMemory,update,index,flag]
    have yy := (fixed index (by decide) (by decide)).trans Q
    have yu := (fixed unit (by decide) (by decide)).trans U
    have yc := (fixed limit (by decide) (by decide)).trans ctrl.count
    refine ⟨B,le_rfl,y,run,yy,yu,yc,?_,?_,?_,?_,?_⟩
    · apply ctrl.retain
      intro r lo hi
      have ri : r≠index := by dsimp [index,limit] at *;omega
      have rf : r≠flag := by dsimp [flag,limit] at *;omega
      rw [nextMemory,update,if_neg rf,update,if_neg ri,fixed r (by dsimp [floor];omega) (by dsimp [limit] at hi;omega)]
    · simp [nextMemory,update,index,flag]
    · simp [nextMemory,update,index,unit,flag,yu]
    · intro j hj; rw [old,cell,go,expr]
      by_cases eq : j=i
      · subst j;simp [i]
      · have ne : loc D n j.val ≠ loc D n q := by
          intro he; apply eq;apply Fin.ext
          exact Nat.eq_of_mul_eq_mul_right hn (Nat.add_left_cancel he)
        rw [if_neg (by exact_mod_cast ne)]
        exact data _ (by have ne' := mt Fin.ext eq; change j.val≠q at ne';omega)
    · intro z avoid
      rw [old,cell,go,if_neg (by exact_mod_cast avoid i (by dsimp [i];omega))]
      exact frame z (fun j hj => avoid j (by omega))
  obtain ⟨t,ht,o,more,res⟩ := repeatN_runs (W:=W) (B:=B) pos body (by decide) Scope guard step init
  refine ⟨1+(1+t),o,by change _≤2+num*(B+3);omega,.seq (.atom (.one ..)) (.seq (.atom (.sub ..)) more),fun i => res.2.2.2.1 i i.isLt,?_⟩
  intro z h; exact res.2.2.2.2 z (fun i _ => h i)

end VWZClique.IntegerRAM.Projected.LeftGather
end

/- ProjectionFactors -/
section
open OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.Projection

private theorem oneBit_off (j : Fin 4) (s u : Bool)
    (h : u ≠ (if j = 0 then false else if j = 1 then true else !s)) :
    oneBit j s u = 0 := by
  revert h
  fin_cases j <;> cases s <;> cases u <;> decide

theorem basis_off {L : ℕ} (j : BasisLabel L) (s u : Bits L) (h : u ≠ partner j s) :
    basisEntry j (s,u) = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (oneBit_off (j i) (s i) (u i) hi)

theorem sum_on_graph {F : Type*} [Field F] [CharZero F] {L : ℕ} (j : BasisLabel L)
    (f : PairBits L → F) :
    (∑ x, (basisEntry j x : F) * f x) =
      ∑ s, (basisEntry j (s,partner j s) : F) * f (s,partner j s) := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_eq_single (partner j s)
  · intro u _ hu
    simp [basis_off j s u hu]
  · simp

/-- A projected pivot block can occupy either argument of a channel. -/
noncomputable def single {F : Type*} [Field F] [CharZero F] {L : ℕ}
    (rev : Bool) (h : Fin 3) (j : BasisLabel L) (z : Bits L) (b : Block L)
    (w : ChannelKey L → F) : F :=
  ∑ x, (basisEntry j x : F) *
    (if rev then channel w h b (block x z) else channel w h (block x z) b)

structure Values (L : ℕ) where
  x : PairBits L
  z : Bits L
  b : Block L

def value {L : ℕ} (v : Values L) : Source → Bits L
  | .pivot false => v.x.1
  | .pivot true => v.x.2
  | .center => v.z
  | .other i => v.b i

private theorem value_slot {L : ℕ} (rev : Bool) (i : Slot) (v : Values L) :
    value v (source rev i) = if rev then Sum.elim v.b (block v.x v.z) i
      else Sum.elim (block v.x v.z) v.b i := by
  cases rev <;> rcases i with i | i <;> fin_cases i <;> rfl

/-- Each group uses only its named inputs. -/
def keep {L : ℕ} (g : Group) (v : Values L) : Values L :=
  match g with
  | .pivotCenter => ⟨v.x,v.z,default⟩
  | .pivotOther => ⟨v.x,default,v.b⟩
  | .centerOther => ⟨default,v.z,v.b⟩

private theorem keep_left {L : ℕ} (v : Values L) (a b : Source) :
    value (keep (group a b) v) a = value v a := by
  cases a with
  | pivot t => cases t <;> cases b <;> rfl
  | center => cases b <;> rfl
  | other i => cases b <;> rfl

private theorem keep_right {L : ℕ} (v : Values L) (a b : Source) :
    value (keep (group a b) v) b = value v b := by
  cases b with
  | pivot t => cases t <;> cases a <;> rfl
  | center => cases a <;> rfl
  | other i => cases a <;> rfl

def address {L : ℕ} (rev : Bool) (h : Fin 3) (v : Values L) : Factor → ChannelKey L
  | .inl i => (h,.inl (i,value v (source rev i)))
  | .inr (i,k) => (h,.inr (i,k,value v (source rev i),value v (source rev k)))

private theorem address_keep {L : ℕ} (rev : Bool) (h : Fin 3) (v : Values L) (t : Factor) :
    address rev h (keep (factorGroup rev t) v) t = address rev h v t := by
  rcases t with i | ⟨i,k⟩
  · simp only [factorGroup, address, keep_left]
  · simp only [factorGroup, address, keep_left, keep_right]

/-- Product of the input factors in one of the three groups. -/
noncomputable def piece {F : Type*} [Field F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (g : Group) (v : Values L) (w : ChannelKey L → F) : F :=
  ∏ t : Factor, if factorGroup rev t = g then w (address rev h v t) else 1

private theorem factor_product {F : Type*} [Field F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (v : Values L) (w : ChannelKey L → F) :
    (∏ t : Factor, w (address rev h v t)) =
      if rev then channel w h v.b (block v.x v.z) else channel w h (block v.x v.z) v.b := by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
  cases rev <;> simp only [address, value_slot, Bool.false_eq_true, if_false, if_true, channel]

theorem factorization {F : Type*} [Field F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (v : Values L) (w : ChannelKey L → F) :
    (if rev then channel w h v.b (block v.x v.z) else channel w h (block v.x v.z) v.b) =
      piece rev h .pivotCenter (keep .pivotCenter v) w *
      piece rev h .pivotOther (keep .pivotOther v) w *
      piece rev h .centerOther (keep .centerOther v) w := by
  rw [← factor_product rev h v w]
  unfold piece
  simp only [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro t _
  have eq := congrArg w (address_keep rev h v t)
  cases hg : factorGroup rev t <;> simpa [hg] using eq.symm

noncomputable def left {F : Type*} [Field F] [CharZero F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (j : BasisLabel L) (z s : Bits L) (w : ChannelKey L → F) : F :=
  (basisEntry j (s,partner j s) : F) * piece rev h .pivotCenter ⟨(s,partner j s),z,default⟩ w

noncomputable def right {F : Type*} [Field F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (j : BasisLabel L) (s : Bits L) (b : Block L) (w : ChannelKey L → F) : F :=
  piece rev h .pivotOther ⟨(s,partner j s),default,b⟩ w

noncomputable def outside {F : Type*} [Field F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (z : Bits L) (b : Block L) (w : ChannelKey L → F) : F :=
  piece rev h .centerOther ⟨default,z,b⟩ w

/-- The projected entries are a matrix product times an entrywise factor (equation 9). -/
theorem single_eq {F : Type*} [Field F] [CharZero F] {L : ℕ} (rev : Bool) (h : Fin 3)
    (j : BasisLabel L) (z : Bits L) (b : Block L) (w : ChannelKey L → F) :
    single rev h j z b w = (∑ s, left rev h j z s w * right rev h j s b w) * outside rev h z b w := by
  unfold single
  rw [sum_on_graph, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [factorization rev h (⟨(s,partner j s),z,b⟩ : Values L) w]
  simp only [left, right, outside, keep, mul_assoc]

end VWZClique.Projection
end

/- NativeProjectionFactors -/
section
namespace VWZClique.IntegerRAM.Projected.Factors
open Projection UniformFolds WeightedProof FoldProof SquareCode
abbrev keyIndex {n : ℕ} (k : WeightKey n) := Graph.Table.wordIndex k

/-! The pattern, wedge placement, channel and factor group are compile-time
parameters on each of the fixed plan's branches. All word sizes, vertex labels,
table addresses and assignment-domain lengths are runtime data. -/

structure Ready {L : ℕ} (args : Source → Expr) (v : Values L) (w : WeightKey (2^L) → ℚ) (base : ℕ) (m : Memory) : Prop where
  n : m sideReg = ((2^L:ℕ):ℤ)
  start : m baseReg = base
  sources : ∀ q, (args q).val m = ((UniformFolds.wordIndex L (value v q)).val:ℤ)
  input : ∀ k, (m ((base+keyIndex k:ℕ):ℤ) : ℚ) = w k

private theorem keyU_val {L} {args : Source → Expr} {v : Values L} {w base m} (hm : Ready args v w base m)
    (i : V) (x : Expr) (y : Bits L) (hy : x.val m = (UniformFolds.wordIndex L y).val) :
    ((keyU i x).val m : ℚ) = w (.inl (i,UniformFolds.wordIndex L y)) := by
  simpa [keyU,Expr.val,Graph.Table.wordIndex,keyIndex,hm.start,hm.n,hy,Nat.cast_add,Nat.cast_mul]
    using hm.input (.inl (i,UniformFolds.wordIndex L y))

private theorem keyE_val {L} {args : Source → Expr} {v : Values L} {w base m} (hm : Ready args v w base m)
    (i j : V) (x y : Expr) (z u : Bits L) (hz : x.val m = (UniformFolds.wordIndex L z).val)
    (hu : y.val m = (UniformFolds.wordIndex L u).val) :
    ((keyE i j x y).val m : ℚ) = w (.inr (i,j,UniformFolds.wordIndex L z,UniformFolds.wordIndex L u)) := by
  simpa [keyE,Expr.val,Graph.Table.wordIndex,keyIndex,hm.start,hm.n,hz,hu,Nat.cast_add,Nat.cast_mul,add_assoc]
    using hm.input (.inr (i,j,UniformFolds.wordIndex L z,UniformFolds.wordIndex L u))

theorem entry_val {L} {args : Source → Expr} {v : Values L} {w base m} (hm : Ready args v w base m)
    (π : Equiv.Perm V) (E : Finset EdgeSlot) (rev : Bool) (h : Fin 3) (f : Factor) :
    ((entry args π E rev h f).val m : ℚ) = literal w (inputKey π E (address rev h v f)) := by
  rcases f with a | ⟨a,b⟩
  · rcases a with i|i
    · exact keyU_val hm _ _ _ (hm.sources _)
    · simp [entry,address,inputKey,literal,Expr.val]
  · by_cases active : (h,a,b)∈E
    · by_cases orientation : π (endpoint h a)<π (endpoint h b)
      · simpa only [entry,active,if_true,orientation,address,inputKey,edgeKey,literal,Sum.elim_inl] using
          keyE_val hm (π (endpoint h a)) (π (endpoint h b)) (src args rev a) (src args rev b) _ _ (hm.sources _) (hm.sources _)
      · simpa only [entry,active,if_true,if_neg orientation,address,inputKey,edgeKey,literal,Sum.elim_inl] using
          keyE_val hm (π (endpoint h b)) (π (endpoint h a)) (src args rev b) (src args rev a) _ _ (hm.sources _) (hm.sources _)
    · simp [entry,active,address,inputKey,literal,Expr.val]

theorem prodExpr_val (xs : List Expr) (m : Memory) :
    (prodExpr xs).val m = (xs.map (Expr.val m)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (x.val m * ·) ih

theorem component_val {L} {args : Source → Expr} {v : Values L} {w base m} (hm : Ready args v w base m)
    (π : Equiv.Perm V) (E : Finset EdgeSlot) (rev : Bool) (h : Fin 3) (g : Group) :
    ((component args π E rev h g).val m : ℚ) =
      piece rev h g v (fun i => literal w (inputKey π E i)) := by
  classical
  simp only [component,prodExpr_val,List.map_map,Int.cast_list_prod,List.map_map,piece]
  rw [Finset.prod_map_toList]
  apply Finset.prod_congr rfl
  intro f _
  by_cases a : factorGroup rev f=g <;> simp [Function.comp_apply,a,entry_val hm,Expr.val]

private theorem keyU_safe {L} {args : Source → Expr} {v : Values L} {w base m} (hm : Ready args v w base m)
    {W : ℕ} {d : ℤ} (hd : d < -67) (i : V) (x : Expr) (y : Bits L)
    (hx : x.safe d W m) (hy : x.val m = (UniformFolds.wordIndex L y).val)
    (hc : ∀ k : WeightKey (2^L), Fits W ((base+keyIndex k:ℕ):ℤ)) :
    (keyU i x).safe d W m := by
  let k : WeightKey (2^L) := .inl (i,UniformFolds.wordIndex L y)
  have eq : m baseReg + ((i.val:ℤ)*m sideReg + x.val m) = (base+keyIndex k : ℕ) := by
    simp [k,keyIndex,Graph.Table.wordIndex,hm.start,hm.n,hy]
  simp only [keyU,Expr.safe,Expr.val,Expr.num_safe,Expr.num_val]
  refine ⟨⟨by dsimp [baseReg]; omega,⟨⟨trivial,by dsimp [sideReg]; omega⟩,hx⟩⟩,?_,?_⟩
  · rw [eq]; omega
  · rw [eq]; exact hc k

private theorem keyE_safe {L} {args : Source → Expr} {v : Values L} {w base m} (hm : Ready args v w base m)
    {W : ℕ} {d : ℤ} (hd : d < -67) (i j : V) (x y : Expr) (z u : Bits L)
    (sx : x.safe d W m) (sy : y.safe d W m)
    (hz : x.val m = (UniformFolds.wordIndex L z).val) (hu : y.val m = (UniformFolds.wordIndex L u).val)
    (hc : ∀ k : WeightKey (2^L), Fits W ((base+keyIndex k:ℕ):ℤ)) :
    (keyE i j x y).safe d W m := by
  let k : WeightKey (2^L) := .inr (i,j,UniformFolds.wordIndex L z,UniformFolds.wordIndex L u)
  let n := m sideReg
  have eq : m baseReg + (9*n + ((i.val*9+j.val:ℕ):ℤ)*(n*n) + (x.val m*n + y.val m)) =
      (base+keyIndex k : ℕ) := by
    simp [n,k,keyIndex,Graph.Table.wordIndex,hm.start,hm.n,hz,hu,add_assoc]
  have hb : d < baseReg := by dsimp [baseReg]; omega
  have hn : d < sideReg := by dsimp [sideReg]; omega
  simp only [keyE,Expr.safe,Expr.val,Expr.num_safe,Expr.num_val,hb,hn,sx,sy, true_and,and_true,Nat.cast_ofNat]
  rw [eq]; exact ⟨by omega,hc k⟩

theorem entry_safe {L} {args : Source → Expr} {v : Values L} {w base m} (hm : Ready args v w base m)
    {W : ℕ} {d : ℤ} (hd : d < -67)
    (ha : ∀ q, (args q).safe d W m)
    (hc : ∀ k : WeightKey (2^L), Fits W ((base+keyIndex k:ℕ):ℤ))
    (π : Equiv.Perm V) (E : Finset EdgeSlot) (rev : Bool) (h : Fin 3) (f : Factor) :
    (entry args π E rev h f).safe d W m := by
  rcases f with (i|i) | ⟨a,b⟩
  · exact keyU_safe hm hd _ _ _ (ha _) (hm.sources _) hc
  · trivial
  · by_cases active : (h,a,b)∈E
    · by_cases orientation : π (endpoint h a)<π (endpoint h b)
      · simp only [entry,active,orientation,if_true]
        exact keyE_safe hm hd _ _ _ _ _ _ (ha _) (ha _)
          (hm.sources _) (hm.sources _) hc
      · simp only [entry,active,if_true,if_neg orientation]
        exact keyE_safe hm hd _ _ _ _ _ _ (ha _) (ha _)
          (hm.sources _) (hm.sources _) hc
    · simp [entry,active,Expr.safe]

private theorem prod_safe {d : ℤ} {W : ℕ} (xs : List Expr) (m : Memory)
    (h : ∀ x ∈ xs, x.safe d W m) : (prodExpr xs).safe d W m := by
  induction xs with
  | nil => trivial
  | cons a xs ih => exact ⟨h _ (by simp),ih (fun x hx => h _ (by simp [hx]))⟩

theorem component_safe {L} {args : Source → Expr} {v : Values L} {w base m} (hm : Ready args v w base m)
    {W : ℕ} {d : ℤ} (hd : d < -67)
    (ha : ∀ q, (args q).safe d W m)
    (hc : ∀ k : WeightKey (2^L), Fits W ((base+keyIndex k:ℕ):ℤ))
    (π : Equiv.Perm V) (E : Finset EdgeSlot) (rev : Bool) (h : Fin 3) (g : Group) :
    (component args π E rev h g).safe d W m := by
  apply prod_safe
  intro x hx
  obtain ⟨f,_,rfl⟩ := List.mem_map.mp hx
  split <;> first | exact entry_safe hm hd ha hc π E rev h f | trivial

end VWZClique.IntegerRAM.Projected.Factors
end

/- TraceDyadicData -/
section
namespace VWZClique.TraceDyadic
open RankSwap UniformFolds Double

private theorem digit_cast (j : Fin 4) (s u : Bool) : (digit j s u : ℚ) = oneBit j s u := by
  fin_cases j <;> cases s <;> cases u <;> decide

theorem basis_cast {L : ℕ} (j : BasisLabel L) (x : PairBits L) :
    (basisInt j x : ℚ) = basisEntry j x := by simp only [basisInt,Int.cast_prod,digit_cast,basisEntry]

private theorem bit_cast {x : ℚ} (hx : Binary x) : (bitInt x : ℚ) = x := by
  rcases hx with rfl | rfl <;> norm_num [bitInt]

theorem channel_cast {L : ℕ} (w : ChannelKey L → ℚ) (hw : ∀ k, Binary (w k))
    (h : Fin 3) (a b : Block L) : (channelInt w h a b : ℚ) = channel w h a b := by
  simp only [channelInt,channel,Int.cast_mul,Int.cast_prod,fun k => bit_cast (hw k)]

end VWZClique.TraceDyadic
end

/- NativeProjectionSlices -/
section
namespace VWZClique.IntegerRAM.Projected.Slices

open Projection UniformFolds TraceDyadic
variable {L : ℕ}

def integral (x : ℚ) : ℤ := if x=1 then 1 else 0

private theorem integral_cast {x : ℚ} (hx : Binary x) : (integral x:ℚ)=x := by
  rcases hx with h|h <;> rw [h] <;> norm_num [integral]

noncomputable def pieceInt (rev : Bool) (h : Fin 3) (g : Group) (v : Values L)
    (w : ChannelKey L → ℚ) : ℤ :=
  ∏ f : Factor, if factorGroup rev f=g then integral (w (address rev h v f)) else 1

theorem pieceInt_cast (rev : Bool) (h : Fin 3) (g : Group) (v : Values L)
    (w : ChannelKey L → ℚ) (hw : ∀ i, Binary (w i)) :
    (pieceInt rev h g v w : ℚ) = piece rev h g v w := by
  simp only [pieceInt,piece,Int.cast_prod]
  apply Finset.prod_congr rfl
  intro a _
  split <;> simp [integral_cast (hw _)]

noncomputable def inputA (rev : Bool) (h : Fin 3) (j : BasisLabel L) (w : ChannelKey L → ℚ) :
    Matrix (Bits L) (Bits L) ℤ := fun z x =>
  basisInt j (x,partner j x) * pieceInt rev h .pivotCenter ⟨(x,partner j x),z,default⟩ w

noncomputable def inputB (rev : Bool) (h : Fin 3) (j : BasisLabel L) (f : PairBits L) (w : ChannelKey L → ℚ) :
    Matrix (Bits L) (Bits L) ℤ := fun x v =>
  pieceInt rev h .pivotOther ⟨(x,partner j x),default,block f v⟩ w

noncomputable def outsideInt (rev : Bool) (h : Fin 3) (f : PairBits L) (w : ChannelKey L → ℚ) :
    Matrix (Bits L) (Bits L) ℤ := fun z v =>
  pieceInt rev h .centerOther ⟨default,z,block f v⟩ w

noncomputable def singleInt (rev : Bool) (h : Fin 3) (j : BasisLabel L) (z : Bits L) (b : Block L)
    (w : ChannelKey L → ℚ) : ℤ :=
  TraceDyadic.transform j (fun x => if rev then channelInt w h b (block x z) else channelInt w h (block x z) b)

theorem singleInt_cast (rev : Bool) (h : Fin 3) (j : BasisLabel L) (z : Bits L) (b : Block L)
    (w : ChannelKey L → ℚ) (hw : ∀ i, Binary (w i)) :
    (singleInt rev h j z b w:ℚ)=single rev h j z b w := by
  cases rev <;> simp [singleInt,TraceDyadic.transform,single,channel_cast w hw,basis_cast]

/-- One fixed pair of coordinates of the remote triple, and one retained
eigenlabel, need one small square multiplication followed by entrywise weights. -/
theorem slice_exact (rev : Bool) (h : Fin 3) (j : BasisLabel L) (f : PairBits L)
    (w : ChannelKey L → ℚ) (hw : ∀ i, Binary (w i)) (z v : Bits L) :
    (inputA rev h j w * inputB rev h j f w) z v * outsideInt rev h f w z v =
      singleInt rev h j z (block f v) w := by
  apply (Int.cast_injective (α:=ℚ))
  rw [singleInt_cast _ _ _ _ _ _ hw,single_eq]
  simp only [Matrix.mul_apply,Int.cast_mul,Int.cast_sum,inputA,inputB,outsideInt,Int.cast_mul,
    pieceInt_cast _ _ _ _ w hw,basis_cast,Projection.left,Projection.right,Projection.outside,Rat.cast_id]

noncomputable def lookupA (rev : Bool) (h : Fin 3) (j : BasisLabel L) (w : ChannelKey L → ℚ) :
    Matrix (Bits L) (Bits L) ℤ := fun z x =>
  basisInt j (x,partner j x) * pieceInt rev h .pivotCenter ⟨(x,lookupPartner j x),z,default⟩ w

noncomputable def lookupB (rev : Bool) (h : Fin 3) (j : BasisLabel L) (f : PairBits L) (w : ChannelKey L → ℚ) :
    Matrix (Bits L) (Bits L) ℤ := fun x v =>
  pieceInt rev h .pivotOther ⟨(x,lookupPartner j x),default,block f v⟩ w

theorem lookup_product (rev : Bool) (h : Fin 3) (j : BasisLabel L) (f : PairBits L) (w : ChannelKey L → ℚ) :
    lookupA rev h j w * lookupB rev h j f w = inputA rev h j w * inputB rev h j f w := by
  funext z v
  apply Finset.sum_congr rfl
  intro x _
  by_cases hs : basisInt j (x,partner j x)=0 <;> simp [lookupA,lookupB,lookupPartner,inputA,inputB,hs]

end VWZClique.IntegerRAM.Projected.Slices
end

/- NativeProjectionLeftButterfly -/
section
namespace VWZClique.IntegerRAM.Projected.Slices
open Structured Butterfly UniformFolds TraceDyadic Double

theorem scaled_transform {L} (P : ℤ) (j : BasisLabel L) (w : PairBits L → ℤ) :
    transformed L (fun f => P*w f) j = P*transform j w := by
  apply Int.cast_injective (α:=ℚ)
  rw [transformed_spec]
  simp only [transform,Int.cast_mul,Int.cast_sum,basis_cast,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  ring

/-- After the first-channel square slices have been scattered, the fixed
full butterfly computes the entire second projection at these two vertices. -/
theorem left_butterfly {L W src dst : ℕ} (S : Finset (BasisLabel L)) (i : S)
    (z v : Bits L) (w : ChannelKey L → ℚ) (P : ℤ) (K : ℕ) (m : Memory)
    (control : Parameters m src dst (4^(L-1))) (stages : m Reg.stages=L)
    (raw : ∀ f : PairBits L, m (src+pairAddress f:ℕ)=P*singleInt false 0 i z (block f v) w)
    (room : Room W src dst (4^(L-1))) (apart : Apart src dst (4^(L-1))) :
    ∃ o, Runs W full m (5+L*(15+20*4^(L-1))) o ∧
      (∀ j : S, (residualInt K L i*residualInt K L j)*
        o (finalBase L src dst+(labelIndex L j.val).val:ℕ) = P*leftTable S S K K w (i,z) (j,v)) ∧
      ∀ j : ℕ, (j<src ∨ src+4*4^(L-1)≤j) → (j<dst ∨ dst+4*4^(L-1)≤j) → o j=m j := by
  obtain ⟨o,run,vals,keep⟩ := full_run m _ control stages raw room apart
  refine ⟨o,run,?_,keep⟩
  intro j
  rw [labelIndex_val,vals,scaled_transform]
  change _*(P*rawLeft S S w (i,z) (j,v))=P*((residualInt K L i*residualInt K L j)*rawLeft S S w (i,z) (j,v))
  ring

end VWZClique.IntegerRAM.Projected.Slices
end

/- NativeProjectionLeftSetup -/
section
namespace VWZClique.IntegerRAM.Projected.LeftSetup
open Structured FoldBits Butterfly

def raw (base n p r c : ℕ) := base+((p*n+r)*n+c)*(n*n)
def out (base n a p r c : ℕ) := base+(p*n+r)*(a*n)+c

theorem start_runs {W L n p r c b d : ℕ} (m : Memory)
    (N : m 0=n) (depth : m 320=L) (P : m 357=p) (R : m 354=r) (C : m 355=c) (B : m 374=b) (D : m 356=d) :
    ∃ v, Runs W (FoldBits.code start) m 12 v ∧ v first=raw b n p r c ∧ v second=d ∧
      v firstOrig=raw b n p r c ∧ v idx=0 ∧ v next=1 ∧ v one=1 ∧ v 320=L ∧ ∀ z : ℕ, v z=m z := by
  let v := start.foldl FoldBits.write m
  refine ⟨v,FoldBits.code_runs _ _ _ (by simp [start,FoldBits.Safe,FoldBits.safe]),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals try intro z
  all_goals simp (disch := omega) [v,start,FoldBits.write,update,one,sq,firstOrig,first,second,next,idx,N,depth,P,R,C,B,D,raw,
    Nat.cast_add,Nat.cast_mul] <;> ring

theorem iterate {W L b d : ℕ} (hL : 0<L) (m : Memory)
    (cf : m first=b) (cs : m second=d) (orig : m firstOrig=b)
    (iter : m idx=0) (scale : m next=1) (unit : m one=1) (limit : m 320=L)
    (fit : ∀ i : ℕ, i≤L → Fits W ((i:ℤ)-L)) :
    ∃ t o, t≤9*L ∧ Runs W loop m t o ∧ o first=finalBase L b d ∧ o current=(4^(L-1):ℕ) ∧
      o firstOrig=b ∧ o one=1 ∧ ∀ z : ℕ, o z=m z := by
  have swap (j b d : ℕ) : finalBase (j+1) b d=finalBase j d b := rfl
  let I (q : ℕ) (v : Memory) := v first=finalBase q b d ∧ v second=finalBase q d b ∧
    v firstOrig=b ∧ v next=(4^q:ℕ) ∧ (0<q → v current=(4^(q-1):ℕ)) ∧
    v idx=q ∧ v one=1 ∧ v 320=L ∧ ∀ z : ℕ, v z=m z
  have initial : I 0 m := ⟨cf,cs,orig,by simpa using scale,by omega,by simpa using iter,unit,limit,fun _ => rfl⟩
  have advance (q : ℕ) (hq : q<L) (v : Memory) (pre : I q v) :
      ∃ t≤6, ∃ o, Runs W (FoldBits.code step) v t o ∧ o idx=q ∧ o one=1 ∧ o 320=L ∧
        I (q+1) (nextMemory o idx test q L) := by
    obtain ⟨fv,sv,ov,scale,_,iv,uv,len,frame⟩ := pre
    let o := step.foldl FoldBits.write v
    have h₁ : v (-74)=1 := uv
    have h₂ : v (-70)=(finalBase q b d:ℤ) := fv
    have h₃ : v (-71)=(finalBase q d b:ℤ) := sv
    have h₄ : v (-73)=((4^q:ℕ):ℤ) := scale
    refine ⟨6,le_rfl,o,FoldBits.code_runs _ _ _ (by simp [step,FoldBits.Safe,FoldBits.safe]),?_,?_,?_,
      ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals try intro z
    all_goals simp (disch := omega) [o,step,FoldBits.write,update,nextMemory,idx,test,first,second,one,next,save,current,
      firstOrig,swap,h₁,h₂,h₃,h₄,pow_succ] at *
    all_goals first | assumption | apply frame | ring
  obtain ⟨t,time,o,run,final⟩ := repeatN_runs (B:=6) hL _ (by decide) I fit advance initial
  obtain ⟨f,_,orig,_,result,_,one,_,keep⟩ := final
  exact ⟨t,o,by omega,run,f,result hL,orig,one,keep⟩

theorem kernel_run {W L n p r c b d : ℕ} (m : Memory) (hL : 0<L)
    (N : m 0=n) (depth : m 320=L) (P : m 357=p) (R : m 354=r) (C : m 355=c) (B : m 374=b) (D : m 356=d)
    (fit : ∀ i : ℕ, i≤L → Fits W ((i:ℤ)-L)) :
    ∃ t o, t≤12+9*L ∧ Runs W kernel m t o ∧ o first=finalBase L (raw b n p r c) d ∧
      o current=(4^(L-1):ℕ) ∧ o firstOrig=raw b n p r c ∧ o one=1 ∧ ∀ z : ℕ, o z=m z := by
  obtain ⟨v,run,left,right,orig,index,next,unit,len,fr⟩ := start_runs (W:=W) m N depth P R C B D
  obtain ⟨t,o,time,walk,answer,sc,ptr,val,keep⟩ := iterate hL v left right orig index next unit len fit
  exact ⟨_,o,by omega,.seq run walk,answer,sc,ptr,val,fun z => (keep z).trans (fr z)⟩

theorem configure_run {W L n p r c b d : ℕ} (m : Memory) (hL : 0<L)
    (N : m 0=n) (depth : m 320=L) (P : m 357=p) (R : m 354=r) (C : m 355=c) (B : m 374=b) (D : m 356=d)
    (fit : ∀ i : ℕ, i≤L → Fits W ((i:ℤ)-L)) :
    ∃ t o, t≤16+9*L ∧ Runs W configure m t o ∧ Parameters o (raw b n p r c) d (4^(L-1)) ∧
      o Reg.stages=L ∧ ∀ z : ℕ, o z=m z := by
  obtain ⟨t,q,time,walk,_,stride,base,unit,keep⟩ := kernel_run m hL N depth P R C B D fit
  let o := control.foldl FoldBits.write q
  have run : Runs W (FoldBits.code control) q 4 o := FoldBits.code_runs _ _ _ (by simp [control,FoldBits.Safe,FoldBits.safe])
  have qo : q (-74)=1 := unit
  have qb : q (-78)=raw b n p r c := base
  have qs : q (-72)=(4^(L-1):ℕ) := stride
  have qd := (keep 356).trans D
  have ql := (keep 320).trans depth
  refine ⟨t+4,o,by omega,.seq walk run,⟨?_,?_,?_⟩,?_,?_⟩
  all_goals try intro z
  all_goals simp (disch := omega) [o,control,FoldBits.write,update,Reg.srcBase,Reg.dstBase,Reg.stages,Reg.stride,
    firstOrig,one,current,qo,qb,qs,qd,ql,keep] <;> assumption

end VWZClique.IntegerRAM.Projected.LeftSetup
end

/- NativeProjectionLeftJob -/
section
namespace VWZClique.IntegerRAM.Projected.LeftSetup
open Structured FoldBits Butterfly UniformFolds TraceDyadic Double

structure Header (L n p r c a rawBase work dense code scale : ℕ) (m : Memory) : Prop where
  N : m 0=n
  Lval : m 320=L
  pval : m 357=p
  rVal : m 354=r
  cVal : m 355=c
  rawVal : m 374=rawBase
  tempVal : m 356=work
  denseVal : m 371=dense
  codeVal : m 358=code
  coeffVal : m 370=scale
  labels : m 359=a

theorem Header.retain {L n p r c a b w d k v : ℕ} {m o : Memory}
    (h : Header L n p r c a b w d k v m) (fr : ∀ j : ℕ, j≤374 → o j=m j) :
    Header L n p r c a b w d k v o :=
  ⟨(fr 0 (by decide)).trans h.N,(fr 320 (by decide)).trans h.Lval,(fr 357 (by decide)).trans h.pval,
   (fr 354 (by decide)).trans h.rVal,(fr 355 (by decide)).trans h.cVal,(fr 374 (by decide)).trans h.rawVal,
   (fr 356 (by decide)).trans h.tempVal,(fr 371 (by decide)).trans h.denseVal,(fr 358 (by decide)).trans h.codeVal,
   (fr 370 (by decide)).trans h.coeffVal,(fr 359 (by decide)).trans h.labels⟩

theorem gather_regs {W L n p r c a b w d k v z : ℕ} (m : Memory) (h : Header L n p r c a b w d k v m)
    (sel : m first=z) (unit : m one=1) (fit : Fits W ((v+p:ℕ):ℤ)) :
    ∃ o, Runs W (FoldBits.code prepareGather) m 13 o ∧
      LeftGather.Ready a k v z (out d n a p r c) n (m (v+p:ℕ)) o ∧ ∀ j : ℕ, o j=m j := by
  let o := prepareGather.foldl FoldBits.write m
  obtain ⟨N,_,P,R,C,_,_,D,K,V,A⟩ := h
  have unit' : m (-74)=1 := unit
  have sel' : m (-70)=z := sel
  have run : Runs W (FoldBits.code prepareGather) m 13 o := FoldBits.code_runs _ _ _ (by
    simpa [prepareGather,FoldBits.Safe,FoldBits.safe,FoldBits.write,update,LeftGather.limit,LeftGather.codes,LeftGather.coeff,
      LeftGather.inputBase,LeftGather.stride,LeftGather.dest,LeftGather.rowScalar,save,V,P,Nat.cast_add] using fit)
  have nonneg {x : ℤ} (hx : x < 0) : (v:ℤ)+p≠x := by omega
  refine ⟨o,run,?_,?_⟩
  · constructor <;> simp [o,prepareGather,FoldBits.write,update,LeftGather.limit,LeftGather.codes,LeftGather.coeff,
      LeftGather.inputBase,LeftGather.stride,LeftGather.dest,LeftGather.rowScalar,save,first,one,unit',sel',out,D,K,V,P,N,A,C,R,Nat.cast_add,Nat.cast_mul,nonneg (by decide : (-75:ℤ)<0),
      nonneg (by decide : (-23:ℤ)<0),nonneg (by decide : (-24:ℤ)<0),nonneg (by decide : (-22:ℤ)<0),
      nonneg (by decide : (-21:ℤ)<0),nonneg (by decide : (-20:ℤ)<0),nonneg (by decide : (-3:ℤ)<0)] <;> ring
  · intro j; simp [o,prepareGather,FoldBits.write,update,LeftGather.limit,LeftGather.codes,
      LeftGather.coeff,LeftGather.inputBase,LeftGather.stride,LeftGather.dest,LeftGather.rowScalar,save]

theorem job_runs {W L K a rawBase temp dense codeBase scaleBase : ℕ}
    (hL : 0<L) (S : Finset (BasisLabel L)) (labels : Fin a→S) (p : Fin a) (r c : Fin (2^L))
    (w : ChannelKey L → ℚ) (P : ℤ) (m : Memory)
    (h : Header L (2^L) p r c a rawBase temp dense codeBase scaleBase m)
    (rawInput : ∀ f : PairBits L, m (raw rawBase (2^L) p r c+pairAddress f:ℕ) =
      P*Slices.singleInt false 0 (labels p) ((wordIndex L).symm r) (block f ((wordIndex L).symm c)) w)
    (rows : ∀ i : Fin a, m (codeBase+i.val:ℕ)=(labelIndex L (labels i).val).val ∧
      m (scaleBase+i.val:ℕ)=residualInt K L (labels i).val)
    (heap : 374<raw rawBase (2^L) p r c ∧ 374<temp)
    (guardL : ∀ i : ℕ, i≤L → Fits W ((i:ℤ)-L)) (guardN : ∀ i : ℕ, i≤a → Fits W ((i:ℤ)-a))
    (room : Room W (raw rawBase (2^L) p r c) temp (4^(L-1)))
    (apart : Apart (raw rawBase (2^L) p r c) temp (4^(L-1)))
    (dataSafe : ∀ i : Fin a, let z := raw rawBase (2^L) p r c
      (codeBase+i.val<z ∨ z+4*4^(L-1)≤codeBase+i.val) ∧ (codeBase+i.val<temp ∨ temp+4*4^(L-1)≤codeBase+i.val) ∧
      (scaleBase+i.val<z ∨ z+4*4^(L-1)≤ scaleBase+i.val) ∧ (scaleBase+i.val<temp ∨ temp+4*4^(L-1)≤ scaleBase+i.val))
    (safe : ∀ i : Fin a, let dest := LeftGather.loc (out dense (2^L) a p r c) (2^L) i
      let z := finalBase L (raw rawBase (2^L) p r c) temp
      Fits W ((codeBase+i.val:ℕ):ℤ) ∧ Fits W ((scaleBase+i.val:ℕ):ℤ) ∧
        Fits W ((z+(labelIndex L (labels i).val).val:ℕ):ℤ) ∧ Fits W (dest:ℤ))
    (disjoint : ∀ i j : Fin a, let addr := LeftGather.loc (out dense (2^L) a p r c) (2^L) j
      addr≠codeBase+i.val ∧ addr≠scaleBase+i.val ∧ addr≠finalBase L (raw rawBase (2^L) p r c) temp+(labelIndex L (labels i).val).val) :
    ∃ t o, t≤budget L a ∧ Runs W job m t o ∧
      (∀ i : Fin a, o (LeftGather.loc (out dense (2^L) a p r c) (2^L) i) =
        P*leftTable S S K K w (labels p,(wordIndex L).symm r) (labels i,(wordIndex L).symm c)) ∧
      ∀ j : ℕ, (j<raw rawBase (2^L) p r c ∨ raw rawBase (2^L) p r c+4*4^(L-1)≤j) →
        (j<temp ∨ temp+4*4^(L-1)≤j) →
        (∀ i : Fin a, j≠LeftGather.loc (out dense (2^L) a p r c) (2^L) i) → o j=m j := by
  let n := 2^L
  let b := raw rawBase n p r c
  let result := finalBase L b temp
  let atCode (i : Fin a) := (labelIndex L (labels i).val).val
  let dc (i : Fin a) := residualInt K L (labels i).val
  obtain ⟨s,v,sc,init,ctrl,stages,fr⟩ := configure_run m hL h.N h.Lval h.pval h.rVal h.cVal h.rawVal h.tempVal guardL
  obtain ⟨u,fly,answer,keep⟩ := Slices.left_butterfly S (labels p) ((wordIndex L).symm r) ((wordIndex L).symm c)
    w P K v ctrl stages (fun f => (fr _).trans (rawInput f)) room apart
  have hh := h.retain (fun j hj => (keep j (Or.inl (by omega)) (Or.inl (by omega))).trans (fr j))
  obtain ⟨t,x,tc,prep,z,_,_,unit,xf⟩ := kernel_run u hL hh.N hh.Lval hh.pval hh.rVal hh.cVal hh.rawVal hh.tempVal guardL
  obtain ⟨y,reg,ready,yf⟩ := gather_regs x (hh.retain (fun j _ => xf j)) z unit (safe p).2.1
  let values (i : Fin a) := u (result+atCode i:ℕ)
  have xx (i : Fin a) : x (scaleBase+i.val:ℕ)=dc i :=
    (xf _).trans ((keep _ (dataSafe i).2.2.1 (dataSafe i).2.2.2).trans ((fr _).trans (rows i).2))
  rw [xx p] at ready
  obtain ⟨q,o,qc,last,words,preserved⟩ := LeftGather.gather (Nat.zero_lt_of_lt p.isLt) (by positivity : 0<n)
    atCode dc values y ready (fun i => ⟨(yf _).trans ((xf _).trans ((keep _ (dataSafe i).1 (dataSafe i).2.1).trans ((fr _).trans (rows i).1))),
       (yf _).trans (xx i),(yf _).trans (xf _)⟩) disjoint guardN safe
  refine ⟨_,o,?_,.seq init (.seq fly (.seq prep (.seq reg last))),fun i => (words i).trans (answer (labels i)),?_⟩
  · dsimp only [budget];omega
  · intro j before after avoid
    exact (preserved j avoid).trans ((yf j).trans ((xf j).trans ((keep j before after).trans (fr j))))

end VWZClique.IntegerRAM.Projected.LeftSetup
end

/- NativeProjectionLeftGridGeometry -/
section
namespace VWZClique.IntegerRAM.Projected.LeftGrid
open Grid Placement LeftSetup UniformFolds

def src {a n : ℕ} (base : ℕ) (v : Site a n) := raw base n v.1.val v.2.1.val v.2.2.val
def dst {a n : ℕ} (base : ℕ) (v : Site a n) (i : Fin a) := LeftGather.loc (out base n a v.1 v.2.1 v.2.2) n i

def packedDst {a n : ℕ} (v : Site a n) (i : Fin a) :=
  packed (packed v.1 v.2.1) (packed i v.2.2)

theorem dst_eq {a n : ℕ} (base : ℕ) (v : Site a n) (i : Fin a) :
    dst base v i=base+(packedDst v i).val := by
  simp [dst,LeftGather.loc,out,packedDst,packed_val];ring

theorem dst_inj {a n base : ℕ} {v u : Site a n} {i j : Fin a} (eq : dst base v i=dst base u j) : v=u := by
  rw [dst_eq,dst_eq,Nat.add_left_cancel_iff] at eq
  have h : packedDst v i=packedDst u j := Fin.ext eq
  have h₁ := finProdFinEquiv.injective h
  have xy := finProdFinEquiv.injective (congrArg Prod.fst h₁)
  have z := finProdFinEquiv.injective (congrArg Prod.snd h₁)
  have a₁ : v.1=u.1 := congrArg (fun x : Fin a × Fin n => x.1) xy
  have a₂ : v.2.1=u.2.1 := congrArg (fun x : Fin a × Fin n => x.2) xy
  have a₃ : v.2.2=u.2.2 := congrArg (fun x : Fin a × Fin n => x.2) z
  exact Prod.ext a₁ (Prod.ext a₂ a₃)

theorem dst_bounds {a n : ℕ} (base : ℕ) (v : Site a n) (i : Fin a) :
    base≤dst base v i ∧ dst base v i<base+(a*n)*(a*n) := by
  rw [dst_eq];have := (packedDst v i).isLt;omega

theorem destination {a n : ℕ} (d : ℕ) (v : Site a n) (i : Fin a) :
    dst d v i=d+(v.1.val*n+v.2.1.val)*(a*n)+(i.val*n+v.2.2.val) := by
  rw [dst_eq];simp [packedDst,packed_val,Nat.add_assoc]

theorem src_bounds {a n : ℕ} (base : ℕ) (v : Site a n) :
    base≤ src base v ∧ src base v+n^2≤base+a*n*n*(n^2) := by
  have h := Nat.mul_le_mul_right (n^2) (serial_lt v)
  rw [Nat.succ_mul] at h
  change base≤base+serial v*(n*n) ∧ base+serial v*(n*n)+n^2≤base+a*n*n*n^2
  rw [←pow_two];omega

theorem src_before {a n : ℕ} (base : ℕ) {u v : Site a n} (lt : serial u< serial v) :
    src base u+n^2≤ src base v := by
  have h := Nat.mul_le_mul_right (n^2) lt
  rw [Nat.succ_mul] at h
  change base+serial u*(n*n)+n^2≤base+serial v*(n*n)
  rw [←pow_two];omega

theorem length_eq (L : ℕ) : (4:ℕ)^L=(2^L)^2 := by rw [←pow_mul,Nat.mul_comm,pow_mul];rfl

theorem width_eq {L : ℕ} (h : 0<L) : 4*4^(L-1)=(2^L)^2 := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L≠0)
  simpa [pow_succ,Nat.mul_comm] using length_eq (l+1)

theorem code_lt {L : ℕ} (f : PairBits L) : Butterfly.pairAddress f<(2^L)^2 := by
  rw [←Butterfly.pairIndex_val,←length_eq]
  exact (Butterfly.pairIndex L f).isLt

theorem outside_private {j : ℕ} (h : 374<j) : ¬ Batch.privateCell j := by
  dsimp [Batch.privateCell];omega

end VWZClique.IntegerRAM.Projected.LeftGrid
end

/- NativeProjectionLeftGrid -/
section
namespace VWZClique.IntegerRAM.Projected.LeftGrid
open Grid LeftSetup UniformFolds TraceDyadic Double Butterfly Structured

structure Static (L n a base work dense codes scales : ℕ) (m : Memory) : Prop where
  dim : m 0=n
  length : m 320=L
  count : m 359=a
  raw : m 374=base
  temp : m 356=work
  dest : m 371=dense
  code : m 358=codes
  coeff : m 370=scales

def frame {a n : ℕ} (base dense : ℕ) (m o : Memory) : Prop :=
  ∀ j : ℕ, j<base → ¬ Batch.privateCell j → (∀ (u : Site a n) (i : Fin a), j≠dst dense u i) → o j=m j

noncomputable def rawValue {L a} {S : Finset (BasisLabel L)} (w : ChannelKey L → ℚ) (P : ℤ)
    (lab : Fin a → S) (v : Site a (2^L)) (f : PairBits L) :=
  P*Slices.singleInt false 0 (lab v.1) ((wordIndex L).symm v.2.1) (block f ((wordIndex L).symm v.2.2)) w

noncomputable def value {L a : ℕ} (K : ℕ) {S : Finset (BasisLabel L)} (w : ChannelKey L → ℚ) (P : ℤ)
    (lab : Fin a → S) (v : Site a (2^L)) (i : Fin a) :=
  P*leftTable S S K K w (lab v.1,(wordIndex L).symm v.2.1) (lab i,(wordIndex L).symm v.2.2)

theorem collect {W M L K a base work dense codes scales : ℕ} (hL : 0<L)
    (S : Finset (BasisLabel L)) (lab : Fin a → S) (w : ChannelKey L → ℚ) (P : ℤ)
    (m : Memory) (h : Static L (2^L) a base work dense codes scales m)
    (input : ∀ (v : Site a (2^L)) (f : PairBits L), m (src base v+pairAddress f:ℕ)=rawValue w P lab v f)
    (rows : ∀ i : Fin a, m (codes+i.val:ℕ)=(labelIndex L (lab i).val).val ∧ m (scales+i.val:ℕ)=residualInt K L (lab i).val)
    (high : 374<codes ∧ 374< scales) (before : codes+a≤dense ∧ scales+a≤dense)
    (AB : dense+(a*2^L)*(a*2^L)≤base)
    (BC : base+a*(2^L)*(2^L)*((2^L)^2)≤work)
    (cap : Graph.Division.Room W M) (space : work+(2^L)^2≤M) :
    ∃ t≤9+(a*(2^L)*(2^L))*(LeftSetup.budget L a+17), ∃ o, Runs W (Batch.grid job) m t o ∧
      frame (a:=a) (n:=2^L) base dense m o ∧ ∀ v i, o (dst dense v i)=value K w P lab v i := by
  let n := 2^L
  have hn : 0<n := by dsimp [n];positivity
  have hn2 : n≤n^2 := by simpa [pow_two] using Nat.mul_le_mul_left n hn
  have nm : n≤M := by change work+n^2≤M at space;omega
  have datahi : 374<dense := by omega
  have bd : dense≤base := by omega
  have bw : base≤work := by omega
  have Wd : 4*4^(L-1)=n^2 := width_eq hL
  have stepClock : a*n*n≤M := by
    have h2 : 1≤n^2 := by omega
    have h3 := Nat.mul_le_mul_left (a*n*n) h2
    change base+a*n*n*(n^2)≤work at BC
    omega
  have guardL (i : ℕ) (ih : i≤L) : Fits W ((i:ℤ)-L) := by
    have ll : L<n := Nat.lt_two_pow_self
    apply cap.fits <;> omega
  have guardA (i : ℕ) (ih : i≤a) : Fits W ((i:ℤ)-a) := by apply cap.fits <;> omega
  let I (q : ℕ) (x : Memory) := frame (a:=a) (n:=n) base dense m x ∧
    ∀ (v : Site a n), q≤ serial v → ∀ f, x (src base v+pairAddress f:ℕ)=rawValue w P lab v f
  have init : I 0 m := ⟨fun _ _ _ _ => rfl,fun v _ => input v⟩
  have ro {q x} (h : I q x) (z : ℕ) (lower : z<dense) (static : ¬Batch.privateCell z) : x z=m z :=
    h.1 _ (by omega) static (fun v i => Nat.ne_of_lt (lt_of_lt_of_le lower (dst_bounds dense v i).1))
  have rkeep {q x} (h : I q x) (i : Fin a) :
      x (codes+i.val:ℕ)=(labelIndex L (lab i).val).val ∧ x (scales+i.val:ℕ)=residualInt K L (lab i).val := by
    have il := i.isLt
    exact ⟨(ro h _ (by omega) (outside_private (by omega))).trans (rows i).1,
      (ro h _ (by omega) (outside_private (by omega))).trans (rows i).2⟩
  have st (q : ℕ) (x y : Memory) (fr : Batch.unchanged x y) (s : I q x) : I q y := by
    refine ⟨fun j bj pj aj => (fr j pj).trans (s.1 j bj pj aj),?_⟩
    intro v hv f
    have sl := (src_bounds base v).1
    exact (fr _ (outside_private (by omega))).trans (s.2 v hv f)
  obtain ⟨t,cost,o,run,last,output⟩ := Grid.collect hn cap nm (by omega : codes+a≤M) stepClock job I
    (fun i => ((labelIndex L (lab i).val).val:ℤ)) (dst dense) (value K w P lab) st
    (fun v i => outside_private (lt_of_lt_of_le datahi (dst_bounds dense v i).1)) (fun _ _ pre i => (rkeep pre i).1)
    m h.dim h.count h.code init (B:=LeftSetup.budget L a) (by
      intro v x pre _ rr cc pp
      have hv : LeftSetup.Header L n v.1 v.2.1 v.2.2 a base work dense codes scales x := by
        have head (j : ℕ) (hj : j≤374) (pj : ¬Batch.privateCell j) := ro pre j (lt_of_le_of_lt hj datahi) pj
        exact ⟨(head 0 (by decide) (by unfold Batch.privateCell;decide)).trans h.dim,
          (head 320 (by decide) (by unfold Batch.privateCell;decide)).trans h.length,pp,rr,cc,
          (head 374 (by decide) (by unfold Batch.privateCell;decide)).trans h.raw,
          (head 356 (by decide) (by unfold Batch.privateCell;decide)).trans h.temp,
          (head 371 (by decide) (by unfold Batch.privateCell;decide)).trans h.dest,
          (head 358 (by decide) (by unfold Batch.privateCell;decide)).trans h.code,
          (head 370 (by decide) (by unfold Batch.privateCell;decide)).trans h.coeff,
          (head 359 (by decide) (by unfold Batch.privateCell;decide)).trans h.count⟩
      have vlow := (src_bounds base v).1
      have vend := (src_bounds base v).2
      have bh : src base v+n^2≤work := vend.trans BC
      have dataCode (i : Fin a) : codes+i.val<dense := by have := i.isLt;omega
      have dataScale (i : Fin a) : scales+i.val<dense := by have := i.isLt;omega
      have maxEnd : max (src base v) work+4*4^(L-1)≤M := by rw [Wd,max_eq_right (by omega)];exact space
      have room : Room W (src base v) work (4^(L-1)) := by
        apply maxEnd.trans
        exact_mod_cast (le_of_lt cap : (M:ℤ)≤(2:ℤ)^(W-1))
      have ap : Apart (src base v) work (4^(L-1)) := Or.inl (Wd ▸ bh)
      have outputPointer : finalBase L (src base v) work = src base v ∨ finalBase L (src base v) work=work := by
        rw [finalBase_parity];split <;> simp
      have labelLo (i : Fin a) : (labelIndex L (lab i).val).val<n^2 := (labelIndex L (lab i).val).isLt.trans_eq (length_eq L)
      have tbound (i : Fin a) := (dst_bounds dense v i).2.trans_le AB
      have rawEnd (i : Fin a) : finalBase L (src base v) work+(labelIndex L (lab i).val).val<M := by
        rcases outputPointer with e|e <;> rw [e] <;> have hi := labelLo i <;> omega
      have rawLo (i : Fin a) : base≤finalBase L (src base v) work+(labelIndex L (lab i).val).val := by
        rcases outputPointer with e|e <;> rw [e] <;> omega
      obtain ⟨u,y,ub,exec,vals,fr⟩ := job_runs hL S lab v.1 v.2.1 v.2.2 w P x hv (pre.2 v le_rfl) (rkeep pre)
        ⟨by change 374< src base v;omega,by omega⟩ guardL guardA room ap
        (fun i => by have d := dataCode i;have s := dataScale i
                     exact ⟨Or.inl (lt_of_lt_of_le d (bd.trans vlow)),Or.inl (lt_of_lt_of_le d (bd.trans bw)),
                            Or.inl (lt_of_lt_of_le s (bd.trans vlow)),Or.inl (lt_of_lt_of_le s (bd.trans bw))⟩)
        (fun i => by have := dataScale i;have := dataCode i;have := rawEnd i;have := tbound i
                     change _ ∧ _ ∧ Fits W ((finalBase L (src base v) work+(labelIndex L (lab i).val).val:ℕ):ℤ) ∧ Fits W (dst dense v i)
                     refine ⟨?_,?_,?_,?_⟩ <;> apply cap.fits <;> omega)
        (fun i j => by
          have := rawLo i;have := dataCode i;have := dataScale i;have := tbound j;have := (dst_bounds dense v j).1
          change dst dense v j≠_ ∧ dst dense v j≠_ ∧ dst dense v j≠finalBase L (src base v) work+_
          omega)
      have keepLow (z : ℕ) (lo : z<base) (avoid : ∀ i, z≠dst dense v i) : y z=x z :=
        fr z (Or.inl (by change z< src base v;omega)) (Or.inl (by omega)) avoid
      refine ⟨u,ub,y,exec,⟨fun j lo pj aj => (keepLow j lo (aj v)).trans (pre.1 j lo pj aj),?_⟩,vals,?_,?_⟩
      · intro u hu f
        have off : pairAddress f<n^2 := code_lt f
        have ub := (src_bounds base u).2.trans BC
        have u0 := (src_bounds base u).1
        have later := src_before base (show serial v< serial u by omega)
        have fixed := fr (src base u+pairAddress f) (Or.inr (by change src base v+_≤_;rw [Wd];omega))
          (Or.inl (by omega)) (fun i => by change _≠dst dense v i;have := tbound i;omega)
        exact fixed.trans (pre.2 u (by omega) f)
      · intro u lt i
        exact keepLow _ ((dst_bounds dense u i).2.trans_le AB) (fun j eq => (Nat.ne_of_lt lt) (congrArg serial (dst_inj eq)))
      · intro j lock
        have hj : 0≤j ∧ j≤374 := by dsimp [Batch.locked,Batch.labels,Batch.labelCount,Batch.clock,Batch.slab] at lock;omega
        have f := keepLow j.toNat (by omega) (fun i => by have := (dst_bounds dense v i).1;omega)
        simpa [Int.toNat_of_nonneg hj.1] using f)
  exact ⟨t,cost,o,run,last.1,output⟩

end VWZClique.IntegerRAM.Projected.LeftGrid
end

/- NativeProjectionCells -/
section
namespace VWZClique.IntegerRAM.Projected.Slices.Fill
open Structured Projection WeightedProof UniformFolds TraceDyadic SquareCode Factors

private def point {L : ℕ} (g : Group) (j : BasisLabel L) (f : PairBits L) (u v : Bits L) : Values L :=
  match g with
  | .pivotCenter => ⟨(v,lookupPartner j v),u,default⟩
  | .pivotOther => ⟨(u,lookupPartner j u),default,block f v⟩
  | .centerOther => ⟨default,u,block f v⟩

private theorem word_zero (L : ℕ) : (wordIndex L (default : Bits L)).val=0 := by
  induction L with
  | zero => rfl
  | succ L ih => change (wordIndex L (default : Bits L)).val+2^L*0=0; simpa using ih

structure Sheet {L : ℕ} (j : BasisLabel L) (f : PairBits L)
    (w : WeightKey (2^L) → ℚ) (base sig pr dst : ℕ) (m : Memory) : Prop where
  n : m sideReg = ((2^L:ℕ):ℤ)
  base_eq : m baseReg = base
  f0 : m remote0 = (wordIndex L f.1).val
  f1 : m remote1 = (wordIndex L f.2).val
  bSig : m signBase=sig
  bPart : m partnerBase=pr
  bDst : m dest=dst
  lab : m label = (Butterfly.labelIndex L j).val
  width : m labelCount = ((4^L:ℕ):ℤ)
  weights : ∀ k, (m ((base+keyIndex k:ℕ):ℤ) : ℚ) = w k
  signs : ∀ x, m ((sig+(wordIndex L x).val*4^L+(Butterfly.labelIndex L j).val:ℕ):ℤ) = basisInt j (x,partner j x)
  partners : ∀ x, m ((pr+(wordIndex L x).val*4^L+(Butterfly.labelIndex L j).val:ℕ):ℤ) = (wordIndex L (lookupPartner j x)).val

structure Context {L : ℕ} (j : BasisLabel L) (f : PairBits L) (u v : Bits L)
    (w : WeightKey (2^L) → ℚ) (base sig pr dst : ℕ) (m : Memory) extends Sheet j f w base sig pr dst m where
  row_eq : m (-5) = (wordIndex L u).val
  col_eq : m (-6) = (wordIndex L v).val

private theorem lookup_val {L : ℕ} {j : BasisLabel L} {f u v w base sig pr dst m}
    (c : Context j f u v w base sig pr dst m) (g : Group) :
    Ready (coords g) (point g j f u v) w base m := by
  refine ⟨c.n,c.base_eq,?_,c.weights⟩
  have fields (e : Expr) (x : Bits L) (he : e.val m=(wordIndex L x).val) :
      (supportEntry partnerBase e).val m=(wordIndex L (lookupPartner j x)).val := by
    simpa [supportEntry,Expr.val,c.bPart,c.lab,c.width,he,Nat.cast_add,Nat.cast_mul,add_assoc] using c.partners x
  have r : row.val m = (wordIndex L u).val := c.row_eq
  have k : col.val m = (wordIndex L v).val := c.col_eq
  have zero : (0:ℤ) = ((wordIndex L (default : Bits L)).val:ℤ) := by rw [word_zero]; rfl
  intro q
  cases g <;> cases q with
  | pivot b => cases b <;> simp [coords,point,idx,value,Expr.val,row,col,r,k,c.row_eq,c.col_eq,word_zero] <;> first | exact fields _ _ r | exact fields _ _ k | exact zero
  | center => simp [coords,point,value,Expr.val,row,c.row_eq,word_zero] <;> exact zero
  | other i => fin_cases i <;> simp [coords,point,value,block,Expr.val,col,c.f0,c.f1,c.col_eq,word_zero] <;> exact zero

private theorem lookup_safe {L W : ℕ} {j : BasisLabel L} {f u v w base sig pr dst m}
    (c : Context j f u v w base sig pr dst m) (r : ℤ) (k : ℕ) (rh : Layout.floor < r) (rb : m r=k)
    (a : Expr) (x : Bits L) (sa : a.safe Layout.floor W m) (eq : a.val m=(wordIndex L x).val)
    (fit : Fits W ((k+(wordIndex L x).val*4^L+(Butterfly.labelIndex L j).val:ℕ):ℤ)) :
    (supportEntry r a).safe Layout.floor W m := by
  have num : m r+(a.val m*m labelCount+m label)=((k+(wordIndex L x).val*4^L+(Butterfly.labelIndex L j).val:ℕ):ℤ) := by
    simp [rb,eq,c.width,c.lab,add_assoc]
  refine ⟨⟨rh,⟨⟨sa,by change Layout.floor < labelCount; decide⟩,by change Layout.floor < label; decide⟩⟩,?_,?_⟩
  · change Layout.floor < m r+(a.val m*m labelCount+m label)
    rw [num]; unfold Layout.floor; omega
  · change Fits W (m r+(a.val m*m labelCount+m label)); rw [num]; exact fit

private theorem src_bounds {L W : ℕ} {j : BasisLabel L} {f u v w base sig pr dst m}
    (c : Context j f u v w base sig pr dst m) (g : Group)
    (fit : ∀ x : Bits L, Fits W ((pr+(wordIndex L x).val*4^L+(Butterfly.labelIndex L j).val:ℕ):ℤ)) :
    ∀ q, (coords g q).safe Layout.floor W m := by
  have ra := lookup_safe c partnerBase pr (by decide) c.bPart row u (by change Layout.floor < -5; decide) c.row_eq (fit u)
  have ca := lookup_safe c partnerBase pr (by decide) c.bPart col v (by change Layout.floor < -6; decide) c.col_eq (fit v)
  intro q
  cases q with
  | pivot b => cases b <;> cases g <;> simp [coords,idx,row,col,Layout.floor,Expr.safe] <;> first | exact ra | exact ca
  | center => cases g <;> simp [coords,row,Layout.floor,Expr.safe]
  | other i => cases g <;> fin_cases i <;> simp [coords,col,remote0,remote1,Layout.floor,Expr.safe]

noncomputable def valueAt {L} (rev : Bool) (h : Fin 3) (j : BasisLabel L) (f : PairBits L)
    (w : ChannelKey L → ℚ) (u v : Bits L) : Group → ℤ
  | .pivotCenter => lookupA rev h j w u v
  | .pivotOther => lookupB rev h j f w u v
  | .centerOther => outsideInt rev h f w u v

/-- Each input array of the small product is tabulated by one fixed write
program. Array pointers and vertex/label words are runtime parameters. -/
theorem cell_runs {L W : ℕ} {j : BasisLabel L} {f u v w base sig pr dst m}
    (c : Context j f u v w base sig pr dst m) (π : Equiv.Perm V) (E : Finset EdgeSlot)
    (rev : Bool) (h : Fin 3) (g : Group)
    (hw : ∀ i, Binary (literal w (inputKey π E i)))
    (fitW : ∀ i : WeightKey (2^L), Fits W ((base+keyIndex i:ℕ):ℤ))
    (fitP : ∀ x : Bits L, Fits W ((pr+(wordIndex L x).val*4^L+(Butterfly.labelIndex L j).val:ℕ):ℤ))
    (fitS : Fits W ((sig+(wordIndex L v).val*4^L+(Butterfly.labelIndex L j).val:ℕ):ℤ))
    (fitD : Fits W ((dst+(wordIndex L u).val*2^L+(wordIndex L v).val:ℕ):ℤ)) :
    ∃ o, Runs W (cell π E rev h g) m (arrayPosition.steps+((entryValue π E rev h g).steps+1)) o ∧
      ∀ z, Layout.floor < z → o z = if z=((dst+(wordIndex L u).val*2^L+(wordIndex L v).val:ℕ):ℤ)
        then valueAt rev h j f (fun i => literal w (inputKey π E i)) u v g else m z := by
  let a := component (coords g) π E rev h g
  have ha := component_safe (lookup_val c g) (by decide : Layout.floor < -67) (src_bounds c g fitP) fitW π E rev h g
  have hv : a.val m=pieceInt rev h g (point g j f u v) (fun i => literal w (inputKey π E i)) := by
    apply (Int.cast_injective (α:=ℚ))
    rw [pieceInt_cast _ _ _ _ _ hw]
    exact component_val (lookup_val c g) π E rev h g
  have qs := lookup_safe c signBase sig (by decide) c.bSig col v (by change Layout.floor < -6; decide) c.col_eq fitS
  have vs : (supportEntry signBase col).val m = basisInt j (v,partner j v) := by
    simpa [supportEntry,Expr.val,col,c.bSig,c.col_eq,c.width,c.lab,Nat.cast_add,Nat.cast_mul,add_assoc] using c.signs v
  have pos : arrayPosition.val m = ((dst+(wordIndex L u).val*2^L+(wordIndex L v).val:ℕ):ℤ) := by
    simp [arrayPosition,Expr.val,row,col,c.bDst,c.n,c.row_eq,c.col_eq,add_assoc]
  have vx : (entryValue π E rev h g).val m = valueAt rev h j f (fun i => literal w (inputKey π E i)) u v g := by
    cases g with
    | pivotCenter => exact congrArg₂ (·*·) vs hv
    | pivotOther => exact hv
    | centerOther => exact hv
  have sx : (entryValue π E rev h g).safe Layout.floor W m := by
    unfold entryValue
    split <;> first | exact ⟨qs,ha⟩ | exact ha
  obtain ⟨o,act,post⟩ := write_run m Layout.floor arrayPosition _ (by simp [arrayPosition,Expr.safe,row,col,dest,sideReg,Layout.floor]) sx (pos ▸ fitD)
  exact ⟨o,act,fun z hz => by simpa only [pos,vx] using post z hz⟩

end VWZClique.IntegerRAM.Projected.Slices.Fill
end

/- NativeProjectionRaster -/
section
namespace VWZClique.IntegerRAM.Projected.Raster
open Structured

def privateReg (z : ℤ) := z=row ∨ z=col ∨ z=unit ∨ z=rowFlag ∨ z=colFlag
def saved (m x : Memory) := ∀ z, floor<z → z<0 → ¬privateReg z → x z=m z

def buffer (b : ℕ) (val : ℕ → ℤ) (m : Memory) (j : ℕ) (x : Memory) := ∀ z : ℕ,
  x z=if b≤z ∧ z<b+j then val (z-b) else m z

private theorem written {b k : ℕ} {val : ℕ → ℤ} {m x y : Memory} (buf : buffer b val m k x)
    (atWord : ∀ z : ℕ, y z=if z=b+k then val k else x z) : buffer b val m (k+1) y := by
  intro z
  rw [atWord z,buf z]
  by_cases e : z=b+k
  · subst z; simp
  · by_cases old : b≤z ∧ z<b+k <;> simp_all <;> omega

private theorem transfer {b j : ℕ} {val : ℕ → ℤ} {m x y : Memory} (buf : buffer b val m j x)
    (fr : ∀ z : ℕ, y z=x z) : buffer b val m j y := fun z => (fr z).trans (buf z)

private theorem tick_word {x : Memory} {i t : ℤ} (hi : i<0) (ht : t<0) (q n z : ℕ) :
    nextMemory x i t q n z=x z := by
  simp only [nextMemory,update,if_neg (by omega : (z:ℤ) ≠ t),if_neg (by omega : (z:ℤ) ≠ i)]

private theorem tick_saved {m x : Memory} {i t : ℤ} (pi : privateReg i) (pt : privateReg t)
    (sx : saved m x) (q n : ℕ) : saved m (nextMemory x i t q n) := by
  intro z h1 h2 hp
  have ai : z≠i := fun h => hp (h ▸ pi)
  have at' : z≠t := fun h => hp (h ▸ pt)
  simp only [nextMemory,update,if_neg ai,if_neg at',sx _ h1 h2 hp]

private theorem set_saved {m x : Memory} {r : ℤ} (pr : privateReg r) (sx : saved m x) (v : ℤ) :
    saved m (update x r v) := by
  intro z h1 h2 hp
  have ne : z≠r := fun h => hp (h ▸ pr)
  rw [update,if_neg ne,sx z h1 h2 hp]

/-- A fixed two-loop raster writes an entire square array and preserves the
input prefix and all non-control parameter registers above the scratch floor.
The cell proof may assume all input words below the output base are intact. -/
theorem run_fills {W n b K : ℕ} (hn : 0<n) (m : Memory) (width : m lim=n)
    (fits : ∀ j≤n, Fits W ((j:ℤ)-n)) (body : Command) (val : ℕ → ℤ)
    (eval : ∀ r<n, ∀ c<n, ∀ x : Memory, saved m x → (∀ z : ℕ, z<b → x z=m z) →
      x row=r → x col=c →
      ∃ f≤K, ∃ y, Runs W body x f y ∧ ∀ z, floor<z →
        y z=if z=((b+(r*n+c):ℕ):ℤ) then val (r*n+c) else x z) :
    ∃ f≤2+n*(1+n*(K+3)+3), ∃ y, Runs W (run body) m f y ∧ buffer b val m (n*n) y ∧ saved m y := by
  let I := fun (r : ℕ) (x : Memory) => x row=r ∧ x unit=1 ∧ saved m x ∧ buffer b val m (r*n) x
  let u := update m unit 1
  let s := update u row (u row-u row)
  have init : I 0 s := by
    refine ⟨by simp [s,update],by simp [s,u,update,unit,row],?_,?_⟩
    · exact set_saved (by unfold privateReg; decide : privateReg row) (set_saved (by unfold privateReg; decide : privateReg unit) (fun _ _ _ _ => rfl) _) _
    · intro z; simp (disch := omega) [s,u,update,unit,row] <;> omega
  have outer (r : ℕ) (hr : r<n) (x : Memory) (inv : I r x) :
      ∃ f, f≤1+n*(K+3) ∧ ∃ y, Runs W (scanRow body) x f y ∧ y row=r ∧ y unit=1 ∧
        y lim=n ∧ I (r+1) (nextMemory y row rowFlag r n) := by
    obtain ⟨rx,one,sx,bx⟩ := inv
    let J := fun (c : ℕ) (a : Memory) => a row=r ∧ a col=c ∧ a unit=1 ∧ saved m a ∧ buffer b val m (r*n+c) a
    let start := update x col (x col-x col)
    have cj : J 0 start := by
      refine ⟨by simpa [start,update,row,col] using rx,by simp [start,update],
        by simpa [start,update,unit,col] using one,set_saved (by unfold privateReg; decide : privateReg col) sx _,?_⟩
      simpa only [Nat.add_zero] using transfer bx (y:=start) (fun z => by simp (disch := omega) [start,update,col])
    have step (c : ℕ) (hc : c<n) (a : Memory) (hj : J c a) :
        ∃ f≤K, ∃ y, Runs W body a f y ∧ y col=c ∧ y unit=1 ∧ y lim=n ∧ J (c+1) (nextMemory y col colFlag c n) := by
      obtain ⟨ar,ac,au,sm,bm⟩ := hj
      obtain ⟨f,hf,y,act,post⟩ := eval r hr c hc a sm (fun z hz => by simpa [buffer,show ¬b≤z by omega] using bm z) ar ac
      have fr (z : ℤ) (lo : floor<z) (hi : z<0) : y z=a z := by rw [post z lo,if_neg (by omega)]
      have sy : saved m y := fun z h₁ h₂ hn => (fr z h₁ h₂).trans (sm z h₁ h₂ hn)
      have by' := written bm (y:=y) (fun z => by simpa only [Int.natCast_inj] using post (z:ℤ) (by dsimp [floor]; omega))
      have uy := (fr unit (by decide) (by decide)).trans au
      have ry := (fr row (by decide) (by decide)).trans ar
      refine ⟨f,hf,y,act,(fr col (by decide) (by decide)).trans ac,uy,
        (sy lim (by decide) (by decide) (by unfold privateReg; decide)).trans width,?_,?_,?_,?_,?_⟩
      · simpa [nextMemory,update,row,col,colFlag] using ry
      · simp [nextMemory,update,col,colFlag]
      · simpa [nextMemory,update,unit,col,colFlag] using uy
      · exact tick_saved (by unfold privateReg; decide) (by unfold privateReg; decide) sy _ _
      · exact transfer by' (tick_word (by decide) (by decide) _ _)
    obtain ⟨f,hf,y,act,yr,_,yu,sy,by'⟩ := repeatN_runs (B:=K) hn body (by decide) J fits step cj
    refine ⟨1+f,by omega,y,.seq (.atom (.sub x col col col)) act,yr,yu,
      (sy lim (by decide) (by decide) (by unfold privateReg; decide)).trans width,?_,?_,?_,?_⟩
    · simp [nextMemory,update,row,rowFlag]
    · simpa [nextMemory,update,unit,row,rowFlag] using yu
    · exact tick_saved (by unfold privateReg; decide) (by unfold privateReg; decide) sy _ _
    · simpa only [Nat.succ_mul] using transfer by' (tick_word (by decide) (by decide) _ _)
  obtain ⟨f,hf,y,act,_,_,sy,buff⟩ := repeatN_runs (B:=1+n*(K+3)) hn (scanRow body) (by decide) I fits outer init
  exact ⟨1+(1+f),by omega,y,.seq (.atom (.one m unit)) (.seq (.atom (.sub u row row row)) act),buff,sy⟩

end VWZClique.IntegerRAM.Projected.Raster
end

/- NativeProjectionSheet -/
section
namespace VWZClique.IntegerRAM.Projected.Slices.Fill
open Structured Projection WeightedProof UniformFolds TraceDyadic Factors

private theorem retain {L : ℕ} {j : BasisLabel L} {f w base sig pr dst m x}
    (s : Sheet j f w base sig pr dst m) (sm : Raster.saved m x) (kept : ∀ z : ℕ, z < dst → x z=m z)
    (wts : ∀ k : WeightKey (2^L), base+keyIndex k < dst)
    (sg : ∀ y : Bits L, sig+(wordIndex L y).val*4^L+(Butterfly.labelIndex L j).val < dst)
    (pt : ∀ y : Bits L, pr+(wordIndex L y).val*4^L+(Butterfly.labelIndex L j).val < dst) :
    Sheet j f w base sig pr dst x := by
  have reg (z : ℤ) (lo : -128 < z) (hi : z < -9) : x z=m z :=
    sm z lo (by omega) (by unfold Raster.privateReg; dsimp [Raster.row,Raster.col,Raster.unit,Raster.rowFlag,Raster.colFlag]; omega)
  refine ⟨(reg _ (by decide) (by decide)).trans s.n,(reg _ (by decide) (by decide)).trans s.base_eq,
    (reg _ (by decide) (by decide)).trans s.f0,(reg _ (by decide) (by decide)).trans s.f1,
    (reg _ (by decide) (by decide)).trans s.bSig,(reg _ (by decide) (by decide)).trans s.bPart,
    (reg _ (by decide) (by decide)).trans s.bDst,(reg _ (by decide) (by decide)).trans s.lab,
    (reg _ (by decide) (by decide)).trans s.width,?_,?_,?_⟩
  · intro k; rw [kept _ (wts k),s.weights]
  · intro y; exact (kept _ (sg y)).trans (s.signs y)
  · intro y; exact (kept _ (pt y)).trans (s.partners y)

private def phaseWord {L : ℕ} (v : Bits L → Bits L → ℤ) (i : ℕ) : ℤ :=
  if hi : i < 2^L*2^L then
    let p : Fin (2^L) × Fin (2^L) := finProdFinEquiv.symm ⟨i,hi⟩
    v ((wordIndex L).symm p.1) ((wordIndex L).symm p.2)
  else 0

private theorem phase_at {L : ℕ} (a : Bits L → Bits L → ℤ) (r c : Fin (2^L)) :
    phaseWord a (r.val*2^L+c.val)=a ((wordIndex L).symm r) ((wordIndex L).symm c) := by
  have hv : (finProdFinEquiv (r,c)).val=r.val*2^L+c.val := by
    change c.val+2^L*r.val=r.val*2^L+c.val; ring
  rw [←hv]
  unfold phaseWord
  rw [dif_pos (finProdFinEquiv (r,c)).isLt]
  change a ((wordIndex L).symm (finProdFinEquiv.symm (finProdFinEquiv (r,c))).1)
    ((wordIndex L).symm (finProdFinEquiv.symm (finProdFinEquiv (r,c))).2)=_
  rw [Equiv.symm_apply_apply]

/-- Materialize one complete row-major small-square input. Every grouped
weight and every support entry is read from the original contiguous heap. -/
theorem sheet_runs {L W : ℕ} {j : BasisLabel L} {f w base sig pr dst m}
    (s : Sheet j f w base sig pr dst m) (π : Equiv.Perm V) (E : Finset EdgeSlot)
    (rev : Bool) (h : Fin 3) (g : Group)
    (hw : ∀ i, Binary (literal w (inputKey π E i)))
    (width : m Raster.lim=(2^L:ℕ)) (guards : ∀ a : ℕ, a ≤ 2^L → Fits W ((a:ℤ)-(2^L:ℕ)))
    (wts : ∀ k : WeightKey (2^L), base+keyIndex k < dst ∧ Fits W ((base+keyIndex k:ℕ):ℤ))
    (sg : ∀ x : Bits L, sig+(wordIndex L x).val*4^L+(Butterfly.labelIndex L j).val < dst ∧
      Fits W ((sig+(wordIndex L x).val*4^L+(Butterfly.labelIndex L j).val:ℕ):ℤ))
    (pt : ∀ x : Bits L, pr+(wordIndex L x).val*4^L+(Butterfly.labelIndex L j).val < dst ∧
      Fits W ((pr+(wordIndex L x).val*4^L+(Butterfly.labelIndex L j).val:ℕ):ℤ))
    (destFits : ∀ u v : Fin (2^L), Fits W ((dst+u.val*2^L+v.val:ℕ):ℤ)) :
    let K := arrayPosition.steps+((entryValue π E rev h g).steps+1)
    ∃ T ≤ 2+2^L*(1+2^L*(K+3)+3), ∃ out, Runs W (Raster.run (cell π E rev h g)) m T out ∧
      (∀ u v : Bits L, out ((dst+(wordIndex L u).val*2^L+(wordIndex L v).val:ℕ):ℤ) =
        valueAt rev h j f (fun i => literal w (inputKey π E i)) u v g) ∧
      ∀ z : ℕ, z < dst ∨ dst+2^L*2^L ≤ z → out z=m z := by
  dsimp only
  let a := fun u v => valueAt rev h j f (fun i => literal w (inputKey π E i)) u v g
  have advance := Raster.run_fills (b:=dst) (K:=arrayPosition.steps+((entryValue π E rev h g).steps+1))
    (show 0 < (2:ℕ)^L by positivity) m width guards (cell π E rev h g) (phaseWord a)
  obtain ⟨t,ht,o,run,buf,_⟩ := advance (by
    intro r hr c hc x save before row column
    let i : Fin (2^L) := ⟨r,hr⟩
    let k : Fin (2^L) := ⟨c,hc⟩
    let u := (wordIndex L).symm i
    let v := (wordIndex L).symm k
    have e : Context j f u v w base sig pr dst x :=
      ⟨retain s save before (fun p => (wts p).1) (fun p => (sg p).1) (fun p => (pt p).1),
        by simpa [u,i] using row,by simpa [v,k] using column⟩
    have runCell := cell_runs e π E rev h g hw (fun p => (wts p).2) (fun p => (pt p).2) (sg v).2
      (by simpa [u,v] using destFits i k)
    obtain ⟨o,run,post⟩ := runCell
    exact ⟨_,le_rfl,o,run,fun z hz => by simpa [u,v,i,k,a,phase_at a i k,Nat.add_assoc] using post z hz⟩)
  refine ⟨t,ht,o,run,?_,?_⟩
  · intro u v
    let r := wordIndex L u
    let c := wordIndex L v
    have lt : r.val*2^L+c.val < 2^L*2^L := by
      have h := Nat.mul_le_mul_right (2^L) r.isLt
      rw [Nat.succ_mul] at h
      have := c.isLt; omega
    have eq := buf (dst+r.val*2^L+c.val)
    simp only [if_pos (by omega : dst ≤ dst+r.val*2^L+c.val ∧ dst+r.val*2^L+c.val < dst+2^L*2^L),
      show dst+r.val*2^L+c.val-dst = r.val*2^L+c.val by omega,phase_at] at eq
    simpa [a,r,c] using eq
  · intro z hz; simpa only [if_neg (by omega : ¬(dst ≤ z ∧ z < dst+2^L*2^L))] using buf z

end VWZClique.IntegerRAM.Projected.Slices.Fill
end

/- NativeProjectionLoop -/
section
namespace VWZClique.IntegerRAM.Projected
open Structured WordDot

namespace Cell
end Cell

theorem Tables.transfer {m out : Memory} {s t} {l : Layout} {a : Tile s} {b c : Fin t → Tile s}
    (ht : Tables m l a b c) (h : ∀ z : ℕ, out z=m z) : Tables out l a b c :=
  ⟨fun i => (h _).trans (ht.weights i),fun p i => (h _).trans (ht.left p i),
    fun p i => (h _).trans (ht.right p i)⟩

end VWZClique.IntegerRAM.Projected
end

/- NativeProjectionHadamard -/
section
namespace VWZClique.IntegerRAM.Projected.Pointwise
open Structured Butterfly

structure Ready (p q n j : ℕ) (m : Memory) : Prop where
  source : m src=(p+j:ℕ)
  dest : m dst=(q+j:ℕ)
  one : m unit=1
  count : m index=j
  lim : m limit=n

set_option maxHeartbeats 1000000 in
private theorem one_run {W p q n i : ℕ} {m : Memory} (h : Ready p q n i m)
    (sFit : Fits W ((p+i:ℕ):ℤ)) (dFit : Fits W ((q+i:ℕ):ℤ)) :
    ∃ out, Runs W (line ops) m 6 out ∧ out index=i ∧ out unit=1 ∧ out limit=n ∧
      Ready p q n (i+1) (nextMemory out index guard i n) ∧
      ∀ k : ℕ, nextMemory out index guard i n k =
        if k=q+i then m ((p+i:ℕ):ℤ)*m ((q+i:ℕ):ℤ) else m k := by
  let p₀ : ℤ := (p+i:ℕ)
  let q₀ : ℤ := (q+i:ℕ)
  have hp : 0 ≤ p₀ := Int.natCast_nonneg _
  have hq : 0 ≤ q₀ := Int.natCast_nonneg _
  obtain ⟨sp,dp,ho,hi,hn⟩ := h
  change m src=p₀ at sp
  change m dst=q₀ at dp
  let o := ops.foldl effect m
  have run : Runs W (line ops) m 6 o := by
    apply line_runs
    simp (disch := omega) [ops,safeLine,safe,effect,update,sp,dp,p₀,q₀,sFit,dFit,
      src,dst,factor,value,unit] at *
    exact ⟨sFit,dFit⟩
  have hh (z : ℤ) (hz : z < 0) : z≠q₀ := by omega
  have hs : o src=p₀+1 ∧ o dst=q₀+1 ∧ o unit=1 ∧ o index=i ∧ o limit=n := by
    dsimp only [src,dst,unit,index,limit] at sp dp ho hi hn
    simp (disch := omega) [o,ops,effect,update,src,dst,value,factor,unit,index,limit,sp,dp,ho,hi,hn]
  obtain ⟨s,d,ho',hi',hn'⟩ := hs
  refine ⟨o,run,hi',ho',hn',?_,?_⟩
  · constructor <;> simp [nextMemory,update,src,dst,unit,index,limit,guard,p₀,q₀,Nat.cast_add] at * <;> omega
  · intro k
    let raw := update (update (update m factor (m p₀)) value (m q₀)) value (m p₀*m q₀)
    let put := update raw q₀ (m p₀*m q₀)
    have rd : q₀≠factor := by dsimp [factor]; omega
    have head : List.foldl effect m [.load factor src,.load value dst,.mul value factor value] = raw := by
      simp [raw,effect,update,sp,dp,rd,factor,value,dst] at *
    have last : o=update (update put src (p₀+1)) dst (q₀+1) := by
      change (List.foldl effect (List.foldl effect m [.load factor src,.load value dst,.mul value factor value])
        [.store dst value,.add src src unit,.add dst dst unit])=_
      rw [head]
      dsimp only [src,dst,unit,factor,value] at sp dp ho rd ⊢
      simp (disch := omega) [put,raw,effect,update,sp,dp,ho]
    have data : raw k=m k := by simp (disch := omega) [raw,update,factor,value]
    change _ = if k=q+i then m p₀*m q₀ else m k
    rw [last]
    simp only [nextMemory,update,if_neg (by dsimp [guard]; omega : (k:ℤ)≠guard),
      if_neg (by dsimp [index]; omega : (k:ℤ)≠index),if_neg (by dsimp [dst]; omega : (k:ℤ)≠dst),
      if_neg (by dsimp [src]; omega : (k:ℤ)≠src)]
    change (if (k:ℤ)=((q+i:ℕ):ℤ) then _ else raw k)=_
    simp only [Int.natCast_inj,data]

theorem run {W p q n : ℕ} (m : Memory) (ready : Ready p q n 0 m) (hn : 0 < n)
    (separate : p+n ≤ q ∨ q+n ≤ p)
    (guardFit : ∀ i ≤ n, Fits W ((i:ℤ)-n))
    (bounds : ∀ i < n, Fits W ((p+i:ℕ):ℤ) ∧ Fits W ((q+i:ℕ):ℤ)) :
    ∃ f, f ≤ 9*n ∧ ∃ out, Runs W kernel m f out ∧
      (∀ i < n, out ((q+i:ℕ):ℤ)=m ((p+i:ℕ):ℤ)*m ((q+i:ℕ):ℤ)) ∧
      ∀ k : ℕ, k < q ∨ q+n ≤ k → out k=m k := by
  let inv := fun i (x : Memory) => Ready p q n i x ∧
    (∀ j < i, x ((q+j:ℕ):ℤ)=m ((p+j:ℕ):ℤ)*m ((q+j:ℕ):ℤ)) ∧
    ∀ k : ℕ, k < q ∨ q+i ≤ k → x k=m k
  have init : inv 0 m := ⟨ready,by omega,fun _ _ => rfl⟩
  have step (i : ℕ) (hi : i < n) (x : Memory) (hx : inv i x) :
      ∃ f : ℕ, f ≤ 6 ∧ ∃ v, Runs W (line ops) x f v ∧ v index=i ∧ v unit=1 ∧
        v limit=n ∧ inv (i+1) (nextMemory v index guard i n) := by
    obtain ⟨r,done,fr⟩ := hx
    obtain ⟨o,act,idx,one,lim,reg,post⟩ := one_run r (bounds i hi).1 (bounds i hi).2
    refine ⟨6,le_rfl,o,act,idx,one,lim,reg,?_,?_⟩
    · intro j hj
      rw [post]
      by_cases old : j < i
      · rw [if_neg (by omega)]; exact done j old
      · have e : j=i := by omega
        subst j
        rw [if_pos rfl,fr (p+i) (by omega),fr (q+i) (by omega)]
    · intro k hk
      rw [post,if_neg (by omega)]
      exact fr k (by omega)
  obtain ⟨f,hf,o,act,_,ans,frame⟩ := repeatN_runs (B:=6) hn _ (by decide) inv guardFit step init
  exact ⟨f,by omega,o,act,ans,frame⟩

end VWZClique.IntegerRAM.Projected.Pointwise
end

/- NativeProjectionSliceWord -/
section
namespace VWZClique.IntegerRAM.Projected.Slices
open Structured Projection UniformFolds

/-- Index the two short axes by the exact word numbering of the grouped tables. -/
def pack {L : ℕ} (A : Matrix (Bits L) (Bits L) ℤ) : Tile (2^L) :=
  fun i j => A ((wordIndex L).symm i) ((wordIndex L).symm j)

theorem pack_mul {L : ℕ} (A B : Matrix (Bits L) (Bits L) ℤ) : pack (A*B)=pack A * pack B := by
  funext i j
  change (∑ x, A ((wordIndex L).symm i) x * B x ((wordIndex L).symm j)) =
    ∑ y, A ((wordIndex L).symm i) ((wordIndex L).symm y) * B ((wordIndex L).symm y) ((wordIndex L).symm j)
  exact (Fintype.sum_equiv (wordIndex L).symm _ _ (fun _ => rfl)).symm

/-- Starting with the small-square output in memory and the outside factor,
one fixed loop materializes all projected entries of the current slice. -/
theorem scale_slice {L W : ℕ} (rev : Bool) (h : Fin 3) (j : BasisLabel L) (f : PairBits L)
    (w : ChannelKey L → ℚ) (hw : ∀ i, Binary (w i))
    (P : ℤ) (p q : ℕ) (m : Memory)
    (wts : bank m p (pack (outsideInt rev h f w)))
    (prod : bank m q (scaleMat P (pack (lookupA rev h j w) * pack (lookupB rev h j f w))))
    (ctl : Pointwise.Ready p q ((2^L)*(2^L)) 0 m)
    (apart : p+2^L*2^L ≤ q ∨ q+2^L*2^L ≤ p)
    (guard : ∀ (i : ℕ) (_ : i ≤ 2^L*2^L), Fits W ((i:ℤ)-((2^L*2^L:ℕ):ℤ)))
    (fit : ∀ i < 2^L*2^L, Fits W ((p+i:ℕ):ℤ) ∧ Fits W ((q+i:ℕ):ℤ)) :
    ∃ t, t ≤ 9*(2^L*2^L) ∧ ∃ out, Runs W Pointwise.kernel m t out ∧
      bank out q (scaleMat P (pack (fun z v => singleInt rev h j z (block f v) w))) ∧
      ∀ k : ℕ, k < q ∨ q+2^L*2^L ≤ k → out k = m k := by
  have hn : 0 < (2:ℕ)^L*2^L := by positivity
  obtain ⟨t,time,out,run,buf,fr⟩ := Pointwise.run m ctl hn apart guard fit
  refine ⟨t,time,out,run,?_,fr⟩
  intro i
  rw [buf i.val i.isLt,wts i,prod i,← pack_mul,lookup_product]
  dsimp only [flat,pack,scaleMat]
  rw [←slice_exact rev h j f w hw]
  ring

end VWZClique.IntegerRAM.Projected.Slices
end

/- NativeProjectionSetup -/
section
namespace VWZClique.IntegerRAM.Projected.Setup
open Structured SquareCode SquareCode.Layout

@[simp] theorem readWord_val (m : Memory) (i : ℕ) : (readWord i).val m=m (i:ℤ) := by simp [readWord,Expr.val]
@[simp] theorem readWord_safe (m : Memory) (W i : ℕ) : (readWord i).safe floor W m ↔ Fits W (i:ℤ) := by
  simp [readWord,Expr.safe,Expr.val,floor] <;> omega

end VWZClique.IntegerRAM.Projected.Setup
end

/- NativeProjectionHeaders -/
section
namespace VWZClique.IntegerRAM.Projected.Headers
open Structured SquareCode SquareCode.Layout

def Value.eval (m : Memory) : Value → ℤ
  | .nat v => v
  | .word k => m k
  | .add a b => a.eval m+b.eval m
  | .mul a b => a.eval m*b.eval m

def Value.high : Value → ℕ
  | .nat _ => 0
  | .word k => k
  | .add a b | .mul a b => max a.high b.high

theorem Value.value {m x : Memory} (a : Value) (h : ∀ i : ℕ, x i=m i) : a.expr.val x=a.eval m := by
  induction a <;> simp_all [expr,eval,Expr.val]

theorem Value.safe {W : ℕ} (a : Value) (x : Memory) (fit : ∀ i ≤ a.high, Fits W (i:ℤ)) : a.expr.safe floor W x := by
  induction a with
  | nat i => exact Expr.num_safe ..
  | word i => exact (Setup.readWord_safe x W i).2 (fit i le_rfl)
  | add a b ia ib | mul a b ia ib => exact ⟨ia (fun i hi => fit i (le_max_of_le_left hi)),ib (fun i hi => fit i (le_max_of_le_right hi))⟩

def stored (m : Memory) (z : ℤ) : Fields → ℤ
  | [] => m z
  | a::xs => if z=a.1 then a.2.eval m else stored m z xs

def room (W k : ℕ) := ∀ i ≤ k, Fits W (i:ℤ)
def admissible (k : ℕ) (xs : Fields) := ∀ a∈xs, floor < a.1 ∧ a.1 < 0 ∧ a.2.high ≤ k

theorem run {W max : ℕ} (xs : Fields) (m : Memory) (ok : admissible max xs) (fit : room W max) :
    ∃ out, Runs W (command xs) m (time xs) out ∧
      (∀ z, floor < z → out z=stored m z xs) ∧ ∀ i : ℕ, out i=m i := by
  induction xs with
  | nil => exact ⟨m,.skip _,fun _ _ => rfl,fun _ => rfl⟩
  | cons a xs ih =>
    obtain ⟨lo,hi,hc⟩ := ok a (by simp)
    obtain ⟨x,first,fr,keep⟩ := ih (fun k hk => ok k (by simp [hk]))
    obtain ⟨o,last,result⟩ := assign_run x lo a.2.expr (a.2.safe x (fun i h => fit i (h.trans hc)))
    refine ⟨o,.seq first last,?_,?_⟩
    · intro z h
      rw [result _ h,stored,a.2.value keep,fr _ h]
    · intro i; exact (result i (by unfold floor; omega)).trans ((if_neg (by omega)).trans (keep i))

end VWZClique.IntegerRAM.Projected.Headers
end

/- NativeProjectionSmall -/
section
namespace VWZClique.IntegerRAM.Projected.Small
open Structured Projection WeightedProof UniformFolds TraceDyadic Slices Slices.Fill SquareCode

private def dst (w n : ℕ) (g : Group) := w+plane g*(n*n)

def frame (work : ℕ) (m x : Memory) := ∀ z : ℕ, z < work → x z=m z

structure Data {L : ℕ} (j : BasisLabel L) (f : PairBits L) (w : WeightKey (2^L) → ℚ)
    (base sig pr work : ℕ) (m : Memory) : Prop where
  above : 356 < work
  n : m 0=(2^L:ℕ)
  baseH : m weightsH=base
  sigH : m signsH=sig
  prH : m partsH=pr
  labelH' : m labelH=(Butterfly.labelIndex L j).val
  f0 : m f0H=(wordIndex L f.1).val
  f1 : m f1H=(wordIndex L f.2).val
  dest : m workH=work
  weights : ∀ k, base+Factors.keyIndex k < work ∧ (m ((base+Factors.keyIndex k:ℕ):ℤ):ℚ)=w k
  signs : ∀ x, let q := sig+(wordIndex L x).val*4^L+(Butterfly.labelIndex L j).val
    q < work ∧ m (q:ℤ)=basisInt j (x,partner j x)
  partners : ∀ x, let q := pr+(wordIndex L x).val*4^L+(Butterfly.labelIndex L j).val
    q < work ∧ m (q:ℤ)=(wordIndex L (lookupPartner j x)).val

theorem Data.kept {L : ℕ} {j : BasisLabel L} {f w base sig pr work m x}
    (g : Data j f w base sig pr work m) (k : frame work m x) : Data j f w base sig pr work x := by
  have h := g.above
  refine ⟨h,(k 0 (by omega)).trans g.n,(k weightsH (by dsimp [weightsH]; omega)).trans g.baseH,
    (k signsH (by dsimp [signsH]; omega)).trans g.sigH,(k partsH (by dsimp [partsH]; omega)).trans g.prH,
    (k labelH (by dsimp [labelH]; omega)).trans g.labelH',(k f0H (by dsimp [f0H]; omega)).trans g.f0,
    (k f1H (by dsimp [f1H]; omega)).trans g.f1,(k workH h).trans g.dest,?_,?_,?_⟩
  · intro i; exact ⟨(g.weights i).1,by rw [k _ (g.weights i).1,(g.weights i).2]⟩
  · intro y; exact ⟨(g.signs y).1,(k _ (g.signs y).1).trans (g.signs y).2⟩
  · intro y; exact ⟨(g.partners y).1,(k _ (g.partners y).1).trans (g.partners y).2⟩

private theorem bank_of_rows {L : ℕ} (p : ℕ) (m : Memory) (A : Bits L → Bits L → ℤ)
    (each : ∀ u v, m ((p+(wordIndex L u).val*2^L+(wordIndex L v).val:ℕ):ℤ)=A u v) : bank m p (pack A) := by
  intro i
  obtain ⟨⟨r,c⟩,rfl⟩ := finProdFinEquiv.surjective i
  have h := each ((wordIndex L).symm r) ((wordIndex L).symm c)
  have pos : (finProdFinEquiv (r,c)).val=r.val*2^L+c.val := by change c.val+2^L*r.val=_; ring
  simpa [flat,pack,pos,Nat.add_assoc] using h

theorem sheet_run {L W M : ℕ} {j : BasisLabel L} {f w base sig pr work m}
    (data : Data j f w base sig pr work m) (π : Equiv.Perm V) (E : Finset EdgeSlot) (rev : Bool) (h : Fin 3) (g : Group)
    (hw : ∀ i, Binary (literal w (inputKey π E i))) (cap : Graph.Division.Room W M)
    (space : work+4*(2^L*2^L) ≤ M) :
    ∃ t ≤ sheetTime π E rev h g (2^L), ∃ o, Runs W (sheet π E rev h g) m t o ∧
      bank o (dst work (2^L) g) (pack (fun u v => valueAt rev h j f (fun i => literal w (inputKey π E i)) u v g)) ∧
      ∀ z : ℕ, z < dst work (2^L) g ∨ dst work (2^L) g+2^L*2^L ≤ z → o z=m z := by
  have top := data.above
  have valid : Headers.admissible 356 (sheetFields g) := by
    cases g <;> simp [Headers.admissible,sheetFields,area,dim,offset,plane,Headers.Value.high,SquareCode.Layout.floor,
      Factors.sideReg,Factors.baseReg,Fill.signBase,Fill.partnerBase,Fill.label,Fill.remote0,Fill.remote1,Fill.dest,Fill.labelCount,Raster.lim] <;> decide
  obtain ⟨x,start,regs,keep⟩ := Headers.run (sheetFields g) m valid (fun i hi => by apply cap.fits <;> omega)
  have sz : 2^L*2^L=(4:ℕ)^L := by rw [←Nat.mul_pow]
  have bs : m 350=base := data.baseH
  have f₁ : m 354=(wordIndex L f.1).val := data.f0
  have f₂ : m 355=(wordIndex L f.2).val := data.f1
  have p₁ : m 351=sig := data.sigH
  have p₂ : m 352=pr := data.prH
  have id : m 353=(Butterfly.labelIndex L j).val := data.labelH'
  have dest0 : m 356=work := data.dest
  have szI : (2:ℤ)^L*2^L=4^L := by rw [←mul_pow];norm_num
  have prepared : Fill.Sheet j f w base sig pr (dst work (2^L) g) x := by
    constructor
    all_goals first | apply (regs _ (by decide)).trans | skip
    all_goals first | intro i; rw [keep]; exact (data.weights i).2 | intro i; exact (keep _).trans (data.signs i).2 | intro i; exact (keep _).trans (data.partners i).2 | skip
    all_goals simp [sheetFields,Headers.stored,Headers.Value.eval,dim,area,offset,dst,data.n,data.baseH,data.sigH,
      data.prH,data.labelH',data.f0,data.f1,data.dest,sz,szI,bs,f₁,f₂,p₁,p₂,id,dest0,Factors.sideReg,Factors.baseReg,Fill.signBase,
      Fill.partnerBase,Fill.label,Fill.remote0,Fill.remote1,Fill.dest,Fill.labelCount,Raster.lim]
  have width : x Raster.lim=(2^L:ℕ) := (regs _ (by decide)).trans (by simp [Headers.stored,sheetFields,dim,Headers.Value.eval,data.n])
  have bound (u v : Fin (2^L)) : dst work (2^L) g+u.val*2^L+v.val < M := by
    have hh := Nat.mul_le_mul_right (2^L) u.isLt
    rw [Nat.succ_mul] at hh
    have vv := v.isLt
    cases g <;> simp only [dst,plane,zero_mul,one_mul,Nat.add_zero] <;> omega
  have dstLo : work ≤ dst work (2^L) g := Nat.le_add_right ..
  have N : 1 ≤ (2:ℕ)^L := Nat.one_le_pow _ _ (by decide)
  have nM : 2^L ≤ M := by have := Nat.mul_le_mul_left (2^L) N; omega
  obtain ⟨t,time,o,r,values,fr⟩ := sheet_runs prepared π E rev h g hw width
    (fun i hi => by apply cap.fits <;> omega)
    (fun i => ⟨(data.weights i).1.trans_le dstLo,by apply cap.fits <;> have := (data.weights i).1 <;> omega⟩)
    (fun i => ⟨(data.signs i).1.trans_le dstLo,by apply cap.fits <;> have := (data.signs i).1 <;> omega⟩)
    (fun i => ⟨(data.partners i).1.trans_le dstLo,by apply cap.fits <;> have := (data.partners i).1 <;> omega⟩)
    (fun u v => by apply cap.fits <;> have := bound u v <;> omega)
  exact ⟨_,Nat.add_le_add_left time _,o,.seq start r,bank_of_rows _ _ _ values,
    fun z hz => (fr z hz).trans (keep z)⟩

def locations (start n : ℕ) : Layout :=
  ⟨start,start+n*n,start+3*(n*n),start+2*(n*n),start⟩

private theorem bank_prefix {n q : ℕ} {m x : Memory} {A : Tile n} (bankM : bank m q A)
    (keep : ∀ z<q+n*n, x (z:ℤ)=m z) : bank x q A :=
  fun i => (keep _ (by have := i.isLt; omega)).trans (bankM i)

/-- The complete native operation for one retained label, one pair of remote
vertices and one channel. This includes three full operand fills, one ordinary
square call, and the entrywise multiplication of the product by external weights. -/
theorem job_run {L W M K : ℕ} {j : BasisLabel L} {f w base sig pr work m}
    (data : Data j f w base sig pr work m) (π : Equiv.Perm V) (E : Finset EdgeSlot) (rev : Bool) (h : Fin 3)
    (hw : ∀ i, Binary (literal w (inputKey π E i))) (cap : Graph.Division.Room W M)
    (space : work+4*(2^L*2^L)≤M) (P : ℤ) (sq : Command) :
    let n := 2^L
    let l := locations work n
    let cw := fun i => literal w (inputKey π E i)
    SquareRun W K P sq l (pack (outsideInt rev h f cw))
      (fun _ : Fin 1 => pack (lookupA rev h j cw)) (fun _ : Fin 1 => pack (lookupB rev h j f cw)) →
    ∃ t≤jobTime π E rev h n K, ∃ o, Runs W (job sq π E rev h) m t o ∧
      bank o l.prod (scaleMat P (pack (fun z v => singleInt rev h j z (block f v) cw))) ∧ frame work m o := by
  dsimp only
  intro square
  let n := 2^L
  let cw := fun i => literal w (inputKey π E i)
  let l := locations work n
  have h0 := data.above
  have fit : Headers.room W 356 := fun i hi => by apply cap.fits <;> omega
  obtain ⟨a,atime,x,A,va,fa⟩ := sheet_run data π E rev h .pivotCenter hw cap space
  have va' : bank x work (pack (lookupA rev h j cw)) := by simpa [valueAt,dst,plane,cw] using va
  have fa' : frame work m x := fun z hz => fa z (Or.inl (by simpa [dst,plane] using hz))
  obtain ⟨b,btime,y,B,vb,fb⟩ := sheet_run (data.kept fa') π E rev h .pivotOther hw cap space
  change bank y (dst work n .pivotOther) (pack (lookupB rev h j f cw)) at vb
  have lowb : ∀ z<work+n*n, y (z:ℤ)=x z := fun z hz => fb z (Or.inl (by simpa [dst,plane] using hz))
  have fb' : frame work m y := fun z hz => (lowb z (by omega)).trans (fa' z hz)
  obtain ⟨c,ctime,z,C,vc,fc⟩ := sheet_run (data.kept fb') π E rev h .centerOther hw cap space
  have lowc : ∀ p<work+2*(n*n), z (p:ℤ)=y p := fun p hp => fc p (Or.inl hp)
  have fc' : frame work m z := fun p hp => (lowc p (by omega)).trans (fb' p hp)
  have ready : Tables z l (pack (outsideInt rev h f cw)) (fun _ : Fin 1 => pack (lookupA rev h j cw))
      (fun _ : Fin 1 => pack (lookupB rev h j f cw)) := by
    refine ⟨vc,?_,?_⟩
    · intro p; obtain rfl := Fin.eq_zero p
      simpa [l,locations] using bank_prefix (bank_prefix va' lowb) (fun v hv => lowc v (by change v<work+n*n at hv; omega))
    · intro p; obtain rfl := Fin.eq_zero p
      simpa [l,locations,dst,plane] using bank_prefix vb (fun v hv => lowc v (by change v<dst work n .pivotOther+n*n at hv; simp [dst,plane] at hv; omega))
  have sqOK : Headers.admissible 356 squareFields := by
    simp [Headers.admissible,squareFields,dim,area,offset,Headers.Value.high,workH,SquareCode.Layout.floor,Cell.lhs,Cell.rhs,Cell.prod,Cell.side]
  obtain ⟨q,load,regs,mem⟩ := Headers.run squareFields z sqOK fit
  have ctx := data.kept fc'
  have ctxDest : z 356=work := ctx.dest
  have lhs : q Cell.lhs=l.lhs ∧ q Cell.rhs=l.rhs ∧ q Cell.prod=l.prod ∧ q Cell.side=n := by
    refine ⟨(regs _ (by decide)).trans ?_,(regs _ (by decide)).trans ?_,(regs _ (by decide)).trans ?_,(regs _ (by decide)).trans ?_⟩
    all_goals simp [l,locations,n,Headers.stored,squareFields,dim,area,offset,Headers.Value.eval,ctx.n,ctx.dest,ctxDest,
      Cell.lhs,Cell.rhs,Cell.prod,Cell.side]
  obtain ⟨s,stime,k,multiply,prod,tables,_,pk⟩ := square 0 q (ready.transfer mem)
    (by simpa using lhs.1) (by simpa using lhs.2.1) lhs.2.2.1 lhs.2.2.2
  have keepK : frame work m k := fun v hv => (pk v hv).trans ((mem v).trans (fc' v hv))
  have dK := data.kept keepK
  have ptOK : Headers.admissible 356 pointFields := by
    simp [Headers.admissible,pointFields,dim,area,offset,Headers.Value.high,workH,SquareCode.Layout.floor,
      Pointwise.src,Pointwise.dst,Pointwise.unit,Pointwise.index,Pointwise.limit]
  obtain ⟨x',pload,regs',mx⟩ := Headers.run pointFields k ptOK fit
  have dKDest : k 356=work := dK.dest
  have ctl : Pointwise.Ready l.wt l.prod (n*n) 0 x' := by
    constructor <;> apply (regs' _ (by decide)).trans
    all_goals simp [l,locations,Headers.stored,pointFields,dim,area,offset,Headers.Value.eval,dK.n,dK.dest,dKDest,n,
      Pointwise.src,Pointwise.dst,Pointwise.unit,Pointwise.index,Pointwise.limit]
  have hN : 0<n := by dsimp [n]; positivity
  have hNN : n*n≤M := by change work+4*(n*n)≤M at space; omega
  obtain ⟨t,ptime,o,point,vals,fr⟩ := scale_slice rev h j f cw hw P l.wt l.prod x'
    (fun i => (mx _).trans (tables.weights i)) (fun i => (mx _).trans (prod i)) ctl
    (Or.inl (by change work+2*(n*n)+(n*n)≤work+3*(n*n);omega))
    (fun i hi => by
      change i≤n*n at hi
      change Fits W ((i:ℤ)-((n*n:ℕ):ℤ))
      have lim : ((n*n:ℕ):ℤ)≤(M:ℤ) := by exact_mod_cast hNN
      have good : (i:ℤ)≤((n*n:ℕ):ℤ) := by exact_mod_cast hi
      exact cap.fits (by linarith [Int.natCast_nonneg i]) (by linarith [Int.natCast_nonneg M]))
    (fun i hi => by
      change i<n*n at hi
      change work+4*(n*n)≤M at space
      have fit (j : ℕ) (hj : j≤M) : Fits W (j:ℤ) := cap.fits (by omega) (by exact_mod_cast hj)
      exact ⟨fit _ (by change work+2*(n*n)+i≤M;omega),fit _ (by change work+3*(n*n)+i≤M;omega)⟩)
  exact ⟨_,Nat.add_le_add atime (Nat.add_le_add btime (Nat.add_le_add ctime (Nat.add_le_add_left
    (Nat.add_le_add stime (Nat.add_le_add_left ptime _)) _))),o,
    .seq A (.seq B (.seq C (.seq load (.seq multiply (.seq pload point))))),vals,
    fun v hv => (fr v (Or.inl (by dsimp [l,locations]; omega))).trans ((mx v).trans (keepK v hv))⟩

end VWZClique.IntegerRAM.Projected.Small
end

/- NativeProjectionPairScan -/
section
namespace VWZClique.IntegerRAM.Projected.PairScan
open Structured FoldBits

theorem extract_runs {W} (m : Memory) (v hit : ℤ) (v0 : v≠0) (b0 : hit≠0)
    (vt : v≠test) (bt : hit≠test) (diff : v≠hit)
    (fit : Fits W (2*m v-m 0)) :
    ∃ f o, f≤6 ∧ Runs W (extract v hit) m f o ∧
      o v=2*m v-(if m 0≤2*m v then m 0 else 0) ∧ o hit=(if m 0≤2*m v then 1 else 0) ∧
      ∀ j : ℤ, j≠v → j≠hit → j≠test → o j=m j := by
  let u := update m v (m v+m v)
  let q := update u test (u v-u 0)
  let r := update q hit (q hit-q hit)
  have first : Runs W (.atom (.add v v v)) m 1 u := .atom (.add ..)
  have second : Runs W (.atom (.sub test v 0)) u 1 q := .atom (.sub ..)
  have third : Runs W (.atom (.sub hit hit hit)) q 1 r := .atom (.sub ..)
  have flag : r test=2*m v-m 0 := by simp [r,q,u,update,Ne.symm bt,Ne.symm v0,two_mul]
  by_cases h : m 0≤2*m v
  · let s := update r v (r v-r 0)
    let o := update s hit 1
    have sub : Runs W (.seq (.atom (.sub v v 0)) (.atom (.one hit))) r 2 o := .seq (.atom (.sub ..)) (.atom (.one ..))
    refine ⟨6,o,le_rfl,.seq first (.seq second (.seq third (.guard_take (flag ▸ fit) (by rw [flag];omega) sub))),?_,?_,?_⟩
    · rw [if_pos h]; simp [o,s,r,q,u,update,diff,vt,Ne.symm b0,Ne.symm v0,test,two_mul]
    · simp [o,update,h]
    · intro j jv jh jt; simp [o,s,r,q,u,update,jv,jt,jh]
  · refine ⟨4,r,by decide,.seq first (.seq second (.seq third (.guard_skip (flag ▸ fit) (by rw [flag];omega)))),?_,?_,?_⟩
    · rw [if_neg h]; simp [r,q,u,update,vt,diff,two_mul]
    · simp [r,update,h]
    · intro j jv jh jt;simp [r,q,u,update,jv,jt,jh]

def digit (a b : Bool) : ℕ :=
  match a,b with | false,false => 0 | true,true => 1 | false,true => 2 | true,false => 3

def digitWord (bs : List (Bool×Bool)) : ℕ :=
  match bs with | [] => 0 | (a,b)::t => digit a b*4^t.length + digitWord t

def numX (bs : List (Bool×Bool)) := FoldBits.encode (bs.map Prod.fst)
def numY (bs : List (Bool×Bool)) := FoldBits.encode (bs.map Prod.snd)

structure State (N X Y : ℕ) (acc j : ℤ) (m : Memory) : Prop where
  side : m 0=N
  fst : m x=X
  snd : m y=Y
  acc : m ans=acc
  count : m counter=j
  unit : m one=1

def Stable (m o : Memory) := ∀ j : ℤ, j≠ans → (-140<j ∨ j< -149) → o j=m j

theorem body_runs {W N Q lx ly P : ℕ} (pos : 0<P) (hlx : lx<Q) (hly : ly<Q)
    (size : N=2*Q*P) (A B : Bool) {acc j : ℤ} (m : Memory)
    (st : State N ((bit A*Q+lx)*P) ((bit B*Q+ly)*P) acc j m) (room : Capacity W N) :
    ∃ f o, f≤23 ∧ Runs W body m f o ∧
      State N (lx*(2*P)) (ly*(2*P)) (4*acc+digit A B) (j+1) o ∧ Stable m o := by
  have bitFact (b : Bool) (l : ℕ) (lt : l<Q) (z : ℤ) (hi : z=((bit b*Q+l)*P:ℕ)) :
      Fits W (2*z-N) ∧ ((N:ℤ)≤2*z ↔ b=true) ∧
      2*z-(if (N:ℤ)≤2*z then (N:ℤ) else 0)=((l*(2*P):ℕ):ℤ) := by
    have raw : (bit b*Q+l)*P<N := by
      rw [size]; apply Nat.mul_lt_mul_of_pos_right _ pos
      cases b <;> simp [bit] <;> omega
    have bound : z<(N:ℤ) := hi ▸ (by exact_mod_cast raw)
    have nn : 0≤z := hi ▸ Int.natCast_nonneg _
    have fit : Fits W (2*z-N) := room.fits (by omega) (by omega)
    have sN : (N:ℤ)=2*Q*P := by exact_mod_cast size
    have hlt : (l:ℤ)*P<(Q:ℤ)*P := by exact_mod_cast Nat.mul_lt_mul_of_pos_right lt pos
    refine ⟨fit,?_⟩
    cases b with
    | false =>
      simp only [bit,Bool.false_eq_true,if_false,zero_mul,zero_add,Nat.cast_mul] at hi
      have neg : ¬(N:ℤ)≤2*z := by nlinarith only [hlt,sN,hi]
      refine ⟨by simp [neg],?_⟩
      rw [if_neg neg,hi];push_cast;ring
    | true =>
      simp only [bit,if_true,one_mul,Nat.cast_mul,Nat.cast_add] at hi
      have more : (N:ℤ)≤2*z := by nlinarith only [sN,hi,mul_nonneg (Int.natCast_nonneg l) (Int.natCast_nonneg P)]
      refine ⟨by simp [more],?_⟩
      rw [if_pos more,hi,sN];push_cast;ring
  obtain ⟨fa,ea,va⟩ := bitFact A lx hlx (m x) st.fst
  obtain ⟨fb,eb,vb⟩ := bitFact B ly hly (m y) st.snd
  obtain ⟨f,u,fu,ra,xv,av,fr⟩ := extract_runs m x a (by decide) (by decide) (by decide) (by decide) (by decide) (by rwa [st.side])
  have uN := (fr 0 (by decide) (by decide) (by decide)).trans st.side
  have uy := fr y (by decide) (by decide) (by decide)
  obtain ⟨g,v,gv,rb,yv,bv,fr'⟩ := extract_runs u y b (by decide) (by decide) (by decide) (by decide) (by decide) (by rwa [uy,uN])
  rw [st.side] at xv av
  rw [uy,uN] at yv bv
  have ax : v x=((lx*(2*P):ℕ):ℤ) := (fr' x (by decide) (by decide) (by decide)).trans (xv.trans va)
  have by' : v y=((ly*(2*P):ℕ):ℤ) := yv.trans vb
  have convertBit (C : Bool) {p : Prop} [Decidable p] (eq : p ↔ C=true) : (if p then (1:ℤ) else 0)=(bit C:ℤ) := by
    cases C with
    | false => rw [if_neg (fun h => Bool.noConfusion (eq.mp h))];rfl
    | true => rw [if_pos (eq.mpr rfl)];rfl
  have av' : v a=(bit A:ℤ) := (fr' a (by decide) (by decide) (by decide)).trans (av.trans (convertBit A ea))
  have bv' : v b=(bit B:ℤ) := bv.trans (convertBit B eb)
  have vStable : Stable m v := by
    intro k ha range
    rw [fr' k (by dsimp [y];omega) (by dsimp [b];omega) (by dsimp [test];omega),
      fr k (by dsimp [x];omega) (by dsimp [a];omega) (by dsimp [test];omega)]
  have vu := (fr' one (by decide) (by decide) (by decide)).trans ((fr one (by decide) (by decide) (by decide)).trans st.unit)
  have vj := (fr' counter (by decide) (by decide) (by decide)).trans ((fr counter (by decide) (by decide) (by decide)).trans st.count)
  have vacc := (fr' ans (by decide) (by decide) (by decide)).trans ((fr ans (by decide) (by decide) (by decide)).trans st.acc)
  have vN := (fr' 0 (by decide) (by decide) (by decide)).trans uN
  let out := finish.foldl write v
  have final : Runs W (code finish) v 11 out := code_runs _ _ _ (by simp [finish,Safe,safe])
  refine ⟨_,out,by omega,.seq ra (.seq rb final),?_,?_⟩
  · have keep (k : ℤ) (ha : k≠ans) (ht : k≠tmp) (hc : k≠cross) (hj : k≠counter) : out k=v k := by
      simp [out,finish,write,update,ha,ht,hc,hj]
    refine ⟨(keep _ (by decide) (by decide) (by decide) (by decide)).trans vN,
      (keep _ (by decide) (by decide) (by decide) (by decide)).trans ax,
      (keep _ (by decide) (by decide) (by decide) (by decide)).trans by',?_,?_,
      (keep _ (by decide) (by decide) (by decide) (by decide)).trans vu⟩
    · have va : v (-142)=(bit A:ℤ) := av'
      have vb : v (-143)=(bit B:ℤ) := bv'
      have vc : v (-56)=acc := vacc
      simp [out,finish,write,update,ans,tmp,cross,counter,x,y,one,a,b,va,vb,vc]
      cases A <;> cases B <;> simp [bit,digit] <;>ring
    · have vv : v (-146)=j := vj
      have v1 : v (-148)=1 := vu
      simp [out,finish,write,update,ans,tmp,cross,counter,one,vv,v1]
  · intro k eq h
    exact (by simp [out,finish,write,update,eq,show k≠tmp by dsimp [tmp];omega,
      show k≠cross by dsimp [cross];omega,show k≠counter by dsimp [counter];omega] : out k=v k).trans (vStable k eq h)

theorem loop_runs (bs : List (Bool×Bool)) (P : ℕ) (acc : ℤ) {W : ℕ}
    (positive : 0<P) (ne : bs≠[]) (m : Memory)
    (st : State (2^bs.length*P) (numX bs*P) (numY bs*P) acc (-(bs.length:ℤ)) m)
    (room : Capacity W (2^bs.length*P)) :
    ∃ f o, f≤24*bs.length ∧ Runs W loop m f o ∧
      o ans=acc*(4:ℤ)^bs.length+digitWord bs ∧ Stable m o := by
  induction bs generalizing P acc m with
  | nil => contradiction
  | cons h t ih =>
    obtain ⟨l,r⟩ := h
    have small (b : Bool×Bool→Bool) : FoldBits.encode (t.map b)<2^t.length := by simpa using encode_lt (t.map b)
    obtain ⟨s,u,sc,exec,res,fr⟩ := body_runs positive (small Prod.fst) (small Prod.snd)
      (by simp only [List.length_cons,pow_succ];ring : 2^((l,r)::t).length*P=2*(2^t.length)*P) l r m
      (by simpa only [numX,numY,List.map_cons,FoldBits.encode,List.length_map] using st) room
    have next := res.count
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at next
    have cn : u counter= -(t.length:ℤ) := by omega
    have lt : t.length<2^t.length := Nat.lt_two_pow_self
    have major : 2^t.length≤2^((l,r)::t).length*P := by
      have h : 2^t.length≤2^(t.length+1) := Nat.pow_le_pow_right (by decide) (by omega)
      exact h.trans (Nat.le_mul_of_pos_right _ positive)
    have fit : Fits W (u counter) := by rw [cn];apply room.fits <;> omega
    by_cases empty : t=[]
    · subst t
      refine ⟨_,u,by simp;omega,.loop_done exec fit (by simpa using cn.ge),?_,fr⟩
      simpa [digitWord,Int.mul_comm] using res.acc
    · have side : 2^((l,r)::t).length*P=2^t.length*(2*P) := by simp [pow_succ];ring
      have st' : State (2^t.length*(2*P)) (numX t*(2*P)) (numY t*(2*P)) (4*acc+digit l r) (-(t.length:ℤ)) u :=
        ⟨res.side.trans (by exact_mod_cast side),res.fst,res.snd,res.acc,cn,res.unit⟩
      obtain ⟨v,o,vc,again,result,fr'⟩ := ih (2*P) _ (by omega) empty u st' (side ▸ room)
      refine ⟨_,o,by simp;omega,.loop_again exec fit (by rw [cn]; have := List.length_pos_iff.mpr empty;omega) again,?_,
        fun z za hi => (fr' z za hi).trans (fr z za hi)⟩
      rw [result]
      simp [digitWord,pow_succ];ring

theorem command_runs {W : ℕ} (bs : List (Bool×Bool)) (ne : bs≠[]) (m : Memory)
    (n : m 0=((2^bs.length:ℕ):ℤ)) (len : m 320=bs.length)
    (a : m srcX=(numX bs:ℤ)) (b : m srcY=(numY bs:ℤ))
    (room : Capacity W (2^bs.length)) :
    ∃ f o, f≤6+24*bs.length ∧ Runs W command m f o ∧ o ans=(digitWord bs:ℤ) ∧ Stable m o := by
  let u := init.foldl write m
  have step : Runs W (code init) m 6 u := code_runs _ _ _ (by simp [init,Safe,safe])
  have st : State (2^bs.length*1) (numX bs*1) (numY bs*1) 0 (-(bs.length:ℤ)) u := by
    have aa : m (-54)=(numX bs:ℤ) := a
    have bb : m (-55)=(numY bs:ℤ) := b
    constructor <;> simp [u,init,write,update,one,srcX,srcY,x,y,ans,counter,n,len,aa,bb]
  obtain ⟨t,o,ht,exec,res,fr⟩ := loop_runs bs 1 0 (by decide) ne u st (by simpa using room)
  refine ⟨_,o,by omega,.seq step exec,by simpa using res,?_⟩
  intro j h hi
  exact (fr j h hi).trans (by simp [u,init,write,update,h,show j≠one by dsimp [one];omega,
    show j≠x by dsimp [x];omega,show j≠y by dsimp [y];omega,show j≠counter by dsimp [counter];omega])

end VWZClique.IntegerRAM.Projected.PairScan
end

/- NativeFoldScan -/
section
namespace VWZClique.IntegerRAM.FoldBits
open Structured VWZClique.UniformFolds VWZClique.FoldProof

def packed {L : ℕ} (x : Bits L) := encode (List.ofFn x)

theorem packed_eq {L : ℕ} (x : Bits L) : packed x = (wordIndex L x).val := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change encode (List.ofFn x) = (wordIndex L (fun i => x i.succ)).val +
      2^L * (finTwoEquiv.symm (x 0)).val
    rw [List.ofFn_succ,encode,List.length_ofFn]
    have h := ih (fun i => x i.succ)
    change encode (List.ofFn (fun i => x i.succ)) = _ at h
    rw [h]
    cases e : x 0 <;> simp [bit,finTwoEquiv] <;> omega

end VWZClique.IntegerRAM.FoldBits
end

/- NativeProjectionPairAddress -/
section
namespace VWZClique.IntegerRAM.Projected.PairScan
open Structured FoldBits UniformFolds

def pairs {L} (f : PairBits L) := List.ofFn fun i => (f.1 i,f.2 i)

theorem pairs_address {L} (f : PairBits L) : digitWord (pairs f)=Butterfly.pairAddress f := by
  induction L with
  | zero => rfl
  | succ L ih =>
    let rest : PairBits L := (fun i => f.1 i.succ,fun i => f.2 i.succ)
    change digitWord (List.ofFn _) = (Butterfly.digit (f.1 0) (f.2 0)).val*4^L + Butterfly.pairAddress rest
    rw [List.ofFn_succ]
    change digit (f.1 0) (f.2 0)*4^(pairs rest).length+digitWord (pairs rest)=_
    rw [ih]
    have h : (pairs rest).length=L := by simp [pairs]
    rw [h]
    cases f.1 0 <;> cases f.2 0 <;> rfl

/-- Compute the exact row-major butterfly address of a pair using its two
ordinary packed vertex numbers. -/
theorem pair_address_runs {W L : ℕ} (pos : 0<L) (f : PairBits L) (m : Memory)
    (n : m 0=((2^L:ℕ):ℤ)) (len : m 320=L)
    (sx : m srcX=(wordIndex L f.1).val) (sy : m srcY=(wordIndex L f.2).val)
    (room : Capacity W (2^L)) :
    ∃ t o, t≤6+24*L ∧ Runs W command m t o ∧ o ans=(Butterfly.pairAddress f:ℤ) ∧ Stable m o := by
  have length : (pairs f).length=L := by simp [pairs]
  have left : numX (pairs f)=(wordIndex L f.1).val := by simpa [numX,pairs,packed,List.map_ofFn,Function.comp_def] using packed_eq f.1
  have right : numY (pairs f)=(wordIndex L f.2).val := by simpa [numY,pairs,packed,List.map_ofFn,Function.comp_def] using packed_eq f.2
  obtain ⟨t,o,time,exec,addr,fr⟩ := command_runs (pairs f) (by intro eq; rw [eq] at length; simp at length;omega) m
    (by simpa [length] using n) (by simpa [length] using len) (by simpa [left] using sx) (by simpa [right] using sy)
    (by simpa [length] using room)
  exact ⟨t,o,by simpa [length] using time,exec,by rwa [pairs_address] at addr,fr⟩

end VWZClique.IntegerRAM.Projected.PairScan
end

/- NativeProjectionScatterValues -/
section
namespace VWZClique.IntegerRAM.Projected.Scatter
open Structured Slices UniformFolds TraceDyadic

/-- A scaled square slice is physically row-major in the two free bitstrings. -/
theorem bank_read {L : ℕ} {m : Memory} {src : ℕ} {V : Matrix (Bits L) (Bits L) ℤ} {P : ℤ}
    (data : bank m src (scaleMat P (pack V))) (r c : Fin (2^L)) :
    m (readAt src (2^L) r c)=P*V ((wordIndex L).symm r) ((wordIndex L).symm c) := by
  have h := data (finProdFinEquiv (r,c))
  have loc : (finProdFinEquiv (r,c)).val=r.val*2^L+c.val := by change c.val+2^L*r.val=_;ring
  simpa [readAt,flat,pack,scaleMat,loc,Nat.add_assoc] using h

end VWZClique.IntegerRAM.Projected.Scatter
end

/- NativeProjectionScatterHeader -/
section
namespace VWZClique.IntegerRAM.Projected.Scatter
open Structured UniformFolds FoldBits

/-- The projector's stable positive loop headers configure this scatter. All
positive headers and all nontarget positive cells are preserved. -/
structure Headers {L : ℕ} (b : Channel) (f : PairBits L) (workspace dense pos count : ℕ) (m : Memory) : Prop where
  size : m 0=((2^L:ℕ):ℤ)
  length : m 320=L
  area : m 356=workspace
  out : m (bufferReg b)=dense
  label : m 357=pos
  total : m 359=count
  first : m 354=(wordIndex L f.1).val
  second : m 355=(wordIndex L f.2).val

def shape {L} (f : PairBits L) (work dst p total : ℕ) : Slice :=
  ⟨2^L,work+3*((2^L)*(2^L)),dst,p,total,(wordIndex L f.1).val,(wordIndex L f.2).val,Butterfly.pairAddress f⟩

theorem start_word {W L work dst p count : ℕ} (b : Channel) (f : PairBits L) (m : Memory)
    (h : Headers b f work dst p count m) :
    ∃ v, Runs W (FoldBits.code (setup b)) m 10 v ∧ ∀ z : ℤ, v z =
      if z=sourceBase then ((work+3*((2^L)*(2^L)):ℕ):ℤ) else if z=targetBase then (dst:ℤ)
      else if z=labelID then (p:ℤ) else if z=labels then (count:ℤ)
      else if z=remoteX then ((wordIndex L f.1).val:ℤ) else if z=remoteY then ((wordIndex L f.2).val:ℤ)
      else if z= -62 then 1 else if z= -63 then 2*((2^L:ℕ):ℤ)^2 else m z := by
  let v := (setup b).foldl FoldBits.write m
  refine ⟨v,FoldBits.code_runs _ _ _ (by simp [setup,FoldBits.Safe,FoldBits.safe]),?_⟩
  intro z
  obtain ⟨N,_,A,D,P,T,X,Y⟩ := h
  cases b <;> dsimp only [bufferReg] at D
  all_goals simp [v,setup,FoldBits.write,update,sourceBase,targetBase,labelID,labels,remoteX,remoteY,
    bufferReg,N,A,D,P,T,X,Y,Nat.cast_add,Nat.cast_mul]
  all_goals by_cases u : z = -50
  all_goals first | subst z; norm_num; ring | skip
  all_goals by_cases u₁ : z = -51
  all_goals first | subst z; norm_num | skip
  all_goals by_cases u₂ : z = -52
  all_goals first | subst z; norm_num | skip
  all_goals by_cases u₃ : z = -53
  all_goals first | subst z; norm_num | skip
  all_goals by_cases u₄ : z = -54
  all_goals first | subst z; norm_num | skip
  all_goals by_cases u₅ : z = -55
  all_goals first | subst z; norm_num | skip
  all_goals simp_all <;> split_ifs <;> first | omega | ring

theorem header_slice {W L work dst p count : ℕ} (b : Channel) (f : PairBits L) (m : Memory)
    (h : Headers b f work dst p count m) (pos : 0<L) (active : p<count) (cap : Capacity W (2^L))
    
    (guard : ∀ i : Fin ((shape f work dst p count).n+1), Fits W ((i.val:ℤ)-(shape f work dst p count).n))
    (one : ∀ i:ℕ, i≤1 → Fits W ((i:ℤ)-1))
    (fit : ∀ r c : Fin (shape f work dst p count).n, Fits W ((shape f work dst p count).target b r c) ∧ Fits W (readAt (shape f work dst p count).src (shape f work dst p count).n r c))
    (apart : ∀ r c i j : Fin (shape f work dst p count).n, (shape f work dst p count).target b r c≠readAt (shape f work dst p count).src (shape f work dst p count).n i j) :
    ∃ t o, t≤16+24*L+128*(2^L)^2 ∧ Runs W (fromHeaders b) m t o ∧
      (∀ r c : Fin (shape f work dst p count).n, o ((shape f work dst p count).target b r c)=m (readAt (shape f work dst p count).src (shape f work dst p count).n r c)) ∧
      ∀ z : ℕ, (∀ r c : Fin (shape f work dst p count).n, z≠(shape f work dst p count).target b r c) → o z=m z := by
  obtain ⟨v,init,fr⟩ := start_word (W:=W) b f m h
  have vk (j : ℕ) : v j=m j := by simp [fr,sourceBase,targetBase,labelID,labels,remoteX,remoteY]
  have vx : v PairScan.srcX=(wordIndex L f.1).val := by simp [fr,PairScan.srcX,sourceBase,targetBase,labelID,labels,remoteX]
  have vy : v PairScan.srcY=(wordIndex L f.2).val := by simp [fr,PairScan.srcY,sourceBase,targetBase,labelID,labels,remoteX,remoteY]
  obtain ⟨t,u,ut,pair,addr,keep⟩ := PairScan.pair_address_runs pos f v ((vk 0).trans h.size) ((vk 320).trans h.length) vx vy cap
  have uk (j : ℕ) : u j=m j := (keep j (by dsimp [PairScan.ans];omega) (Or.inl (by omega))).trans (vk j)
  let s := shape f work dst p count
  have ctrl : s.control u := by
    refine ⟨(uk 0).trans h.size,?_,?_,?_,?_,?_,?_,addr⟩
    all_goals rw [keep _ (by decide) (by decide),fr]
    all_goals simp [s,shape,sourceBase,targetBase,labelID,labels,remoteX,remoteY]
  have hn : 0<(shape f work dst p count).n := by dsimp [s,shape];positivity
  obtain ⟨vtime,o,vt,more,res,fixed⟩ := copy_slice s b hn active u ctrl guard one fit apart
  have est : vtime≤128*(2^L)^2 := vt.trans (cost_le hn)
  exact ⟨10+(t+vtime),o,by omega,.seq init (.seq pair more),fun r c => (res r c).trans (uk _),
    fun z hz => (fixed _ hz).trans (uk _)⟩

end VWZClique.IntegerRAM.Projected.Scatter
end

/- NativeProjectionChannels -/
section
namespace VWZClique.IntegerRAM.Projected.Channels
open Structured Projection UniformFolds WeightedProof TraceDyadic BlockMM Scatter Placement Grid

def point {L a : ℕ} (ch : Channel) (dst : ℕ) (v : Site a (2^L)) (k : Fin (2^L) × Fin (2^L)) :=
  dst+location ch v k

noncomputable def result {L a : ℕ} (P : ℤ) (lab : Fin a → BasisLabel L) (ch : Channel)
    (w : ChannelKey L → ℚ) (v : Site a (2^L)) (k : Fin (2^L) × Fin (2^L)) :=
  P*Slices.singleInt (rev ch) (index ch) (lab v.1) ((wordIndex L).symm k.1)
    (block (remote v.2.1 v.2.2) ((wordIndex L).symm k.2)) w

private theorem target {L a : ℕ} (ch : Channel) (dst work : ℕ) (v : Site a (2^L)) (z c : Fin (2^L)) :
    (shape (remote v.2.1 v.2.2) work dst v.1.val a).target ch z c=point ch dst v (z,c) := by
  cases ch <;> simp only [Slice.target_middle,Slice.target_right,Slice.target_left,shape,remote,Equiv.apply_symm_apply,
    point,location,packed_val,lo3_val,pairCode_val,Nat.add_assoc]

/-- A full slice from its graph-derived weight bank to the selected channel's
absolute dense addresses. All positive words below workspace outside this
slice are preserved, including the physical counters of the enclosing loop. -/
theorem job_runs {W M L b r a base sig pr work dst : ℕ} (S : Scheme b r) (hb : 2≤b) (hr : 0<r)
    (π : Equiv.Perm V) (E : Finset EdgeSlot) (ch : Channel) (v : Site a (2^L)) (lab : Fin a → BasisLabel L)
    (w : WeightKey (2^L)→ℚ) (hw : ∀ i, Binary (literal w (inputKey π E i))) (m : Memory)
    (data : Small.Data (lab v.1) (remote v.2.1 v.2.2) w base sig pr work m)
    (ctrl : Scatter.Headers ch (remote v.2.1 v.2.2) work dst v.1.val a m)
    (hL : 0<L) (high : 380<dst) (extent : dst+a*(2^L)^4≤work)
    (cap : Graph.Division.Room W M)
    (space : work+4*(2^L*2^L)+BlockMM.WordLayout.space b r (BlockMM.depth b (2^L)) 1≤M) :
    let P := S.scale^(BlockMM.depth b (2^L))
    ∃ t ≤ time S π E ch L, ∃ o, Runs W (job S π E ch) m t o ∧
      (∀ k, o (point ch dst v k)=result P lab ch (fun i => literal w (inputKey π E i)) v k) ∧
      ∀ z : ℕ, z<work → (∀ k, z≠point ch dst v k) → o z=m z := by
  intro P
  let n := 2^L
  let f := remote v.2.1 v.2.2
  let cw := fun i => literal w (inputKey π E i)
  let l := Small.locations work n
  have npos : 0<n := by dsimp [n]; positivity
  have ht : work≤M := by omega
  have nw : n≤M := by
    have s := Nat.mul_le_mul_left n npos
    change work+4*(n*n)+_≤M at space
    omega
  have sq := SquareCaller.square_run S hb hr npos (W:=W) (M:=M) (fun _ low hi => cap.fits low hi) l
    (Slices.pack (Slices.outsideInt (rev ch) (index ch) f cw))
    (fun _ : Fin 1 => Slices.pack (Slices.lookupA (rev ch) (index ch) (lab v.1) cw))
    (fun _ : Fin 1 => Slices.pack (Slices.lookupB (rev ch) (index ch) (lab v.1) f cw))
    (by simp [l,Small.locations];omega) (by simp [l,Small.locations]; omega)
    (by dsimp [l,Small.locations]; omega) (by dsimp [l,Small.locations];omega)
    (by change work+4*(n*n)+WordLayout.space b r (depth b n) 1≤M at space; dsimp [l,Small.locations];omega)
  obtain ⟨t,tb,x,exec,bankX,prior⟩ := Small.job_run data π E (rev ch) (index ch) hw cap
    (by omega) P (SquareCode.Layout.multiply S) sq
  have below : dst≤work := by omega
  have reg (z : ℕ) (h : z≤380) := prior z (by omega)
  have heads : Scatter.Headers ch f work dst v.1.val a x := by
    refine ⟨(reg _ (by decide)).trans ctrl.size,(reg _ (by decide)).trans ctrl.length,
      (reg _ (by decide)).trans ctrl.area,?_,(reg _ (by decide)).trans ctrl.label,
      (reg _ (by decide)).trans ctrl.total,(reg _ (by decide)).trans ctrl.first,(reg _ (by decide)).trans ctrl.second⟩
    cases ch <;> exact (reg _ (by decide)).trans ctrl.out
  let sh := shape f work dst v.1.val a
  have inside (i j : Fin n) : sh.target ch i j<work := by
    have g := location_lt ch v (i,j)
    rw [target] ; unfold point; omega
  have srcBounds (i j : Fin n) : work≤readAt sh.src sh.n i j ∧ readAt sh.src sh.n i j<M := by
    have il := Nat.mul_le_mul_right n i.isLt
    rw [Nat.succ_mul] at il
    have jl := j.isLt
    change work+4*(n*n)+_≤M at space
    change work≤work+3*(n*n)+i.val*n+j.val ∧ work+3*(n*n)+i.val*n+j.val<M
    omega
  obtain ⟨u,o,ub,copy,vals,frame⟩ := header_slice (W:=W) ch f x heads hL v.1.isLt
    (show FoldBits.Capacity W (2^L) from (show (n:ℤ)≤M by exact_mod_cast nw).trans_lt cap)
    (fun i => by have hi : i.val<n+1 := i.isLt; change Fits W ((i.val:ℤ)-(n:ℤ)); apply cap.fits <;> omega)
    (fun i hi => by apply cap.fits <;> omega)
    (fun i j => ⟨cap.fits (by omega) (by exact_mod_cast (inside i j).le.trans ht),cap.fits (by omega) (by exact_mod_cast (srcBounds i j).2.le)⟩)
    (fun i j k d => ne_of_lt ((inside i j).trans_le (srcBounds k d).1))
  refine ⟨_,Nat.add_le_add tb ub,o,.seq exec copy,?_,?_⟩
  · rintro ⟨i,j⟩
    rw [←target ch dst work v i j]
    exact (vals i j).trans (bank_read bankX i j)
  · intro z hz away
    exact (frame z (fun i j => (target ch dst work v i j) ▸ away (i,j))).trans (prior z hz)

end VWZClique.IntegerRAM.Projected.Channels
end

/- NativeProjection -/
section
namespace VWZClique.IntegerRAM.Projected
open Structured UniformFolds TraceDyadic Double
open Double.IntegerTiling

theorem longNumber_block {L} (f : PairBits L) (z : Bits L) :
    (longNumber L (block f z)).val=
      ((wordIndex L f.1).val*2^L+(wordIndex L f.2).val)*2^L+(wordIndex L z).val := by
  change (wordIndex L z).val+2^L*((wordIndex L f.2).val+2^L*(wordIndex L f.1).val)=_
  ring

theorem blockNumber_linear (L q : ℕ) (p : Fin (blocks L q)) (x : Fin (IntegerTiling.side L q)) :
    (longNumber L ((blockNumber L q).symm (p,x))).val=p.val*IntegerTiling.side L q+x.val := by
  change (longNumber L ((longNumber L).symm _)).val=_
  rw [Equiv.apply_symm_apply]
  change x.val+IntegerTiling.side L q*p.val=p.val*IntegerTiling.side L q+x.val
  ring

end VWZClique.IntegerRAM.Projected
end

/- NativeProjectionSourceBinding -/
section
namespace VWZClique.IntegerRAM.Projected.Channels
open UniformFolds TraceDyadic Double Double.IntegerTiling Grid Placement Scatter

private theorem nodeLinear {L : ℕ} {S : Finset (BasisLabel L)} (v : Node S) :
    (labelNumber S v.1).val * 2^L + (wordIndex L v.2).val = (nodeNumber S v).val :=
  (packed_val (labelNumber S v.1) (wordIndex L v.2)).symm

private theorem blockFull {L} (t : Block L) : block (t 0,t 1) (t 2)=t :=
  (threeVertices L).left_inv t

private theorem blockLinear {L q} (p : Fin (blocks L q)) (c : Fin (IntegerTiling.side L q)) :
    let t := (blockNumber L q).symm (p,c)
    ((wordIndex L (t 0)).val*2^L+(wordIndex L (t 1)).val)*2^L+(wordIndex L (t 2)).val
      = p.val * IntegerTiling.side L q + c.val := by
  intro t
  rw [←longNumber_block (t 0,t 1) (t 2),blockFull]
  exact blockNumber_linear L q p c

/-- Identify the dense row-major words written by the three channel grids
with all matrix entries consumed by the subsequent rectangular tile packing. -/
theorem dense_sources {L : ℕ} (S : Finset (BasisLabel L)) (K q : ℕ) (w : ChannelKey L → ℚ)
    (P : ℤ) (l : Large.Banks) (m : Memory)
    (weight : ∀ (p : Fin S.card) (z v : Fin (2^L)) (j : Fin S.card),
      m (l.A+((p.val*2^L+z.val)*(S.card*2^L)+(j.val*2^L+v.val)):ℕ)=
        P*leftTable S S K K w ((labelNumber S).symm p,(wordIndex L).symm z)
          ((labelNumber S).symm j,(wordIndex L).symm v))
    (mid : ∀ (v : Site S.card (2^L)) k, m (point .middle l.B v k)=
      result P (fun p => ((labelNumber S).symm p).val) .middle w v k)
    (rhs : ∀ (v : Site S.card (2^L)) k, m (point .right l.C v k)=
      result P (fun p => ((labelNumber S).symm p).val) .right w v k) :
    Large.Sources m l (scaleMat P (shortWeight S K w)) (scaleMat P (middle S q w))
      (scaleMat P (Projected.right S q w)) := by
  constructor
  · intro i j
    obtain ⟨x,rfl⟩ := (nodeNumber S).surjective i
    obtain ⟨y,rfl⟩ := (nodeNumber S).surjective j
    simpa only [nodeLinear,scaleMat,shortWeight,Equiv.symm_apply_apply,Prod.mk.eta] using
      weight (labelNumber S x.1) (wordIndex L x.2) (wordIndex L y.2) (labelNumber S y.1)
  · intro i p c
    obtain ⟨x,rfl⟩ := (nodeNumber S).surjective i
    let t := (blockNumber L q).symm (p,c)
    have hl := blockLinear p c
    change ((wordIndex L (t 0)).val*2^L+(wordIndex L (t 1)).val)*2^L+(wordIndex L (t 2)).val
      = p.val * IntegerTiling.side L q + c.val at hl
    have h := mid (labelNumber S x.1,wordIndex L (t 0),wordIndex L (t 1))
      (wordIndex L x.2,wordIndex L (t 2))
    simpa only [point,location,packed_val,lo3_val,nodeLinear,hl,exact_shape,result,rev,index,
      remote,Equiv.symm_apply_apply,blockFull,Slices.singleInt,scaleMat,middle,midTable,
      Bool.false_eq_true,if_false] using h
  · intro p c i
    obtain ⟨x,rfl⟩ := (nodeNumber S).surjective i
    let t := (blockNumber L q).symm (p,c)
    have hl := blockLinear p c
    change ((wordIndex L (t 0)).val*2^L+(wordIndex L (t 1)).val)*2^L+(wordIndex L (t 2)).val
      = p.val * IntegerTiling.side L q + c.val at hl
    have h := rhs (labelNumber S x.1,wordIndex L (t 0),wordIndex L (t 1))
      (wordIndex L x.2,wordIndex L (t 2))
    simpa only [point,location,packed_val,lo3_val,nodeLinear,hl,exact_shape,result,rev,index,
      remote,Equiv.symm_apply_apply,blockFull,Slices.singleInt,scaleMat,Projected.right,rightTable,if_true] using h

end VWZClique.IntegerRAM.Projected.Channels
end

/- NativeMaskScan -/
section
/-! Uniform stable compaction for mask and projected-label records. -/
namespace VWZClique.IntegerRAM.MaskScan
open Structured Butterfly

theorem rank_mono (keep : ℕ → Bool) {i j : ℕ} (h : i≤j) : rank keep i ≤ rank keep j := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (by rw [rank]; split <;> omega)

theorem rank_strict {keep : ℕ → Bool} {i j : ℕ} (lt : i<j) (sel : keep i=true) :
    rank keep i < rank keep j := by
  have h := rank_mono keep (show i+1≤j from lt)
  simpa only [rank,sel,if_true,Nat.add_one_le_iff] using h

end VWZClique.IntegerRAM.MaskScan
end

/- EnumerationBudget -/
section
namespace VWZClique.RankSwap.MaskEnumeration

theorem digit_extraction {b L : ℕ} (x : Fin (b^L)) (p : Fin L) :
    ((finFunctionFinEquiv.symm x : Fin L → Fin b) p).val = x.val / b^p.val % b := rfl

end VWZClique.RankSwap.MaskEnumeration
end

/- NativeMaskScanSpectral -/
section
namespace VWZClique.IntegerRAM.MaskScan
open RankSwap RankSwap.MaskEnumeration Graph

theorem totalN_sum (b h z L : ℕ) : totalN b h z L =
    ∑ i : Fin L, localN h (z / b^i.val % b) := by
  induction L with
  | zero => simp [totalN]
  | succ L ih => rw [Fin.sum_univ_castSucc,totalN,ih]; rfl

theorem label_pop {L : ℕ} (z : Fin (4^L)) : totalN 4 3 z.val L =
    (antisymmetric (finFunctionFinEquiv.symm z : BasisLabel L)).card := by
  rw [totalN_sum,antisymmetric,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  let d := (finFunctionFinEquiv.symm z : BasisLabel L) i
  change localN 3 (z.val/4^i.val%4) = if d=3 then 1 else 0
  rw [← digit_extraction z i]
  change localN 3 d.val = if d=3 then 1 else 0
  have iff : d=3 ↔ 3≤d.val := by
    constructor
    · intro e; rw [e]; decide
    · intro h; apply Fin.ext; change d.val=3; have ht : d.val<4 := d.isLt; omega
  simp only [localN,iff]

theorem labelKey_iff {L a d : ℕ} (z : Fin (4^L)) : labelKey L a d z.val = true ↔
    (finFunctionFinEquiv.symm z : BasisLabel L)∈outside L a d := by
  simp only [labelKey,selected,decide_eq_true_eq,outside,Finset.mem_filter,Finset.mem_univ,true_and,label_pop]
  omega

theorem rank_card (keep : ℕ → Bool) (N : ℕ) :
    rank keep N = ((Finset.univ : Finset (Fin N)).filter fun z => keep z.val=true).card := by
  rw [Finset.card_filter]
  induction N with
  | zero => simp [rank]
  | succ N ih => rw [Fin.sum_univ_castSucc,rank,ih]; rfl

theorem label_count (L a d : ℕ) : rank (labelKey L a d) (4^L)=(outside L a d).card := by
  rw [rank_card]
  apply Finset.card_bij (fun x _ => (finFunctionFinEquiv.symm x : BasisLabel L))
  · intro x hx; exact (labelKey_iff x).mp (Finset.mem_filter.mp hx).2
  · intro x _ y _ he; exact finFunctionFinEquiv.symm.injective he
  · intro x hx; refine ⟨finFunctionFinEquiv x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,by simp⟩
    apply (labelKey_iff _).mpr; simpa using hx

end VWZClique.IntegerRAM.MaskScan
end

/- NativeProjectionLabels -/
section
namespace VWZClique.IntegerRAM.Projected.Labels
open Butterfly MaskScan RankSwap TraceDyadic

/-- The butterfly and the mask scanner read the same base-four integer from
opposite ends. Reversing label coordinates preserves both spectral counts. -/
def flipped {L : ℕ} (j : BasisLabel L) : BasisLabel L := fun i => j i.rev

private theorem address_sum (L : ℕ) (j : BasisLabel L) :
    address L j = ∑ i : Fin L, (j i.rev : ℕ)*4^i.val := by
  induction L with
  | zero => simp [address]
  | succ L ih =>
    rw [address,ih,Fin.sum_univ_castSucc]
    simp [Fin.rev_castSucc,add_comm]

theorem same_code {L : ℕ} (j : BasisLabel L) :
    finFunctionFinEquiv (flipped j) = labelIndex L j := by
  apply Fin.ext
  rw [finFunctionFinEquiv_apply,labelIndex_val,address_sum]
  rfl

theorem coefficient_digits {L : ℕ} (z : Fin (4^L)) :
    (finFunctionFinEquiv.symm z : BasisLabel L) = flipped ((labelIndex L).symm z) := by
  apply finFunctionFinEquiv.injective
  simp only [same_code,Equiv.apply_symm_apply]

theorem count_reverse {L : ℕ} (j : BasisLabel L) (p : Fin 4 → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun i => p (flipped j i))).card = (Finset.univ.filter (fun i => p (j i))).card := by
  simp only [Finset.card_filter]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)

theorem antisym_reverse {L} (j : BasisLabel L) : (antisymmetric (flipped j)).card=(antisymmetric j).card :=
  count_reverse j (·=3)

theorem denom_reverse {L} (j : BasisLabel L) : denominatorExponent (flipped j)=denominatorExponent j :=
  count_reverse j (fun x => ¬x<2)

theorem code_outside {L a d : ℕ} (z : Fin (4^L)) :
    labelKey L a d z.val = true ↔ (labelIndex L).symm z ∈ outside L a d := by
  rw [labelKey_iff,coefficient_digits]
  simp [RankSwap.outside,antisym_reverse]

theorem code_residual {L K : ℕ} (z : Fin (4^L)) :
    residualInt K L (finFunctionFinEquiv.symm z) = residualInt K L ((labelIndex L).symm z) := by
  simp only [coefficient_digits,residualInt,antisym_reverse,denom_reverse]

end VWZClique.IntegerRAM.Projected.Labels
end

/- NativeArenaChoiceOrder -/
section
namespace VWZClique.IntegerRAM.NativeArena.Choice
open MaskScan RankSwap RankSwap.MaskEnumeration NativeTraversal UniformFolds

theorem ranked_order {N : ℕ} (key : ℕ → Bool) (s : Finset (Fin N))
    (select : ∀ z : Fin N, z∈s → key z.val=true) (total : rank key N=s.card)
    (i : Fin s.card) :
    rank key ((s.orderIsoOfFin rfl i).val.val)=i.val := by
  let sel (k : Fin s.card) := s.orderIsoOfFin rfl k
  let f (k : Fin s.card) : Fin s.card :=
    ⟨rank key ((sel k).val.val), by rw [←total]; exact rank_strict (sel k).val.isLt (select _ (sel k).property)⟩
  have mono : StrictMono f := by
    intro a b lt
    apply rank_strict (by exact (s.orderIsoOfFin rfl).strictMono lt) (select _ (sel a).property)
  have uni : (Finset.univ : Finset (Fin s.card)).card=s.card := by simp
  have mun : ∀ k, f k∈(Finset.univ : Finset (Fin s.card)) := by simp
  have ident : ∀ k, id k∈(Finset.univ : Finset (Fin s.card)) := by simp
  have eq : f=id := (Finset.orderEmbOfFin_unique uni mun mono).trans
    (Finset.orderEmbOfFin_unique uni ident strictMono_id).symm
  exact congrArg Fin.val (congrFun eq i)

end VWZClique.IntegerRAM.NativeArena.Choice
end

/- NativeProjectionLabelArena -/
section
namespace VWZClique.IntegerRAM.Projected.Labels
open UniformFolds RankSwap MaskScan Butterfly TraceDyadic

private theorem sorted_code {L} (S : Finset (BasisLabel L)) (i : Fin S.card) :
    labelIndex L ((labelNumber S).symm i).val = (S.map (labelIndex L).toEmbedding).orderEmbOfFin (Finset.card_map ..) i := by
  let e := (labelIndex L).toEmbedding
  let y := (S.map e).orderIsoOfFin (Finset.card_map ..) i
  exact congrArg Subtype.val ((S.equivMap e).apply_symm_apply y)

/-- The physical compact slot enumerates the exact numbered node label in
butterfly address order, including its supplied integer normalization factor. -/
theorem prepared_row {L K q : ℕ} {m : Memory} (p : Arena.Prepared L K q m)
    (i : Fin (windowExpansion K L).labels.card) :
    let j := ((labelNumber (windowExpansion K L).labels).symm i).val
    m (Arena.slot q (2^L) 5+i.val:ℕ)=(labelIndex L j).val ∧
      m (Arena.slot q (2^L) 6+i.val:ℕ)=residualInt K L j := by
  let S := (windowExpansion K L).labels
  let R := S.map (labelIndex L).toEmbedding
  let key := labelKey L (lower K L) (width K L)
  let j := ((labelNumber S).symm i).val
  let z := labelIndex L j
  have pick (x : Fin (4^L)) (hx : x∈R) : key x.val=true := by
    obtain ⟨k,hk,eq⟩ := Finset.mem_map.mp hx
    change labelIndex L k=x at eq
    rw [←eq]
    exact (code_outside _).mpr (by rw [Equiv.symm_apply_apply]; exact hk)
  have length : rank key (4^L) = R.card := by simpa [R,S,key,windowExpansion] using label_count L (lower K L) (width K L)
  let i' : Fin R.card := (finCongr (Finset.card_map ..).symm) i
  have zr : z=R.orderEmbOfFin rfl i' := (sorted_code S i).trans (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl)
  have selected := pick z (zr ▸ R.orderEmbOfFin_mem _ _)
  have rk := NativeArena.Choice.ranked_order key R pick length i'
  change rank key (R.orderEmbOfFin rfl i').val=i.val at rk
  rw [←zr] at rk
  have hit := p.labels z ((labelKey_iff z).mp selected)
  rw [show rank (labelKey L (lower K L) (width K L)) z.val=i.val from rk] at hit
  exact ⟨hit.1,hit.2.trans (by simpa [z] using code_residual (K:=K) z)⟩

end VWZClique.IntegerRAM.Projected.Labels
end

/- NativeProjectionWorkspace -/
section
namespace VWZClique.IntegerRAM.Projected.Workspace

theorem level_lo (start h : ℕ) : start ≤ level start h := by
  induction h with | zero => rfl | succ h ih => simp only [level]; omega

theorem level_bound (start h : ℕ) : level start h+2*8^h ≤ start+3*8^h := by
  induction h with
  | zero => simp [level]
  | succ h ih => simp only [level,pow_succ]; omega

theorem support_prefix (start L : ℕ) :
    level start L+2*8^L ≤ (banks start (2^L)).left := by
  have eq : ((2:ℕ)^L)^3=8^L := by rw [←pow_mul,Nat.mul_comm,pow_mul]; rfl
  dsimp [banks]; rw [eq]; have := level_bound start L; omega

end VWZClique.IntegerRAM.Projected.Workspace
end

/- NativeProjectionPrepare -/
section
namespace VWZClique.IntegerRAM.Projected.Preparation
open Structured UniformFolds NativeFrame NativeTraversal NativeArena BlockMM

/-- A projection grid changes its own counters and destination bank. All
previously certified input weights, compact rows, headers and support tables
survive the operation. -/
theorem Ready.transfer {L K base count b c : ℕ} {w : WeightKey (2^L) → ℚ} {m o : Memory}
    (r : Ready L K base count b c w m) (large : 512 ≤ base)
    (fr : ∀ z : ℕ, z < (Workspace.banks (MaskScan.Arena.slot base (2^L) 7+2) (2^L)).left →
      ¬ Batch.privateCell z → o z=m z) : Ready L K base count b c w o := by
  let n := 2^L
  let start := MaskScan.Arena.slot base n 7+2
  let sig := Workspace.level start L
  let bound := (Workspace.banks start n).left
  have startLo : base+9*n+81*(n*n) ≤ start := by
    dsimp [start,MaskScan.Arena.slot,MaskScan.Arena.origin]; rw [pow_two]; omega
  have st : start ≤ sig := Workspace.level_lo start L
  have endBound : sig+2*8^L ≤ bound := Workspace.support_prefix start L
  have safeCell (z : ℕ) (lo : base ≤ z) (hi : z < bound) : o z=m z :=
    fr z hi (by unfold Batch.privateCell;omega)
  have hdr (z : ℕ) (hz : z ≤ 380) (ok : ¬ Batch.privateCell z) : o z=m z :=
    fr z (by change z < bound;omega) ok
  have tr (j : Fin (4^L)) (v : Fin (2^L)) : v.val*4^L+j.val < 8^L := by
    have eq : (2^L:ℕ)*4^L=8^L := by rw [←Nat.mul_pow]
    have h := Nat.mul_le_mul_right (4^L) (Nat.succ_le_of_lt v.isLt)
    rw [Nat.succ_mul] at h
    omega
  have banks : SupportDP.BanksAt L sig (sig+8^L) o := by
    constructor
    · intro j v
      have cut := tr (Butterfly.labelIndex L j) (wordIndex L v)
      exact (safeCell _ (by omega) (by omega)).trans (r.banks.signs j v)
    · intro j v
      have cut := tr (Butterfly.labelIndex L j) (wordIndex L v)
      exact (safeCell _ (by omega) (by omega)).trans (r.banks.partners j v)
  have params : Init.Params base n count o := by
    constructor
    · exact (hdr 350 (by decide) (by unfold Batch.privateCell;decide)).trans r.params.weights
    · exact (hdr 358 (by decide) (by unfold Batch.privateCell;decide)).trans r.params.codeBase
    · exact (hdr 359 (by decide) (by unfold Batch.privateCell;decide)).trans r.params.size
    · exact (hdr 370 (by decide) (by unfold Batch.privateCell;decide)).trans r.params.coefficients
    · exact (hdr 379 (by decide) (by unfold Batch.privateCell;decide)).trans r.params.start
    · exact (hdr 371 (by decide) (by unfold Batch.privateCell;decide)).trans r.params.source
    · exact (hdr 372 (by decide) (by unfold Batch.privateCell;decide)).trans r.params.middle
    · exact (hdr 373 (by decide) (by unfold Batch.privateCell;decide)).trans r.params.right
    · exact (hdr 374 (by decide) (by unfold Batch.privateCell;decide)).trans r.params.raw
    · exact (hdr 356 (by decide) (by unfold Batch.privateCell;decide)).trans r.params.smallWork
    · exact (hdr 375 (by decide) (by unfold Batch.privateCell;decide)).trans r.params.wt
    · exact (hdr 376 (by decide) (by unfold Batch.privateCell;decide)).trans r.params.leftPack
    · exact (hdr 377 (by decide) (by unfold Batch.privateCell;decide)).trans r.params.rightPack
    · exact (hdr 378 (by decide) (by unfold Batch.privateCell;decide)).trans r.params.product
  have same (z : ℕ) (lo : base ≤ z) (hi : z < start) : o z=m z := safeCell z lo (by omega)
  refine ⟨r.metadata.congr same,params,?_,
    (hdr 0 (by decide) (by unfold Batch.privateCell;decide)).trans r.domain,
    (hdr 320 (by decide) (by unfold Batch.privateCell;decide)).trans r.length,banks,
    (hdr 351 (by decide) (by unfold Batch.privateCell;decide)).trans r.signBase,
    (hdr 352 (by decide) (by unfold Batch.privateCell;decide)).trans r.partnerBase,
    (hdr 367 (by decide) (by unfold Batch.privateCell;decide)).trans r.scale⟩
  intro i
  have index : Graph.Table.wordIndex i < 9*n+81*(n*n) := NativeLeaf.index_lt i
  exact (congrArg (Int.cast : ℤ → ℚ) (same _ (by omega) (by omega))).trans (r.weights i)

end VWZClique.IntegerRAM.Projected.Preparation
end

/- NativeProjectionLeftGridArena -/
section
namespace VWZClique.IntegerRAM.Projected.LeftGrid
open UniformFolds TraceDyadic Structured Grid Placement Butterfly

private theorem raw_of_channel {L a : ℕ} {S : Finset (BasisLabel L)} {base : ℕ} {m : Memory}
    (w : ChannelKey L → ℚ) (P : ℤ) (lab : Fin a → S)
    (raw : ∀ (v : Site a (2^L)) k, m (Channels.point .left base v k)=
      Channels.result P (fun p => (lab p).val) .left w v k) (v : Site a (2^L)) (f : PairBits L) :
    m (src base v+pairAddress f:ℕ)=rawValue w P lab v f := by
  have h := raw (v.1,wordIndex L f.1,wordIndex L f.2) (v.2.1,v.2.2)
  simpa only [src,LeftSetup.raw,rawValue,Channels.point,Channels.result,Scatter.rev,Scatter.index,
    location,packed_val,pairCode_val,remote,Equiv.symm_apply_apply,Prod.mk.eta,pow_two,Nat.add_assoc] using h

theorem window_table_sizes {L : ℕ} (S : Finset (BasisLabel L)) :
    let n := 2^L
    (S.card*n)*(S.card*n) ≤ n^6 ∧ S.card*n*n*(n^2) ≤ n^6 ∧ S.card*n^4 ≤ n^6 ∧ S.card ≤ n^3 := by
  intro n
  have ca : S.card ≤ (4:ℕ)^L := by simpa [BasisLabel] using Finset.card_le_univ S
  have small : S.card ≤ n^2 := ca.trans_eq (length_eq L)
  have hn : 1 ≤ n := Nat.one_le_pow _ _ (by decide)
  have side : S.card*n ≤ n^3 := by simpa only [pow_succ] using Nat.mul_le_mul_right n small
  have sq := (Nat.mul_le_mul side side).trans_eq (pow_add n 3 3).symm
  have pane := (Nat.mul_le_mul_right (n^4) small).trans_eq (pow_add n 2 4).symm
  refine ⟨sq,?_,pane,small.trans (Nat.pow_le_pow_right hn (by decide))⟩
  simpa only [pow_succ,Nat.pow_zero,Nat.one_mul,Nat.mul_assoc] using pane

/-- Consume the complete first-stage left channel, using the physical label codes
and residuals created by the window scan, to materialize the short-by-short bank. -/
theorem window_runs {W M L base b c : ℕ} (hL : 0<L) (large : 512 ≤ base) (K : ℕ)
    (w : WeightKey (2^L) → ℚ) (cw : ChannelKey L → ℚ) (P : ℤ) (m : Memory)
    (ready : Preparation.Ready L K base (windowExpansion K L).labels.card b c w m)
    (cap : Graph.Division.Room W M) :
    let n := 2^L
    let S := (windowExpansion K L).labels
    let lab := (labelNumber S).symm
    let banks := Workspace.banks (MaskScan.Arena.slot base n 7+2) n
    banks.weights+n^2 ≤ M →
    (∀ (v : Site S.card n) k, m (Channels.point .left banks.transform v k)=
      Channels.result P (fun j => (lab j).val) .left cw v k) →
    ∃ t≤9+(S.card*n*n)*(LeftSetup.budget L S.card+17), ∃ o, Runs W (Batch.grid LeftSetup.job) m t o ∧
      frame (a:=S.card) (n:=n) banks.transform banks.left m o ∧
      ∀ v i, o (dst banks.left v i)=value K cw P lab v i := by
  intro n S lab banks space raw
  let codes := MaskScan.Arena.slot base n 5
  let scales := MaskScan.Arena.slot base n 6
  have h : Static L n S.card banks.transform banks.weights banks.left codes scales m :=
    ⟨ready.domain,ready.length,ready.params.size,ready.params.raw,ready.params.smallWork,ready.params.source,
      ready.params.codeBase,ready.params.coefficients⟩
  obtain ⟨sizeW,sizeR,_,n3⟩ := window_table_sizes S
  change (S.card*n)*(S.card*n) ≤ n^6 at sizeW
  change S.card*n*n*(n^2) ≤ n^6 at sizeR
  change S.card ≤ n^3 at n3
  apply collect hL S lab cw P m h (raw_of_channel cw P lab raw) (Labels.prepared_row ready.metadata)
  · dsimp [codes,scales,MaskScan.Arena.slot,MaskScan.Arena.origin]; omega
  · dsimp [codes,scales,banks,Workspace.banks,MaskScan.Arena.slot,MaskScan.Arena.span]; omega
  · change banks.left+(S.card*n)*(S.card*n) ≤ banks.transform
    dsimp [banks,Workspace.banks]; omega
  · change banks.transform+S.card*n*n*n^2 ≤ banks.weights
    dsimp [banks,Workspace.banks]; omega
  · exact cap
  · exact space

end VWZClique.IntegerRAM.Projected.LeftGrid
end

/- NativeProjectionChannelGrid -/
section
namespace VWZClique.IntegerRAM.Projected.Channels
open Structured BlockMM Grid Placement Scatter Projection WeightedProof UniformFolds

def outside (dst len work : ℕ) (m o : Memory) :=
  ∀ z : ℕ, z<work → ¬Batch.privateCell z → (z<dst ∨ dst+len≤z) → o z=m z

theorem entire {W M L b r a base sig pr work dst codeBase : ℕ}
    (S : Scheme b r) (hb : 2≤b) (hr : 0<r) (π : Equiv.Perm V) (E : Finset EdgeSlot) (ch : Channel)
    (lab : Fin a → BasisLabel L) (w : WeightKey (2^L)→ℚ) (hw : ∀ i, Binary (literal w (inputKey π E i)))
    (m : Memory) (hL : 0<L) (high : 380<dst) (extent : dst+a*(2^L)^4≤work)
    (cap : Graph.Division.Room W M)
    (space : work+4*(2^L*2^L)+BlockMM.WordLayout.space b r (BlockMM.depth b (2^L)) 1≤M)
    (codes : 380<codeBase ∧ codeBase+a≤dst) (counter : a*2^L*2^L≤M)
    (dim : m 0=((2^L:ℕ):ℤ)) (count : m 359=a) (codeHead : m 358=codeBase)
    (labelTable : ∀ p : Fin a, m ((codeBase+p.val:ℕ):ℤ)=(Butterfly.labelIndex L (lab p)).val)
    (read : ∀ (v : Site a (2^L)) (x : Memory), outside dst (a*(2^L)^4) work m x →
      x 353=(Butterfly.labelIndex L (lab v.1)).val → x 354=v.2.1.val → x 355=v.2.2.val → x 357=v.1.val →
      Small.Data (lab v.1) (remote v.2.1 v.2.2) w base sig pr work x ∧
      Scatter.Headers ch (remote v.2.1 v.2.2) work dst v.1.val a x) :
    let P := S.scale^(depth b (2^L))
    ∃ t≤cost S π E ch L a, ∃ o, Runs W (program S π E ch) m t o ∧
      outside dst (a*(2^L)^4) work m o ∧
      ∀ v k, o (point ch dst v k)=result P lab ch (fun i => literal w (inputKey π E i)) v k := by
  intro P
  let n := 2^L
  let width := a*n^4
  let preserve : ℕ→Memory→Prop := fun _ => outside dst width work m
  have ht : work≤M := by omega
  have npos : 0<n := by dsimp [n];positivity
  have nM : n≤M := by
    have grow := Nat.mul_le_mul_left n npos
    change work+4*(n*n)+_≤M at space;omega
  have bounds (v : Site a n) (k : Fin n × Fin n) : dst≤point ch dst v k ∧ point ch dst v k<dst+width :=
    ⟨Nat.le_add_right _ _,Nat.add_lt_add_left (location_lt ch v k) _⟩
  have wd : dst+width≤work := extent
  have ctrlLock {j : ℤ} (locked : Batch.locked j) : ∃ k : ℕ, j=k ∧ k≤366 := by
    dsimp [Batch.locked,Batch.labels,Batch.labelCount,Batch.clock,Batch.slab] at locked
    exact ⟨j.toNat,by omega,by omega⟩
  apply Grid.collect (b:=codeBase) (n:=n) npos cap nM (by omega) counter (job S π E ch) preserve
    (fun p => ((Butterfly.labelIndex L (lab p)).val:ℤ)) (point ch dst) (result P lab ch (fun i => literal w (inputKey π E i)))
  · intro i x y frame prev z hz clean range
    exact (frame z clean).trans (prev z hz clean range)
  · intro v k; have h := (bounds v k).1;unfold Batch.privateCell;omega
  · intro i x prev p
    have r := p.isLt
    exact (prev _ (by omega) (by unfold Batch.privateCell;omega) (Or.inl (by omega))).trans (labelTable p)
  · exact dim
  · exact count
  · exact codeHead
  · exact fun _ _ _ _ => rfl
  · intro v x old id row col ix
    obtain ⟨D,H⟩ := read v x old id row col ix
    obtain ⟨t,cost,y,run,wrote,fix⟩ := job_runs S hb hr π E ch v lab w hw x D H hL high extent cap space
    refine ⟨t,cost,y,run,?_,wrote,?_,?_⟩
    · intro z hz clean range
      exact (fix z hz (fun k => by have limits := bounds v k;omega)).trans (old z hz clean range)
    · intro u before k
      apply fix _ (by have := (bounds u k).2;omega)
      intro k' same
      have locEq : location ch u k=location ch v k' := Nat.add_left_cancel same
      have eq := different ch locEq
      exact before.ne (congrArg Grid.serial eq)
    · intro j locked
      obtain ⟨k,rfl,hk⟩ := ctrlLock locked
      exact fix k (by omega) (fun i => by have := (bounds v i).1;omega)

end VWZClique.IntegerRAM.Projected.Channels
end

/- NativeProjectionSmallContext -/
section
namespace VWZClique.IntegerRAM.Projected.SmallContext
open UniformFolds RankSwap Grid Placement Scatter

def start (base L : ℕ) := MaskScan.Arena.slot base (2^L) 7+2
def banks (base L : ℕ) := Workspace.banks (start base L) (2^L)
def sig (base L : ℕ) := Workspace.level (start base L) L
def codeBase (base L : ℕ) := MaskScan.Arena.slot base (2^L) 5
def dest (base L : ℕ) : Channel → ℕ
  | .left => (banks base L).transform
  | .middle => (banks base L).middle
  | .right => (banks base L).right

structure Bounds (K L base : ℕ) (ch : Channel) : Prop where
  left_le : (banks base L).left ≤ dest base L ch
  extent : dest base L ch + (windowExpansion K L).labels.card*(2^L)^4 ≤ (banks base L).weights
  high : 512 ≤ dest base L ch
  codeHigh : 380 < codeBase base L
  codeEnd : codeBase base L+(windowExpansion K L).labels.card ≤ (banks base L).left
  counter : (windowExpansion K L).labels.card*2^L*2^L ≤ (banks base L).weights
  left_work : (banks base L).left ≤ (banks base L).weights

theorem geometry {K L base : ℕ} (large : 512 ≤ base) (ch : Channel) : Bounds K L base ch := by
  let n := (2:ℕ)^L
  let a := (windowExpansion K L).labels.card
  have hn : 1 ≤ n := Nat.one_le_pow _ _ (by decide)
  have ha : a ≤ n^2 := by
    have c : a ≤ (4:ℕ)^L := by simpa [a,BasisLabel] using Finset.card_le_univ (windowExpansion K L).labels
    exact c.trans_eq (by dsimp [n];rw [show (4:ℕ)=2^2 by decide,←pow_mul,←pow_mul,Nat.mul_comm 2 L])
  have h4 : a*n^4 ≤ n^6 := (Nat.mul_le_mul_right (n^4) ha).trans_eq (pow_add n 2 4).symm
  have h2 : n^2 ≤ n^3 := Nat.pow_le_pow_right hn (by decide)
  have h24 : n^2 ≤ n^4 := Nat.pow_le_pow_right hn (by decide)
  have hut : a*n*n ≤ n^6 := by
    rw [Nat.mul_assoc,←pow_two]
    exact (Nat.mul_le_mul_left a h24).trans h4
  dsimp only [a,n] at ha h4 h2 hut
  cases ch <;> constructor <;>
    dsimp only [dest,banks,start,codeBase,Workspace.banks,MaskScan.Arena.slot,MaskScan.Arena.origin,MaskScan.Arena.span] <;>
    omega

/-- Every operand used by a small multiplication is already present in the
prepared memory. Only the current label and its two free coordinates change
across grid sites. -/
theorem read {K L base b c : ℕ} {w : WeightKey (2^L) → ℚ} {m : Memory}
    (ready : Preparation.Ready L K base (windowExpansion K L).labels.card b c w m)
    (large : 512 ≤ base) (ch : Channel) (v : Site (windowExpansion K L).labels.card (2^L)) (x : Memory)
    (keep : ∀ z : ℕ, z < (banks base L).left → ¬Batch.privateCell z → x z=m z)
    (id : x 353=(Butterfly.labelIndex L ((labelNumber (windowExpansion K L).labels).symm v.1).val).val)
    (row : x 354=v.2.1.val) (col : x 355=v.2.2.val) (pos : x 357=v.1.val) :
    let j := ((labelNumber (windowExpansion K L).labels).symm v.1).val
    let f := remote v.2.1 v.2.2
    Small.Data j f w base (sig base L) (sig base L+8^L) (banks base L).weights x ∧
      Scatter.Headers ch f (banks base L).weights (dest base L ch) v.1.val (windowExpansion K L).labels.card x := by
  intro j f
  have r := ready.transfer large keep
  have geom := geometry (K:=K) (L:=L) large ch
  have wr := geom.left_work
  have dw : dest base L ch ≤ (banks base L).weights := (Nat.le_add_right _ _).trans geom.extent
  have high := geom.high
  have bs : base+9*2^L+81*(2^L*2^L) ≤ start base L := by
    dsimp [start,MaskScan.Arena.slot,MaskScan.Arena.origin];rw [pow_two];omega
  have sg : start base L ≤ sig base L := Workspace.level_lo _ _
  have sl : sig base L+2*8^L ≤ (banks base L).left := Workspace.support_prefix _ _
  have f0 : x 354=(wordIndex L f.1).val := by simpa [f,remote] using row
  have f1 : x 355=(wordIndex L f.2).val := by simpa [f,remote] using col
  have lim (u : Bits L) : (wordIndex L u).val*4^L+(Butterfly.labelIndex L j).val < 8^L := by
    have eq : (2^L:ℕ)*4^L=8^L := by rw [←Nat.mul_pow]
    have h := Nat.mul_le_mul_right (4^L) (Nat.succ_le_of_lt (wordIndex L u).isLt)
    rw [Nat.succ_mul] at h
    have hl := (Butterfly.labelIndex L j).isLt
    omega
  refine ⟨⟨by omega,r.domain,r.params.weights,r.signBase,r.partnerBase,id,f0,f1,r.params.smallWork,?_,?_,?_⟩,
    ⟨r.domain,r.length,r.params.smallWork,?_,pos,r.params.size,f0,f1⟩⟩
  · intro k
    have pos : Factors.keyIndex k < 9*2^L+81*(2^L*2^L) := NativeLeaf.index_lt k
    exact ⟨by omega,r.weights k⟩
  · intro u
    exact ⟨by have := lim u;omega,r.banks.signs j u⟩
  · intro u
    exact ⟨by have := lim u;omega,r.banks.partners j u⟩
  · cases ch with
    | left => exact r.params.raw
    | middle => exact r.params.middle
    | right => exact r.params.right

end VWZClique.IntegerRAM.Projected.SmallContext
end

/- NativeProjectionThree -/
section
namespace VWZClique.IntegerRAM.Projected.Dense
open Structured BlockMM Scatter Grid UniformFolds Projection WeightedProof

noncomputable def label {L} (K : ℕ) (p : Fin (labelSet K L).card) : BasisLabel L :=
  ((labelNumber (labelSet K L)).symm p).val

def fixed (base L z : ℕ) := z<(Bank base L).left ∧ ¬Batch.privateCell z

noncomputable def array {L K : ℕ} (base : ℕ) (ch : Channel) (P : ℤ) (cw : ChannelKey L→ℚ) (m : Memory) :=
  ∀ (v : Site (labelSet K L).card (2^L)) (k : Fin (2^L) × Fin (2^L)),
    m (Channels.point ch (SmallContext.dest base L ch) v k)=Channels.result P (label K) ch cw v k

theorem «prefix» {base L : ℕ} (large : 512≤base) (z : ℕ) (h : projectionPrefix base (2^L) z) : fixed base L z := by
  have p : base+9*(2^L)+81*((2^L)*(2^L)) ≤ (Bank base L).left := by
    dsimp [Bank,Workspace.banks,MaskScan.Arena.slot,MaskScan.Arena.origin]
    rw [pow_two];omega
  dsimp [projectionPrefix,NativeArena.metaBase,NativeArena.tableWords] at h
  exact ⟨by omega,by dsimp [Batch.privateCell];omega⟩

theorem channel_run {W M L K b r c base : ℕ} (S : Scheme b r) (hb : 2≤b) (hr : 0<r)
    (π : Equiv.Perm V) (E : Finset EdgeSlot) (ch : Channel) (w : WeightKey (2^L)→ℚ)
    (hw : ∀i, Binary (literal w (inputKey π E i))) (m : Memory) (hL : 0<L) (large : 512≤base)
    (ready : Preparation.Ready L K base (labelSet K L).card b c w m)
    (cap : Graph.Division.Room W M)
    (space : (Bank base L).weights+4*(2^L*2^L)+WordLayout.space b r (depth b (2^L)) 1≤M) :
    let a := (labelSet K L).card
    let p := S.scale^(depth b (2^L))
    let dst := SmallContext.dest base L ch
    ∃f≤Channels.cost S π E ch L a, ∃o, Runs W (Channels.program S π E ch) m f o ∧
      Preparation.Ready L K base a b c w o ∧ array (K:=K) base ch p (fun i => literal w (inputKey π E i)) o ∧
      Channels.outside dst (a*(2^L)^4) (Bank base L).weights m o := by
  intro a p dst
  let l := Bank base L
  have g := SmallContext.geometry (K:=K) (L:=L) large ch
  have below (x : Memory) (pres : Channels.outside dst (a*(2^L)^4) l.weights m x) :
      ∀z : ℕ, z<l.left → ¬Batch.privateCell z → x z=m z := by
    intro z hz clean
    have lo : l.left≤dst := g.left_le
    have hi : dst+a*(2^L)^4≤l.weights := g.extent
    exact pres z (by omega) clean (Or.inl (by omega))
  have counter : a*(2^L)*(2^L)≤M := g.counter.trans (by change l.weights≤M;change l.weights+_+_≤M at space;omega)
  have cRange : SmallContext.codeBase base L+a≤dst := g.codeEnd.trans g.left_le
  obtain ⟨t,tc,o,go,fr,rows⟩ := Channels.entire S hb hr π E ch (label K) w hw m hL
    (by have := g.high;omega : 380<dst) g.extent cap space ⟨g.codeHigh,cRange⟩ counter
    ready.domain ready.params.size ready.params.codeBase
    (fun i => (Labels.prepared_row ready.metadata i).1)
    (fun v x pre id row col ix => SmallContext.read ready large ch v x (below x pre) id row col ix)
  exact ⟨t,tc,o,go,ready.transfer large (below o fr),rows,fr⟩

theorem three_runs {W M L K b r c base : ℕ} (S : Scheme b r) (hb : 2≤b) (hr : 0<r)
    (π : Equiv.Perm V) (E : Finset EdgeSlot) (w : WeightKey (2^L)→ℚ)
    (hw : ∀i, Binary (literal w (inputKey π E i))) (m : Memory) (hL : 0<L) (large : 512≤base)
    (ready : Preparation.Ready L K base (labelSet K L).card b c w m)
    (cap : Graph.Division.Room W M)
    (space : (Bank base L).weights+4*(2^L*2^L)+WordLayout.space b r (depth b (2^L)) 1≤M) :
    let a := (labelSet K L).card
    let p := S.scale^(depth b (2^L))
    let cw := fun i => literal w (inputKey π E i)
    ∃f≤threeCost S π E L a, ∃o, Runs W (three S π E) m f o ∧
      Preparation.Ready L K base a b c w o ∧
      (∀ch, array (K:=K) base ch p cw o) ∧
      ∀ z : ℕ, projectionPrefix base (2^L) z → o z=m z := by
  intro a p cw
  let l := Bank base L
  let n := 2^L
  obtain ⟨t,tb,x,middle,xready,B,bframe⟩ := channel_run S hb hr π E .middle w hw m hL large ready cap space
  obtain ⟨u,ub,y,right,yready,C,cframe⟩ := channel_run S hb hr π E .right w hw x hL large xready cap space
  obtain ⟨h,hbnd,o,left,ordy,A,aframe⟩ := channel_run S hb hr π E .left w hw y hL large yready cap space
  have G := SmallContext.geometry (L:=L) (K:=K) large Channel.left
  have aBound : a*n^4≤n^6 := by
    have hh : a≤n^2 := by
      have count : a≤4^L := by simpa [a,labelSet,BasisLabel] using Finset.card_le_univ (labelSet K L)
      exact count.trans_eq (by dsimp [n];rw [←pow_mul,Nat.mul_comm,pow_mul];rfl)
    exact (Nat.mul_le_mul_right (n^4) hh).trans_eq (by ring)
  have cut : l.middle+a*n^4≤l.right ∧ l.right+a*n^4≤l.transform ∧ l.transform≤l.weights := by
    dsimp [l,Bank,Workspace.banks,n] at *;omega
  have mid : 380<l.middle := by have h : 512≤l.middle := (SmallContext.geometry (L:=L) (K:=K) large Channel.middle).high;omega
  have deep (ch : Channel) : l.left≤SmallContext.dest base L ch := (SmallContext.geometry (L:=L) (K:=K) large ch).left_le
  have fr {ch : Channel} {old new : Memory} (f : Channels.outside (SmallContext.dest base L ch) (a*n^4) l.weights old new)
      (z : ℕ) (hz : projectionPrefix base n z) : new z=old z := by
    obtain ⟨lo,clean⟩ := Dense.prefix large z hz
    change z<l.left at lo
    have lo' : l.left≤SmallContext.dest base L ch := deep ch
    have hi := (SmallContext.geometry (K:=K) (L:=L) large ch).extent
    exact f z (by change _≤l.weights at hi;omega) clean (Or.inl (by omega))
  refine ⟨_,Nat.add_le_add tb (Nat.add_le_add ub hbnd),o,.seq middle (.seq right left),ordy,?_,
    fun z hz => (fr aframe z hz).trans ((fr cframe z hz).trans (fr bframe z hz))⟩
  intro ch
  cases ch with
  | left => exact A
  | middle =>
    intro v k
    let t := Channels.point .middle l.middle v k
    have h : l.middle≤t ∧ t<l.middle+a*n^4 := ⟨Nat.le_add_right _ _,Nat.add_lt_add_left (Placement.location_lt .middle v k) _⟩
    have clean : ¬Batch.privateCell t := by dsimp [Batch.privateCell];omega
    have t0 : t<l.weights := by omega
    have r0 : t<l.right := by omega
    have a0 : t<l.transform := by omega
    exact (aframe t t0 clean (Or.inl a0)).trans ((cframe t t0 clean (Or.inl r0)).trans (B v k))
  | right =>
    intro v k
    let t := Channels.point .right l.right v k
    have h : l.right≤t ∧ t<l.right+a*n^4 := ⟨Nat.le_add_right _ _,Nat.add_lt_add_left (Placement.location_lt .right v k) _⟩
    have clean : ¬Batch.privateCell t := by dsimp [Batch.privateCell];omega
    have t0 : t<l.weights := by omega
    have a0 : t<l.transform := by omega
    exact (aframe t t0 clean (Or.inl a0)).trans (C v k)

end VWZClique.IntegerRAM.Projected.Dense
end

/- NativeProjectionMaterialized -/
section
namespace VWZClique.IntegerRAM.Projected.LeftGrid
open UniformFolds TraceDyadic Structured Grid Placement Scatter

/-- Starting with the three scattered grids, perform the second left transform
and certify all dense matrix operands together in the resulting word memory. -/
theorem materialized_sources {W M L K b c base : ℕ} (hL : 0<L) (large : 512 ≤ base) (q : ℕ)
    (w : WeightKey (2^L) → ℚ) (cw : ChannelKey L → ℚ) (P : ℤ) (m : Memory)
    (ready : Preparation.Ready L K base (Dense.labelSet K L).card b c w m)
    (all : ∀ ch, Dense.array (K:=K) base ch P cw m) (room : Graph.Division.Room W M)
    (space : (Dense.Bank base L).weights+(2^L)^2 ≤ M) :
    let n := 2^L
    let S := Dense.labelSet K L
    let l := Large.workspaceBanks (MaskScan.Arena.slot base n 7+2) n
    ∃ t≤9+(S.card*n*n)*(LeftSetup.budget L S.card+17), ∃ o, Runs W (Batch.grid LeftSetup.job) m t o ∧
      Preparation.Ready L K base S.card b c w o ∧
      Large.Sources o l (scaleMat P (shortWeight S K cw)) (scaleMat P (middle S q cw))
        (scaleMat P (Projected.right S q cw)) ∧
      ∀ z : ℕ, projectionPrefix base n z → o z=m z := by
  intro n S l
  let B := Dense.Bank base L
  let a := S.card
  have sq := window_table_sizes S
  change (a*n)*(a*n)≤n^6 ∧ _ ∧ a*n^4≤n^6 ∧ _ at sq
  have bounds : B.left+(a*n)*(a*n) ≤ B.middle ∧ B.middle+a*n^4 ≤ B.right ∧
      B.right+a*n^4 ≤ B.transform ∧ B.middle ≤ B.right := by
    dsimp only [B,Dense.Bank,Workspace.banks]
    dsimp only [n] at sq ⊢
    omega
  have start : 512 ≤ B.left := by
    dsimp only [B,Dense.Bank,Workspace.banks,MaskScan.Arena.slot,MaskScan.Arena.origin]
    omega
  obtain ⟨t,ht,o,run,fr,vals⟩ := window_runs hL large K w cw P m ready room space (all .left)
  have low (z : ℕ) (hz : z < B.left) (clean : ¬Batch.privateCell z) : o z=m z :=
    fr z (by change z < B.transform; omega) clean (fun v i =>
      Nat.ne_of_lt (hz.trans_le (dst_bounds B.left v i).1))
  have sameData (z : ℕ) (lo : B.middle ≤ z) (hi : z < B.transform) : o z=m z :=
    fr z hi (outside_private (by omega)) (fun v i => (lt_of_lt_of_le ((dst_bounds B.left v i).2.trans_le bounds.1) lo).ne')
  refine ⟨t,ht,o,run,ready.transfer large low,?_,?_⟩
  · apply Channels.dense_sources S K q cw P l o
    · intro p z v i
      have h := vals (p,z,v) i
      simpa only [destination,value,Nat.add_assoc,l,Large.workspaceBanks,n,S,Dense.labelSet] using h
    · intro v k
      let j := Channels.point .middle B.middle v k
      have range : B.middle ≤ j ∧ j < B.middle+a*n^4 :=
        ⟨Nat.le_add_right _ _,Nat.add_lt_add_left (location_lt .middle v k) _⟩
      exact (sameData j range.1 (by omega)).trans (all .middle v k)
    · intro v k
      let j := Channels.point .right B.right v k
      have range : B.right ≤ j ∧ j < B.right+a*n^4 :=
        ⟨Nat.le_add_right _ _,Nat.add_lt_add_left (location_lt .right v k) _⟩
      exact (sameData j (bounds.2.2.2.trans range.1) (range.2.trans_le bounds.2.2.1)).trans (all .right v k)
  · intro z hz
    obtain ⟨lo,clean⟩ := Dense.«prefix» large z hz
    exact low z lo clean

end VWZClique.IntegerRAM.Projected.LeftGrid
end

/- NativeProjectionDense -/
section
namespace VWZClique.IntegerRAM.Projected.Dense
open Structured BlockMM Projection UniformFolds WeightedProof Double

/-- Materialize all three scaled dense channel matrices using the actual
conditional control loops, small square multiplication, and left butterfly. -/
theorem verifiedPublicationStep {W M L K b r c base : ℕ} (S : Scheme b r) (hb : 2≤b) (hr : 0<r)
    (π : Equiv.Perm V) (E : Finset EdgeSlot) (q : ℕ) (w : WeightKey (2^L)→ℚ)
    (hw : ∀i, Binary (literal w (inputKey π E i))) (m : Memory) (hL : 0<L) (large : 512≤base)
    (ready : Preparation.Ready L K base (labelSet K L).card b c w m)
    (room : Graph.Division.Room W M)
    (space : (Bank base L).weights+4*(2^L*2^L)+WordLayout.space b r (depth b (2^L)) 1≤M) :
    let labels := labelSet K L
    let P := S.scale^(depth b (2^L))
    let cw := fun i => literal w (inputKey π E i)
    let banks := Large.workspaceBanks (MaskScan.Arena.slot base (2^L) 7+2) (2^L)
    ∃t≤cost S π E L labels.card, ∃o, Runs W (code S π E) m t o ∧
      Preparation.Ready L K base labels.card b c w o ∧
      Large.Sources o banks (scaleMat P (shortWeight labels K cw)) (scaleMat P (middle labels q cw))
        (scaleMat P (Projected.right labels q cw)) ∧ ∀z : ℕ, projectionPrefix base (2^L) z → o z=m z := by
  intro labels P cw banks
  obtain ⟨f,cf,x,go,r,all,fr⟩ := three_runs S hb hr π E w hw m hL large ready room space
  obtain ⟨g,cg,o,done,post,values,keep⟩ := LeftGrid.materialized_sources hL large q w cw P x r all room
    (by rw [pow_two];omega)
  exact ⟨_,Nat.add_le_add cf cg,o,.seq go done,post,values,fun z h => (keep z h).trans (fr z h)⟩

end VWZClique.IntegerRAM.Projected.Dense
end

open VWZClique VWZClique.IntegerRAM VWZClique.IntegerRAM.Structured VWZClique.IntegerRAM.Projected VWZClique.BlockMM VWZClique.Projection VWZClique.UniformFolds VWZClique.WeightedProof VWZClique.Double
theorem solution {W M L K b r c base : ℕ} (S : Scheme b r) (hb : 2≤b) (hr : 0<r)
    (π : Equiv.Perm V) (E : Finset EdgeSlot) (q : ℕ) (w : WeightKey (2^L)→ℚ)
    (hw : ∀i, Binary (literal w (inputKey π E i))) (m : Memory) (hL : 0<L) (large : 512≤base)
    (ready : Preparation.Ready L K base (Dense.labelSet K L).card b c w m)
    (room : Graph.Division.Room W M)
    (space : (Dense.Bank base L).weights+4*(2^L*2^L)+WordLayout.space b r (depth b (2^L)) 1≤M) :
    let labels := Dense.labelSet K L
    let P := S.scale^(depth b (2^L))
    let cw := fun i => literal w (inputKey π E i)
    let banks := Large.workspaceBanks (MaskScan.Arena.slot base (2^L) 7+2) (2^L)
    ∃t≤Dense.cost S π E L labels.card, ∃o, Runs W (Dense.code S π E) m t o ∧
      Preparation.Ready L K base labels.card b c w o ∧
      Large.Sources o banks (scaleMat P (shortWeight labels K cw)) (scaleMat P (middle labels q cw))
        (scaleMat P (Projected.right labels q cw)) ∧ ∀z : ℕ, projectionPrefix base (2^L) z → o z=m z
  := @VWZClique.IntegerRAM.Projected.Dense.verifiedPublicationStep W M L K b r c base S hb hr π E q w hw m hL large ready room space
