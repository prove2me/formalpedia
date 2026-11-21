-- Prove2me | solution 1 for VWZClique.IntegerRAM.Projected.Preparation.run
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T14:07:07.933011+00:00
-- url     : https://prove2.me/submissions/168e9e0c-d96d-4a09-9d00-f9e36790bebc

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

set_option maxHeartbeats 1600000

attribute [local simp] Reg.p0 Reg.p1 Reg.p2 Reg.p3 Reg.dest Reg.x0 Reg.x1 Reg.x2 Reg.x3
  Reg.sum Reg.diff Reg.count Reg.srcBase Reg.dstBase Reg.stride Reg.one Reg.zero Reg.stages Reg.swap

end VWZClique.IntegerRAM.Butterfly
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

structure Controls (N codeBase valBase i r : ℕ) (m : Memory) : Prop where
  index : m idx=i
  limit : m lim=N
  one : m unit=1
  p : m outC=((codeBase+r:ℕ):ℤ)
  v : m outV=((valBase+r:ℕ):ℤ)

/-- The classifier's scratch can be changed between iterations; specify its
persistent tables via inv. The append and loop-control steps only alter their
reserved registers and the two next output cells. -/
def privateCell (z : ℤ) := z=idx ∨ z=lim ∨ z=unit ∨ z=test ∨ z=outC ∨ z=outV

theorem append_run {W N c v i r : ℕ} (m : Memory) (cs : Controls N c v i r m)
    (apart : c+r ≠ v+r) (fc : Fits W ((c+r:ℕ):ℤ)) (fv : Fits W ((v+r:ℕ):ℤ)) :
    ∃ y, Runs W (line appendRow) m 4 y ∧ Controls N c v i (r+1) y ∧
      ∀ z : ℤ, z≠outC → z≠outV → y z =
        if z=((v+r:ℕ):ℤ) then m value else if z=((c+r:ℕ):ℤ) then (i:ℤ) else m z := by
  have nonnegC : 0 ≤ m outC := by rw [cs.p]; omega
  have nonnegV : 0 ≤ m outV := by rw [cs.v]; omega
  have different (z : ℤ) (hz : z<0) : z≠m outC ∧ z≠m outV := by omega
  have ao : outV ≠ ((c+r:ℕ):ℤ) := by dsimp [outV]; omega
  have av : value ≠ ((c+r:ℕ):ℤ) := by dsimp [value]; omega
  have run := line_runs (W:=W) appendRow m (by
    simp only [appendRow,safeLine,safe,effect,update,if_neg (different outV (by decide)).1,cs.p,cs.v,if_neg ao,fc,fv,and_self,true_and,and_true])
  refine ⟨_,run,?_,?_⟩
  · constructor <;> simp only [appendRow,List.foldl,effect,update] <;>
      simp (disch := omega) [different,idx,lim,unit,outC,outV,cs.index,cs.limit,cs.one,cs.p,cs.v] at * <;> omega
  · intro z h₁ h₂
    simp only [appendRow,List.foldl,effect,update,if_neg h₁,if_neg h₂,
      if_neg (different outV (by decide)).1,if_neg (different value (by decide)).1,cs.p,cs.v,if_neg ao,if_neg av,cs.index]

/-- Scan every numeric code once and emit the survivors in increasing order.
Both resulting pointers encode the returned count. The specification also
preserves an arbitrary client invariant, for example auxiliary digit tables. -/
theorem scan_runs {W N c v K : ℕ} (positive : 0<N) (separate : c+N≤v)
    (fits : ∀ j<N, Fits W ((c+j:ℕ):ℤ) ∧ Fits W ((v+j:ℕ):ℤ))
    (guard : ∀ j≤N, Fits W ((j:ℤ)-N)) (keep : ℕ → Bool) (val : ℕ → ℤ)
    (I : ℕ → Memory → Prop) (cl : Command)
    (classRun : ∀ j<N, ∀ m, I j m → Controls N c v j (rank keep j) m →
      ∃ f≤K, ∃ x, Runs W cl m f x ∧ Controls N c v j (rank keep j) x ∧
        (0 ≤ x flag ↔ keep j=true) ∧ Fits W (x flag) ∧ x value=val j ∧ I (j+1) x ∧
        (∀ a<rank keep j, x (c+a:ℕ)=m (c+a:ℕ) ∧ x (v+a:ℕ)=m (v+a:ℕ)))
    (stable : ∀ j<N, ∀ x y, I (j+1) x →
        (∀ z : ℤ, ¬privateCell z → z≠((c+rank keep j:ℕ):ℤ) → z≠((v+rank keep j:ℕ):ℤ) → y z=x z) → I (j+1) y)
    {m : Memory} (init : I 0 m) (ctrl : Controls N c v 0 0 m) :
    ∃ f≤N*(K+8), ∃ y, Runs W (scan cl) m f y ∧ I N y ∧
      Controls N c v N (rank keep N) y ∧ ∀ j<N, keep j=true →
        y (c+rank keep j:ℕ)=j ∧ y (v+rank keep j:ℕ)=val j := by
  let inv := fun j (x : Memory) => I j x ∧ Controls N c v j (rank keep j) x ∧
    ∀ a<j, keep a=true → x (c+rank keep a:ℕ)=a ∧ x (v+rank keep a:ℕ)=val a
  have initial : inv 0 m := ⟨init,ctrl,by omega⟩
  have tickData (x : Memory) (j : ℕ) (a : ℤ) (h₁ : a≠idx) (h₂ : a≠test) :
      nextMemory x idx test j N a=x a := by simp [nextMemory,update,h₁,h₂]
  have step (j : ℕ) (hj : j<N) (x : Memory) (hx : inv j x) :
      ∃ f, f≤K+5 ∧ ∃ y, Runs W (scanBody cl) x f y ∧
        y idx=(j:ℤ) ∧ y unit=1 ∧ y lim=(N:ℤ) ∧ inv (j+1) (nextMemory y idx test j N) := by
    obtain ⟨old,ctl,previous⟩ := hx
    obtain ⟨f,hf,o,run,hc,sel,testfit,vv,next,past⟩ := classRun j hj x old ctl
    let r := rank keep j
    have rlt : r<N := Nat.lt_of_le_of_lt (rank_le keep j) hj
    have rdC : c+r<v := by omega
    have retain (z : ℤ) (hz : ¬privateCell z) : z≠idx ∧ z≠test ∧ z≠outC ∧ z≠outV := by
      unfold privateCell at hz; grind
    have finish (y : Memory) (rr : ℕ) (ctrlY : Controls N c v j rr y) :
        Controls N c v (j+1) rr (nextMemory y idx test j N) := by
      constructor <;> simp [nextMemory,update,idx,test,lim,outC,outV,unit,Nat.cast_add,
        ctrlY.limit,ctrlY.one,ctrlY.p,ctrlY.v] at *
    by_cases h : keep j=true
    · have rnext : rank keep (j+1)=r+1 := by simp [rank,h,r]
      obtain ⟨y,ap,yc,mem⟩ := append_run o hc (by omega) (fits r rlt).1 (fits r rlt).2
      refine ⟨_,by omega,y,.seq run (.guard_take testfit (by have := sel.mpr h; omega) ap),
        yc.index,yc.one,yc.limit,stable j hj o _ next ?_,rnext ▸ finish y _ yc,?_⟩
      · intro z hz h₁ h₂
        obtain ⟨i,t,a,b⟩ := retain z hz
        rw [tickData _ _ _ i t,mem _ a b,if_neg h₂,if_neg h₁]
      · intro a ha hs
        have cr := mem ((c+rank keep a:ℕ):ℤ) (by dsimp [outC]; omega) (by dsimp [outV]; omega)
        have vr := mem ((v+rank keep a:ℕ):ℤ) (by dsimp [outC]; omega) (by dsimp [outV]; omega)
        simp only [Nat.cast_add] at cr vr ⊢
        rw [tickData _ _ _ (by dsimp [idx]; omega) (by dsimp [test]; omega),cr,
          tickData _ _ _ (by dsimp [idx]; omega) (by dsimp [test]; omega),vr]
        by_cases eq : a=j
        · subst a
          have nc : (c:ℤ)≠v := by omega
          simp [vv,nc]
        · have small : rank keep a<r := rank_strict (by omega) hs
          obtain ⟨l,r'⟩ := past _ small
          obtain ⟨cl',vl'⟩ := previous a (by omega) hs
          simp only [Nat.cast_add] at l r' cl' vl'
          have sm := small
          dsimp [r] at sm
          grind
    · have rnext : rank keep (j+1)=r := by simp [rank,h,r]
      refine ⟨_,by omega,o,.seq run (.guard_skip testfit (by have := mt sel.mp h; omega)),
        hc.index,hc.one,hc.limit,stable j hj o _ next ?_,rnext ▸ finish o _ hc,?_⟩
      · intro z hz _ _; exact tickData _ _ _ (retain _ hz).1 (retain _ hz).2.1
      · intro a ha hs
        have lt : a<j := by
          by_cases e : a=j
          · subst a; contradiction
          · omega
        obtain ⟨l,r'⟩ := past _ (rank_strict lt hs)
        obtain ⟨cl',vl'⟩ := previous a lt hs
        rw [tickData _ _ _ (by dsimp [idx]; omega) (by dsimp [test]; omega),l,cl',
          tickData _ _ _ (by dsimp [idx]; omega) (by dsimp [test]; omega),r',vl']
        exact ⟨rfl,rfl⟩
  obtain ⟨f,b,y,run,last⟩ := repeatN_runs (B:=K+5) positive _ (by decide : lim≠idx) inv guard step initial
  exact ⟨f,by simpa only [Nat.add_assoc] using b,y,run,last⟩

end VWZClique.IntegerRAM.MaskScan
end

/- WordGraph -/
section
/-! Native row-major graph reads and grouped input tests for the clique word RAM. -/

namespace VWZClique.IntegerRAM.Graph
open Structured BlockReduction Classical
open TrulySubcubicAPSP

/-- Within a test the scratch cells are -1 through -4. Every graph cell and every digit register
outside that interval survives a weight test. -/
def Protected (a : ℤ) : Prop := a ≤ -5 ∨ 0 ≤ a

def Frame (m out : Memory) : Prop := ∀ a, Protected a → out a = m a

theorem Frame.trans {a b c : Memory} (ab : Frame a b) (bc : Frame b c) : Frame a c :=
  fun i hi => (bc i hi).trans (ab i hi)

theorem Frame.write (m : Memory) {r : ℤ} (hr : -5 < r ∧ r < 0) (v : ℤ) :
    Frame m (update m r v) := by
  intro i hi
  have hd : i ≠ r := by rcases hi with h|h <;> omega
  simp [update,hd]

namespace Reg
end Reg

end VWZClique.IntegerRAM.Graph
end

/- WordGraphDivide -/
section
/-! Repeated subtraction for radix decoding. It uses one graph-order cell and
four negative cells, with a time linear in the quotient. A blocked input table
can afford linear work per packed key. -/

namespace VWZClique.IntegerRAM.Graph
open Structured BlockReduction

namespace Division

def state (m : Memory) (z q s : ℤ) : Memory :=
  update (update (update m num z) quot q) test s

theorem state_frame (m : Memory) (z q s : ℤ) : Frame m (state m z q s) :=
  ((Frame.write _ (by decide : -5 < num ∧ num < 0) _).trans
    (Frame.write _ (by decide : -5 < quot ∧ quot < 0) _)).trans
    (Frame.write _ (by decide : -5 < test ∧ test < 0) _)

theorem state_num (m : Memory) (z q s : ℤ) : state m z q s num = z := by
  simp [state,update,num,quot,test]

theorem state_quot (m : Memory) (z q s : ℤ) : state m z q s quot = q := by
  simp [state,update,quot,test]

theorem state_test (m : Memory) (z q s : ℤ) : state m z q s test = s := by
  simp [state,update]

theorem body_runs {W : ℕ} (m : Memory) (ho : m one=1) :
    Runs W body m 4 (state m (m num-m 0) (m quot+1) (m 0-(m num-m 0)-1)) := by
  let m₁ := update m num (m num-m 0)
  let m₂ := update m₁ quot (m₁ quot + m₁ one)
  let m₃ := update m₂ test (m₂ 0-m₂ num)
  let m₄ := update m₃ test (m₃ test-m₃ one)
  have run : Runs W body m 4 m₄ :=
    Runs.seq (t:=3) (.atom (.sub _ _ _ _))
      (.seq (t:=2) (.atom (.add _ _ _ _)) (.seq (.atom (.sub _ _ _ _)) (.atom (.sub _ _ _ _))))
  convert run using 1
  funext p
  by_cases h : p=test <;> simp [h,m₄,m₃,m₂,m₁,state,update,num,quot,test,one] at *
  all_goals simp [←ho]

/-- Execute exactly q positive subtraction rounds, starting with q*n+r.
The quotient register can already contain an arbitrary accumulator. -/
theorem loop_runs {W M n r : ℕ} (cap : Room W M) (hnM : n ≤ M) (hr : r<n)
    (q : ℕ) (hq : 0<q) (ha : q*n+r ≤ M) (m : Memory)
    (dn : m 0 = n) (ho : m one=1) (hn : m num = ((q*n+r:ℕ):ℤ)) :
    ∃ out, Runs W loop m (5*q) out ∧ Frame m out ∧ out num = r ∧ out quot = m quot+q := by
  induction q generalizing m with
  | zero => omega
  | succ q ih =>
    let v : ℤ := ((q*n+r:ℕ):ℤ)
    let d : ℤ := (n:ℤ)-v-1
    let y := state m v (m quot+1) d
    have subn : m num-m 0=v := by rw [hn,dn]; dsimp [v]; ring
    have act : Runs W body m 4 y := by
      have h := body_runs (W:=W) m ho
      rw [subn,dn] at h
      exact h
    have fy : Frame m y := state_frame m v (m quot+1) d
    have ynum : y num = v := state_num .. 
    have yquot : y quot = m quot+1 := state_quot .. 
    have ytest : y test = d := state_test ..
    have hvn : q*n+r ≤ M := by rw [Nat.succ_mul] at ha; omega
    have hv : v ≤ (M:ℤ) := by dsimp [v]; exact_mod_cast hvn
    have hnv : 0 ≤ v := Int.natCast_nonneg _
    have hN : (n:ℤ) ≤ M := by exact_mod_cast hnM
    have hNpos : 0 < (n:ℤ) := by exact_mod_cast (show 0<n by omega)
    have hf : Fits W (y test) := by rw [ytest]; apply cap.fits <;> dsimp [d] <;> omega
    by_cases done : q = 0
    · subst q
      have hvr : v=(r:ℤ) := by simp [v]
      refine ⟨y,?_,fy,ynum.trans hvr,by simpa using yquot⟩
      have nonneg : ¬ y test<0 := by rw [ytest]; dsimp [d]; rw [hvr]; omega
      exact Runs.loop_done act hf nonneg
    · have hqn : 1 ≤ q := by omega
      have hnb : n ≤ q*n+r := by
        have := Nat.mul_le_mul_right n hqn
        omega
      have hn' : (n:ℤ) ≤ v := by dsimp [v]; exact_mod_cast hnb
      have neg : y test<0 := by rw [ytest]; dsimp [d]; omega
      obtain ⟨out,more,fr,rem,result⟩ := ih (by omega) hvn y
        ((fy _ (Or.inr le_rfl)).trans dn) ((fy _ (Or.inl (by decide : one≤ -5))).trans ho) ynum
      refine ⟨out,?_,fy.trans fr,rem,?_⟩
      · rw [show 5*(q+1)=4+1+5*q by omega]
        exact Runs.loop_again act hf neg more
      · rw [result,yquot]
        push_cast
        ring

/-- Native Euclidean quotient and remainder. It takes three setup/guard
instructions and precisely five instructions per quotient unit. -/
theorem command_runs {W M n a : ℕ} (hn : 0<n) (cap : Room W M) (hnM : n≤M) (haM : a≤M)
    (m : Memory) (dn : m 0=n) (ho : m one=1) (ha : m num=a) :
    ∃ out, Runs W command m (3+5*(a/n)) out ∧ Frame m out ∧
      out num = ((a%n:ℕ):ℤ) ∧ out quot = ((a/n:ℕ):ℤ) := by
  let x := update m quot 0
  let y := update x test ((a:ℤ)-n)
  have fx : Frame m x := Frame.write _ (by decide : -5 < quot ∧ quot < 0) _
  have fy : Frame m y := fx.trans (Frame.write _ (by decide : -5 < test ∧ test < 0) _)
  have act₁ : Runs W (.atom (.sub quot quot quot)) m 1 x := by
    simpa [x] using Runs.atom (Step.sub (W:=W) m quot quot quot)
  have xn : x num=(a:ℤ) := by simpa [x,update,num,quot] using ha
  have xd : x 0=(n:ℤ) := (fx _ (Or.inr le_rfl)).trans dn
  have act₂ : Runs W (.atom (.sub test num 0)) x 1 y := by
    simpa only [y,xn,xd] using Runs.atom (Step.sub (W:=W) x test num 0)
  have yt : y test=(a:ℤ)-n := by simp [y,update]
  have yq : y quot=0 := by simp [y,x,update,quot,test]
  have yn : y num=(a:ℤ) := by simpa [y,x,update,num,quot,test] using ha
  have hf : Fits W (y test) := by rw [yt]; apply cap.fits <;> omega
  by_cases small : a<n
  · have q0 := Nat.div_eq_of_lt small
    have r0 := Nat.mod_eq_of_lt small
    have neg : y test<0 := by omega
    refine ⟨y,?_,fy,by simpa only [r0] using yn,by simpa only [q0,Nat.cast_zero] using yq⟩
    simpa [command,q0] using Runs.seq act₁ (.seq act₂ (Runs.guard_skip (c:=loop) hf neg))
  · have ge : n≤a := by omega
    have qpos : 0<a/n := Nat.div_pos ge hn
    have parts : a/n*n+a%n=a := by rw [Nat.add_comm,Nat.mul_comm, Nat.mod_add_div]
    have nonneg : ¬ y test<0 := by omega
    obtain ⟨out,more,fr,rem,qout⟩ := loop_runs cap hnM (Nat.mod_lt a hn) (a/n) qpos
      (by simpa only [parts] using haM) y ((fy _ (Or.inr le_rfl)).trans dn)
      ((fy _ (Or.inl (by decide : one≤ -5))).trans ho) (by simpa only [parts] using yn)
    refine ⟨out,?_,fy.trans fr,rem,by simpa [yq] using qout⟩
    simpa only [command,show 1+(1+(1+5*(a/n)))=3+5*(a/n) by omega] using
      Runs.seq act₁ (.seq act₂ (Runs.guard_take hf nonneg more))

end Division
end VWZClique.IntegerRAM.Graph
end

/- WordGraphDigits -/
section
/-! Radix-n unpacking of a blocked vertex label by the native word machine. -/

namespace VWZClique.IntegerRAM.Graph
open Structured BlockReduction

namespace Digits
open Division

theorem step_runs {W M n a : ℕ} (hn : 0<n) (cap : Room W M) (hnM : n≤M) (haM : a≤M)
    (m : Memory) (dn : m 0=n) (ho : m one=1) (ha : m num=a) (r : ℤ) (hr : r ≤ -6) :
    ∃ out, Runs W (step r) m (5+5*(a/n)) out ∧ out num = ((a/n:ℕ):ℤ) ∧
      out r = ((a%n:ℕ):ℤ) ∧ ∀ z, Protected z → z ≠ r → out z=m z := by
  obtain ⟨v,division,fr,rem,q⟩ := command_runs hn cap hnM haM m dn ho ha
  let x := update v r ((a%n:ℕ):ℤ)
  let y := update x num ((a/n:ℕ):ℤ)
  have vone : v one=1 := (fr _ (Or.inl (by decide : one ≤ -5))).trans ho
  have rr : r ≠ num := by change r ≠ -1; omega
  have hq : quot ≠ r := by change -2 ≠ r; omega
  have h1 : one ≠ r := by change -5 ≠ r; omega
  have first : Runs W (.atom (.mul r num one)) v 1 x := by
    simpa only [rem,vone,mul_one,x] using Runs.atom (Step.mul (W:=W) v r num one)
  have xq : x quot=((a/n:ℕ):ℤ) := by simpa [x,update,hq] using q
  have xone : x one=1 := by simpa [x,update,h1] using vone
  have second : Runs W (.atom (.mul num quot one)) x 1 y := by
    simpa only [xq,xone,mul_one,y] using Runs.atom (Step.mul (W:=W) x num quot one)
  refine ⟨y,?_,by simp [y,update],by simp [y,x,update,rr],?_⟩
  · simpa only [step,show 3+5*(a/n)+(1+1) = 5+5*(a/n) by omega] using
      Runs.seq division (Runs.seq first second)
  · intro z hz hz'
    have hznum : z ≠ num := by rcases hz with h|h <;> change z ≠ -1 <;> omega
    simpa [y,x,update,hznum,hz'] using fr z hz

end Digits
end VWZClique.IntegerRAM.Graph
end

/- NativeMaskScanClass -/
section
namespace VWZClique.IntegerRAM.MaskScan
open Structured Graph
open Graph.Division (num)

def localZ (h x : ℕ) : ℤ := if h≤x then -1 else 1

def totalZ (b h z : ℕ) : ℕ → ℤ
  | 0 => 1
  | j+1 => totalZ b h z j * localZ h (z/b^j%b)

def markState (m : Memory) (h dst y : ℤ) : Memory :=
  let p := update m cmp (m digit - m h)
  if m h ≤ m digit then update p dst y else p

/-- Additive and multiplicative digit statistics share the same branch. -/
theorem mark_runs {W : ℕ} (m : Memory) (h dst y : ℤ) (a : Atom)
    (fit : Fits W (m digit-m h))
    (step : let p := update m cmp (m digit-m h); Step W a p (update p dst y)) :
    ∃ f≤3, Runs W (mark h dst a) m f (markState m h dst y) := by
  let p := update m cmp (m digit-m h)
  have r : Runs W (.atom (.sub cmp digit h)) m 1 p := .atom (.sub ..)
  have pc : p cmp=m digit-m h := by simp [p,update]
  by_cases yes : m h ≤ m digit
  · refine ⟨3,by decide,?_⟩
    simp only [markState,if_pos yes]
    exact .seq r (.guard_take (pc ▸ fit) (by omega) (.atom step))
  · refine ⟨2,by decide,?_⟩
    simp only [markState,if_neg yes]
    exact .seq r (.guard_skip (pc ▸ fit) (by omega))

theorem mark_other (m : Memory) (h dst y z : ℤ) (c : z≠cmp) (d : z≠dst) :
    markState m h dst y z=m z := by unfold markState; split <;> simp [update,c,d]

def untouched (z : ℤ) : Prop := z< -214 ∨ 0≤z ∨ z≤ -5 ∧ z≠digit ∧ z≠amount ∧ z≠sign ∧ z≠cmp ∧ z≠remSteps

theorem oneDigit_runs {W M b z h g : ℕ} (pos : 0<b) (cap : Division.Room W M)
    (hb : b≤M) (hz : z≤M) (hh : h≤M) (hg : g≤M) (m : Memory) (rad : m 0=b)
    (u : m unit=1) (src : m num=z) (c : m countFrom=h) (s : m signFrom=g) (o : m zero=0) :
    ∃ f≤12+5*(z/b), ∃ y, Runs W oneDigit m f y ∧ y num=((z/b:ℕ):ℤ) ∧
      y amount=m amount+localN h (z%b) ∧ y sign=m sign*localZ g (z%b) ∧
      y remSteps=m remSteps+1 ∧ ∀ k, untouched k → y k=m k := by
  obtain ⟨a,act,aq,ad,af⟩ := Digits.step_runs pos cap hb hz m rad u src digit (by decide)
  have keep (j : ℤ) (hj : j≤ -5) (hd : j≠digit) : a j=m j := af _ (Or.inl hj) hd
  have ac := (keep countFrom (by decide) (by decide)).trans c
  have asg := (keep signFrom (by decide) (by decide)).trans s
  have ao := (keep zero (by decide) (by decide)).trans o
  have au := (keep unit (by decide) (by decide)).trans u
  have modlt := Nat.mod_lt z pos
  have firstFit : Fits W (a digit-a countFrom) := by rw [ad,ac]; apply cap.fits <;> omega
  obtain ⟨f,hf,r⟩ := mark_runs a countFrom amount (a amount+1) (.add amount amount unit) firstFit (by
    dsimp only; simpa [update,amount,unit,cmp,au] using
      (Step.add (W:=W) (update a cmp (a digit-a countFrom)) amount amount unit))
  let x := markState a countFrom amount (a amount+1)
  have xo (j : ℤ) (h₁ : j≠cmp) (h₂ : j≠amount) : x j=a j := mark_other _ _ _ _ _ h₁ h₂
  have xc : x amount=m amount+localN h (z%b) := by
    have av := keep amount (by decide) (by decide)
    by_cases ge : h≤z%b
    · have ge' : a countFrom ≤ a digit := by rw [ac,ad]; omega
      dsimp only [x]; rw [markState,if_pos ge',localN,if_pos ge]; simp [update,av]
    · have ge' : ¬ a countFrom ≤ a digit := by rw [ac,ad]; omega
      dsimp only [x]; rw [markState,if_neg ge',localN,if_neg ge]; simp [update,amount,cmp,av]
  have xd := (xo digit (by decide) (by decide)).trans ad
  have xsg := (xo signFrom (by decide) (by decide)).trans asg
  have x0 := (xo zero (by decide) (by decide)).trans ao
  have secondFit : Fits W (x digit-x signFrom) := by rw [xd,xsg]; apply cap.fits <;> omega
  obtain ⟨f',hf',r'⟩ := mark_runs x signFrom sign (-x sign) (.sub sign zero sign) secondFit (by
    dsimp only; simpa [update,zero,sign,cmp,x0] using
      (Step.sub (W:=W) (update x cmp (x digit-x signFrom)) sign zero sign))
  let y := markState x signFrom sign (-x sign)
  have yo (j : ℤ) (h₁ : j≠cmp) (h₂ : j≠sign) : y j=x j := mark_other _ _ _ _ _ h₁ h₂
  have xs := (xo sign (by decide) (by decide)).trans (keep sign (by decide) (by decide))
  have ys : y sign=m sign * localZ g (z%b) := by
    by_cases ge : g≤z%b
    · have ge' : x signFrom≤x digit := by rw [xsg,xd]; omega
      dsimp only [y]; rw [markState,if_pos ge',localZ,if_pos ge]; simp [update,xs]
    · have ge' : ¬ x signFrom≤x digit := by rw [xsg,xd]; omega
      dsimp only [y]; rw [markState,if_neg ge',localZ,if_neg ge]; simp [update,sign,cmp,xs]
  let out := update y remSteps (y remSteps+y unit)
  have last : Runs W (.atom (.add remSteps remSteps unit)) y 1 out := .atom (.add ..)
  refine ⟨_,by omega,out,.seq act (.seq r (.seq r' last)),?_,?_,?_,?_,?_⟩
  · simp only [out,update,if_neg (by decide : num≠remSteps),yo num (by decide) (by decide),xo num (by decide) (by decide),aq]
  · simp only [out,update,if_neg (by decide : amount≠remSteps),yo amount (by decide) (by decide),xc]
  · simp only [out,update,if_neg (by decide : sign≠remSteps),ys]
  · simp only [out,update,if_pos rfl,yo remSteps (by decide) (by decide),xo remSteps (by decide) (by decide),
      keep remSteps (by decide) (by decide),yo unit (by decide) (by decide),xo unit (by decide) (by decide),au,if_true]
  · intro j hj
    have z : j≠remSteps ∧ j≠cmp ∧ j≠sign ∧ j≠amount ∧ Protected j ∧ j≠digit := by
      rcases hj with hj|hj|hj <;> dsimp [remSteps,cmp,sign,amount,digit,Protected] at * <;> omega
    simp only [out,update,if_neg z.1,yo j z.2.1 z.2.2.1,xo j z.2.1 z.2.2.2.1,af j z.2.2.2.2.1 z.2.2.2.2.2]

end VWZClique.IntegerRAM.MaskScan
end

/- NativeMaskScanDigits -/
section
namespace VWZClique.IntegerRAM.MaskScan
open Structured Graph
open Division (num)

/-- A single loop bound applies to every candidate z even with the simple
repeated-subtraction division. -/
def digBudget (L bound : ℕ) := 7+L*(13+5*bound)

/-- Input counters and all nonnegative heap words survive classification. -/
def protectedCell (j : ℤ) := untouched j ∧ j≠zero

private theorem loopDigits {W M b h g z L j k : ℕ} (pos : 0<b) (cap : Division.Room W M)
    (hb : b≤M) (hz : z≤M) (hh : h≤M) (hg : g≤M) (hl : L≤M)
    (endAt : j+k=L) (positive : 0<k) (m : Memory) (rad : m 0=b)
    (u : m unit=1) (src : m num=((z/b^j:ℕ):ℤ)) (c : m countFrom=h) (s : m signFrom=g) (o : m zero=0)
    (atCount : m amount=totalN b h z j) (atSign : m sign=totalZ b g z j)
    (atRem : m remSteps = (j:ℤ)-L) :
    ∃ f≤k*(13+5*M), ∃ y, Runs W (.repeatWhileNegative oneDigit remSteps) m f y ∧
      y amount=totalN b h z L ∧ y sign=totalZ b g z L ∧ ∀ a, untouched a → y a=m a := by
  induction k generalizing j m with
  | zero => omega
  | succ k ih =>
    have small := Nat.le_trans (Nat.div_le_self z (b^j)) hz
    obtain ⟨f,fc,x,body,xq,xc,xs,xr,xf⟩ := oneDigit_runs pos cap hb small hh hg m rad u src c s o
    have fuel : f+1≤13+5*M := by have := Nat.div_le_self (z/b^j) b; omega
    have cq : x num=((z/b^(j+1):ℕ):ℤ) := by simpa only [Nat.pow_succ,Nat.div_div_eq_div_mul] using xq
    have cc : x amount=totalN b h z (j+1) := by simpa only [totalN,Nat.cast_add,atCount] using xc
    have cs : x sign=totalZ b g z (j+1) := by simpa only [totalZ,atSign] using xs
    have cr : x remSteps=((j+1:ℕ):ℤ)-L := by rw [xr,atRem]; omega
    have fit : Fits W (x remSteps) := by rw [cr]; apply cap.fits <;> omega
    by_cases done : k=0
    · subst k
      have eq : j+1=L := by omega
      refine ⟨f+1,by simpa using fuel,x,.loop_done body fit (by omega),eq ▸ cc,eq ▸ cs,xf⟩
    · have run := ih (j:=j+1) (by omega) (by omega) x
        ((xf 0 (by unfold untouched <;> decide)).trans rad) ((xf unit (by unfold untouched <;> decide)).trans u) cq
        ((xf countFrom (by unfold untouched <;> decide)).trans c) ((xf signFrom (by unfold untouched <;> decide)).trans s)
        ((xf zero (by unfold untouched <;> decide)).trans o) cc cs cr
      obtain ⟨t,tc,y,next,vv,ss,frame⟩ := run
      refine ⟨f+1+t,?_,y,.loop_again body fit (by omega) next,vv,ss,
        fun a ha => (frame a ha).trans (xf a ha)⟩
      rw [Nat.succ_mul]; omega

theorem digits_run {W M b h g z L : ℕ} (pos : 0<b) (cap : Division.Room W M)
    (hb : b≤M) (hz : z≤M) (hh : h≤M) (hg : g≤M) (hl : L≤M)
    (m : Memory) (rad : m 0=b) (u : m unit=1) (src : m idx=z) (cl : m len=L)
    (c : m countFrom=h) (s : m signFrom=g) :
    ∃ f≤digBudget L M, ∃ y, Runs W allDigits m f y ∧
      y amount=totalN b h z L ∧ y sign=totalZ b g z L ∧ ∀ a, protectedCell a → y a=m a := by
  let x := beginDigits.foldl Butterfly.effect m
  have run : Runs W (Butterfly.line beginDigits) m 6 x := Butterfly.line_runs _ _ (by simp [beginDigits,Butterfly.safeLine,Butterfly.safe])
  have inputs : x zero=0 ∧ x num=z ∧ x sign=1 ∧ x amount=0 ∧ x remSteps=-(L:ℤ) ∧ x cmp=(L:ℤ)-1 := by
    simp [x,beginDigits,Butterfly.effect,update,zero,unit,num,idx,remSteps,cmp,amount,sign,len,u,src,cl] at *
  obtain ⟨x0,xq,xs,xc,xr,cf⟩ := inputs
  have before (a : ℤ) (ha : protectedCell a) : x a=m a := by
    have ne : a≠zero ∧ a≠num ∧ a≠sign ∧ a≠amount ∧ a≠remSteps ∧ a≠cmp := by
      rcases ha with ⟨h,ne⟩
      rcases h with h|h|h <;> dsimp [zero,num,sign,amount,remSteps,cmp,digit] at * <;> omega
    simp only [x,beginDigits,List.foldl,Butterfly.effect,update,if_neg ne.1,if_neg ne.2.1,
      if_neg ne.2.2.1,if_neg ne.2.2.2.1,if_neg ne.2.2.2.2.1,if_neg ne.2.2.2.2.2]
  have cfFit : Fits W (x cmp) := by rw [cf]; apply cap.fits <;> omega
  by_cases hL : L=0
  · subst L
    exact ⟨7,by simp [digBudget],x,.seq run (.guard_skip cfFit (by omega)),xc,xs,before⟩
  · obtain ⟨f,fc,y,body,yc,ys,fr⟩ := loopDigits (j:=0) (k:=L) pos cap hb hz hh hg hl (by omega) (by omega) x
      ((before 0 (by unfold protectedCell untouched <;> decide)).trans rad) ((before unit (by unfold protectedCell untouched <;> decide)).trans u) (by simpa using xq)
      ((before countFrom (by unfold protectedCell untouched <;> decide)).trans c) ((before signFrom (by unfold protectedCell untouched <;> decide)).trans s) x0 xc xs (by simpa using xr)
    exact ⟨_,by unfold digBudget; omega,y,.seq run (.guard_take cfFit (by omega) body),yc,ys,
      fun a ha => (fr a ha.1).trans (before a ha)⟩

end VWZClique.IntegerRAM.MaskScan
end

/- NativeMaskScanTable -/
section
namespace VWZClique.IntegerRAM.MaskScan
open Structured Graph Butterfly

def preserved (z : ℤ) := protectedCell z ∧ z≠ptr ∧ z≠value ∧ z≠flag ∧ z≠cmp

theorem post_runs {W : ℕ} (m : Memory) (left right : ℤ) (base a : ℕ) (s γ : ℤ)
    (hc : m amount=a) (hs : m sign=s) (hl : m leftCut=left) (hr : m rightCut=right)
    (hb : m coef=base) (val : m ((base+a:ℕ):ℤ)=γ) (addr : Fits W ((base+a:ℕ):ℤ))
    (fleft : Fits W (left-a)) (fright : Fits W ((a:ℤ)-right)) (oneFit : Fits W 1) :
    ∃ f≤7, ∃ o, Runs W post m f o ∧ (0≤o flag ↔ selected left right a=true) ∧
      Fits W (o flag) ∧ o value=γ*s ∧
      ∀ z, z≠ptr → z≠value → z≠flag → z≠cmp → o z=m z := by
  let x := writeValue.foldl effect m
  have safe : safeLine W m writeValue := by
    simpa [writeValue,safeLine,Butterfly.safe,effect,update,hb,hc,Nat.cast_add] using addr
  have run : Runs W (line writeValue) m 5 x := line_runs _ _ safe
  have inputs : x flag=(a:ℤ)-right ∧ x value=γ*s ∧ x cmp=left-(a:ℤ) := by
    simp [x,writeValue,effect,update,ptr,coef,amount,sign,flag,rightCut,value,leftCut,cmp,
      hb,hc,hs,hl,hr,Nat.cast_add] at val ⊢
    simp [val,show (base:ℤ)+a≠ -218 by omega]
  obtain ⟨xf,xv,xc⟩ := inputs
  have unchanged (z : ℤ) (hp : z≠ptr) (hv : z≠value) (hf : z≠flag) (ht : z≠cmp) : x z=m z := by
    simp only [x,writeValue,List.foldl,effect,update,if_neg hp,if_neg hv,if_neg hf,if_neg ht]
  by_cases keep : (a:ℤ)≤left
  · let o := update x flag 1
    have one : Runs W (.atom (.one flag)) x 1 o := .atom (.one ..)
    refine ⟨7,by decide,o,.seq run (.guard_take (xc ▸ fleft) (by omega) one),?_,?_,?_,?_⟩
    · simp [o,update,selected,keep]
    · simpa [o,update] using oneFit
    · simpa [o,update,flag,value] using xv
    · intro z hp hv hf ht; exact (if_neg hf).trans (unchanged z hp hv hf ht)
  · refine ⟨6,by decide,x,.seq run (.guard_skip (xc ▸ fleft) (by omega)),?_,xf ▸ fright,xv,unchanged⟩
    simp [selected,keep,xf] <;> omega

/-- The table of signed coefficients may occupy any region disjoint from the
two compact arrays. Input data and controls are runtime words. -/
structure Parameters (m : Memory) (b L h g base : ℕ) (left right : ℤ) (C : ℕ → ℤ) : Prop where
  radix : m 0=b
  length : m len=L
  countAt : m countFrom=h
  signAt : m signFrom=g
  low : m leftCut=left
  high : m rightCut=right
  coeffBase : m coef=base
  coeff : ∀ a≤L, m ((base+a:ℕ):ℤ)=C a

private theorem paramCell {z : ℤ} (h : 0≤z) : preserved z := by
  refine ⟨⟨Or.inr (Or.inl h),?_⟩,?_,?_,?_,?_⟩ <;> dsimp [zero,ptr,value,flag,cmp] <;> omega

private theorem parReg {b L h g base : ℕ} {l r : ℤ} {C : ℕ → ℤ} {u v : Memory}
    (p : Parameters u b L h g base l r C) (keep : ∀ z, preserved z → v z=u z) :
    Parameters v b L h g base l r C := by
  constructor
  · exact (keep 0 (paramCell (by decide))).trans p.radix
  · exact (keep len (by unfold preserved protectedCell untouched; decide)).trans p.length
  · exact (keep countFrom (by unfold preserved protectedCell untouched; decide)).trans p.countAt
  · exact (keep signFrom (by unfold preserved protectedCell untouched; decide)).trans p.signAt
  · exact (keep leftCut (by unfold preserved protectedCell untouched; decide)).trans p.low
  · exact (keep rightCut (by unfold preserved protectedCell untouched; decide)).trans p.high
  · exact (keep coef (by unfold preserved protectedCell untouched; decide)).trans p.coeffBase
  · intro a ha; exact (keep _ (paramCell (by omega))).trans (p.coeff a ha)

theorem totalN_le (b h z j : ℕ) : totalN b h z j ≤ j := by
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih => simp only [totalN,localN]; split <;> omega

theorem classify_one {W M N c v j k b L h g base : ℕ} {left right : ℤ} (C : ℕ→ℤ)
    (pos : 0<b) (cap : Division.Room W M) (hb : b≤M) (hj : j≤M) (hh : h≤M) (hg : g≤M) (hl : L≤M)
    (addr : ∀ a≤L, Fits W ((base+a:ℕ):ℤ)) (cut : ∀ a≤L, Fits W (left-a) ∧ Fits W ((a:ℤ)-right))
    (m : Memory) (p : Parameters m b L h g base left right C) (ctl : Controls N c v j k m) :
    let a := totalN b h j L
    ∃ f≤digBudget L M+7, ∃ o, Runs W classifier m f o ∧
      (0≤o flag ↔ selected left right a=true) ∧ Fits W (o flag) ∧ o value=C a*totalZ b g j L ∧
      (∀ z, preserved z → o z=m z) := by
  obtain ⟨f,ft,x,act,xc,xs,frame⟩ := digits_run pos cap hb hj hh hg hl m p.radix ctl.one ctl.index p.length p.countAt p.signAt
  have u := parReg p (fun z hz => frame z hz.1)
  have ha := totalN_le b h j L
  obtain ⟨n,nt,o,run,sel,fit,val,fr⟩ := post_runs x left right base _ _ _ xc xs u.low u.high u.coeffBase
    (u.coeff _ ha) (addr _ ha) (cut _ ha).1 (cut _ ha).2 (by apply cap.fits <;> omega)
  exact ⟨_,Nat.add_le_add ft nt,o,.seq act run,sel,fit,val,
    fun z hz => (fr z hz.2.1 hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2).trans (frame z hz.1)⟩

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

theorem totalZ_prod (b h z L : ℕ) : totalZ b h z L =
    ∏ i : Fin L, localZ h (z / b^i.val % b) := by
  induction L with
  | zero => simp [totalZ]
  | succ L ih => rw [Fin.prod_univ_castSucc,totalZ,ih]; rfl

theorem mask_pop {L : ℕ} (z : Fin (5^L)) : totalN 5 1 z.val L =
    (support (finFunctionFinEquiv.symm z : Digits L)).card := by
  rw [totalN_sum,support,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  let d := ((finFunctionFinEquiv.symm z : Digits L) i)
  change localN 1 (z.val/5^i.val%5) = if d≠0 then 1 else 0
  rw [← digit_extraction z i]
  change localN 1 d.val = if d≠0 then 1 else 0
  have iff : d≠0 ↔ 1≤d.val := by
    constructor
    · intro h; by_contra n; exact h (Fin.ext (by change d.val=0; omega))
    · intro h e; have hv := congrArg Fin.val e; change d.val=0 at hv; omega
  simp only [localN,iff]

theorem mask_signed {L : ℕ} (z : Fin (5^L)) (C : ℕ→ℤ) :
    C (totalN 5 1 z.val L)*totalZ 5 3 z.val L = integerWeight C (finFunctionFinEquiv.symm z) := by
  rw [mask_pop,totalZ_prod,integerWeight]
  rfl

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

theorem maskKey_iff {L d : ℕ} (z : Fin (5^L)) : maskKey L d z.val = true ↔ z∈allowed L d := by
  have hn := totalN_le 5 1 z.val L
  simp only [maskKey,selected,decide_eq_true_eq,allowed,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [← mask_pop z]; omega

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

theorem mask_count (L d : ℕ) : rank (maskKey L d) (5^L)=Fintype.card (Terms L d) := by
  rw [rank_card,Fintype.card_congr (enumerate L d),Fintype.card_coe]
  congr 1
  ext z; simpa using (maskKey_iff z : maskKey L d z.val=true ↔ z∈allowed L d)

theorem label_count (L a d : ℕ) : rank (labelKey L a d) (4^L)=(outside L a d).card := by
  rw [rank_card]
  apply Finset.card_bij (fun x _ => (finFunctionFinEquiv.symm x : BasisLabel L))
  · intro x hx; exact (labelKey_iff x).mp (Finset.mem_filter.mp hx).2
  · intro x _ y _ he; exact finFunctionFinEquiv.symm.injective he
  · intro x hx; refine ⟨finFunctionFinEquiv x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,by simp⟩
    apply (labelKey_iff _).mpr; simpa using hx

private theorem scale (L : ℕ) : (L+1)*25^L ≤ 4*32^L := by
  induction L with
  | zero => decide
  | succ L ih =>
    have u : 25^L ≤ 32^L := Nat.pow_le_pow_left (by decide) L
    calc
      _ = 25*((L+1)*25^L)+25*25^L := by rw [pow_succ]; ring
      _ ≤ 25*(4*32^L)+25*32^L := Nat.add_le_add (Nat.mul_le_mul_left _ ih) (Nat.mul_le_mul_left _ u)
      _ ≤ _ := by rw [pow_succ]; omega

theorem scan_budget {b : ℕ} (hb : b≤5) (L : ℕ) :
    b^L * (digBudget L (5*5^L)+15) ≤ 240 * (2^L)^5 := by
  have h := Nat.pow_le_pow_left hb L
  have u : 1≤5^L := Nat.one_le_pow _ _ (by decide)
  have v : 5^L≤5^L*5^L := by simpa only [one_mul] using Nat.mul_le_mul_right (5^L) u
  have w : L*5^L ≤ L*(5^L*5^L) := Nat.mul_le_mul_left _ v
  have sq : 5^L*5^L=25^L := by rw [←Nat.mul_pow]
  calc
    _ ≤ 5^L*(digBudget L (5*5^L)+15) := Nat.mul_le_mul_right _ h
    _ ≤ 60*((L+1)*25^L) := by rw [←sq]; unfold digBudget; nlinarith only [v,w,Nat.zero_le (L*(5^L*5^L))]
    _ ≤ 60*(4*32^L) := Nat.mul_le_mul_left _ (scale L)
    _ = _ := by rw [← pow_mul, Nat.mul_comm L 5, pow_mul]; change 60*(4*32^L)=240*32^L; ring

end VWZClique.IntegerRAM.MaskScan
end

/- TraceDyadicData -/
section
namespace VWZClique.TraceDyadic
open RankSwap UniformFolds Double

private theorem digit_cast (j : Fin 4) (s u : Bool) : (digit j s u : ℚ) = oneBit j s u := by
  fin_cases j <;> cases s <;> cases u <;> decide

private theorem digit_bound (j : Fin 4) (s u : Bool) : |digit j s u| ≤ 1 := by
  fin_cases j <;> cases s <;> cases u <;> decide

theorem basis_cast {L : ℕ} (j : BasisLabel L) (x : PairBits L) :
    (basisInt j x : ℚ) = basisEntry j x := by simp only [basisInt,Int.cast_prod,digit_cast,basisEntry]

private theorem prod_unit {I : Type*} [Fintype I] (f : I → ℤ) (h : ∀ i, |f i| ≤ 1) :
    |∏ i, f i| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => h i)

theorem basis_bound {L : ℕ} (j : BasisLabel L) (x : PairBits L) : |basisInt j x| ≤ 1 :=
  prod_unit _ (fun i => digit_bound (j i) (x.1 i) (x.2 i))

end VWZClique.TraceDyadic
end

/- NativeMaskScanScale -/
section
namespace VWZClique.IntegerRAM.MaskScan
open Structured Graph Butterfly

/-- Generate the dyadically cleared integer diagonal in the native classifier.
The first walk extracts the antisymmetric count. The second counts mixed
coordinates and uses that index in the reverse power-of-two table. -/
theorem scaleClass_runs {W M N c v j k L base pw : ℕ} {left right : ℤ} (C : ℕ→ℤ)
    (cap : Division.Room W M) (hm : 4≤M) (hj : j≤M) (hl : L≤M)
    (addr : ∀ a≤L, Fits W ((base+a:ℕ):ℤ)) (cut : ∀ a≤L, Fits W (left-a) ∧ Fits W ((a:ℤ)-right))
    (powAddr : ∀ a≤L, Fits W ((pw+a:ℕ):ℤ)) (m : Memory) (p : Parameters m 4 L 3 4 base left right C)
    (pt : m powBase=pw) (powTab : ∀ a≤L, m (pw+a:ℕ)=2^(L-a)) (ctl : Controls N c v j k m) :
    let a := totalN 4 3 j L
    let d := totalN 4 2 j L
    ∃ f≤2*digBudget L M+12, ∃ o, Runs W scaleClass m f o ∧
      (0≤o flag ↔ selected left right a=true) ∧ Fits W (o flag) ∧ o value=(C a*totalZ 4 4 j L)*2^(L-d) ∧
      ∀ z, preserved z → o z=m z := by
  obtain ⟨f,hf,x,rc,keep,flagF,val,same⟩ := classify_one C (by decide : 0<4) cap hm hj (by omega) hm hl addr cut m p ctl
  let s := update x countFrom (x unit+x unit)
  have set : Runs W (.atom (.add countFrom unit unit)) x 1 s := .atom (.add ..)
  have xUnit := (same unit (by unfold preserved protectedCell untouched; decide)).trans ctl.one
  have own (z : ℤ) (h : preserved z) (e : z≠countFrom) : s z=m z :=
    (if_neg e).trans (same z h)
  obtain ⟨g,hg,y,walk,amount',_,stay⟩ := digits_run (by decide : 0<4) cap hm hj (by omega : 2≤M) hm hl s
    ((own 0 (by unfold preserved protectedCell untouched; decide) (by decide)).trans p.radix)
    ((own unit (by unfold preserved protectedCell untouched; decide) (by decide)).trans ctl.one)
    ((own idx (by unfold preserved protectedCell untouched; decide) (by decide)).trans ctl.index)
    ((own len (by unfold preserved protectedCell untouched; decide) (by decide)).trans p.length)
    (by simp [s,update,xUnit])
    ((own signFrom (by unfold preserved protectedCell untouched; decide) (by decide)).trans p.signAt)
  have after (z : ℤ) (h : preserved z) (e : z≠countFrom) : y z=m z :=
    (stay z h.1).trans (own z h e)
  have yp := (after powBase (by unfold preserved protectedCell untouched; decide) (by decide)).trans pt
  have yf : y flag=x flag := (stay flag (by unfold protectedCell untouched; decide)).trans (if_neg (by decide))
  have yv : y value=x value := (stay value (by unfold protectedCell untouched; decide)).trans (if_neg (by decide))
  have yu := (after unit (by unfold preserved protectedCell untouched; decide) (by decide)).trans ctl.one
  have yc : y countFrom=2 := (stay countFrom (by unfold protectedCell untouched; decide)).trans (by simp [s,update,xUnit])
  let d := totalN 4 2 j L
  have hd : d≤L := totalN_le _ _ _ _
  have mem := (after ((pw+d:ℕ):ℤ) (by
    unfold preserved protectedCell untouched; refine ⟨⟨Or.inr (Or.inl (by omega)),?_⟩,?_,?_,?_,?_⟩ <;>
       dsimp [zero,ptr,value,flag,cmp] <;> omega) (by dsimp [countFrom];omega)).trans (powTab d hd)
  have safe : safeLine W y scaleFinish := by
    simpa [scaleFinish,safeLine,Butterfly.safe,effect,update,yp,amount',Nat.cast_add] using powAddr d hd
  let o := scaleFinish.foldl effect y
  have stay' (z : ℤ) (p : z≠ptr) (v : z≠value) (c : z≠countFrom) : o z=y z := by
    simp only [o,scaleFinish,List.foldl,effect,update,if_neg p,if_neg v,if_neg c]
  have oflag := (stay' flag (by decide) (by decide) (by decide)).trans yf
  have oc : o countFrom=3 := by simp [o,scaleFinish,effect,update,countFrom,ptr,value,unit,yc,yu] at *
  refine ⟨_,by change f+(1+(g+4))≤_; omega,o,.seq rc (.seq set (.seq walk (line_runs _ _ safe))),oflag ▸ keep,oflag ▸ flagF,?_,?_⟩
  · simp (disch := omega) [o,scaleFinish,effect,update,yp,amount',ptr,value,countFrom,yv,val,
      Nat.cast_add,d] at mem ⊢
    rw [if_neg (by omega),mem]
  · intro z hz
    by_cases eq : z=countFrom
    · subst z; exact oc.trans p.countAt.symm
    · exact (stay' z hz.2.1 hz.2.2.1 eq).trans (after z hz eq)

end VWZClique.IntegerRAM.MaskScan
end

/- NativeMaskScanFramed -/
section
namespace VWZClique.IntegerRAM.MaskScan
open Structured Graph Butterfly

/-- Every caller-owned register outside the classifier/loop temporaries and
every heap word outside the two compact arrays is preserved by a framed scan. -/
def stationary (N c v : ℕ) (z : ℤ) := preserved z ∧ ¬privateCell z ∧
  (z<c ∨ (c:ℤ)+N≤z) ∧ (z<v ∨ (v:ℤ)+N≤z)

private theorem heapFrame (z : ℕ) : preserved (z:ℤ) := by
  refine ⟨⟨Or.inr (Or.inl (by omega)),?_⟩,?_,?_,?_,?_⟩ <;> dsimp [zero,ptr,value,flag,cmp] <;> omega

theorem framed_scan {W N c v K : ℕ} (hn : 0<N) (hv : c+N≤v)
    (fits : ∀ j<N, Fits W ((c+j:ℕ):ℤ) ∧ Fits W ((v+j:ℕ):ℤ))
    (guard : ∀ j≤N, Fits W ((j:ℤ)-N)) (key : ℕ→Bool) (weight : ℕ→ℤ) (cl : Command)
    (m : Memory) (init : Controls N c v 0 0 m)
    (one : ∀ j<N, ∀ x, (∀ z, stationary N c v z → x z=m z) → Controls N c v j (rank key j) x →
      ∃ f≤K, ∃ y, Runs W cl x f y ∧ (0≤y flag ↔ key j=true) ∧ Fits W (y flag) ∧ y value=weight j ∧
        ∀ z, preserved z → y z=x z) :
    ∃ f≤N*(K+8), ∃ o, Runs W (scan cl) m f o ∧ (∀ z, stationary N c v z → o z=m z) ∧
      Controls N c v N (rank key N) o ∧ ∀ j<N, key j=true → o (c+rank key j:ℕ)=j ∧ o (v+rank key j:ℕ)=weight j := by
  let I := fun (_ : ℕ) (x : Memory) => ∀ z, stationary N c v z → x z=m z
  apply scan_runs hn hv fits guard key weight I cl ?_ ?_ (fun _ _ => rfl) init
  · intro j hj x same ctl
    obtain ⟨f,hf,y,run,keep,fit,val,frame⟩ := one j hj x same ctl
    have ctr : Controls N c v j (rank key j) y := by
      constructor
      · exact (frame idx (by unfold preserved protectedCell untouched; decide)).trans ctl.index
      · exact (frame lim (by unfold preserved protectedCell untouched; decide)).trans ctl.limit
      · exact (frame unit (by unfold preserved protectedCell untouched; decide)).trans ctl.one
      · exact (frame outC (by unfold preserved protectedCell untouched; decide)).trans ctl.p
      · exact (frame outV (by unfold preserved protectedCell untouched; decide)).trans ctl.v
    exact ⟨f,hf,y,run,ctr,keep,fit,val,fun z h => (frame z h.1).trans (same z h),
      fun _ _ => ⟨frame _ (heapFrame _),frame _ (heapFrame _)⟩⟩
  · intro j hj x y same hold z st
    have small := rank_le key j
    obtain ⟨h,hp,hc,hv'⟩ := st
    exact (hold z hp (by omega) (by omega)).trans (same z ⟨h,hp,hc,hv'⟩)

theorem stationary_nat {N c v : ℕ} (z : ℕ) (low : z<c) (high : z<v) : stationary N c v z := by
  exact ⟨heapFrame _,by unfold privateCell; dsimp [idx,lim,unit,test,outC,outV];omega,Or.inl (by omega),Or.inl (by omega)⟩

theorem before_data {N c v b L h g base : ℕ} {left right : ℤ} {C : ℕ→ℤ} {m x : Memory}
    (sep : base+L<c ∧ c+N≤v) (p : Parameters m b L h g base left right C)
    (same : ∀ z, stationary N c v z → x z=m z) : Parameters x b L h g base left right C := by
  have neg (z : ℤ) (hz : z<0) (h : preserved z) (k : ¬privateCell z) : x z=m z :=
    same z ⟨h,k,Or.inl (by omega),Or.inl (by omega)⟩
  constructor
  · exact (same 0 (stationary_nat 0 (by omega) (by omega))).trans p.radix
  · exact (neg len (by decide) (by unfold preserved protectedCell untouched;decide) (by unfold privateCell;decide)).trans p.length
  · exact (neg countFrom (by decide) (by unfold preserved protectedCell untouched;decide) (by unfold privateCell;decide)).trans p.countAt
  · exact (neg signFrom (by decide) (by unfold preserved protectedCell untouched;decide) (by unfold privateCell;decide)).trans p.signAt
  · exact (neg leftCut (by decide) (by unfold preserved protectedCell untouched;decide) (by unfold privateCell;decide)).trans p.low
  · exact (neg rightCut (by decide) (by unfold preserved protectedCell untouched;decide) (by unfold privateCell;decide)).trans p.high
  · exact (neg coef (by decide) (by unfold preserved protectedCell untouched;decide) (by unfold privateCell;decide)).trans p.coeffBase
  · intro j hj; exact (same _ (stationary_nat _ (by omega) (by omega))).trans (p.coeff j hj)

theorem scale_enumerate {W M N c v L base pw : ℕ} {left right : ℤ} (C : ℕ→ℤ)
    (hn : 0<N) (cap : Division.Room W M) (hm : 4≤M) (hN : N≤M) (hl : L≤M)
    (fits : ∀ j<N, Fits W ((c+j:ℕ):ℤ) ∧ Fits W ((v+j:ℕ):ℤ))
    (addr : ∀ a≤L, Fits W ((base+a:ℕ):ℤ)) (cut : ∀ a≤L, Fits W (left-a) ∧ Fits W ((a:ℤ)-right))
    (powAddr : ∀ a≤L, Fits W ((pw+a:ℕ):ℤ)) (sep : base+L<c ∧ c+N≤v) (pp : pw+L<c)
    (m : Memory) (p : Parameters m 4 L 3 4 base left right C)
    (pt : m powBase=pw) (powTab : ∀ a≤L, m (pw+a:ℕ)=2^(L-a)) (ctl : Controls N c v 0 0 m) :
    let key := fun j => selected left right (totalN 4 3 j L)
    ∃ f≤N*(2*digBudget L M+20), ∃ o, Runs W (scan scaleClass) m f o ∧
      (∀ z, stationary N c v z → o z=m z) ∧ Controls N c v N (rank key N) o ∧ ∀ j<N, key j=true →
      o (c+rank key j:ℕ)=j ∧ o (v+rank key j:ℕ)=C (totalN 4 3 j L)*totalZ 4 4 j L*2^(L-totalN 4 2 j L) := by
  apply framed_scan (K:=2*digBudget L M+12) hn sep.2 fits (fun j hj => by apply cap.fits <;>omega) _ _ _ _ ctl
  intro j hj x same ctrl
  have tab (a : ℕ) (ha : a≤L) := (same _ (stationary_nat (pw+a) (by omega) (by omega))).trans (powTab a ha)
  have register : stationary N c v powBase := by
    refine ⟨by unfold preserved protectedCell untouched;decide,by unfold privateCell;decide,Or.inl ?_,Or.inl ?_⟩ <;>
      dsimp [powBase] <;> omega
  exact scaleClass_runs C cap hm (by omega) hl addr cut powAddr x (before_data sep p same) ((same _ register).trans pt) tab ctrl

end VWZClique.IntegerRAM.MaskScan
end

/- NativeMaskScanForward -/
section
/-! A contiguous convolution triangle realizes every coefficient (shift^[s] c) 0
with one pass in O((L+1)^2) native instructions. -/
namespace VWZClique.IntegerRAM.MaskScan.Forward
open Structured Butterfly

def V (C : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0,j => C j
  | r+1,j => V C r j-2*V C r (j+1)

structure Controls (src dst N j : ℕ) (m : Memory) : Prop where
  read : m rd=((src+j:ℕ):ℤ)
  write : m wr=((dst+j:ℕ):ℤ)
  iter : m ireg=j
  limit : m maxI=N
  one : m unit=1

private theorem once {W src dst N j : ℕ} (m : Memory) (ctl : Controls src dst N j m)
    (a : Fits W ((src+j:ℕ):ℤ)) (b : Fits W ((src+j+1:ℕ):ℤ)) (d : Fits W ((dst+j:ℕ):ℤ)) :
    ∃ y, Runs W (line block) m 8 y ∧ y ireg=j ∧ y unit=1 ∧ y maxI=N ∧
      y rd=((src+(j+1):ℕ):ℤ) ∧ y wr=((dst+(j+1):ℕ):ℤ) ∧
      ∀ z : ℕ, y z=if z=dst+j then m (src+j:ℕ)-2*m (src+j+1:ℕ) else m z := by
  have safe : safeLine W m block := by
    simp [block,safeLine,Butterfly.safe,effect,update,other,rd,wr,va,vb,ctl.one,ctl.read,ctl.write,Nat.cast_add] at *
    exact ⟨a,b,d⟩
  let y := block.foldl effect m
  refine ⟨y,line_runs _ _ safe,?_,?_,?_,?_,?_,?_⟩
  all_goals try intro z
  all_goals simp (disch := omega) [y,block,effect,update,other,rd,wr,va,vb,ireg,unit,maxI,check,
    ctl.iter,ctl.read,ctl.write,ctl.limit,ctl.one,Nat.cast_add] at *
  all_goals first | omega | split <;> omega

/-- Place the first L+1 coefficients of C in row zero. Every subsequent row
is produced by two loads and one store per word. The triangle r+j≤L suffices,
so the unconditional reads at the right boundary need no padding hypotheses. -/
theorem triangle {W L b : ℕ} (hL : 0<L) (C : ℕ → ℤ) (m : Memory)
    (fit : ∀ i≤(L+1)^2, Fits W ((b+i:ℕ):ℤ)) (guard : ∀ j≤(L+1)*L, Fits W ((j:ℤ)-(L+1)*L))
    (start : Controls b (b+(L+1)) ((L+1)*L) 0 m) (input : ∀ j≤L, m (b+j:ℕ)=C j) :
    ∃ f≤11*((L+1)*L), ∃ y, Runs W forward m f y ∧
      (∀ r j, r+j≤L → y (b+r*(L+1)+j:ℕ)=V C r j) ∧
      ∀ z : ℕ, z<b+(L+1) ∨ b+(L+1)^2≤z → y z=m z := by
  let S := L+1
  let N := S*L
  have sq : S+N=S^2 := by dsimp [N,S]; rw [Nat.pow_succ,Nat.pow_one,Nat.mul_succ]; omega
  let I := fun i (x : Memory) => Controls b (b+S) N i x ∧
    (∀ r j, r+j≤L → r*S+j < S+i → x (b+r*S+j:ℕ)=V C r j) ∧
    ∀ z : ℕ, z<b+S ∨ b+S+i≤z → x z=m z
  have init : I 0 m := by
    refine ⟨start,?_,fun _ _ => rfl⟩
    intro r j h hj
    cases r with
    | zero => simpa [V] using input j (by omega)
    | succ r => rw [Nat.succ_mul] at hj; omega
  have action (i : ℕ) (hi : i<N) (x : Memory) (hx : I i x) :
      ∃ f≤8, ∃ y, Runs W (line block) x f y ∧ y ireg=i ∧ y unit=1 ∧ y maxI=N ∧ I (i+1) (nextMemory y ireg check i N) := by
    obtain ⟨ctr,table,fr⟩ := hx
    have f₁ := fit i (by change i≤S^2; omega)
    have f₂ : Fits W ((b+i+1:ℕ):ℤ) := by simpa [Nat.add_assoc] using fit (i+1) (by change i+1≤S^2; omega)
    have f₃ : Fits W ((b+S+i:ℕ):ℤ) := by simpa [Nat.add_assoc] using fit (S+i) (by change S+i≤S^2; omega)
    obtain ⟨y,run,yi,yu,yl,yr,yw,upd⟩ := once x ctr f₁ f₂ f₃
    have after (z : ℕ) : nextMemory y ireg check i N z = y z := by
      simp (disch := omega) [nextMemory,update,ireg,check]
    refine ⟨8,by decide,y,run,yi,yu,yl,?_,?_,?_⟩
    · constructor <;> simp [nextMemory,update,ireg,check,rd,wr,unit,maxI,yi,yu,yl,yr,yw,Nat.cast_add] at *
    · intro r j h hj
      rw [after,upd]
      by_cases earlier : r*S+j<S+i
      · rw [if_neg (by omega)]; exact table r j h earlier
      · have atNow : r*S+j=S+i := by omega
        rw [if_pos (by omega)]
        cases r with
        | zero => simp [S] at atNow; omega
        | succ r =>
          rw [Nat.succ_mul] at atNow
          have read : r*S+j=i := by omega
          have first := table r j (by omega) (by omega)
          have second := table r (j+1) (by omega) (by dsimp [S] at *; omega)
          simpa only [V, Nat.add_assoc,read,show r*S+(j+1)=i+1 by omega] using
            (show x (b+r*S+j:ℕ)-2*x (b+r*S+(j+1):ℕ)=V C r j-2*V C r (j+1) by rw [first,second])
    · intro z hz
      rw [after,upd,if_neg (by omega),fr z (by omega)]
  obtain ⟨f,hf,y,run,done⟩ := repeatN_runs (B:=8) (Nat.mul_pos (by dsimp [S];omega) hL) _
    (by decide : maxI≠ireg) I (fun j hj => by simpa [N,S,Nat.cast_mul,Nat.cast_add] using guard j hj) action init
  refine ⟨f,by simpa [N,S,Nat.mul_comm] using hf,y,run,?_,?_⟩
  · intro r j h
    apply done.2.1 r j h
    have := Nat.mul_le_mul_right S (show r≤L by omega)
    have pivot : N=L*S := Nat.mul_comm _ _
    have hj : j<S := by dsimp [S]; omega
    omega
  · intro z hz; apply done.2.2; change z<b+S ∨ b+S^2≤z at hz; omega

end VWZClique.IntegerRAM.MaskScan.Forward
end

/- NativeMaskScanResidual -/
section
namespace VWZClique.IntegerRAM.MaskScan.Forward
open Structured Butterfly

structure GatherCtrl (b u v L j : ℕ) (m : Memory) : Prop where
  read : m rd=((b+j*(L+1):ℕ):ℤ)
  rp : m resWr=((u+j:ℕ):ℤ)
  pp : m powWr=(v:ℤ)+L-j
  it : m ireg=j
  lim : m maxI=((L+1:ℕ):ℤ)
  st : m stride=((L+1:ℕ):ℤ)
  sgn : m parity=(-1)^j
  pow : m power=2^j
  z : m nilReg=0
  one : m unit=1

private theorem gatherStep {W b u v L j : ℕ} (hj : j≤L) (m : Memory) (ct : GatherCtrl b u v L j m)
    (fr : Fits W ((b+j*(L+1):ℕ):ℤ)) (fu : Fits W ((u+j:ℕ):ℤ)) (fv : Fits W ((v+(L-j):ℕ):ℤ)) :
    ∃ y, Runs W (line gatherBlock) m 10 y ∧ y ireg=j ∧ y unit=1 ∧ y maxI=((L+1:ℕ):ℤ) ∧
      GatherCtrl b u v L (j+1) (nextMemory y ireg check j (L+1)) ∧
      ∀ z : ℕ, y z=if z=v+(L-j) then 2^j else if z=u+j then 1-(-1)^j*m (b+j*(L+1):ℕ) else m z := by
  have eq : (v:ℤ)+L-j=((v+(L-j):ℕ):ℤ) := by omega
  have keep₁ : ∀ (r : ℤ), r<0 → r≠(u:ℤ)+j := by intro r h;omega
  have keep₂ : ∀ (r : ℤ), r<0 → r≠(v:ℤ)+L-j := by intro r h;omega
  have keep₃ : ∀ (r : ℤ), r<0 → r≠(v:ℤ)+(L-j:ℕ) := by intro r h;omega
  have safe : safeLine W m gatherBlock := by
    simp (disch := omega) [gatherBlock,safeLine,Butterfly.safe,effect,update,
      ct.read,ct.rp,ct.pp,rd,resWr,powWr,va,keep₁,keep₂] at *
    exact ⟨fr,fu,eq ▸ fv⟩
  let y := gatherBlock.foldl effect m
  refine ⟨y,line_runs _ _ safe,?_,?_,?_,?_,?_⟩
  · simp (disch := omega) [y,gatherBlock,effect,update,ireg,rd,va,resWr,powWr,parity,power,
      ct.rp,ct.pp,ct.it,keep₁,keep₂] at *
  · simp (disch := omega) [y,gatherBlock,effect,update,unit,rd,va,resWr,powWr,parity,power,
      ct.rp,ct.pp,ct.one,keep₁,keep₂] at *
  · simp (disch := omega) [y,gatherBlock,effect,update,maxI,rd,va,resWr,powWr,parity,power,
      ct.rp,ct.pp,ct.lim,keep₁,keep₂] at *
  · constructor <;> simp (disch := omega) [y,gatherBlock,nextMemory,effect,update,
      ireg,check,maxI,rd,va,resWr,powWr,parity,power,nilReg,unit,stride,ct.read,ct.rp,
      keep₁,keep₂,ct.pp,ct.st,ct.sgn,ct.pow,ct.z,ct.one,ct.lim,Nat.succ_mul,Int.pow_succ,Nat.cast_add,Nat.cast_mul] at * <;> omega
  · intro z
    simp (disch := omega) [y,gatherBlock,effect,update,rd,va,resWr,powWr,parity,power,unit,
      ct.read,ct.one,ct.rp,ct.pp,ct.pow,ct.sgn,keep₁,keep₂,keep₃,eq,Nat.cast_add] at *
    all_goals grind

/-- Read successive left edges of the forward difference triangle. One output
array stores the residual numerators, the other stores the dyadic multipliers. -/
theorem gather_tables {W b u v L : ℕ} (C : ℕ → ℤ) (m : Memory) (start : GatherCtrl b u v L 0 m)
    (dataIn : ∀ j≤L, m (b+j*(L+1):ℕ)=V C j 0)
    (sep : b+L*(L+1)<u ∧ u+L<v)
    (fits : ∀ j≤L, Fits W ((b+j*(L+1):ℕ):ℤ) ∧ Fits W ((u+j:ℕ):ℤ) ∧ Fits W ((v+(L-j):ℕ):ℤ))
    (guard : ∀ j≤L+1, Fits W ((j:ℤ)-(L+1))) :
    ∃ f≤13*(L+1), ∃ y, Runs W gather m f y ∧
      (∀ j≤L, y (u+j:ℕ)=1-(-1)^j*V C j 0 ∧ y (v+j:ℕ)=2^(L-j)) ∧
      ∀ z : ℕ, z<u ∨ u+L<z ∧ z<v ∨ v+L<z → y z=m z := by
  let fr := fun (z : ℕ) => z<u ∨ u+L<z ∧ z<v ∨ v+L<z
  let I := fun i (x : Memory) => GatherCtrl b u v L i x ∧
    (∀ j < i, x (u+j:ℕ)=1-(-1)^j*V C j 0 ∧ x (v+(L-j):ℕ)=2^j) ∧
    ∀ z, fr z → x z=m z
  have action (i : ℕ) (hi : i<L+1) (x : Memory) (hx : I i x) :
      ∃ f≤10, ∃ y, Runs W (line gatherBlock) x f y ∧ y ireg=i ∧ y unit=1 ∧ y maxI=((L+1:ℕ):ℤ) ∧ I (i+1) (nextMemory y ireg check i (L+1)) := by
    obtain ⟨ctl,old,same⟩ := hx
    have hj : i≤L := by omega
    obtain ⟨y,r,it,one,lim,ctr,upd⟩ := gatherStep hj x ctl (fits i hj).1 (fits i hj).2.1 (fits i hj).2.2
    have aft (z : ℕ) : nextMemory y ireg check i (L+1) z=y z := by simp (disch := omega) [nextMemory,update,ireg,check]
    refine ⟨10,by decide,y,r,it,one,lim,ctr,?_,?_⟩
    · intro j h
      rw [aft,aft,upd,upd]
      by_cases equal : j=i
      · subst j
        have bound := Nat.mul_le_mul_right (L+1) hj
        have read := (same (b+i*(L+1)) (Or.inl (by omega))).trans (dataIn i hj)
        simp only [if_neg (show u+i≠v+(L-i) by omega),ite_true,read,and_self]
      · have prev := old j (by omega)
        simp only [if_neg (show u+j≠v+(L-i) by omega),if_neg (show u+j≠u+i by omega),
          if_neg (show v+(L-j)≠v+(L-i) by omega),if_neg (show v+(L-j)≠u+i by omega),prev.1,prev.2,and_self]
    · intro z hz; change z<u ∨ u+L<z ∧ z<v ∨ v+L<z at hz
      rw [aft,upd,if_neg (by omega),if_neg (by omega),same z hz]
  obtain ⟨f,hf,y,act,done⟩ := repeatN_runs (B:=10) (Nat.zero_lt_succ L) _ (by decide : maxI≠ireg) I
    (fun j hj => by simpa only [Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one] using guard j hj) action ⟨start,by omega,fun _ _ => rfl⟩
  refine ⟨f,by simpa only [Nat.mul_comm] using hf,y,act,?_,done.2.2⟩
  intro j hj
  have p := (done.2.1 (L-j) (by omega)).2
  rw [show L-(L-j)=j by omega] at p
  exact ⟨(done.2.1 j (by omega)).1,p⟩

end VWZClique.IntegerRAM.MaskScan.Forward
end

/- NativeMaskScanPrecompute -/
section
namespace VWZClique.IntegerRAM.MaskScan.Forward
open Structured Butterfly

structure Header (b u v L : ℕ) (m : Memory) : Prop where
  l : m inLen=L
  b : m inTriangle=b
  u : m inResidual=u
  v : m inPowers=v

private theorem start_forward {W b u v L : ℕ} (m : Memory) (h : Header b u v L m) :
    ∃ x, Runs W (line startF) m 7 x ∧ Controls b (b+(L+1)) ((L+1)*L) 0 x ∧ x check=(L:ℤ)-1 ∧
      ∀ z : ℕ, x z=m z := by
  let x := startF.foldl effect m
  have run : Runs W (line startF) m 7 x := line_runs _ _ (by simp [startF,safeLine,Butterfly.safe])
  refine ⟨x,run,?_,?_,?_⟩
  · constructor <;> simp [x,startF,effect,update,unit,ireg,rd,wr,maxI,stride,check,inLen,inTriangle,
      h.l,h.b,Nat.cast_add,Nat.cast_mul,Int.mul_comm] at *
  · simp [x,startF,effect,update,check,inLen,unit,h.l,maxI,rd,wr,stride,ireg] at *
  · intro z
    simp (disch := omega) [x,startF,effect,update,ireg,rd,wr,unit,maxI,stride,check]

private theorem start_gather {W b u v L : ℕ} (m : Memory) (h : Header b u v L m) :
    ∃ x, Runs W (line startG) m 10 x ∧ GatherCtrl b u v L 0 x ∧ ∀ z : ℕ, x z=m z := by
  let x := startG.foldl effect m
  have run : Runs W (line startG) m 10 x := line_runs _ _ (by simp [startG,safeLine,Butterfly.safe])
  refine ⟨x,run,?_,?_⟩
  · constructor <;> simp [x,startG,effect,update,unit,ireg,nilReg,rd,resWr,powWr,parity,power,maxI,stride,
      inPowers,inResidual,inLen,inTriangle,h.l,h.b,h.u,h.v,Nat.cast_add] at *
  · intro z
    simp (disch := omega) [x,startG,effect,update,ireg,rd,resWr,powWr,unit,maxI,nilReg,power,parity,stride]

/-- Evaluate the complete residual/power precomputation from its runtime
header, including the degenerate length-zero case. The cost is quadratic in L. -/
theorem precompute_run {W b u v L : ℕ} (C : ℕ→ℤ) (m : Memory) (h : Header b u v L m)
    (init : ∀ j≤L, m (b+j:ℕ)=C j) (space : 303<b ∧ b+(L+1)^2≤u ∧ u+L<v)
    (triFits : ∀ i≤(L+1)^2, Fits W ((b+i:ℕ):ℤ))
    (fits : ∀ j≤L, Fits W ((u+j:ℕ):ℤ) ∧ Fits W ((v+(L-j):ℕ):ℤ))
    (sg : Fits W ((L:ℤ)-1)) (tg : ∀ j≤(L+1)*L, Fits W ((j:ℤ)-(L+1)*L))
    (gg : ∀ j≤L+1, Fits W ((j:ℤ)-(L+1))) :
    ∃ f≤18+11*((L+1)*L)+13*(L+1), ∃ o, Runs W precompute m f o ∧
      (∀ j≤L, o (u+j:ℕ)=1-(-1)^j*V C j 0 ∧ o (v+j:ℕ)=2^(L-j)) ∧
      ∀ z : ℕ, z<b+(L+1) ∨ v+L<z → o z=m z := by
  have sq : (L+1)^2=L*(L+1)+(L+1) := by rw [Nat.pow_succ,Nat.pow_one,Nat.succ_mul]
  have strictly : b+L*(L+1)<u := by omega
  obtain ⟨x,xrun,ctl,test,xf⟩ := start_forward (W:=W) m h
  have input (j : ℕ) (hj : j≤L) := (xf (b+j)).trans (init j hj)
  have front : ∃ f≤1+11*((L+1)*L), ∃ y, Runs W (.whenNonnegative check forward) x f y ∧
      (∀ r j, r+j≤L → y (b+r*(L+1)+j:ℕ)=V C r j) ∧
      ∀ z : ℕ, z<b+(L+1) ∨ b+(L+1)^2≤z → y z=m z := by
    by_cases hz : L=0
    · subst L
      refine ⟨1,by decide,x,.guard_skip (test ▸ sg) (by omega),?_,fun z _ => xf z⟩
      intro r j h
      obtain rfl : r=0 := by omega
      obtain rfl : j=0 := by omega
      simpa [V] using input 0 (by omega)
    · obtain ⟨f,hf,y,act,tab,fr⟩ := triangle (by omega : 0<L) C x triFits tg ctl input
      exact ⟨1+f,by omega,y,.guard_take (test ▸ sg) (by omega) act,tab,fun z hh => (fr z hh).trans (xf z)⟩
  obtain ⟨g,hg,y,yr,rows,same⟩ := front
  have header : Header b u v L y := by
    exact ⟨(same 300 (Or.inl (by omega))).trans h.l,(same 301 (Or.inl (by omega))).trans h.b,
      (same 302 (Or.inl (by omega))).trans h.u,(same 303 (Or.inl (by omega))).trans h.v⟩
  obtain ⟨t,tr,tc,tf⟩ := start_gather (W:=W) y header
  have tt (j : ℕ) (hj : j≤L) : t (b+j*(L+1):ℕ)=V C j 0 := by simpa using (tf (b+j*(L+1))).trans (by simpa using rows j 0 (by omega))
  have fs (j : ℕ) (hj : j≤L) : Fits W ((b+j*(L+1):ℕ):ℤ) := by
    have hmul := Nat.mul_le_mul_right (L+1) hj
    exact triFits _ (by omega)
  obtain ⟨a,ha,o,act,dataOut,rest⟩ := gather_tables C t tc tt ⟨strictly,space.2.2⟩ (fun j hj => ⟨fs j hj,fits j hj⟩) gg
  refine ⟨_,by omega,o,.seq xrun (.seq yr (.seq tr act)),dataOut,?_⟩
  intro z hz
  exact (rest z (by omega)).trans ((tf z).trans (same z (by omega)))

end VWZClique.IntegerRAM.MaskScan.Forward
end

/- NativeMaskScanReady -/
section
namespace VWZClique.IntegerRAM.MaskScan
open Structured Graph RankSwap RankSwap.MaskEnumeration UniformFolds

theorem Forward.V_shift (C : ℕ→ℤ) (r j : ℕ) : Forward.V C r j=(shift^[r] C) j := by
  induction r generalizing j with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply',Forward.V,shift,ih,ih]

theorem label_den {L : ℕ} (z : Fin (4^L)) : totalN 4 2 z.val L =
    denominatorExponent (finFunctionFinEquiv.symm z : BasisLabel L) := by
  rw [totalN_sum,denominatorExponent,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  let d := (finFunctionFinEquiv.symm z : BasisLabel L) i
  change localN 2 (z.val/4^i.val%4) = if ¬d<2 then 1 else 0
  rw [← digit_extraction z i]
  change (if 2≤ d.val then 1 else 0) = if ¬d<2 then 1 else 0
  change (if 2≤ d.val then 1 else 0) = if ¬d.val<2 then 1 else 0
  by_cases h : d.val<2
  · simp [h,show ¬2≤ d.val by omega]
  · simp [h,show 2≤ d.val by omega]

/-- This fixed code writes precisely the dyadically cleared diagonal numerators
in the compact order of ordinary base-four integers used for projection. -/
theorem scaled_label_table {W K L c v base pw : ℕ}
    (hl : lower K L≤ L) (hw : width K L≤ L)
    (room : Division.Room W (5*5^L)) (sep : base+L< c ∧ c+4^L≤ v) (pp : pw+L< c)
    (fits : ∀ j<4^L, Fits W ((c+j:ℕ):ℤ) ∧ Fits W ((v+j:ℕ):ℤ))
    (addr : ∀ j≤ L, Fits W ((base+j:ℕ):ℤ)) (powAddr : ∀ j≤ L, Fits W ((pw+j:ℕ):ℤ)) (m : Memory)
    (p : Parameters m 4 L 3 4 base ((lower K L:ℤ)-1) ((lower K L:ℤ)+width K L+1)
      (residualNum (windowCoeff K L))) (pt : m powBase=pw) (powTab : ∀ a≤ L, m (pw+a:ℕ)=2^(L-a))
    (ctl : Controls (4^L) c v 0 0 m) :
    let key := labelKey L (lower K L) (width K L)
    ∃ f≤480*(2^L)^5, ∃ o, Runs W (scan scaleClass) m f o ∧ (∀ z, stationary (4^L) c v z → o z=m z) ∧
      Controls (4^L) c v (4^L) (outside L (lower K L) (width K L)).card o ∧
      ∀ z : Fin (4^L), (finFunctionFinEquiv.symm z : BasisLabel L)∈outside L (lower K L) (width K L) →
        o (c+rank key z.val:ℕ)=z.val ∧ o (v+rank key z.val:ℕ)=TraceDyadic.residualInt K L (finFunctionFinEquiv.symm z) := by
  have b4 : 4^L≤5^L := Nat.pow_le_pow_left (by decide) L
  have b5 : 1≤5^L := Nat.one_le_pow _ _ (by decide)
  have bl : L+1≤5^L := (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=L))).trans (Nat.pow_le_pow_left (by decide : 2≤5) L)
  have cut : ∀ j≤ L, Fits W (((lower K L:ℤ)-1)-j) ∧ Fits W ((j:ℤ)-((lower K L:ℤ)+width K L+1)) := by
    intro j hj; constructor <;> apply room.fits <;> omega
  obtain ⟨f,hf,o,run,frame,ctrl,atCell⟩ := scale_enumerate (residualNum (windowCoeff K L)) (by positivity) room
    (by omega) (by omega) (by omega) fits addr cut powAddr sep pp m p pt powTab ctl
  have bound := scan_budget (b:=4) (by decide) L
  have dom : 4^L*(2*digBudget L (5*5^L)+20)≤2*(4^L*(digBudget L (5*5^L)+15)) := by
    ring_nf; omega
  refine ⟨f,hf.trans (dom.trans (by omega)),o,run,frame,?_,?_⟩
  · rw [←label_count]; exact ctrl
  · intro z h
    obtain ⟨cc,vv⟩ := atCell z.val z.isLt ((labelKey_iff z).mpr h)
    have signOne : totalZ 4 4 z.val L=1 := by
      rw [totalZ_prod]; apply Finset.prod_eq_one
      intro i _
      exact if_neg (by omega : ¬4≤ z.val/4^i.val%4)
    change o (v+rank (labelKey L (lower K L) (width K L)) z.val:ℕ) = residualNum (windowCoeff K L) (totalN 4 3 z.val L)*totalZ 4 4 z.val L*2^(L-totalN 4 2 z.val L) at vv
    exact ⟨cc,by rw [label_pop,label_den,signOne,mul_one] at vv; exact vv⟩

theorem signed_mask_table {W L d c v base : ℕ} (hd : d≤ L) (C : ℕ→ℤ)
    (room : Division.Room W (5*5^L)) (sep : base+L< c ∧ c+5^L≤ v)
    (fits : ∀ j<5^L, Fits W ((c+j:ℕ):ℤ) ∧ Fits W ((v+j:ℕ):ℤ))
    (addr : ∀ j≤ L, Fits W ((base+j:ℕ):ℤ)) (m : Memory)
    (p : Parameters m 5 L 1 3 base d ((L:ℤ)+1) C) (ctl : Controls (5^L) c v 0 0 m) :
    ∃ f≤240*(2^L)^5, ∃ o, Runs W (scan classifier) m f o ∧ (∀ z, stationary (5^L) c v z → o z=m z) ∧
      Controls (5^L) c v (5^L) (Fintype.card (Terms L d)) o ∧
      ∀ z : Fin (5^L), z∈allowed L d →
        o (c+rank (maskKey L d) z.val:ℕ)=z.val ∧
        o (v+rank (maskKey L d) z.val:ℕ)=integerWeight C (finFunctionFinEquiv.symm z) := by
  have b5 : 1≤5^L := Nat.one_le_pow _ _ (by decide)
  have bl : L+1≤5^L := (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=L))).trans (Nat.pow_le_pow_left (by decide : 2≤5) L)
  have cut : ∀ j≤ L, Fits W ((d:ℤ)-j) ∧ Fits W ((j:ℤ)-(L+1)) := by
    intro j hj; constructor <;> apply room.fits <;> omega
  obtain ⟨f,hf,o,run,frame,ctrl,atCell⟩ := framed_scan (K:=digBudget L (5*5^L)+7)
    (by positivity : 0<5^L) sep.2 fits (fun j hj => by apply room.fits <;> omega)
    (maskKey L d) (fun j => C (totalN 5 1 j L)*totalZ 5 3 j L) classifier m ctl (fun j hj x same ctrl =>
      classify_one C (by decide) room (by omega) (by omega) (by omega) (by omega) (by omega) addr cut x
        (before_data sep p same) ctrl)
  refine ⟨f,hf.trans (scan_budget (b:=5) (by decide) L),o,run,frame,?_,?_⟩
  · rw [←mask_count]; exact ctrl
  · intro z h
    obtain ⟨cc,vv⟩ := atCell z.val z.isLt ((maskKey_iff z).mpr h)
    exact ⟨cc,vv.trans (mask_signed z C)⟩

end VWZClique.IntegerRAM.MaskScan
end

/- NativeMaskScanPower -/
section
namespace VWZClique.IntegerRAM.MaskScan.Pow
open Structured Butterfly

def outside (r : ℤ) := r≠x ∧ r≠ireg ∧ r≠flag ∧ r≠one

theorem runs {W n : ℕ} {b : ℤ} (m : Memory) (hn : m bound=n) (hb : m base=b)
    (fg : Fits W ((n:ℤ)-1)) (ft : ∀ z≤n, Fits W ((z:ℤ)-n)) :
    ∃ f≤5+4*n, ∃ o, Runs W command m f o ∧ o x=b^n ∧ ∀ r, outside r → o r=m r := by
  let s := setup.foldl effect m
  have prep : Runs W (line setup) m 4 s := line_runs _ _ (by simp [setup,safeLine,Butterfly.safe])
  have pre : s ireg=0 ∧ s one=1 ∧ s x=1 ∧ s flag=(n:ℤ)-1 := by simp [s,setup,effect,update,ireg,one,x,flag,bound,hn] at *
  have sf (r : ℤ) (h : outside r) : s r=m r := by
    obtain ⟨a,b,c,d⟩ := h; simp only [s,setup,List.foldl,effect,update,if_neg a,if_neg b,if_neg c,if_neg d]
  by_cases stop : n=0
  · subst n; exact ⟨5,by decide,s,.seq prep (.guard_skip (pre.2.2.2 ▸ fg) (by omega)),by simpa using pre.2.2.1,sf⟩
  let inv := fun (j : ℕ) (z : Memory) => z ireg=j ∧ z one=1 ∧ z x=b^j ∧ ∀ r, outside r → z r=m r
  have init : inv 0 s := ⟨pre.1,pre.2.1,by simpa using pre.2.2.1,sf⟩
  have action (j : ℕ) (_ : j<n) (z : Memory) (hz : inv j z) :
      ∃ f≤1, ∃ y, Runs W (.atom (.mul x x base)) z f y ∧ y ireg=j ∧ y one=1 ∧ y bound=n ∧ inv (j+1) (nextMemory y ireg flag j n) := by
    let y := update z x (z x*z base)
    have zbase := (hz.2.2.2 base (by unfold outside;decide)).trans hb
    have zh := (hz.2.2.2 bound (by unfold outside;decide)).trans hn
    refine ⟨1,by decide,y,.atom (.mul ..),?_,?_,?_,?_,?_,?_,?_⟩
    all_goals try simp [y,nextMemory,update,x,ireg,flag,one,bound,base,hz.1,hz.2.1,hz.2.2.1,zbase,zh,Int.pow_succ] at *
    intro r h; obtain ⟨a,b,c,d⟩ := h
    simp only [nextMemory,y,update,if_neg a,if_neg b,if_neg c,hz.2.2.2 r ⟨a,b,c,d⟩]
  obtain ⟨f,hf,o,body,done⟩ := repeatN_runs (B:=1) (by omega : 0<n) _ (by decide : bound≠ireg) inv ft action init
  exact ⟨_,by omega,o,.seq prep (.guard_take (pre.2.2.2 ▸ fg) (by omega) body),done.2.2.1,done.2.2.2⟩

end VWZClique.IntegerRAM.MaskScan.Pow
end

/- NativeMaskScanArena -/
section
namespace VWZClique.IntegerRAM.MaskScan.Arena
open Structured Butterfly

structure Placed (w N L : ℕ) (m : Memory) : Prop where
  l : m Lr=L
  c : m Cr=origin w N
  r : m Rr=slot w N 1
  p : m Pr=slot w N 2
  mc : m MC=slot w N 3
  mv : m MV=slot w N 4
  lc : m LC=slot w N 5
  lv : m LV=slot w N 6
  counts : m Arena.counts=slot w N 7
  n : m originalN=N
  four : m labelN=N^2

def preserveAddr (z : ℕ) := z<300 ∨ 319< z

set_option maxHeartbeats 2800000 in
theorem layout_runs {W w N L : ℕ} {source : ℤ} (m : Memory) (mn : m 0=N) (ml : m inputLen=L)
    (ms : m source=w) (sourceLow : 0< source ∧ source<297) :
    ∃ x, Runs W (line (layout source)) m 21 x ∧ Placed w N L x ∧ x (-2)=origin w N ∧ x (-12)=L ∧
      ∀ z : ℕ, preserveAddr z → x z=m z := by
  let x := (layout source).foldl effect m
  have run : Runs W (line (layout source)) m 21 x := line_runs _ _ (by simp [layout,safeLine,Butterfly.safe])
  have Slo (k : ℤ) (hk : k≤0) : source≠k := by omega
  have Shi (k : ℤ) (hk : 297≤ k) : source≠k := by omega
  have l : m 320=L := ml
  have next (r : ℤ) (h : r≠(-12) ∧ r≠(-2) ∧ r≠310 ∧ r≠309 ∧ r≠308 ∧ r≠307 ∧ r≠306 ∧ r≠303 ∧ r≠302 ∧ r≠301 ∧ r≠(-275) ∧ r≠313 ∧ r≠314 ∧ r≠300 ∧ r≠311 ∧ r≠(-5)) : x r=m r := by
    obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂,a₁₃,a₁₄,a₁₅,a₁₆⟩ := h
    simp only [x,layout,List.foldl,effect,update,if_neg a₁,if_neg a₂,if_neg a₃,if_neg a₄,if_neg a₅,if_neg a₆,
      if_neg a₇,if_neg a₈,if_neg a₉,if_neg a₁₀,if_neg a₁₁,if_neg a₁₂,if_neg a₁₃,if_neg a₁₄,if_neg a₁₅,if_neg a₁₆]
  refine ⟨x,run,?_,?_,?_,?_⟩
  · constructor
    all_goals simp (config := {maxSteps := 170000}) (disch := decide) [x,layout,effect,update,Slo,Shi,scratch,unit,Cr,Rr,Pr,Lr,MC,MV,LC,LV,counts,originalN,
      labelN,slab,inputLen,mn,l,ms,slot,origin,span,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
    all_goals ring
  · simp (config := {maxSteps := 170000}) (disch := decide) [x,layout,effect,update,Slo,Shi,scratch,unit,Cr,Rr,Pr,Lr,MC,MV,LC,LV,counts,originalN,
      labelN,slab,inputLen,mn,l,ms,origin,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
    ring
  · simp (config := {maxSteps := 170000}) [x,layout,effect,update,Lr,inputLen,unit,scratch,Cr,Rr,Pr,MC,MV,LC,LV,counts,slab,labelN,originalN,l]
  · intro z hz
    dsimp [preserveAddr] at hz
    apply next
    omega

end VWZClique.IntegerRAM.MaskScan.Arena
end

/- NativeMaskScanStart -/
section
namespace VWZClique.IntegerRAM.MaskScan.Arena
open Structured Butterfly

theorem make_radix {W L : ℕ} (m : Memory) (ml : m Lr=L) (fg : Fits W ((L:ℤ)-1)) (ft : ∀ j≤ L, Fits W ((j:ℤ)-L)) :
    ∃ f≤11+4*L, ∃ y, Runs W radixCommand m f y ∧ y maskN=(5:ℤ)^L ∧ ∀ z : ℕ, z≠312 → y z=m z := by
  let s := radixSetup.foldl effect m
  have run : Runs W (line radixSetup) m 5 s := line_runs _ _ (by simp [radixSetup,safeLine,Butterfly.safe])
  have k : s Pow.bound=L ∧ s Pow.base=5 ∧ s unit=1 := by simp [s,radixSetup,effect,update,unit,Pow.bound,Pow.base,Lr,ml] at *
  obtain ⟨f,hf,x,pow,v,fr⟩ := Pow.runs s k.1 k.2.1 fg ft
  let y := update x maskN (x Pow.x*x unit)
  have xu : x unit=1 := (fr unit (by unfold Pow.outside;decide)).trans k.2.2
  refine ⟨_,by omega,y,.seq run (.seq pow (.atom (.mul ..))),by simp [y,update,v,xu],?_⟩
  intro z hz
  have fi := fr (z:ℤ) (by unfold Pow.outside; dsimp [Pow.x,Pow.ireg,Pow.flag,Pow.one];omega)
  simp (disch := omega) [y,update,maskN,fi,s,radixSetup,effect,unit,Pow.base,Pow.bound,show (z:ℤ)≠312 by omega] at *

theorem init_mask {W b c v L d : ℕ} (C : ℕ→ℤ) (m : Memory) (mb : m Cr=b) (mc : m MC=c)
    (mv : m MV=v) (ml : m Lr=L) (md : m Dr=d) (mn : m maskN=(5:ℤ)^L) (pos : 0< b)
    (tab : ∀ i≤ L, m (b+i:ℕ)=C i) :
    ∃ x, Runs W (line maskInit) m 15 x ∧ Parameters x 5 L 1 3 b d ((L:ℤ)+1) C ∧
      Controls (5^L) c v 0 0 x ∧ ∀ z : ℕ, 0< z → x z=m z := by
  let x := maskInit.foldl effect m
  have run : Runs W (line maskInit) m 15 x := line_runs _ _ (by simp [maskInit,safeLine,Butterfly.safe])
  have fr (z : ℕ) (hz : 0< z) : x z=m z := by
    simp (disch := omega) [x,maskInit,effect,update,idx,unit,len,countFrom,signFrom,coef,leftCut,rightCut,outC,outV,lim,show z≠0 by omega] at *
  refine ⟨x,run,?_,?_,fr⟩
  · constructor
    all_goals first | exact fun j hj => (fr (b+j) (by omega)).trans (tab j hj) |
      simp [x,maskInit,effect,update,Cr,MC,MV,Lr,Dr,maskN,lim,unit,idx,len,countFrom,signFrom,coef,leftCut,rightCut,outC,outV,
        mb,mc,mv,ml,md,mn] at *
  · constructor <;> simp [x,maskInit,effect,update,Cr,MC,MV,Lr,Dr,maskN,lim,unit,idx,len,countFrom,signFrom,coef,leftCut,rightCut,outC,outV,
        mb,mc,mv,ml,md,mn,Nat.cast_pow] at *

theorem init_label {W b pw c v N L a d : ℕ} (C : ℕ→ℤ) (m : Memory) (mb : m Rr=b) (mp : m Pr=pw) (mc : m LC=c)
    (mv : m LV=v) (ml : m Lr=L) (ma : m Ar=a) (md : m Dr=d) (mn : m labelN=N) (pos : 0< b)
    (tab : ∀ i≤ L, m (b+i:ℕ)=C i) :
    ∃ x, Runs W (line labelInit) m 15 x ∧ Parameters x 4 L 3 4 b ((a:ℤ)-1) ((a:ℤ)+d+1) C ∧
      Controls N c v 0 0 x ∧ x powBase=pw ∧ ∀ z : ℕ, 0< z → x z=m z := by
  let x := labelInit.foldl effect m
  have run : Runs W (line labelInit) m 15 x := line_runs _ _ (by simp [labelInit,safeLine,Butterfly.safe])
  have fr (z : ℕ) (hz : 0< z) : x z=m z := by
    simp (disch := omega) [x,labelInit,effect,update,idx,unit,len,countFrom,signFrom,coef,powBase,leftCut,rightCut,outC,outV,lim,show z≠0 by omega] at *
  refine ⟨x,run,?_,?_,?_,fr⟩
  · constructor
    all_goals first | exact fun j hj => (fr (b+j) (by omega)).trans (tab j hj) |
      simp [x,labelInit,effect,update,Rr,Pr,LC,LV,Lr,Ar,Dr,labelN,lim,unit,idx,len,countFrom,signFrom,coef,powBase,leftCut,rightCut,outC,outV,
        mb,mp,mc,mv,ml,ma,md,mn] at *
  · constructor <;> simp [x,labelInit,effect,update,Rr,Pr,LC,LV,Lr,Ar,Dr,labelN,lim,unit,idx,len,countFrom,signFrom,coef,powBase,leftCut,rightCut,outC,outV,
        mb,mp,mc,mv,ml,ma,md,mn] at *
  · simp [x,labelInit,effect,update,Rr,Pr,LC,LV,Lr,Ar,Dr,labelN,lim,unit,idx,len,countFrom,signFrom,coef,powBase,leftCut,rightCut,outC,outV,
        mb,mp,mc,mv,ml,ma,md,mn] at *

end VWZClique.IntegerRAM.MaskScan.Arena
end

/- NativeMaskScanSave -/
section
namespace VWZClique.IntegerRAM.MaskScan.Arena
open Structured Butterfly

theorem save_mask {W r c a : ℕ} (m : Memory) (b : m MC=c) (p : m outC=((c+r:ℕ):ℤ))
    (hl : m counts=a) (addr : Fits W (a:ℤ)) :
    ∃ o, Runs W (line saveMask) m 2 o ∧ o (a:ℤ)=r ∧ ∀ z : ℕ, z≠a → o z=m z := by
  let o := saveMask.foldl effect m
  have safe : safeLine W m saveMask := by simpa [saveMask,safeLine,Butterfly.safe,effect,update,counts,scratch,hl] using addr
  refine ⟨o,line_runs _ _ safe,?_,?_⟩
  · simp [o,saveMask,effect,update,scratch,counts,outC,MC,hl,p,b,Nat.cast_add] at *
  · intro z hz
    simp (disch := omega) [o,saveMask,effect,update,scratch,counts,hl,hz] at *

theorem save_label {W N r c a : ℕ} (m : Memory) (b : m LC=c) (p : m outC=((c+r:ℕ):ℤ))
    (n : m originalN=N) (u : m unit=1) (hl : m counts=a) (addr : Fits W ((a+1:ℕ):ℤ)) (low : 320≤ a) :
    ∃ o, Runs W (line saveLabel) m 4 o ∧ o ((a+1:ℕ):ℤ)=r ∧ o 0=N ∧ ∀ z : ℕ, z≠0 → z≠a+1 → o z=m z := by
  let o := saveLabel.foldl effect m
  have safe : safeLine W m saveLabel := by simpa [saveLabel,safeLine,Butterfly.safe,effect,update,counts,scratch,ptr,unit,hl,u,Nat.cast_add] using addr
  refine ⟨o,line_runs _ _ safe,?_,?_,?_⟩
  · simp (disch := omega) [o,saveLabel,effect,update,scratch,counts,outC,LC,ptr,unit,originalN,hl,p,b,u,Nat.cast_add,show (a:ℤ)+1≠0 by omega] at *
  · simp (disch := omega) [o,saveLabel,effect,update,scratch,counts,outC,LC,ptr,unit,originalN,hl,p,b,u,n,Nat.cast_add] at *
    all_goals split <;> omega
  · intro z hz ha
    simp (disch := omega) [o,saveLabel,effect,update,scratch,counts,outC,LC,ptr,unit,originalN,hl,u,
      hz,show (z:ℤ)≠(a:ℤ)+1 by omega] at *

end VWZClique.IntegerRAM.MaskScan.Arena
end

/- NativeMaskScanBoth -/
section
namespace VWZClique.IntegerRAM.MaskScan.Arena
open Structured Graph RankSwap RankSwap.MaskEnumeration UniformFolds Butterfly

/-- Per-depth addresses and the counters supplied by coefficient generation. -/
structure Config (K L b r p u v t s e : ℕ) (m : Memory) : Prop where
  length : m Lr=L
  n : m originalN=((2^L:ℕ):ℤ)
  a : m Ar=lower K L
  d : m Dr=width K L
  mc : m MC=u
  mv : m MV=v
  lc : m LC=t
  lv : m LV=s
  co : m counts=e
  cp : m Cr=b
  rp : m Rr=r
  pp : m Pr=p
  maskN : m Arena.maskN=(5:ℤ)^L
  labelN : m Arena.labelN=((4^L:ℕ):ℤ)

structure Buffers (L b r p u v t s e : ℕ) : Prop where
  start : 320< b
  row : b+L< r
  residual : r+L< p
  powers : p+L< u
  codes : u+5^L≤ v
  weights : v+5^L≤ t
  labels : t+4^L≤ s
  diagonal : s+4^L≤ e

private theorem heapStationary {N c v : ℕ} (z : ℕ) (lo : z< c ∨ c+N≤ z) (hi : z< v ∨ v+N≤ z) :
    stationary N c v z := by
  refine ⟨?_,?_,by omega,by omega⟩
  · refine ⟨⟨Or.inr (Or.inl (by omega)),?_⟩,?_,?_,?_,?_⟩ <;> dsimp [zero,ptr,value,flag,cmp] <;> omega
  · unfold privateCell; dsimp [idx,lim,unit,test,outC,outV]; omega

theorem compact_run {W K L b r p u v t s e : ℕ} (m : Memory) (cfg : Config K L b r p u v t s e m)
    (geo : Buffers L b r p u v t s e) (bounds : lower K L≤ L ∧ width K L≤ L)
    (room : Division.Room W (5*5^L)) (fitaddr : ∀ j≤ e+1, Fits W (j:ℤ))
    (coeff : ∀ i≤ L, m (b+i:ℕ)=windowCoeff K L i)
    (nums : ∀ i≤ L, m (r+i:ℕ)=residualNum (windowCoeff K L) i)
    (dyad : ∀ i≤ L, m (p+i:ℕ)=2^(L-i)) :
    ∃ f≤36+720*(2^L)^5, ∃ o, Runs W compact m f o ∧ o 0=((2^L:ℕ):ℤ) ∧ CompactTables K L u v t s e o ∧
      ∀ z : ℕ, 0< z → z< u ∨ e+1< z → o z=m z := by
  obtain ⟨b0,br,rp,pu,uv,vt,ts,se⟩ := geo
  have n5 : 0<5^L := Nat.pow_pos (by decide)
  have n4 : 0<4^L := Nat.pow_pos (by decide)
  obtain ⟨x,xa,xp,xc,xf⟩ := init_mask (W:=W) (windowCoeff K L) m cfg.cp cfg.mc cfg.mv cfg.length cfg.d cfg.maskN (by omega) coeff
  obtain ⟨f,hf,y,yr,ys,yc,rows⟩ := signed_mask_table bounds.2 (windowCoeff K L) room ⟨by omega,uv⟩
    (fun j hj => ⟨fitaddr _ (by omega),fitaddr _ (by omega)⟩) (fun j hj => fitaddr _ (by omega)) x xp xc
  have ysame (z : ℕ) (hz : 0< z) (l : z< u ∨ v+5^L≤ z) : y z=m z :=
    (ys _ (heapStationary z (by omega) (by omega))).trans (xf z hz)
  obtain ⟨g,gr,count₁,gf⟩ := save_mask y
    ((ysame 306 (by decide) (Or.inl (by omega))).trans cfg.mc) yc.p
    ((ysame 310 (by decide) (Or.inl (by omega))).trans cfg.co) (fitaddr e (by omega))
  have gs (z : ℕ) (hz : 0< z) (a : z< u ∨ v+5^L≤ z) (h : z≠e) : g z=m z :=
    (gf z h).trans (ysame z hz a)
  have low (z : ℕ) (lo : 0< z) (hi : z< u) : g z=m z := gs z lo (Or.inl hi) (by omega)
  obtain ⟨h,hr,hp,hc,pp,hfr⟩ := init_label (W:=W) (residualNum (windowCoeff K L)) g
    ((low 302 (by decide) (by omega)).trans cfg.rp) ((low 303 (by decide) (by omega)).trans cfg.pp)
    ((low 308 (by decide) (by omega)).trans cfg.lc) ((low 309 (by decide) (by omega)).trans cfg.lv)
    ((low 300 (by decide) (by omega)).trans cfg.length) ((low 304 (by decide) (by omega)).trans cfg.a)
    ((low 305 (by decide) (by omega)).trans cfg.d) ((low 314 (by decide) (by omega)).trans cfg.labelN) (by omega)
    (fun i hi => (low _ (by omega) (by omega)).trans (nums i hi))
  obtain ⟨k,hk,l,lr,ls,lc,project⟩ := scaled_label_table bounds.1 bounds.2 room ⟨by omega,ts⟩ (by omega)
    (fun j hj => ⟨fitaddr _ (by omega),fitaddr _ (by omega)⟩) (fun j hj => fitaddr _ (by omega)) (fun j hj => fitaddr _ (by omega))
    h hp pp (fun i hi => (hfr _ (by omega)).trans ((low _ (by omega) (by omega)).trans (dyad i hi))) hc
  have lg (z : ℕ) (hz : 0< z) (safe : z< t ∨ s+4^L≤ z) : l z=g z :=
    (ls _ (heapStationary z (by omega) (by omega))).trans (hfr _ hz)
  have lm (z : ℕ) (hz : 0< z) (less : z< u) : l z=m z := (lg z hz (Or.inl (by omega))).trans (low z hz less)
  obtain ⟨o,done,count₂,native,ofr⟩ := save_label l
    ((lm 308 (by decide) (by omega)).trans cfg.lc) lc.p
    ((lm 311 (by decide) (by omega)).trans cfg.n) lc.one
    ((lm 310 (by decide) (by omega)).trans cfg.co) (fitaddr (e+1) (by omega)) (by omega)
  refine ⟨_,by omega,o,.seq xa (.seq yr (.seq gr (.seq hr (.seq lr done)))),native,?_,?_⟩
  · refine ⟨(ofr e (by omega) (by omega)).trans ((lg _ (by omega) (Or.inr (by omega))).trans count₁),count₂,?_,?_⟩
    · intro z hz
      have sm := rank_le (maskKey L (width K L)) z.val
      have zlt := z.isLt
      have rest (a : ℕ) (ha : u≤ a ∧ a< t) : o a=y a :=
        (ofr a (by omega) (by omega)).trans ((lg a (by omega) (Or.inl ha.2)).trans (gf a (by omega)))
      obtain ⟨aa,bb⟩ := rows z hz
      exact ⟨(rest _ (by omega)).trans aa,(rest _ (by omega)).trans bb⟩
    · intro z hz
      have sm := rank_le (labelKey L (lower K L) (width K L)) z.val
      have zlt := z.isLt
      obtain ⟨aa,bb⟩ := project z hz
      exact ⟨(ofr _ (by omega) (by omega)).trans aa,(ofr _ (by omega) (by omega)).trans bb⟩
  · intro z hz outside
    exact (ofr _ (by omega) (by omega)).trans ((lg _ hz (by omega)).trans (gs _ hz (by omega) (by omega)))

end VWZClique.IntegerRAM.MaskScan.Arena
end

/- NativeSignedDivision -/
section
/-! Exact signed division on the published add/subtract/multiply word machine.
The divisor is positive. A fixed scan takes one quotient bit per iteration. -/
namespace VWZClique.IntegerRAM.SignedDivision
open Structured

/-- The inputs lie outside the range of scratch cells, so they are preserved. -/
def Frame (m out : Memory) := ∀ z : ℤ, z < signReg ∨ result < z ∧ z ≠ remn → out z = m z

private theorem frame_refl (m : Memory) : Frame m m := fun _ _ => rfl
private theorem frame_trans {m u v : Memory} (a : Frame m u) (b : Frame u v) : Frame m v :=
  fun z hz => (b z hz).trans (a z hz)

private theorem frame_tick (m : Memory) (q h : ℕ) : Frame m (nextMemory m index flag q h) := by
  intro z hz
  have h1 : z ≠ index := by rcases hz with h|h <;> norm_num [signReg,result,index] at * <;> omega
  have h2 : z ≠ flag := by rcases hz with h|h <;> norm_num [signReg,result,flag] at * <;> omega
  simp [nextMemory,update,h1,h2]

/-- After doubling the running quotient and remainder, subtract a single divisor
threshold if the doubled remainder reaches it. -/
theorem digit_runs {W : ℕ} (m : Memory) (u : m unit=1)
    (hf : Fits W (2*m remn-m threshold)) :
    ∃ f out, f≤6 ∧ Runs W digit m f out ∧
      out remn = 2*m remn - (if m threshold ≤ 2*m remn then m threshold else 0) ∧
      out result = 2*m result + (if m threshold ≤ 2*m remn then 1 else 0) ∧
      (∀ z, z ≠ remn → z ≠ result → z ≠ flag → out z=m z) := by
  let a := update m result (m result+m result)
  let b := update a remn (a remn+a remn)
  let c := update b flag (b remn-b threshold)
  have ca : c flag = 2*m remn-m threshold := by simp [c,b,a,update,flag,threshold,remn,result,two_mul]
  have left : Runs W (.atom (.add result result result)) m 1 a := .atom (.add ..)
  have middle : Runs W (.atom (.add remn remn remn)) a 1 b := .atom (.add ..)
  have test : Runs W (.atom (.sub flag remn threshold)) b 1 c := .atom (.sub ..)
  by_cases good : m threshold ≤ 2*m remn
  · let d := update c remn (c remn-c threshold)
    let e := update d result (d result+d unit)
    have act : Runs W save c 2 e := .seq (.atom (.sub ..)) (.atom (.add ..))
    refine ⟨6,e,le_rfl,.seq left (.seq middle (.seq test (.guard_take (by rwa [ca]) (by rw [ca]; omega) act))),?_,?_,?_⟩
    · rw [if_pos good]; simp [e,d,c,b,a,update,flag,threshold,remn,result,two_mul]
    · rw [if_pos good]; simp [e,d,c,b,a,update,flag,threshold,remn,result,unit,two_mul] at u ⊢
      omega
    · intro z hr hq hflag; simp [e,d,c,b,a,update,hr,hq,hflag]
  · refine ⟨4,c,by decide,.seq left (.seq middle (.seq test (.guard_skip (by rwa [ca]) (by rw [ca]; omega)))),?_,?_,?_⟩
    · rw [if_neg good]; simp [c,b,a,update,flag,threshold,remn,result,two_mul]
    · rw [if_neg good]; simp [c,b,a,update,flag,threshold,remn,result,two_mul]
    · intro z hr hq hflag; simp [c,b,a,update,hr,hq,hflag]

/-- The input remainder A is in [0,D). After h iterations, Q D + R = 2^h A,
with R in [0,D). The bound counts all arithmetic, tests and loop instructions. -/
theorem scan_runs {W h M : ℕ} (hh : 0<h) (hM : h≤M)
    (room : Graph.Division.Room W M) {D A : ℤ} (hD : D≤(M:ℤ)) (a0 : 0≤A) (aD : A<D)
    (m : Memory) (mi : m index=0) (mu : m unit=1) (mh : m length=h)
    (mq : m result=0) (mr : m remn=A) (md : m threshold=D) :
    ∃ f out, f≤h*9 ∧ Runs W scan m f out ∧ Frame m out ∧
      0≤out remn ∧ out remn<D ∧ out result*D+out remn=(2:ℤ)^h*A ∧ out signReg=m signReg := by
  let inv := fun (j : ℕ) (x : Memory) =>
    x index=j ∧ x unit=1 ∧ x length=h ∧ x threshold=D ∧
    0≤x remn ∧ x remn<D ∧ x result*D+x remn=(2:ℤ)^j*A ∧ Frame m x ∧ x signReg=m signReg
  have init : inv 0 m := ⟨by simpa using mi,mu,mh,md,by omega,by omega,by simp [mq,mr],frame_refl m,rfl⟩
  have guard (q : ℕ) (hq : q≤h) : Fits W ((q:ℤ)-h) := by apply room.fits <;> omega
  have step (q : ℕ) (_ : q<h) (x : Memory) (hx : inv q x) :
      ∃ f : ℕ, f≤6 ∧ ∃ y : Memory, Runs W digit x f y ∧ y index=q ∧ y unit=1 ∧ y length=h ∧
        inv (q+1) (nextMemory y index flag q h) := by
    obtain ⟨xi,xu,xh,xd,rl,rh,eqn,fr,sg⟩ := hx
    obtain ⟨f,y,hf,run,yr,yq,kept⟩ := digit_runs x xu
      (by rw [xd]; apply room.fits <;> omega)
    have yi := (kept index (by decide) (by decide) (by decide)).trans xi
    have yu := (kept unit (by decide) (by decide) (by decide)).trans xu
    have yh := (kept length (by decide) (by decide) (by decide)).trans xh
    have yd := (kept threshold (by decide) (by decide) (by decide)).trans xd
    have fr' : Frame x y := by
      intro z hz; apply kept z <;> rcases hz with hh|hh <;> norm_num [remn,result,signReg,flag] at * <;> omega
    refine ⟨f,hf,y,run,yi,yu,yh,?_⟩
    have rng : 0≤y remn ∧ y remn<D := by rw [yr,xd]; split <;> omega
    have coeff : y result*D+y remn=2^(q+1)*A := by
      rw [yr,yq,xd,pow_succ]
      split <;> nlinarith only [eqn]
    have ys := (kept signReg (by decide) (by decide) (by decide)).trans sg
    refine ⟨?_,?_,?_,?_,?_,?_,?_,frame_trans fr (frame_trans fr' (frame_tick y q h)),?_⟩ <;>
      simp_all [nextMemory,update,index,flag,unit,length,threshold,remn,result,signReg]
  obtain ⟨f,hf,y,run,hy⟩ := repeatN_runs (W:=W) (B:=6) hh digit (by decide : length ≠ index)
    inv guard step init
  exact ⟨f,y,hf,run,hy.2.2.2.2.2.2.2.1,hy.2.2.2.2.1,hy.2.2.2.2.2.1,hy.2.2.2.2.2.2.1,hy.2.2.2.2.2.2.2.2⟩

theorem scale_runs {W h M : ℕ} (hh : 0<h) (hM : h≤M) (room : Graph.Division.Room W M)
    (m : Memory) (mi : m index=0) (mu : m unit=1) (mh : m length=h) :
    ∃ f out, f≤h*4 ∧ Runs W scale m f out ∧ out threshold=2^h*m threshold ∧
      ∀ z, z ≠ threshold → z ≠ index → z ≠ flag → out z=m z := by
  let inv := fun (j : ℕ) (x : Memory) => x index=j ∧ x unit=1 ∧ x length=h ∧
    x threshold=2^j*m threshold ∧ ∀ z, z ≠ threshold → z ≠ index → z ≠ flag → x z=m z
  have init : inv 0 m := ⟨by simpa using mi,mu,mh,by simp,fun _ _ _ _ => rfl⟩
  have guard (q : ℕ) (hq : q≤h) : Fits W ((q:ℤ)-h) := by apply room.fits <;> omega
  have step (q : ℕ) (_ : q<h) (x : Memory) (hx : inv q x) :
      ∃ f : ℕ, f≤1 ∧ ∃ y : Memory, Runs W grow x f y ∧ y index=q ∧ y unit=1 ∧ y length=h ∧
        inv (q+1) (nextMemory y index flag q h) := by
    obtain ⟨xi,xu,xh,xd,fr⟩ := hx
    let y := update x threshold (x threshold+x threshold)
    have act : Runs W grow x 1 y := .atom (.add ..)
    refine ⟨1,le_rfl,y,act,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [y,update,index,threshold] using xi
    · simpa [y,update,unit,threshold] using xu
    · simpa [y,update,length,threshold] using xh
    · simp [nextMemory,update,index,flag]
    · simpa [nextMemory,y,update,index,flag,unit,threshold] using xu
    · simpa [nextMemory,y,update,index,flag,length,threshold] using xh
    · simp [nextMemory,y,update,index,flag,threshold,xd,pow_succ]; ring
    · intro z hd hi hf; simpa [nextMemory,y,update,hd,hi,hf] using fr z hd hi hf
  obtain ⟨f,hf,y,run,hy⟩ := repeatN_runs (W:=W) (B:=1) hh grow (by decide : length ≠ index) inv guard step init
  exact ⟨f,y,hf,run,hy.2.2.2.1,hy.2.2.2.2⟩

theorem init_runs {W : ℕ} (m : Memory) (hf : Fits W (m value)) :
    ∃ f out, f≤9 ∧ Runs W initCode m f out ∧ Frame m out ∧
      out index=0 ∧ out unit=1 ∧ out result=0 ∧ out threshold=m divisor ∧
      out remn=|(m value)| ∧
      out signReg=(if m value<0 then -1 else 1) := by
  let a := update m unit 1
  let b := update a index (a index-a index)
  let c := update b result (b result-b result)
  let d := update c threshold (c divisor*c unit)
  let e := update d remn (d result-d value)
  let g := update e signReg (e result-e unit)
  have pre : ∀ {v : ℕ} {out : Memory},
     Runs W (.whenNonnegative value (.seq (.atom (.mul remn value unit)) (.atom (.one signReg)))) g v out →
     Runs W initCode m (1+(1+(1+(1+(1+(1+v)))))) out := fun act =>
    .seq (.atom (.one ..)) (.seq (.atom (.sub ..)) (.seq (.atom (.sub ..))
      (.seq (.atom (.mul ..)) (.seq (.atom (.sub ..)) (.seq (.atom (.sub ..)) act)))))
  have gv : g value=m value := by simp [g,e,d,c,b,a,update,value,signReg,remn,result,index,unit,threshold]
  by_cases neg : m value<0
  · refine ⟨7,g,by decide,pre (.guard_skip (by rwa [gv]) (by rwa [gv])),?_,?_,?_,?_,?_,?_,?_⟩
    · intro z hz
      simp [g,e,d,c,b,a,update,signReg,threshold,remn,result,index,unit] at *
      split_ifs <;> omega
    all_goals simp [g,e,d,c,b,a,update,signReg,threshold,remn,result,index,unit,divisor,value,neg,abs_of_neg neg] at *
  · let j := update g remn (g value*g unit)
    let k := update j signReg 1
    have run : Runs W (.seq (.atom (.mul remn value unit)) (.atom (.one signReg))) g 2 k :=
      .seq (.atom (.mul ..)) (.atom (.one ..))
    refine ⟨9,k,by decide,pre (.guard_take (by rwa [gv]) (by rwa [gv]) run),?_,?_,?_,?_,?_,?_,?_⟩
    · intro z hz
      simp [k,j,g,e,d,c,b,a,update,signReg,threshold,remn,result,index,unit] at *
      split_ifs <;> omega
    all_goals simp [k,j,g,e,d,c,b,a,update,signReg,threshold,remn,result,index,unit,divisor,value,
      neg,abs_of_nonneg (le_of_not_gt neg)] at *

/-- Signed truncating quotient, in at most 13h+11 instructions. A positive
divisor d may be arbitrary, and h bounds the quotient bit length. -/
theorem divide_runs {W h M : ℕ} (hh : 0<h) (hM : h≤M) (room : Graph.Division.Room W M)
    {d : ℕ} (hd : 0<d) (capacity : (2:ℤ)^h*d≤(M:ℤ)) (m : Memory)
    (bound : |m value|<(2:ℤ)^h*d) (md : m divisor=d) (mh : m length=h) :
    ∃ f out, f≤13*h+11 ∧ Runs W command m f out ∧ Frame m out ∧
      out result=(|m value|/(d:ℤ))*(if m value<0 then -1 else 1) := by
  let D := (2:ℤ)^h*d
  have dp : (0:ℤ)<d := by exact_mod_cast hd
  have aD : |m value|<D := bound
  have vf : Fits W (m value) := by
    apply room.fits <;> have v := abs_le.mp ((le_of_lt aD).trans capacity) <;> omega
  obtain ⟨f,a,hf,start,fr,ai,au,aq,ad,ar,asign⟩ := init_runs m vf
  have al := (fr length (by decide)).trans mh
  obtain ⟨g,b,hg,growRun,bd,bfix⟩ := scale_runs hh hM room a ai au al
  have bd' : b threshold=D := by rw [bd,ad,md]
  let c := update b index (b index-b index)
  have reset : Runs W (.atom (.sub index index index)) b 1 c := .atom (.sub ..)
  have cfix {j : ℤ} (hj : j≠index) (ht : j≠threshold) (hf : j≠flag) : c j=a j := by
    simpa [c,update,hj] using bfix j ht hj hf
  obtain ⟨s,v,hs,run,frame,rl,rh,eqn,vs⟩ := scan_runs hh hM room capacity (abs_nonneg _) aD c
    (by simp [c,update]) ((cfix (by decide) (by decide) (by decide)).trans au)
    ((cfix (by decide) (by decide) (by decide)).trans al)
    ((cfix (by decide) (by decide) (by decide)).trans aq)
    ((cfix (by decide) (by decide) (by decide)).trans ar)
    (by simpa [c,update,index,threshold] using bd')
  have frbc : Frame a c := by
    intro j hj; apply cfix <;> rcases hj with x|x <;> norm_num [signReg,threshold,flag,index,result] at * <;> omega
  -- The scan also preserves its caller's sign cell, which sits in the writable
  -- interval used by initialization. Recover this through the scan frame below.
  have positive : 0<(2:ℤ)^h := by positivity
  have ans : v result=|m value|/(d:ℤ) := by
    symm
    apply (Int.ediv_eq_iff_of_pos dp).2
    constructor
    · apply le_of_mul_le_mul_left (a:= (2:ℤ)^h) _ positive
      nlinarith only [eqn,rl]
    · apply lt_of_mul_lt_mul_left (a:= (2:ℤ)^h) _ positive.le
      nlinarith only [eqn,rh]
  have vsign := vs.trans ((cfix (j:=signReg) (by decide) (by decide) (by decide)).trans asign)
  let out := update v result (v result*v signReg)
  have last : Runs W (.atom (.mul result result signReg)) v 1 out := .atom (.mul ..)
  refine ⟨f+(g+(1+(s+1))),out,by omega,.seq start (.seq growRun (.seq reset (.seq run last))),?_,?_⟩
  · apply frame_trans fr (frame_trans frbc (frame_trans frame _))
    intro j hj
    have ne : j≠result := by rcases hj with hh|hh <;> norm_num [signReg,result] at * <;> omega
    simp [out,update,ne]
  · change v result*v signReg=_
    rw [ans,vsign]

end VWZClique.IntegerRAM.SignedDivision
end

/- NativeWindowInit -/
section
namespace VWZClique.IntegerRAM.WindowInit
open Structured SignedDivision

theorem constant_run (W : ℕ) {dest : ℤ} (hd : dest≠unit) (m : Memory) (hu : m unit=1) (n : ℕ) :
    Runs W (constant dest n) m (n+1) (update m dest n) := by
  induction n with
  | zero => simpa [constant] using Runs.atom (Step.sub (W:=W) m dest dest dest)
  | succ n ih =>
    have run := Runs.seq ih (Runs.atom (Step.add (W:=W) (update m dest n) dest dest unit))
    unfold constant
    convert run using 1
    funext z
    by_cases eq : z=dest <;> simp [update,eq,Ne.symm hd,hu]

theorem setup_runs {W L : ℕ} (c r : ℕ) (m : Memory) (hl : m Lreg=L) :
    ∃ x, Runs W (setup c r) m (1+((c+1)+((r+1)+(1+1)))) x ∧
      x value=((c*L:ℕ):ℤ) ∧ x divisor=r ∧ x length=((L+1:ℕ):ℤ) ∧
      ∀ z, z≠value → z≠divisor → z≠length → z≠unit → x z=m z := by
  let a := update m unit 1
  let b := update a value c
  let e := update b divisor r
  let f := update e value (e value*e Lreg)
  let x := update f length (f Lreg+f unit)
  have ac := constant_run W (by decide : value≠unit) a (by simp [a,update]) c
  have br := constant_run W (by decide : divisor≠unit) b (by simp [b,a,update,value,unit]) r
  refine ⟨x,.seq (.atom (.one ..)) (.seq ac (.seq br (.seq (.atom (.mul ..)) (.atom (.add ..))))),?_,?_,?_,?_⟩
  all_goals try intro z hv hd hh hu
  all_goals simp_all [x,f,e,b,a,update,value,divisor,length,unit,Lreg] 

theorem ratio_runs {W M L : ℕ} (c r : ℕ) (hr : 0<r) (hc : c≤r)
    (room : Graph.Division.Room W M) (cap : 2^(L+1)*r≤M) (m : Memory) (hl : m Lreg=L) :
    ∃ T x, T≤13*(L+1)+c+r+16 ∧ Runs W (ratio c r) m T x ∧
      x result=((c*L/r:ℕ):ℤ) ∧
      ∀ j : ℤ, value<j ∨ j<signReg → x j=m j := by
  obtain ⟨a,start,av,ad,ah,fr⟩ := setup_runs (W:=W) c r m hl
  have hb : L < 2^(L+1) := (Nat.lt_two_pow_self (n:=L)).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hm : L+1≤M := (Nat.succ_le_of_lt hb).trans ((Nat.le_mul_of_pos_right _ hr).trans cap)
  have aB : c*L<2^(L+1)*r := by
    calc
      c*L ≤ r*L := Nat.mul_le_mul_right _ hc
      _ < r*2^(L+1) := Nat.mul_lt_mul_of_pos_left hb hr
      _ = _ := Nat.mul_comm _ _
  have av0 : 0≤a value := by rw [av]; positivity
  obtain ⟨f,x,hf,run,frame,q⟩ := divide_runs (by omega : 0<L+1) hm room hr
    (by exact_mod_cast cap) a
    (by rw [abs_of_nonneg av0,av]; exact_mod_cast aB) ad ah
  refine ⟨_,x,by omega,.seq start run,?_,?_⟩
  · rw [if_neg (not_lt_of_ge av0),abs_of_nonneg av0,mul_one,av] at q
    exact_mod_cast q
  · intro j hj
    have protect : j<signReg ∨ result<j ∧ j≠remn := by
      rcases hj with h|h <;> norm_num [value,signReg,result,remn] at * <;> omega
    rw [frame j protect]
    apply fr <;> rcases hj with h|h <;> norm_num [value,signReg,divisor,length,unit] at * <;> omega

theorem copy_runs (W : ℕ) (m : Memory) (dst src : ℤ) (hs : src≠unit) :
    Runs W (copy dst src) m 2 (update (update m unit 1) dst (m src)) := by
  let a := update m unit 1
  have h : Runs W (copy dst src) m 2 (update a dst (a src*a unit)) :=
    .seq (.atom (.one ..)) (.atom (.mul ..))
  simpa [a,update,hs] using h

theorem window_runs {W M L K : ℕ} (hK : 4<K) (room : Graph.Division.Room W M)
    (cap : 2^(L+1)*(4*K)≤M) (m : Memory) (hl : m Lreg=L) :
    ∃ T out, T≤26*(L+1)+10*K+43 ∧ Runs W (window K) m T out ∧
      out loReg=UniformFolds.lower K L ∧ out hiReg=UniformFolds.upper K L ∧
      out degreeReg=UniformFolds.width K L ∧ out negLower= -((UniformFolds.lower K L:ℕ):ℤ) ∧
      out Lreg=L ∧ out (-2)=m (-2) ∧ ∀ j : ℕ, out (j:ℤ)=m j := by
  obtain ⟨f,a,hf,left,lo,keep⟩ := ratio_runs (K-4) (4*K) (by omega) (by omega) room cap m hl
  let b := update (update a unit 1) loReg (a result)
  have bL : b Lreg=L := by
    rw [show b Lreg=a Lreg by simp [b,update,Lreg,loReg,unit],keep _ (Or.inl (by decide)),hl]
  obtain ⟨g,c,hg,right,hi,keep'⟩ := ratio_runs (K+4) (4*K) (by omega) (by omega) room cap b bL
  let e := update (update c unit 1) hiReg (c result)
  let u := update e degreeReg (e hiReg-e loReg)
  let v := update u negLower (u negLower-u negLower)
  let out := update v negLower (v negLower-v loReg)
  have clo : c loReg=a result := by rw [keep' _ (Or.inl (by decide))]; simp [b,update]
  have monot : UniformFolds.lower K L≤UniformFolds.upper K L :=
    Nat.div_le_div_right (Nat.mul_le_mul_right L (by omega : K-4≤K+4))
  change a result=UniformFolds.lower K L at lo
  change c result=UniformFolds.upper K L at hi
  have after := copy_runs W a loReg result (by decide)
  have done := copy_runs W c hiReg result (by decide)
  have last : Runs W (.seq (.atom (.sub degreeReg hiReg loReg)) (.seq
      (.atom (.sub negLower negLower negLower)) (.atom (.sub negLower negLower loReg)))) e
      (1+(1+1)) out := .seq (.atom (.sub ..)) (.seq (.atom (.sub ..)) (.atom (.sub ..)))
  refine ⟨f+(2+(g+(2+(1+(1+1))))),out,by omega,.seq left (.seq after (.seq right (.seq done last))),?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [out,v,u,e,update,negLower,degreeReg,hiReg,loReg,unit] using clo.trans lo
  · simpa [out,v,u,e,update,negLower,degreeReg,hiReg,loReg,unit] using hi
  · rw [UniformFolds.width,Nat.cast_sub monot]
    simp [out,v,u,e,update,negLower,degreeReg,hiReg,loReg,unit] at *
    omega
  · simp [out,v,u,e,update,negLower,degreeReg,hiReg,loReg,unit] at *
    omega
  · simpa [out,v,u,e,update,negLower,degreeReg,hiReg,loReg,unit,Lreg] using
      (keep' Lreg (Or.inl (by decide))).trans bL
  · have sep := (keep' (-2) (Or.inl (by decide))).trans (show b (-2)=m (-2) by
      simpa [b,update,loReg,unit] using keep (-2) (Or.inl (by decide)))
    simpa [out,v,u,e,update,negLower,degreeReg,hiReg,loReg,unit] using sep
  · intro j
    have jl : value<(j:ℤ) := by dsimp [value]; omega
    simp [out,v,u,e,b,update,negLower,degreeReg,hiReg,loReg,unit,keep' _ (Or.inl jl),keep _ (Or.inl jl)]

end VWZClique.IntegerRAM.WindowInit
end

/- NativeFoldBits -/
section
namespace VWZClique.IntegerRAM.FoldBits
open Structured

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

/- NativeWindowSeed -/
section
namespace VWZClique.IntegerRAM.WindowSeed
open Structured FoldBits

def outside (j : ℤ) := j < -28 ∨ -20 < j ∧ j≠one

theorem parity_runs {W a M : ℕ} (cap : Graph.Division.Room W M) (size : a+1≤M)
    (m : Memory) (counter : m WindowInit.negLower= -(a:ℤ)) :
    ∃ t y, t ≤ 5+4*(a+1) ∧ Runs W parity m t y ∧ y sign=(-1:ℤ)^a ∧ y one=1 ∧
      ∀ j, outside j → y j=m j := by
  let s := paritySetup.foldl write m
  have start : Runs W (code paritySetup) m 5 s := code_runs _ _ _ (by simp [paritySetup,Safe,safe])
  let I := fun (q : ℕ) (x : Memory) => x idx=q ∧ x one=1 ∧ x lim=((a+1:ℕ):ℤ) ∧
    x zero=0 ∧ x sign= -((-1:ℤ)^q) ∧ ∀ j, outside j → x j=m j
  have init : I 0 s := by
    have cv : m (-8)= -(a:ℤ) := counter
    constructor <;> dsimp [s,paritySetup,write,update,I]
    all_goals try refine ⟨?_,?_,?_,?_,?_⟩
    all_goals try intro j hj
    all_goals dsimp [outside,WindowInit.negLower,idx,zero,one,lim,sign] at *
    all_goals simp (disch := omega) [cv] <;> try omega
  have iter (q : ℕ) (hq : q<a+1) (x : Memory) (h : I q x) :
      ∃ t≤1, ∃ y, Runs W (.atom (.sub sign zero sign)) x t y ∧ y idx=q ∧ y one=1 ∧
        y lim=((a+1:ℕ):ℤ) ∧ I (q+1) (nextMemory y idx test q (a+1)) := by
    obtain ⟨hx,ho,hl,hz,hs,fr⟩ := h
    let y := update x sign (x zero-x sign)
    refine ⟨1,le_rfl,y,.atom (.sub ..),?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals try intro j hj
    all_goals dsimp [outside,one,zero,sign,idx,test,lim] at *
    all_goals simp (disch := omega) [y,nextMemory,update,one,zero,sign,idx,test,lim,hx,ho,hl,hz,hs,pow_succ,fr, *] <;> try omega
  obtain ⟨f,hf,x,run,done⟩ := repeatN_runs (W:=W) (B:=1) (by omega : 0<a+1) _
    (by decide : lim≠idx) I (fun j hj => cap.fits (by omega) (by omega)) iter init
  exact ⟨_,x,by omega,.seq start run,by simpa [pow_succ] using done.2.2.2.2.1,done.2.1,done.2.2.2.2.2⟩

theorem fill_runs {W L b d M : ℕ} (cap : Graph.Division.Room W M) (bdd : b+L+1≤M) (hd : d≤L)
    (m : Memory) (hl : m WindowInit.Lreg=L) (baseV : m base=b) (deg : m WindowInit.degreeReg=d)
    (unit : m one=1) (v : ℤ) (sg : m sign=v) :
    ∃ t y, t≤3+9*(L+1) ∧ Runs W fill m t y ∧
      (∀ j≤L, y ((b+j:ℕ):ℤ)=if j≤d then v else 0) ∧ y one=1 ∧
      (∀ i : ℤ, i<0 → outside i → y i=m i) ∧
      ∀ i : ℕ, i < b ∨ b+L < i → y i=m i := by
  let s := fillSetup.foldl write m
  let I := fun (q : ℕ) (x : Memory) => x idx=q ∧ x one=1 ∧ x lim=((L+1:ℕ):ℤ) ∧
    x ptr=((b+q:ℕ):ℤ) ∧ x sign=v ∧ x WindowInit.degreeReg=d ∧
    (∀ j<q, x ((b+j:ℕ):ℤ)=if j≤d then v else 0) ∧
    (∀ i : ℤ, i<0 → outside i → x i=m i) ∧ ∀ i : ℕ, i < b ∨ b+q ≤ i → x i=m i
  have start : Runs W (code fillSetup) m 3 s := code_runs _ _ _ (by simp [fillSetup,Safe,safe])
  have init : I 0 s := by
    refine ⟨?_,?_,?_,?_,?_,?_,by omega,?_,?_⟩
    all_goals try intro i h hi
    all_goals try intro i h
    all_goals dsimp [outside,one,zero,sign,idx,test,lim,ptr,base,WindowInit.Lreg,WindowInit.degreeReg] at *
    all_goals simp (disch := omega) [s,fillSetup,write,update,one,zero,sign,idx,test,lim,ptr,base,WindowInit.Lreg,WindowInit.degreeReg, *] <;> split_ifs <;> omega
  have iter (q : ℕ) (hq : q<L+1) (x : Memory) (h : I q x) :
      ∃ t≤6, ∃ y, Runs W fillOne x t y ∧ y idx=q ∧ y one=1 ∧ y lim=((L+1:ℕ):ℤ) ∧
        I (q+1) (nextMemory y idx test q (L+1)) := by
    obtain ⟨hx,ho,hn,hp,hs,hdeg,earlier,neg,fr⟩ := h
    let a := before.foldl write x
    let c := if q≤d then update a term (a sign*a one) else a
    have run₁ : Runs W (code before) x 2 a := code_runs _ _ _ (by simp [before,Safe,safe])
    have cmp : a cut=(d:ℤ)-q := by simpa [a,before,write,update,WindowInit.degreeReg,idx,cut,term] using congrArg₂ (·-·) hdeg hx
    have testFit : Fits W (a cut) := by rw [cmp]; apply cap.fits <;> omega
    have run₂ : Runs W (.whenNonnegative cut (.atom (.mul term sign one))) a (if q≤d then 2 else 1) c := by
      by_cases h : q≤d
      · simpa only [c,if_pos h] using Runs.guard_take testFit (by rw [cmp]; omega) (Runs.atom (Step.mul a term sign one))
      · simpa only [c,if_neg h] using (@Runs.guard_skip W cut (.atom (.mul term sign one)) a testFit (by rw [cmp]; omega))
    have avail (i : ℤ) (a₁ : i≠term) (a₂ : i≠cut) : c i=x i := by
      by_cases e : q≤d <;> simp [c,e,a,before,write,update,a₁,a₂]
    have data : c term=if q≤d then v else 0 := by
      have s : x (-24)=v := hs
      have o : x (-6)=1 := ho
      by_cases e : q≤d <;> simp [c,e,a,before,write,update,cut,term,one,sign,s,o]
    have cp := (avail ptr (by decide) (by decide)).trans hp
    have co := (avail one (by decide) (by decide)).trans ho
    have ptrFit : Fits W (c ptr) := by rw [cp]; apply cap.fits <;> omega
    let y := writeCell.foldl write c
    have run₃ : Runs W (code writeCell) c 2 y := code_runs _ _ _ (by simpa [writeCell,Safe,safe] using ptrFit)
    have keep (i : ℤ) (o : i≠ptr) (u : i≠((b+q:ℕ):ℤ)) (z : i≠term) (t : i≠cut) : y i=x i := by
      have ne : i≠(b:ℤ)+q := by exact_mod_cast u
      simpa [y,writeCell,write,update,cp,o,ne] using avail i z t
    have step (i : ℤ) (h₁ : i≠idx) (h₂ : i≠test) : nextMemory y idx test q (L+1) i=y i := by simp [nextMemory,update,h₁,h₂]
    have stepN (i : ℕ) : nextMemory y idx test q (L+1) i=y i := step _ (by dsimp [idx];omega) (by dsimp [test];omega)
    have k (i : ℤ) (hi : i<0) (a₁ : i≠ptr) (a₂ : i≠term) (a₃ : i≠cut) : y i=x i := keep i a₁ (by omega) a₂ a₃
    have yi := (k idx (by decide) (by decide) (by decide) (by decide)).trans hx
    have yo := (k one (by decide) (by decide) (by decide) (by decide)).trans ho
    have yl := (k lim (by decide) (by decide) (by decide) (by decide)).trans hn
    refine ⟨_,by split <;> decide,y,.seq run₁ (.seq run₂ run₃),yi,yo,yl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp [nextMemory,update,idx,test]
    · exact (step _ (by decide) (by decide)).trans yo
    · exact (step _ (by decide) (by decide)).trans yl
    · have sep : one≠((b+q:ℕ):ℤ) := by dsimp [one];omega
      rw [step _ (by decide) (by decide)]; simp [y,writeCell,write,update,cp,co,sep,ptr,one,Nat.cast_add] <;> split_ifs <;> omega
    · exact (step _ (by decide) (by decide)).trans ((k sign (by decide) (by decide) (by decide) (by decide)).trans hs)
    · exact (step _ (by decide) (by decide)).trans ((k _ (by decide) (by decide) (by decide) (by decide)).trans hdeg)
    · intro j hj
      rw [stepN]
      by_cases eq : j=q
      · subst j; have sep : ((b+q:ℕ):ℤ)≠ptr := by dsimp [ptr];omega
        simp [y,writeCell,write,update,cp,data,ptr,one] <;> split_ifs <;> omega
      · rw [keep _ (by dsimp [ptr];omega) (by omega) (by dsimp [term];omega) (by dsimp [cut];omega)]
        exact earlier _ (by omega)
    · intro j hj out
      have h₁ : j≠idx ∧ j≠test ∧ j≠ptr ∧ j≠term ∧ j≠cut := by dsimp [outside,idx,test,ptr,term,cut] at *;omega
      rw [step _ h₁.1 h₁.2.1,k _ hj h₁.2.2.1 h₁.2.2.2.1 h₁.2.2.2.2,neg _ hj out]
    · intro j hj
      rw [stepN,keep _ (by dsimp [ptr];omega) (by omega) (by dsimp [term];omega) (by dsimp [cut];omega),fr _ (by omega)]
  obtain ⟨f,hf,x,run,done⟩ := repeatN_runs (B:=6) (by omega : 0<L+1) _ (by decide : lim≠idx) I
    (fun j hj => cap.fits (by omega) (by omega)) iter init
  exact ⟨_,x,by omega,.seq start run,fun j hj => done.2.2.2.2.2.2.1 j (by omega),
    done.2.1,done.2.2.2.2.2.2.2.1,fun i hi => done.2.2.2.2.2.2.2.2 i (by omega)⟩

end VWZClique.IntegerRAM.WindowSeed
end

/- WordWindow -/
section
namespace VWZClique.IntegerRAM.WindowSweep
open Structured
namespace Reg
end Reg

def after (m : Memory) : Memory :=
  let m₁ := update m Reg.val (m (m Reg.ptr))
  let m₂ := update m₁ Reg.carry (m₁ Reg.carry + m₁ Reg.carry)
  let m₃ := update m₂ Reg.carry (m₂ Reg.val + m₂ Reg.carry)
  let m₄ := update m₃ (m₃ Reg.ptr) (m₃ Reg.carry)
  let m₅ := update m₄ Reg.test (m₄ Reg.base - m₄ Reg.ptr)
  update m₅ Reg.ptr (m₅ Reg.ptr - m₅ Reg.one)

theorem body_run {W : ℕ} (m : Memory) (hf : Fits W (m Reg.ptr)) :
    Runs W body m 6 (after m) := by
  unfold body after
  refine Runs.seq (t := 5) (.atom (.load _ _ _ hf)) ?_
  refine Runs.seq (t := 4) (.atom (.add _ _ _ _)) ?_
  refine Runs.seq (t := 3) (.atom (.add _ _ _ _)) ?_
  refine Runs.seq (t := 2) (.atom (.store _ _ _ ?_)) ?_
  · simpa [update,Reg.ptr,Reg.val,Reg.carry] using hf
  exact .seq (.atom (.sub _ _ _ _)) (.atom (.sub _ _ _ _))

theorem locations (m : Memory) (b i : ℕ) (hp : m Reg.ptr = (b+i:ℕ)) (hb : m Reg.base = b)
    (ho : m Reg.one = 1) :
    (after m Reg.ptr = ((b+i:ℕ):ℤ)-1) ∧ (after m Reg.base = b) ∧
    (after m Reg.one = 1) ∧ (after m Reg.test = -(i:ℤ)) ∧
    (after m Reg.carry = m (b+i:ℕ) + 2*m Reg.carry) ∧
    ∀ a : ℕ, after m a = if a=b+i then m (b+i:ℕ) + 2*m Reg.carry else m a := by
  dsimp only [Reg.ptr,Reg.base,Reg.one] at hp hb ho
  have negpos (k : ℤ) (hk : k<0) : k ≠ (b:ℤ)+i := by omega
  simp [after,update,Reg.ptr,Reg.base,Reg.carry,Reg.test,Reg.one,Reg.val,
    hp,hb,ho,Nat.cast_add,two_mul, negpos (-1) (by decide),negpos (-2) (by decide),
    negpos (-3) (by decide),negpos (-6) (by decide)]
  intro a
  by_cases ha : a=b+i
  · subst a; simp
  · have h : (a:ℤ) ≠ (b:ℤ)+i := by exact_mod_cast ha
    simp [ha,h]

theorem after_private (m : Memory) {b i : ℕ} (hp : m Reg.ptr = (b+i:ℕ))
    (z : ℤ) (hz : z ≤ -7) : after m z = m z := by
  have h1 : z ≠ Reg.ptr := by dsimp [Reg.ptr]; omega
  have h3 : z ≠ Reg.carry := by dsimp [Reg.carry]; omega
  have h4 : z ≠ Reg.val := by dsimp [Reg.val]; omega
  have h5 : z ≠ Reg.test := by dsimp [Reg.test]; omega
  have haddr : z ≠ ((b+i:ℕ):ℤ) := by omega
  simp only [after,update,if_neg h1,if_neg h3,if_neg h4,if_neg h5]
  simp only [Reg.ptr,Reg.carry,Reg.val,reduceCtorEq,Int.reduceNeg,Int.reduceEq,↓reduceIte,Reg.ptr] at *
  simp_all [update]

/-- Start at the top entry. The ghost array y satisfies the finite difference
equations for every unprocessed entry. Every other nonnegative address is preserved. -/
theorem run {W : ℕ} (b i : ℕ) (m : Memory) (y : ℕ → ℤ)
    (hp : m Reg.ptr = (b+i:ℕ)) (hb : m Reg.base = b) (ho : m Reg.one = 1)
    (hc : m Reg.carry = y (i+1))
    (hin : ∀ j ≤ i, m (b+j:ℕ) = y j - 2*y (j+1))
    (hf : ∀ j ≤ i, Fits W ((b+j:ℕ):ℤ)) (ht : ∀ j ≤ i, Fits W (-(j:ℤ))) :
    ∃ out, Runs W command m (7*(i+1)) out ∧ out Reg.carry = y 0 ∧
      (∀ j ≤ i, out (b+j:ℕ) = y j) ∧
      (∀ a : ℕ, a < b ∨ b+i<a → out a = m a) ∧ out Reg.base=b ∧ out Reg.one=1 ∧
      ∀ z : ℤ, z ≤ -7 → out z=m z := by
  induction i generalizing m with
  | zero =>
    obtain ⟨_,base,one,test,carry,read⟩ := locations m b 0 hp hb ho
    have hv : m (b+0:ℕ) + 2*m Reg.carry = y 0 := by rw [hin 0 (by omega),hc]; ring
    have act := body_run m (hp ▸ hf 0 (by omega))
    refine ⟨after m, Runs.loop_done act (test ▸ ht 0 (by omega)) (by rw [test]; simp),carry.trans hv,?_,?_,base,one,after_private m hp⟩
    · intro j hj
      have : j=0 := by omega
      subst j
      exact (read (b+0)).trans (by rw [if_pos rfl]; exact hv)
    · intro a ha
      rw [read,if_neg (by omega)]
  | succ i ih =>
    obtain ⟨ptr,base,one,test,carry,read⟩ := locations m b (i+1) hp hb ho
    have hv : m (b+(i+1):ℕ) + 2*m Reg.carry = y (i+1) := by rw [hin (i+1) (by omega),hc]; ring
    have hi (j : ℕ) (hj : j ≤ i) : after m (b+j:ℕ) = y j - 2*y (j+1) := by
      rw [read,if_neg (by omega),hin j (by omega)]
    have hp' : after m Reg.ptr = (b+i:ℕ) := by rw [ptr]; push_cast; ring
    obtain ⟨out,more,c0,done,untouched,baseOut,oneOut,priv⟩ := ih (after m) hp' base one (carry.trans hv) hi
      (fun j h => hf j (by omega)) (fun j h => ht j (by omega))
    have act := body_run m (hp ▸ hf (i+1) (by omega))
    refine ⟨out,?_,c0,?_,?_,baseOut,oneOut,fun z hz => (priv z hz).trans (after_private m hp z hz)⟩
    · rw [show 7*(i+1+1) = 6+1+7*(i+1) by omega]
      exact Runs.loop_again (reg:=Reg.test) act (test ▸ ht (i+1) (by omega))
        (by rw [test]; push_cast; omega) more
    · intro j hj
      by_cases small : j ≤ i
      · exact done j small
      · have : j=i+1 := by omega
        subst j
        rw [untouched _ (Or.inr (by omega)),read,if_pos rfl,hv]
    · intro a ha
      rw [untouched a (by omega),read,if_neg (by omega)]

/-- The native sweep implements the same table used in the rank-or-swap identity.
Only the address and signed loop tests are required to fit the chosen machine word. -/
theorem implements_framed {W b d : ℕ} (m : Memory) (xs : List ℤ) (len : xs.length=d+1)
    (hp : m Reg.ptr = (b+d:ℕ)) (hb : m Reg.base = b) (ho : m Reg.one=1) (hc : m Reg.carry=0)
    (data : ∀ j ≤ d, m (b+j:ℕ) = RankSwap.Window.entry xs j)
    (hf : ∀ j ≤ d, Fits W ((b+j:ℕ):ℤ)) (ht : ∀ j ≤ d, Fits W (-(j:ℤ))) :
    ∃ out, Runs W command m (7*(d+1)) out ∧
      (∀ j ≤ d, out (b+j:ℕ) = RankSwap.Window.entry (RankSwap.Window.sweep xs).2 j) ∧
      (∀ a : ℕ, a<b ∨ b+d<a → out a=m a) ∧ out Reg.base=b ∧ out Reg.one=1 ∧
      ∀ z : ℤ, z ≤ -7 → out z=m z := by
  let y := RankSwap.Window.entry (RankSwap.Window.sweep xs).2
  have next : y (d+1) = 0 := RankSwap.Window.tail_zero _ _ (by rw [RankSwap.Window.sweep_length,len])
  have input (j : ℕ) (hj : j≤d) : m (b+j:ℕ) = y j - 2*y (j+1) := by
    exact (data j hj).trans (congrFun (RankSwap.Window.undo xs) j).symm
  obtain ⟨out,h,_,hout,hrest,hb,ho,priv⟩ := run b d m y hp hb ho (hc.trans next.symm) input hf ht
  exact ⟨out,h,hout,hrest,hb,ho,priv⟩

end VWZClique.IntegerRAM.WindowSweep
end

/- WordWindowTable -/
section
namespace VWZClique.IntegerRAM.WindowSweep
open Structured
open VWZClique.RankSwap.Window

def resetMem (m : Memory) := update (update m Reg.ptr (m Reg.base+m degrees)) Reg.carry 0

theorem reset_run (W : ℕ) (m : Memory) : Runs W reset m 2 (resetMem m) := by
  have h := Runs.seq (Runs.atom (Step.add (W:=W) m Reg.ptr Reg.base degrees))
    (Runs.atom (Step.sub _ Reg.carry Reg.one Reg.one))
  simpa [reset,resetMem] using h

theorem first_sweep (k : ℕ) (xs : List ℤ) :
    generate k (sweep xs).2 = generate (k+1) xs := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun ys => (sweep ys).2) ih

def blockCost (d : ℕ) := 7*(d+1)+4

/-- Repeating the sweep k+1 times uses one fixed program and four control
instructions per sweep. Input and output use the same contiguous array. -/
theorem table_run {W b d : ℕ} (k : ℕ) (m : Memory) (xs : List ℤ) (len : xs.length=d+1)
    (hb : m Reg.base=b) (hd : m degrees=d) (ho : m Reg.one=1) (hk : m counter = -((k+1:ℕ):ℤ))
    (data : ∀ j ≤ d, m (b+j:ℕ) = entry xs j)
    (hf : ∀ j ≤ d, Fits W ((b+j:ℕ):ℤ)) (ht : ∀ j ≤ d, Fits W (-(j:ℤ)))
    (hc : ∀ u ≤ k, Fits W (-(u:ℤ))) :
    ∃ out, Runs W tableCommand m ((k+1)*blockCost d) out ∧ out counter=0 ∧
      (∀ j ≤ d, out (b+j:ℕ) = entry (generate (k+1) xs) j) ∧
      ∀ a : ℕ, a<b ∨ b+d<a → out a=m a := by
  induction k generalizing m xs
  all_goals
    have p (i : ℤ) (hi : i≤ -7) : resetMem m i = m i := by
      simp [resetMem,update,if_neg (by dsimp [Reg.ptr]; omega : i ≠ Reg.ptr),
        if_neg (by dsimp [Reg.carry]; omega : i ≠ Reg.carry)]
    have hdata (a : ℕ) : resetMem m a = m a := by
      simp [resetMem,update,Reg.ptr,Reg.carry]
    have ss := implements_framed (W:=W) (b:=b) (d:=d) (resetMem m) xs len
      (by simp [resetMem,update,Reg.ptr,Reg.carry,hb,hd]) (by simpa [resetMem,update,Reg.base,Reg.ptr,Reg.carry] using hb)
      (by simpa [resetMem,update,Reg.one,Reg.ptr,Reg.carry] using ho)
      (by simp [resetMem,update])
      (fun j hj => (hdata _).trans (data j hj)) hf ht
    obtain ⟨o,hs,hvalues,houtside,ob,oo,keep⟩ := ss
    let u := update o counter (o counter+o Reg.one)
    have tick : Runs W (.atom (.add counter counter Reg.one)) o 1 u := .atom (.add _ _ _ _)
    have tickset : u counter=m counter+1 := by
      simp [u,update,keep counter (by decide),p counter (by decide),oo]
    have tickN (a : ℕ) : u a = o a := by simp [u,update,counter]
    have r := Runs.seq (reset_run W m) (Runs.seq hs tick)
    have r' : Runs W outerBody m (2+(7*(d+1)+1)) u := r
  case zero =>
    have h0 : u counter=0 := by rw [tickset,hk]; norm_num
    have done := Runs.loop_done (reg:=counter) r' (h0 ▸ (by simpa using hc 0 (by omega))) (by omega)
    refine ⟨u,?_,h0,fun j hj => (tickN _).trans (hvalues j hj),?_⟩
    · rw [show (0+1)*blockCost d = (2+(7*(d+1)+1))+1 by unfold blockCost; ring]
      exact done
    · intro a ha
      exact (tickN _).trans ((houtside a ha).trans (hdata a))
  case succ k ih =>
    have hnext : u counter = -((k+1:ℕ):ℤ) := by rw [tickset,hk]; push_cast; ring
    have din : u degrees=d := by simpa [u,update,counter,degrees] using (keep degrees (by decide)).trans ((p degrees (by decide)).trans hd)
    have bin : u Reg.base=b := by simpa [u,update,counter,Reg.base] using ob
    have one : u Reg.one=1 := by simpa [u,update,counter,Reg.one] using oo
    obtain ⟨endMem,more,last,vals,rest⟩ := ih u (sweep xs).2 ((sweep_length xs).trans len)
      bin din one hnext (fun j hj => (tickN _).trans (hvalues j hj)) (fun n hn => hc n (by omega))
    have moreRuns := Runs.loop_again (reg:=counter) r' (hnext ▸ hc (k+1) (by omega))
      (by rw [hnext]; push_cast; omega) more
    refine ⟨endMem,?_,last,?_,?_⟩
    · rw [show (k+1+1)*blockCost d = (2+(7*(d+1)+1))+1+(k+1)*blockCost d by unfold blockCost; ring]
      exact moreRuns
    · simpa only [first_sweep] using vals
    · intro a ha
      exact (rest a ha).trans ((tickN _).trans ((houtside a ha).trans (hdata a)))

def guardMem (m : Memory) := update m Reg.test (-1-m counter)

theorem guarded (W : ℕ) (m : Memory) (ho : m Reg.one=1) :
    Runs W guardSetup m 3 (guardMem m) := by
  have h := Runs.seq (Runs.atom (Step.sub (W:=W) m Reg.test Reg.one Reg.one))
    (Runs.seq (Runs.atom (Step.sub _ Reg.test Reg.test Reg.one))
      (Runs.atom (Step.sub _ Reg.test Reg.test counter)))
  have norm (x y : ℤ) : update (update m Reg.test x) Reg.test y = update m Reg.test y := by
    funext z; by_cases hz : z=Reg.test <;> simp [update,hz]
  have hh : Runs W guardSetup m 3 (update (update (update m Reg.test 0) Reg.test (-1))
      Reg.test (-1-m counter)) := by
    simpa [guardSetup,update,Reg.test,Reg.one,counter,ho] using h
  simpa only [guardMem,norm] using hh

end VWZClique.IntegerRAM.WindowSweep
end

/- NativeWindowTables -/
section
namespace VWZClique.IntegerRAM.WindowSweep
open Structured VWZClique.RankSwap.Window

theorem generate_runs {W b d : ℕ} (a : ℕ) (m : Memory) (xs : List ℤ)
    (len : xs.length=d+1) (hb : m Reg.base=b) (hd : m degrees=d) (ho : m Reg.one=1)
    (ha : m counter = -(a:ℤ)) (data : ∀ j ≤ d, m (b+j:ℕ)=entry xs j)
    (hf : ∀ j ≤ d, Fits W ((b+j:ℕ):ℤ)) (ht : ∀ j ≤ d, Fits W (-(j:ℤ)))
    (hc : ∀ j < a, Fits W (-(j:ℤ))) (hg : Fits W ((a:ℤ)-1)) :
    ∃ out : Memory, Runs W generateCommand m (a*blockCost d+4) out ∧
      (∀ j ≤ d, out (b+j:ℕ)=entry (generate a xs) j) ∧
      ∀ j : ℕ, j<b ∨ b+d<j → out j=m j := by
  have val : guardMem m Reg.test = (a:ℤ)-1 := by simp [guardMem,update,ha]; ring
  have old (j : ℕ) : guardMem m j = m j := by simp [guardMem,update,Reg.test]
  have fit : Fits W (guardMem m Reg.test) := val ▸ hg
  cases a with
  | zero =>
    have guard : Runs W (.whenNonnegative Reg.test tableCommand) (guardMem m) 1 (guardMem m) :=
      .guard_skip fit (by rw [val]; norm_num)
    have h := Runs.seq (guarded W m ho) guard
    exact ⟨guardMem m,by simpa [generateCommand] using h,fun j hj => (old _).trans (data j hj),
      fun j _ => old j⟩
  | succ k =>
    have more := table_run (W:=W) (b:=b) (d:=d) k (guardMem m) xs len
      (by simpa [guardMem,update,Reg.base,Reg.test] using hb)
      (by simpa [guardMem,update,degrees,Reg.test] using hd)
      (by simpa [guardMem,update,Reg.one,Reg.test] using ho)
      (by simpa [guardMem,update,counter,Reg.test] using ha)
      (fun j hj => (old _).trans (data _ hj)) hf ht (fun j hj => hc j (by omega))
    obtain ⟨out,r,_,values,other⟩ := more
    have guard := Runs.guard_take (reg:=Reg.test) fit (by rw [val]; push_cast; omega) r
    have h := Runs.seq (guarded W m ho) guard
    refine ⟨out,?_,values,fun j hj => (other j hj).trans (old j)⟩
    rw [show (k+1)*blockCost d+4 = (3 + (1+(k+1)*blockCost d)) by omega]
    exact h

end VWZClique.IntegerRAM.WindowSweep

namespace VWZClique.IntegerRAM.WindowSeed
open Structured UniformFolds VWZClique.RankSwap.Window

local instance (j : ℤ) : Decidable (outside j) := inferInstanceAs (Decidable (_ ∨ _))

/-- Starting only with the logarithmic size L and a destination pointer, construct
all L+1 interpolation coefficients, including zero padding above the window. -/
theorem coefficients_run {W L M K b : ℕ} (hk : 4<K) (room : Graph.Division.Room W M)
    (cap : 2^(L+1)*(4*K)≤M) (space : b+L+1≤M) (m : Memory) (dim : m WindowInit.Lreg=L) (addr : m base=b) :
    ∃ f out, f≤26*(L+1)+10*K+55+13*(L+1)+L*WindowSweep.blockCost L ∧
      Runs W (coefficients K) m f out ∧
      (∀ j≤L, out ((b+j:ℕ):ℤ)=entry (RankSwap.Window.coefficients (lower K L) (width K L)) j) ∧
      ∀ j : ℕ, j<b ∨ b+L<j → out j=m j := by
  let a := lower K L
  let d := width K L
  have hi : upper K L≤L := Nat.div_le_of_le_mul (Nat.mul_le_mul_right L (by omega : K+4≤4*K))
  have hd : d≤L := (Nat.sub_le ..).trans hi
  have ha : a≤L := Nat.div_le_of_le_mul (Nat.mul_le_mul_right L (by omega : K-4≤4*K))
  obtain ⟨t,x,ht,winRun,lo,hi',de,neg,xl,xb,pre⟩ := WindowInit.window_runs hk room cap m dim
  obtain ⟨s,y,hs,par,sg,oneY,fr⟩ := parity_runs room (by omega : a+1≤M) x neg
  obtain ⟨u,v,hu,init,arr,oneV,rkeep,vkeep⟩ := fill_runs room space hd y
    ((fr _ (by decide)).trans xl) ((fr _ (by decide)).trans (xb.trans addr))
    ((fr _ (by decide)).trans de) oneY _ sg
  let seed := List.replicate (d+1) ((-1:ℤ)^a)
  have g₁ (j : ℕ) (hj : j≤d) : Fits W ((b+j:ℕ):ℤ) := by apply room.fits <;> omega
  have g₂ (j : ℕ) (hj : j≤L) : Fits W (-(j:ℤ)) := by apply room.fits <;> omega
  have baseV : v base=b := (rkeep _ (by decide) (by decide)).trans ((fr _ (by decide)).trans (xb.trans addr))
  obtain ⟨o,run,vals,keep⟩ := WindowSweep.generate_runs (W:=W) (d:=d) (b:=b) a v seed
    (by simp [seed]) baseV ((rkeep _ (by decide) (by decide)).trans ((fr _ (by decide)).trans de))
    oneV ((rkeep _ (by decide) (by decide)).trans ((fr _ (by decide)).trans neg))
    (fun j hj => by rw [arr j (by omega),if_pos hj,entry_constant _ _ _ (by omega)])
    g₁ (fun j hj => g₂ j (by omega)) (fun j hj => g₂ j (by omega))
    (by apply room.fits <;> omega)
  have bc : WindowSweep.blockCost d≤WindowSweep.blockCost L := by unfold WindowSweep.blockCost; omega
  have cost := Nat.mul_le_mul ha bc
  refine ⟨_,o,by omega,.seq winRun (.seq par (.seq init run)),?_,?_⟩
  · intro j hj
    by_cases e : j≤d
    · exact vals j e
    · rw [keep (b+j) (by omega),arr j hj,if_neg e,tail_zero _ j (by rw [RankSwap.Window.coefficients,gen_length,List.length_replicate];omega)]
  · intro j hj
    have good : outside (j:ℤ) := by dsimp [outside,one];omega
    rw [keep j (by omega),vkeep j hj,fr _ good,pre j]

end VWZClique.IntegerRAM.WindowSeed
end

/- NativeMaskScanLocal -/
section
namespace VWZClique.IntegerRAM.MaskScan.Arena
open Structured Graph RankSwap UniformFolds Butterfly

private theorem reload {W L : ℕ} (m : Memory) (h : m Lr=L) :
    ∃ o, Runs W (line reloadLength) m 2 o ∧ o WindowInit.Lreg=L ∧ ∀ z : ℕ, o z=m z := by
  refine ⟨_,line_runs _ _ (by simp [reloadLength,safeLine,Butterfly.safe]),?_,?_⟩
  · simp [reloadLength,effect,update,unit,WindowInit.Lreg,Lr,h] at *
  · intro z; simp (disch := omega) [reloadLength,effect,update,unit,WindowInit.Lreg]

private theorem stash {W a d : ℕ} (m : Memory) (h : m WindowInit.loReg=a) (g : m WindowInit.degreeReg=d) :
    ∃ o, Runs W (line stashCuts) m 3 o ∧ o Ar=a ∧ o Dr=d ∧ ∀ z : ℕ, z≠304 → z≠305 → o z=m z := by
  refine ⟨_,line_runs _ _ (by simp [stashCuts,safeLine,Butterfly.safe]),?_,?_,?_⟩
  · simp [stashCuts,effect,update,unit,WindowInit.loReg,WindowInit.degreeReg,Ar,Dr,h] at *
  · simp [stashCuts,effect,update,unit,WindowInit.loReg,WindowInit.degreeReg,Ar,Dr,g] at *
  · intro z h g; simp (disch := omega) [stashCuts,effect,update,unit,Ar,Dr,show (z:ℤ)≠304 by omega,show (z:ℤ)≠305 by omega] at *

def prepCost (K L : ℕ) := 21+(26*(L+1)+10*K+55+13*(L+1)+L*WindowSweep.blockCost L) +
  2+(26*(L+1)+10*K+43)+3+(18+11*((L+1)*L)+13*(L+1))+(11+4*L)

theorem prepare_run {W M K q L : ℕ} {source : ℤ} (hk : 4< K) (room : Division.Room W M) (base : 512≤ q)
    (memFit : slot q (2^L) 7+1≤ M) (ratioFit : 2^(L+1)*(4*K)≤ M) (m : Memory)
    (mn : m 0=((2^L:ℕ):ℤ)) (ml : m inputLen=L) (ms : m source=q) (hs : 0< source ∧ source<297) :
    let n := 2^L
    let b := origin q n
    let r := slot q n 1
    let p := slot q n 2
    ∃ f≤ prepCost K L, ∃ out, Runs W (prepare K source) m f out ∧
      Config K L b r p (slot q n 3) (slot q n 4) (slot q n 5) (slot q n 6) (slot q n 7) out ∧
      (∀ j≤ L, out (b+j:ℕ)=windowCoeff K L j) ∧ (∀ j≤ L, out (r+j:ℕ)=residualNum (windowCoeff K L) j) ∧
      (∀ j≤ L, out (p+j:ℕ)=2^(L-j)) ∧
      ∀ z : ℕ, preserveAddr z → z< b ∨ p+L< z → out z=m z := by
  let n := 2^L
  let b := origin q n
  let B := span n
  have ns : L+1≤ n := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=L))
  have npos : 0< n := Nat.pow_pos (by decide)
  have nn : n^2≤ B := Nat.pow_le_pow_right (by omega : 1≤ n) (by decide : 2≤3)
  have sq : (L+1)^2≤ B := (Nat.pow_le_pow_left ns 2).trans nn
  have small : L+1≤ B := ns.trans (by change n≤ n^3; simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤ n) (by decide : 1≤3))
  have b0 : 512≤ b := by dsimp [b,origin]; omega
  have mem : b+7*B+1≤ M := memFit
  have guard (z : ℤ) (lo : -(M:ℤ)≤ z) (hi : z≤ M) : Fits W z := room.fits lo hi
  obtain ⟨x,xr,header,xb,xl,xf⟩ := layout_runs (W:=W) m mn ml ms hs
  obtain ⟨f,y,hf,yr,yC,yfr⟩ := WindowSeed.coefficients_run hk room ratioFit (by change b+L+1≤ M; omega) x xl xb
  have hx (z : ℕ) (h : z< b ∨ b+L< z) : y z=x z := yfr z h
  obtain ⟨t,tr,tlen,tf⟩ := reload (W:=W) y ((hx 300 (Or.inl (by omega))).trans header.l)
  obtain ⟨g,u,hg,ur,ua,_,ud,_,_,_,uf⟩ := WindowInit.window_runs hk room ratioFit t tlen
  obtain ⟨v,vr,va,vd,vf⟩ := stash (W:=W) u ua ud
  have vy (z : ℕ) (nz₁ : z≠304) (nz₂ : z≠305) : v z=y z := (vf z nz₁ nz₂).trans ((uf z).trans (tf z))
  have vx (z : ℕ) (h : z< b ∨ b+L< z) (nz₁ : z≠304) (nz₂ : z≠305) : v z=x z := (vy z nz₁ nz₂).trans (hx z h)
  have hdr : Forward.Header b (b+B) (b+2*B) L v := by
    refine ⟨(vx 300 (Or.inl (by omega)) (by decide) (by decide)).trans header.l,
      (vx 301 (Or.inl (by omega)) (by decide) (by decide)).trans header.c,?_,?_⟩
    · simpa [slot,b,B] using (vx 302 (Or.inl (by omega)) (by decide) (by decide)).trans header.r
    · exact (vx 303 (Or.inl (by omega)) (by decide) (by decide)).trans header.p
  have ctab (j : ℕ) (hj : j≤ L) : v (b+j:ℕ)=windowCoeff K L j :=
    (vy _ (by omega) (by omega)).trans (yC j hj)
  have tri : (L+1)*L≤(L+1)^2 := by rw [pow_two]; exact Nat.mul_le_mul_left _ (by omega)
  have triM : ((L:ℤ)+1)*L≤ M := by exact_mod_cast (show (L+1)*L≤ M by omega)
  have triPos : 0≤((L:ℤ)+1)*L := by positivity
  obtain ⟨i,hi,w,wr,wp,wf⟩ := Forward.precompute_run (windowCoeff K L) v hdr ctab ⟨by omega,by omega,by omega⟩
    (fun j hj => guard _ (by omega) (by omega)) (fun j hj => ⟨guard _ (by omega) (by omega),guard _ (by omega) (by omega)⟩)
    (guard _ (by omega) (by omega)) (fun j hj => guard _ (by omega) (by omega)) (fun j hj => guard _ (by omega) (by omega))
  have wlow (z : ℕ) (hz : z< b+(L+1)) : w z=v z := wf z (Or.inl hz)
  obtain ⟨k,hk',out,act,radix,ofr⟩ := make_radix (W:=W) w ((wlow 300 (by omega)).trans hdr.l)
    (guard _ (by omega) (by omega)) (fun j hj => guard _ (by omega) (by omega))
  have ov (z : ℕ) (h : z< b+(L+1)) (e : z≠312) : out z=v z := (ofr z e).trans (wlow z h)
  have ox (z : ℕ) (h : z< b) (a : z≠304) (d : z≠305) (e : z≠312) : out z=x z :=
    (ov z (by omega) e).trans (vx z (Or.inl h) a d)
  refine ⟨_,by unfold prepCost; omega,out,.seq xr (.seq yr (.seq tr (.seq ur (.seq vr (.seq wr act))))),?_,?_,?_,?_,?_⟩
  · constructor
    · exact (ox 300 (by omega) (by decide) (by decide) (by decide)).trans header.l
    · exact (ox 311 (by omega) (by decide) (by decide) (by decide)).trans header.n
    · exact (ov 304 (by omega) (by decide)).trans va
    · exact (ov 305 (by omega) (by decide)).trans vd
    · exact (ox 306 (by omega) (by decide) (by decide) (by decide)).trans header.mc
    · exact (ox 307 (by omega) (by decide) (by decide) (by decide)).trans header.mv
    · exact (ox 308 (by omega) (by decide) (by decide) (by decide)).trans header.lc
    · exact (ox 309 (by omega) (by decide) (by decide) (by decide)).trans header.lv
    · exact (ox 310 (by omega) (by decide) (by decide) (by decide)).trans header.counts
    · exact (ox 301 (by omega) (by decide) (by decide) (by decide)).trans header.c
    · exact (ox 302 (by omega) (by decide) (by decide) (by decide)).trans header.r
    · exact (ox 303 (by omega) (by decide) (by decide) (by decide)).trans header.p
    · exact radix
    · have h := (ox 314 (by omega) (by decide) (by decide) (by decide)).trans header.four
      have sqn : (2^L:ℕ)^2=4^L := by rw [←pow_mul,Nat.mul_comm L 2,pow_mul]; rfl
      rw [←sqn,Nat.cast_pow]; exact h
  · intro j hj; exact (ov (b+j) (by omega) (by omega)).trans (ctab j hj)
  · intro j hj
    have h := (wp j hj).1
    simpa [slot,b,B,residualNum,Forward.V_shift] using
      (ofr (b+B+j) (by omega)).trans h
  · intro j hj; exact (ofr (b+2*B+j) (by omega)).trans (wp j hj).2
  · intro z mz hz
    have hz' : z< b ∨ b+2*B+L< z := hz
    have mZ : z<300 ∨ 319< z := mz
    exact (ofr z (by omega)).trans ((wf z (by omega)).trans ((vx z (by omega) (by omega) (by omega)).trans (xf z mz)))

/-- A single static native program consumes the frame's weight pointer, N at
word zero, and L at word 320. It creates the compact record arrays and both
counts inside this frame, returning the graph alphabet to word zero. -/
theorem initialize_run {W M K q L : ℕ} {source : ℤ} (hk : 4< K) (room : Division.Room W M) (base : 512≤ q)
    (memFit : slot q (2^L) 7+1≤ M) (ratioFit : 2^(L+1)*(4*K)≤ M) (m : Memory)
    (mn : m 0=((2^L:ℕ):ℤ)) (ml : m inputLen=L) (ms : m source=q) (hs : 0< source ∧ source<297) :
    ∃ f≤ prepCost K L+36+720*(2^L)^5, ∃ o, Runs W (buildMaskMetadata K source) m f o ∧ o 0=((2^L:ℕ):ℤ) ∧
      Prepared L K q o ∧ ∀ z : ℕ, preserveAddr z → z< origin q (2^L) ∨ slot q (2^L) 7+2≤ z → o z=m z := by
  let n := 2^L
  let b := origin q n
  let B := span n
  have nq : 0< n := Nat.pow_pos (by decide)
  have small : L+1≤ B := (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=L))).trans (by
    change n≤ n^3; simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤ n) (by decide : 1≤3))
  have bLow : 512≤ b := by dsimp [b,origin];omega
  have endBound : b+7*B+1≤ M := memFit
  obtain ⟨five,four⟩ := scan_lengths L
  change 5^L≤ B at five
  change 4^L≤ B at four
  have cap : Division.Room W (5*5^L) := by
    unfold Division.Room at *; exact (show ((5*5^L:ℕ):ℤ)≤ M by omega).trans_lt room
  have geo : Buffers L b (b+1*B) (b+2*B) (b+3*B) (b+4*B) (b+5*B) (b+6*B) (b+7*B) := by
    constructor <;> omega
  have lim : lower K L≤ L ∧ width K L≤ L := by
    have lc : K-4≤4*K := by omega
    have hc : K+4≤4*K := by omega
    exact ⟨Nat.div_le_of_le_mul (Nat.mul_le_mul_right L lc),(Nat.sub_le ..).trans (Nat.div_le_of_le_mul (Nat.mul_le_mul_right L hc))⟩
  obtain ⟨f,hf,y,yr,cfg,C,R,P,yrs⟩ := prepare_run hk room base memFit ratioFit m mn ml ms hs
  obtain ⟨g,hg,o,act,nout,tables,fr⟩ := compact_run y cfg geo lim cap
    (fun j hj => room.fits (by omega) (by omega)) C R P
  refine ⟨_,by omega,o,.seq yr act,nout,tables,?_⟩
  intro z protected' hz
  by_cases z0 : z=0
  · subst z; exact nout.trans mn.symm
  · have hz' : z< b ∨ b+7*B+2≤ z := hz
    exact (fr z (by omega) (by change z< b+3*B ∨ b+7*B+1< z; omega)).trans
      (yrs z protected' (by change z< b ∨ b+2*B+L< z; omega))

theorem initialize_budget (K L : ℕ) :
    prepCost K L+36+720*(2^L)^5 ≤ (1200+30*K)*(2^L)^5 := by
  let n := 2^L
  have pos : 1≤ n := Nat.one_le_pow _ _ (by decide)
  have s : L+1≤ n := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=L))
  have n1 : n≤ n^5 := by simpa only [pow_one] using Nat.pow_le_pow_right pos (by decide : 1≤5)
  have n2 : n^2≤ n^5 := Nat.pow_le_pow_right pos (by decide)
  have prod : L*(L+1)≤ n^5 := (Nat.mul_le_mul (by omega : L≤ n) s).trans (by simpa [pow_two] using n2)
  have charge : K≤ K*n^5 := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left K (pos.trans n1)
  change prepCost K L+36+720*n^5≤(1200+30*K)*n^5
  unfold prepCost WindowSweep.blockCost
  nlinarith only [s,n1,pos,prod,charge,Nat.zero_le (K*n^5)]

end VWZClique.IntegerRAM.MaskScan.Arena
end

/- MMUniform -/
section
namespace VWZClique.BlockMM

theorem depth_bounds {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) :
    n ≤ b^(depth b n) ∧ b^(depth b n) ≤ b*n := by
  refine ⟨(Nat.lt_pow_succ_log_self hb n).le,?_⟩
  rw [depth,pow_succ,Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ (by omega))

end VWZClique.BlockMM
end

/- UniformFoldBudget -/
section
namespace VWZClique.UniformFolds

/-- The entire choice of real asymptotic parameters can be discarded after
writing these 37 pairs of natural numbers to a fixed finite table. -/
noncomputable def cutoffTable : Array (ℕ × ℕ) :=
  Array.ofFn (fun i : Fin 37 => (windowAt i.val,tileAt i.val))

theorem cutoffTable_spec (H : SimpleGraph V) :
    cutoffTable.size = 37 ∧
    cutoffTable[Nat.card H.edgeSet]? =
      some (windowAt (Nat.card H.edgeSet),tileAt (Nat.card H.edgeSet)) ∧
    4 < windowAt (Nat.card H.edgeSet) ∧ 0 < tileAt (Nat.card H.edgeSet) := by
  have he : Nat.card H.edgeSet < 37 := Nat.lt_succ_of_le (edge_limit H)
  exact ⟨by simp [cutoffTable],by simp only [cutoffTable,Array.getElem?_ofFn,dif_pos he],
    (selectCut _).window_large,(selectCut _).tile_pos⟩

end VWZClique.UniformFolds
end

/- NativeFrameStack -/
section
namespace VWZClique.IntegerRAM.NativeFrame
open Structured UniformFolds NativeTraversal

/-- Sufficient capacity per depth, including the last row of every edge table. -/
def Capacity (lay : StackLayout) (L : ℕ) := ∀ d,
  lay.base d + 9*(2^L) + 81*(2^L*2^L) ≤ lay.base (d+1)

theorem capacity_mono {lay : StackLayout} {L} (cap : Capacity lay L) : Monotone lay.base :=
  monotone_nat_of_le_succ fun d => by have := cap d; omega

theorem weights_region {L : ℕ} {lay : StackLayout} (cap : Capacity lay L) {d w} {m o : Memory}
    (src : @Weights L lay d w m) (ptr : o (reg d .weights)=m (reg d .weights))
    (fr : ∀ a : ℕ, lay.base d ≤ a → a < lay.base (d+1) → o a=m a) : Weights lay d w o := by
  refine ⟨ptr.trans src.1,?_⟩
  intro i
  have hl := NativeLeaf.index_lt i
  have hb := cap d
  exact (congrArg (Int.cast : ℤ → ℚ) (fr _ (Nat.le_add_right _ _) (by omega))).trans (src.2 i)

/-- Writes to a child arena, deeper scratch, or the stable temporary bank do
not disturb suspended ancestors. Only the live positive prefix of the tables
and the explicit ancestor register cells need be preserved. -/
theorem saved_before {L} (lay : StackLayout) (cap : Capacity lay L) (d : ℕ) (q : List (NativeTraversal.Slot L))
    {m o : Memory} (tables : ∀ a : ℕ, 512 ≤ a → a < lay.base d → o a=m a)
    (regs : ∀ i<d, ∀ f, o (reg i f)=m (reg i f)) (src : Saved lay d q m) :
    Saved lay d q o := by
  induction q generalizing d with
  | nil => trivial
  | cons h rest ih =>
    obtain ⟨lt,ok,arm,tail⟩ := src
    let j := depthOf h
    have gj : lay.base (j+1) ≤ lay.base d := capacity_mono cap lt
    have inside (a : ℕ) (ha : lay.base j ≤ a) (hb : a < lay.base (j+1)) :=
      tables a ((lay.large j).trans ha) (hb.trans_le gj)
    have savedTail := ih j (fun a ha hb => tables a ha (hb.trans_le (capacity_mono cap lt.le)))
      (fun k hk f => regs k (hk.trans lt) f) tail
    refine ⟨lt,?_,?_,savedTail⟩
    · cases h with
      | input k w => exact weights_region cap ok (regs k lt _) inside
      | value k z => exact (regs k lt _).trans ok
      | cursor k H π b w i z =>
        obtain ⟨wt,p,l,idx,v⟩ := ok
        exact ⟨weights_region cap wt (regs k lt _) inside,lay.transfer k H m o inside p,
          fun e => (regs k lt _).trans (l e),(regs k lt _).trans idx,(regs k lt _).trans v⟩
    · cases h with
      | input => exact False.elim arm
      | value => exact False.elim arm
      | cursor k H π b w i z =>
        obtain ⟨hi,hc⟩ := arm
        exact ⟨hi,(regs k lt _).trans hc⟩

end VWZClique.IntegerRAM.NativeFrame
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

@[simp] theorem Expr.int_val (m : Memory) (z : ℤ) : (int z).val m=z := by
  cases z <;> simp [int,val] <;> omega

@[simp] theorem Expr.num_safe (m : Memory) (d : ℤ) (W n : ℕ) : (num n).safe d W m := by
  induction n <;> simp_all [num,safe]

@[simp] theorem Expr.int_safe (m : Memory) (d : ℤ) (W : ℕ) (z : ℤ) : (int z).safe d W m := by
  cases z <;> simp [int,safe]

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

/- NativeArenaLayout -/
section
namespace VWZClique.IntegerRAM.NativeArena
open NativeFrame NativeTraversal UniformFolds BlockReduction MaskScan.Arena

theorem layoutCapacity (L root output : ℕ) (start : 512≤root) : @NativeFrame.Capacity (layout L root output start) L := by
  intro d
  change atDepth root (2^L) d + 9*2^L + 81*(2^L*2^L) ≤ child (atDepth root (2^L) d) (2^L)
  dsimp [child,rows,maps,metaBase,tableWords]
  omega

end VWZClique.IntegerRAM.NativeArena
end

/- NativeMaskScanFrame -/
section
namespace VWZClique.IntegerRAM.Projected
open Structured UniformFolds NativeTraversal NativeFrame NativeArena

/-- Initialize projection metadata for an occupied stack frame. Its incoming
weights, suspended frames, dimensions and output pointer remain available. -/
theorem frame_init {W M L root output d : ℕ} (start : 512≤ root) (hd : d≤36) (H : SimpleGraph V)
    (w : WeightKey (2^L)→ℚ) (q : List (NativeTraversal.Slot L)) (m : Memory)
    (room : Graph.Division.Room W M)
    (addr : MaskScan.Arena.slot (atDepth root (2^L) d) (2^L) 7+1≤ M)
    (ratio : 2^(L+1)*(4*windowAt (Nat.card H.edgeSet))≤ M)
    (src : Repr (layout L root output start) (.input d w::q) m) :
    let base := atDepth root (2^L) d
    let K := windowAt (Nat.card H.edgeSet)
    ∃ f≤(1200+30*K)*(2^L)^5, ∃ o,
      Runs W (MaskScan.Arena.buildMaskMetadata K (reg d .weights)) m f o ∧
      Repr (layout L root output start) (.input d w::q) o ∧ MaskScan.Arena.Prepared L K base o ∧
      ∀ j : ℕ, projectionPrefix base (2^L) j → o j=m j := by
  let lay := layout L root output start
  let n := 2^L
  let base := atDepth root n d
  let K := windowAt (Nat.card H.edgeSet)
  have b0 : 512≤ base := lay.large d
  obtain ⟨glob,wt,rest⟩ := src
  obtain ⟨f,hf,o,act,nat,table,fr⟩ := MaskScan.Arena.initialize_run (cutoffTable_spec H).2.2.1 room
    b0 addr ratio m glob.dim glob.length wt.1 ⟨reg_positive ..,reg_below hd _⟩
  have origin : MaskScan.Arena.origin base n=metaBase base n := by dsimp [MaskScan.Arena.origin,metaBase,tableWords];ring
  have before : base≤ MaskScan.Arena.origin base n := by dsimp [MaskScan.Arena.origin];omega
  have prior (j : ℕ) (h : projectionPrefix base n j) : o j=m j := by
    apply fr
    · change j<300 ∨ 319< j
      dsimp [projectionPrefix] at h; omega
    · apply Or.inl
      change j< MaskScan.Arena.origin base n
      dsimp [projectionPrefix] at h; rw [←origin] at h; omega
  have cell (i : ℕ) (h : i≤36) (c : Field) : o (reg i c)=m (reg i c) := by
    have lp := reg_positive i c
    have hp := reg_below h c
    have z := prior (reg i c).toNat (Or.inl (by omega))
    simpa only [Int.toNat_of_nonneg lp.le] using z
  have oo : Globals L lay o := glob.transfer (nat.trans glob.dim.symm)
    (prior 320 (Or.inr (Or.inl rfl))) (prior 321 (Or.inr (Or.inr (Or.inl rfl))))
  have weight : Weights lay d w o := by
    refine ⟨(cell d hd _).trans wt.1,?_⟩
    intro a
    have h : Graph.Table.wordIndex a<9*n+81*(n*n) := NativeLeaf.index_lt a
    have bound : projectionPrefix base n (base+Graph.Table.wordIndex a) := by
      refine Or.inr (Or.inr (Or.inr ⟨by omega,?_⟩)); dsimp [metaBase,tableWords]
      omega
    exact (congrArg (Int.cast : ℤ→ℚ) (prior _ bound)).trans (wt.2 a)
  have saved := saved_before lay (layoutCapacity L root output start) d q
    (fun a low high => prior a (Or.inr (Or.inr (Or.inr ⟨low,by change a< base at high; rw [←origin];omega⟩))))
    (fun i hi c => cell i (by omega) c) rest
  exact ⟨f,hf.trans (MaskScan.Arena.initialize_budget K L),o,act,⟨oo,weight,saved⟩,table,prior⟩

end VWZClique.IntegerRAM.Projected
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

theorem Value.safe {W : ℕ} (a : Value) (x : Memory) (fit : ∀ i ≤ a.high, Fits W (i:ℤ)) : a.expr.safe floor W x := by
  induction a with
  | nat i => exact Expr.num_safe ..
  | word i => exact (Setup.readWord_safe x W i).2 (fit i le_rfl)
  | add a b ia ib | mul a b ia ib => exact ⟨ia (fun i hi => fit i (le_max_of_le_left hi)),ib (fun i hi => fit i (le_max_of_le_right hi))⟩

def stored (m : Memory) (z : ℤ) : Fields → ℤ
  | [] => m z
  | a::xs => if z=a.1 then a.2.eval m else stored m z xs

def room (W k : ℕ) := ∀ i ≤ k, Fits W (i:ℤ)

private theorem eval_on {m x : Memory} (a : Value) (h : ∀ i≤a.high, x (i:ℤ)=m i) : a.expr.val x=a.eval m := by
  induction a with
  | nat i => simp [Value.expr,Value.eval]
  | word i => exact (Setup.readWord_val _ _).trans (h i le_rfl)
  | add a b ia ib | mul a b ia ib =>
    simp only [Value.expr,Value.eval,Expr.val,ia (fun i hi => h i (le_max_of_le_left hi)),ib (fun i hi => h i (le_max_of_le_right hi))]

/-- Initialize immediate-address scratch header cells from lower, immutable
metadata. All outputs have word addresses chosen at compile time. -/
theorem initialize_run {W lo : ℕ} (xs : Fields) (m : Memory)
    (ranges : ∀ a∈xs, (lo:ℤ)<a.1 ∧ a.2.high≤lo) (fit : room W lo) :
    ∃ out, Runs W (command xs) m (time xs) out ∧ (∀ z, floor<z → out z=stored m z xs) ∧
      ∀ z, floor<z → (∀ a∈xs,z≠a.1) → out z=m z := by
  induction xs with
  | nil => exact ⟨m,.skip _,fun _ _ => rfl,fun _ _ _ => rfl⟩
  | cons a xs ih =>
    obtain ⟨p,v⟩ := ranges a (by simp)
    obtain ⟨x,first,st,keep⟩ := ih (fun k hk => ranges k (by simp [hk]))
    have rd : ∀ i≤a.2.high,x (i:ℤ)=m i := by
      intro i hi; apply keep _ (by unfold floor; omega)
      intro k hk; have := (ranges k (by simp [hk])).1; omega
    obtain ⟨o,last,result⟩ := assign_run x (by unfold floor; omega : floor<a.1) a.2.expr
      (a.2.safe x (fun i h => fit i (h.trans v)))
    refine ⟨o,.seq first last,?_,?_⟩
    · intro z hz; rw [result _ hz,stored,eval_on a.2 rd,st _ hz]
    · intro z hz none; rw [result _ hz,if_neg (none a (by simp))]; exact keep z hz (fun t ht => none t (by simp [ht]))

end VWZClique.IntegerRAM.Projected.Headers
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

end VWZClique.IntegerRAM.Projected.Workspace
end

/- NativeProjectionInit -/
section
namespace VWZClique.IntegerRAM.Projected.Init
open Structured Headers NativeFrame MaskScan RankSwap UniformFolds

theorem run {W L K d base M : ℕ} (depth : d≤36) (large : 512≤base)
    (m : Memory) (domain : m 0=(2^L:ℕ)) (input : m (reg d .weights)=base) (prep : Arena.Prepared L K base m)
    (room : Graph.Division.Room W M) (space : Arena.slot base (2^L) 7+2≤M) :
    ∃ o, Runs W (command d) m (Headers.time (fields d)+(countExpr.steps+2)) o ∧
      Params base (2^L) (RankSwap.outside L (lower K L) (width K L)).card o ∧
      (∀ z : ℕ, z<350 ∨ 380<z → o z=m z) := by
  let N := 2^L
  change Arena.slot base N 7+2≤M at space
  have hd : (8+8*d:ℕ)≤296 := by omega
  have nrt : m ((8+8*d:ℕ):ℤ)=base := by convert input using 2 <;> simp [NativeFrame.reg,NativeFrame.Field.offset] <;> omega
  have lim : base≤Arena.slot base N 7 := by simp [Arena.slot,Arena.origin]; omega
  have regRanges : ∀ x∈fields d,(349:ℤ)<x.1 ∧ x.2.high≤349 := by
    simp [fields,Value.high,parent,dense,start,orig,slot,n,sq,cube,sixth,mul] <;> omega
  obtain ⟨x,head,st,keep⟩ := Headers.initialize_run (fields d) m regRanges (fun (i : ℕ) (hi : i≤349) => by apply room.fits <;> omega)
  have evalParent : (parent d).eval m=base := nrt
  have evN : n.eval m=(N:ℤ) := domain
  have E (i : ℕ) : (slot d i).eval m=(Arena.slot base N i:ℕ) := by
    simp only [slot,orig,mul,sq,cube,Value.eval,evalParent,evN,Arena.slot,Arena.origin,Arena.span,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]; ring
  have St : (start d).eval m=((Arena.slot base N 7+2:ℕ):ℤ) := by simp [start,Value.eval,E]
  have D (i : ℕ) : (dense d i).eval m=((Arena.slot base N 7+2+4*N^3 + i*N^6:ℕ):ℤ) := by
    simp [dense,sixth,mul,cube,sq,n,Value.eval,St,domain,N]; ring
  have arg : x 380=((Arena.slot base N 7+1:ℕ):ℤ) := (st 380 (by decide)).trans (by simp [fields,Headers.stored,Value.eval,E])
  have source : x ((Arena.slot base N 7+1:ℕ):ℤ)=(RankSwap.outside L (lower K L) (width K L)).card := by
    rw [keep _ (by unfold SquareCode.Layout.floor; omega) (by simp [fields]; omega)]; exact prep.labelCount
  have safe : countExpr.safe SquareCode.Layout.floor W x := by
    refine ⟨by change SquareCode.Layout.floor<(380:ℤ); decide,?_,?_⟩
    · change SquareCode.Layout.floor<x 380; rw [arg]; unfold SquareCode.Layout.floor; omega
    · change Fits W (x 380); rw [arg]; apply room.fits <;> omega
  obtain ⟨o,count,post⟩ := SquareCode.Layout.assign_run x (by decide : SquareCode.Layout.floor<(359:ℤ)) countExpr safe
  have result : o 359=(RankSwap.outside L (lower K L) (width K L)).card := by
    rw [post _ (by decide)]; simpa [countExpr,SquareCode.Expr.val,arg] using source
  have read (k : ℤ) (lo : SquareCode.Layout.floor<k) (other : k≠359) : o k=Headers.stored m k (fields d) := by
    rw [post k lo,if_neg other,st k lo]
  refine ⟨o,.seq head count,?_,?_⟩
  · constructor
    all_goals first | exact result | apply (read _ (by decide) (by decide)).trans
    all_goals simp [fields,Headers.stored,evalParent,E,St,D,Workspace.banks,N]
  · intro z hz
    have neq : (z:ℤ)≠359 := by omega
    rw [post _ (by unfold SquareCode.Layout.floor; omega),if_neg neq]
    apply keep _ (by unfold SquareCode.Layout.floor; omega)
    simp [fields] <;> omega

end VWZClique.IntegerRAM.Projected.Init
end

/- WordButterflyTransform -/
section
/-! A uniform native program for all bit lengths. A stage moves the leading raw
    digit to a transformed trailing digit. After all stages the trailing labels
    are in their original order. -/

namespace VWZClique.IntegerRAM.Butterfly
open Structured TrulySubcubicAPSP

/-- Big-endian base-four address of a tensor coordinate. -/
def address : (L : ℕ) → BasisLabel L → ℕ
  | 0, _ => 0
  | L+1, a => (a 0 : ℕ)*4^L + address L (fun i => a i.succ)

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

end VWZClique.IntegerRAM.Butterfly
end

/- NativeProjectionSupport -/
section
namespace VWZClique.IntegerRAM.Projected.Support
open Projection TraceDyadic

theorem sign_square {L} (s : Bits L) (j : BasisLabel L) :
    let e := basisInt j (s,partner j s)
    e*e = if e=0 then 0 else 1 := by
  have h := abs_le.mp (basis_bound j (s,partner j s))
  have h' : basisInt j (s,partner j s) = -1 ∨ basisInt j (s,partner j s) = 0 ∨
    basisInt j (s,partner j s) = 1 := by omega
  rcases h' with h|h|h <;> simp [h]

end VWZClique.IntegerRAM.Projected.Support
end

/- NativeProjectionSupportDP -/
section
namespace VWZClique.IntegerRAM.Projected.SupportDP
open Structured Projection UniformFolds TraceDyadic SquareCode

theorem partner_cons {L : ℕ} (j : BasisLabel L) (x : Bits L) (d : Fin 4) (b : Bool) :
    partner (Fin.cons d j) (Fin.cons b x) = Fin.cons (localPartner d b) (partner j x) := by
  funext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp [partner,localPartner]

theorem word_cons {L : ℕ} (b : Bool) (x : Bits L) :
    (wordIndex (L+1) (Fin.cons b x)).val=bit b*2^L+(wordIndex L x).val := by
  cases b <;> change (wordIndex L x).val+2^L*_= _ <;> simp [bit,finTwoEquiv,add_comm]

theorem label_cons {L : ℕ} (d : Fin 4) (j : BasisLabel L) :
    (Butterfly.labelIndex (L+1) (Fin.cons d j)).val=d.val*4^L+(Butterfly.labelIndex L j).val := by
  simp [Butterfly.labelIndex_val,Butterfly.address]

theorem sign_cons {L : ℕ} (j : BasisLabel L) (x : Bits L) (d : Fin 4) (b : Bool) :
    sign (Fin.cons d j) (Fin.cons b x)=coeff d b*sign j x := by
  apply (Int.cast_injective (α:=ℚ))
  have cv : (coeff d b:ℚ)=oneBit d b (localPartner d b) := by
    fin_cases d <;> cases b <;> decide
  simp only [sign,partner_cons,basis_cast,Int.cast_mul,cv,basisEntry,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem index_cons {L : ℕ} (j : BasisLabel L) (x : Bits L) (d : Fin 4) (b : Bool) :
    let σ := coeff d b*sign j x
    index (Fin.cons d j) (Fin.cons b x)=σ*σ*(bit (localPartner d b)*((2^L:ℕ):ℤ)+index j x) := by
  dsimp only
  have code (l : ℕ) (k : BasisLabel l) (s : Bits l) :
      index k s = if sign k s=0 then 0 else ((wordIndex l (partner k s)).val:ℤ) := by
    by_cases h : sign k s=0 <;> simp_all [index,sign,Slices.lookupPartner]
  rw [code,sign_cons,code]
  have ss := Support.sign_square (Fin.cons b x) (Fin.cons d j)
  change sign (Fin.cons d j) (Fin.cons b x) * sign (Fin.cons d j) (Fin.cons b x) = _ at ss
  change _ = if sign (Fin.cons d j) (Fin.cons b x)=0 then 0 else 1 at ss
  rw [sign_cons] at ss
  rw [ss,partner_cons,word_cons]
  by_cases zero : coeff d b*sign j x=0
  · simp [zero]
  · have pos : sign j x≠0 := fun h => zero (by rw [h,mul_zero])
    simp [zero,pos]

structure Addresses where
  signs : ℕ
  indices : ℕ
  nextSigns : ℕ
  nextIndices : ℕ

structure Grid (a : Addresses) (n p u v : ℕ) (m : Memory) : Prop where
  side : m (-3)=n
  pos : m (-4)=p
  row : m (-5)=u
  col : m (-6)=v
  sig : m inSign=a.signs
  ind : m inIndex=a.indices
  nsig : m outSign=a.nextSigns
  nind : m outIndex=a.nextIndices

def oldPos (n p u v : ℕ) := p*(n*n)+(u*n+v)
def newPos (n p u v : ℕ) (d : Fin 4) (b : Bool) := (bit b*n+p)*(4*(n*n))+(d.val*(n*n)+(u*n+v))

/-- One prefix write occupies a fixed number of native instructions at every
length. It computes its child using two source words at most. -/
theorem cell_run {W n p u v : ℕ} {a : Addresses} {m : Memory} (g : Grid a n p u v m)
    (d : Fin 4) (b which : Bool)
    (fs : Fits W ((a.signs+oldPos n p u v:ℕ):ℤ)) (fi : Fits W ((a.indices+oldPos n p u v:ℕ):ℤ))
    (fw : Fits W (((if which then a.nextIndices else a.nextSigns)+newPos n p u v d b:ℕ):ℤ)) :
    let z := coeff d b*m ((a.signs+oldPos n p u v:ℕ):ℤ)
    let y := z*z*((bit (localPartner d b):ℤ)*n + m ((a.indices+oldPos n p u v:ℕ):ℤ))
    ∃ out, Runs W (cell d b which) m (cellCost d b which) out ∧ ∀ i, Layout.floor < i → out i =
      if i=(((if which then a.nextIndices else a.nextSigns)+newPos n p u v d b:ℕ):ℤ)
      then (if which then y else z) else m i := by
  dsimp only
  have os (r : ℤ) (k : ℕ) (h : m r=k) : (src r).val m=((k+oldPos n p u v:ℕ):ℤ) := by
    simp [src,SupportDP.n,vertex,plane,label,oldPos,Expr.val,h,g.side,g.pos,g.row,g.col]
  have ns (r : ℤ) (k : ℕ) (h : m r=k) : (dst d b r).val m=((k+newPos n p u v d b:ℕ):ℤ) := by
    simp [dst,SupportDP.n,vertex,plane,label,newPos,Expr.val,h,g.side,g.pos,g.row,g.col]
  have readSafe (r : ℤ) (k : ℕ) (h : m r=k) (hr : Layout.floor < r)
      (fit : Fits W ((k+oldPos n p u v:ℕ):ℤ)) : (Expr.read (src r)).safe Layout.floor W m := by
    refine ⟨?_,?_,?_⟩
    · simp [src,Expr.safe,SupportDP.n,vertex,plane,label,Layout.floor] at *; assumption
    · rw [os _ _ h]; unfold Layout.floor; omega
    · rw [os _ _ h]; exact fit
  have sgn := readSafe _ _ g.sig (by decide) fs
  have ix := readSafe _ _ g.ind (by decide) fi
  have safeS : (signValue d b).safe Layout.floor W m := ⟨Expr.int_safe ..,sgn⟩
  have safeI : (indexValue d b).safe Layout.floor W m := ⟨⟨safeS,safeS⟩,⟨⟨Expr.num_safe ..,by change (-128:ℤ)< -3;decide⟩,ix⟩⟩
  have sa (r : ℤ) (h : Layout.floor < r) : (dst d b r).safe Layout.floor W m := by
    simp [dst,Expr.safe,SupportDP.n,vertex,plane,label,Layout.floor] at *; exact h
  cases which with
  | false =>
    obtain ⟨o,act,post⟩ := write_run m Layout.floor (dst d b outSign) (signValue d b)
      (sa _ (by decide)) safeS ((ns _ _ g.nsig) ▸ fw)
    refine ⟨o,act,?_⟩
    intro i hi
    simpa only [Bool.false_eq_true,if_false,signValue,Expr.val,Expr.int_val,os inSign _ g.sig,ns outSign _ g.nsig] using post i hi
  | true =>
    obtain ⟨o,act,post⟩ := write_run m Layout.floor (dst d b outIndex) (indexValue d b)
      (sa _ (by decide)) safeI ((ns _ _ g.nind) ▸ fw)
    refine ⟨o,act,?_⟩
    intro i hi
    simpa only [if_true,indexValue,signValue,Expr.val,SupportDP.n,g.side,Expr.int_val,Expr.num_val,os inSign _ g.sig,os inIndex _ g.ind,ns outIndex _ g.nind] using post i hi

end VWZClique.IntegerRAM.Projected.SupportDP
end

/- NativeProjectionSupportPass -/
section
namespace VWZClique.IntegerRAM.Projected.SupportDP
open Structured SquareCode.Layout

def outBank (a : Addresses) (idx : Bool) := if idx then a.nextIndices else a.nextSigns

def position (a : Addresses) (n : ℕ) (d : Fin 4) (b idx : Bool) (i : Position) :=
  outBank a idx + newPos n i.1 i.2.1 i.2.2 d b

def result (a : Addresses) (n : ℕ) (d : Fin 4) (b idx : Bool) (i : Position) (H : Heap) : ℤ :=
  let src := oldPos n i.1 i.2.1 i.2.2
  let z := coeff d b * H (a.signs+src)
  if idx then z*z*((bit (localPartner d b):ℤ)*n + H (a.indices+src)) else z

private theorem pack_lt {n p q : ℕ} (hp : p< n) (hq : q< n) : p*n+q< n*n := by
  have h := Nat.mul_le_mul_right n hp
  rw [Nat.succ_mul] at h; omega

theorem old_lt {n : ℕ} {i : Position} (h : i∈points n n) : oldPos n i.1 i.2.1 i.2.2 < n*(n*n) := by
  obtain ⟨pp,uu,vv⟩ := (points_mem _ _ _).1 h
  have rr := pack_lt uu vv
  have hi := Nat.mul_le_mul_right (n*n) pp
  rw [Nat.succ_mul] at hi
  unfold oldPos; omega

private theorem pack_inj {N p P r R : ℕ} (nPos : 0< N) (hr : r< N) (hR : R< N) (h : p*N+r=P*N+R) :
    p=P ∧ r=R := by
  have div (u v : ℕ) (hv : v< N) : (u*N+v)/N=u := by
    rw [Nat.mul_comm,Nat.mul_add_div nPos,Nat.div_eq_of_lt hv,Nat.add_zero]
  have pp := (div p r hr).symm.trans ((congrArg (·/N) h).trans (div P R hR))
  subst P; exact ⟨rfl,Nat.add_left_cancel h⟩

private theorem pos_inj {n : ℕ} (hn : 0< n) (a : Addresses) (d : Fin 4) (b idx : Bool)
    (i j : Position) (hi : i∈points n n) (hj : j∈points n n)
    (h : position a n d b idx i=position a n d b idx j) : i=j := by
  obtain ⟨ip,iu,iv⟩ := (points_mem _ _ _).1 hi
  obtain ⟨jp,ju,jv⟩ := (points_mem _ _ _).1 hj
  have ia := pack_lt iu iv
  have ja := pack_lt ju jv
  have col (q : ℕ) (hq : q< n*n) : d.val*(n*n)+q<4*(n*n) := by
    have h := Nat.mul_le_mul_right (n*n) d.isLt
    rw [Nat.succ_mul] at h; omega
  have he := Nat.add_left_cancel (show outBank a idx + newPos n i.1 i.2.1 i.2.2 d b=
    outBank a idx + newPos n j.1 j.2.1 j.2.2 d b from h)
  obtain ⟨row,c⟩ := pack_inj (by positivity) (col _ ia) (col _ ja) he
  obtain ⟨u,v⟩ := pack_inj hn iv jv (Nat.add_left_cancel c)
  exact Prod.ext (Nat.add_left_cancel row) (Prod.ext u v)

structure Parameters (a : Addresses) (n : ℕ) (m : Memory) : Prop where
  outer : m (-2)=n
  side : m (-3)=n
  sig : m inSign=a.signs
  ind : m inIndex=a.indices
  nsig : m outSign=a.nextSigns
  nind : m outIndex=a.nextIndices

/-- One full signtable or partnertable pass over a binary vertex and a
base-four label. Decomposing the label into two radix-n coordinates gives
exactly n³ cells with no native division or modulus. -/
theorem pass_run {W n cutoff : ℕ} (hn : 0< n) (a : Addresses) (d : Fin 4) (b idx : Bool)
    (m : Memory) (hp : Parameters a n m) (guard : ∀ i≤ n, Fits W ((i:ℤ)-n))
    (sep : a.signs+n*(n*n)≤ cutoff ∧ a.indices+n*(n*n)≤ cutoff ∧ cutoff≤ outBank a idx)
    (fits : ∀ z∈points n n, Fits W ((a.signs+oldPos n z.1 z.2.1 z.2.2:ℕ):ℤ) ∧
      Fits W ((a.indices+oldPos n z.1 z.2.1 z.2.2:ℕ):ℤ) ∧ Fits W (position a n d b idx z)) :
    ∃ t≤ gridCost n n (cellCost d b idx), ∃ o, Runs W (grid (cell d b idx)) m t o ∧
      (∀ i∈points n n, o (position a n d b idx i:ℕ) = result a n d b idx i (heap m)) ∧
      (∀ z : ℕ, (∀ i∈points n n, z≠position a n d b idx i) → o z=m z) ∧ Parameters a n o ∧ regs (-4) m o := by
  let D := position a n d b idx
  let V := result a n d b idx
  let op := fun r u v => scatter D V (r,u,v)
  have act := grid_run (B:=cellCost d b idx) hn hn m hp.outer hp.side guard guard (cell d b idx) op
  obtain ⟨t,ht,o,run,data,regs',_⟩ := act (by
    intro p pp u uu v vv x stable xp xu xv xone
    have mem : (p,u,v)∈points n n := (points_mem _ _ _).2 ⟨pp,uu,vv⟩
    have g : Grid a n p u v x := ⟨(stable _ (by decide) (by decide)).trans hp.side,xp,xu,xv,
      (stable _ (by decide) (by decide)).trans hp.sig,(stable _ (by decide) (by decide)).trans hp.ind,
      (stable _ (by decide) (by decide)).trans hp.nsig,(stable _ (by decide) (by decide)).trans hp.nind⟩
    obtain ⟨fs,fi,fw⟩ := fits _ mem
    obtain ⟨y,body,post⟩ := cell_run g d b idx fs fi fw
    have keep (z : ℤ) (lo : floor< z) (neg : z<0) : y z=x z := by
      rw [post z lo,if_neg (by omega)]
    refine ⟨_,le_rfl,y,body,?_,?_,(keep _ (by decide) (by decide)).trans xone⟩
    · funext z
      change y z=if z=D (p,u,v) then V (p,u,v) (heap x) else x z
      have atZ := post (z:ℤ) (by unfold floor;omega)
      by_cases eq : z=D (p,u,v)
      · rw [if_pos eq]
        have ec : (z:ℤ)=(((if idx then a.nextIndices else a.nextSigns)+newPos n p u v d b:ℕ):ℤ) := congrArg (fun k : ℕ => (k:ℤ)) eq
        rw [if_pos ec] at atZ
        exact atZ
      · rw [if_neg eq]
        have ec : (z:ℤ)≠(((if idx then a.nextIndices else a.nextSigns)+newPos n p u v d b:ℕ):ℤ) := by
          intro h; exact eq (Int.natCast_inj.mp h)
        rw [if_neg ec] at atZ
        exact atZ
    · intro z hz neg
      exact keep z (by unfold floor at *; omega) neg)
  have sc := scatter_result (points n n) (heap m) D V (fun z => z< cutoff)
    (by intro i _; change ¬(outBank a idx+_ < cutoff); omega)
    (by intro i hi x y agree; have ls := old_lt hi
        have l := agree (a.signs+oldPos n i.1 i.2.1 i.2.2) (by omega)
        have r := agree (a.indices+oldPos n i.1 i.2.1 i.2.2) (by omega)
        simp only [V,result,l,r]) (fun i hi j hj => pos_inj hn a d b idx i j hi hj)
  rw [gridFold_list] at data
  refine ⟨t,ht,o,run,fun i hi => (congrFun data (D i)).trans (sc.1 i hi),
    fun z h => (congrFun data z).trans (sc.2 z h),?_,regs'⟩
  exact ⟨(regs' _ (by decide) (by decide)).trans hp.outer,(regs' _ (by decide) (by decide)).trans hp.side,
    (regs' _ (by decide) (by decide)).trans hp.sig,(regs' _ (by decide) (by decide)).trans hp.ind,
    (regs' _ (by decide) (by decide)).trans hp.nsig,(regs' _ (by decide) (by decide)).trans hp.nind⟩

end VWZClique.IntegerRAM.Projected.SupportDP
end

/- NativeProjectionSupportStage -/
section
namespace VWZClique.IntegerRAM.Projected.SupportDP
open Structured SquareCode.Layout

def target (a : Addresses) (n : ℕ) (k : Tag) := position a n k.1 k.2.1 k.2.2
def word (a : Addresses) (n : ℕ) (k : Tag) := result a n k.1 k.2.1 k.2.2

theorem mem_tags (k : Tag) : k∈tags := by rcases k with ⟨d,b,e⟩; fin_cases d <;> cases b <;> cases e <;> decide

private theorem lt_pair {N K p u : ℕ} (hp : p< K) (hu : u< N) : p*N+u< K*N := by
  have h := Nat.mul_le_mul_right N hp
  rw [Nat.succ_mul] at h; omega

private theorem pair_injective {N p P r R : ℕ} (nPos : 0< N) (hr : r< N) (hR : R< N) (h : p*N+r=P*N+R) :
    p=P ∧ r=R := by
  have div (u v : ℕ) (hv : v< N) : (u*N+v)/N=u := by rw [Nat.mul_comm,Nat.mul_add_div nPos,Nat.div_eq_of_lt hv,Nat.add_zero]
  have pp := (div p r hr).symm.trans ((congrArg (·/N) h).trans (div P R hR))
  subst P; exact ⟨rfl,Nat.add_left_cancel h⟩

private theorem bit_lt (b : Bool) : bit b<2 := by cases b <;> decide

theorem new_lt {n : ℕ} {i : Position} (h : i∈points n n) (d : Fin 4) (b : Bool) :
    newPos n i.1 i.2.1 i.2.2 d b < (2*n)*(4*(n*n)) := by
  obtain ⟨p,u,v⟩ := (points_mem _ _ _).1 h
  exact lt_pair (lt_pair (bit_lt b) p) (lt_pair d.isLt (lt_pair u v))

/-- Distinct combinations of prefix bit, digit and component own disjoint
physical words in the next level. -/
theorem tags_disjoint {n : ℕ} (hn : 0< n) (a : Addresses)
    (sep : a.nextSigns+(2*n)*(4*(n*n))≤ a.nextIndices) {i j : Position}
    (hi : i∈points n n) (hj : j∈points n n) (k h : Tag) (e : target a n k i=target a n h j) : k=h := by
  rcases k with ⟨d,b,w⟩; rcases h with ⟨e',c,z⟩
  have l := new_lt hi d b
  have r := new_lt hj e' c
  obtain ⟨ip,iu,iv⟩ := (points_mem _ _ _).1 hi
  obtain ⟨jp,ju,jv⟩ := (points_mem _ _ _).1 hj
  have same : w=z := by
    cases w <;> cases z <;> simp_all only [target,position,outBank,Bool.false_eq_true,if_false,if_true] <;> omega
  subst z
  have e0 := Nat.add_left_cancel e
  obtain ⟨p,q⟩ := pair_injective (by positivity) (lt_pair d.isLt (lt_pair iu iv)) (lt_pair e'.isLt (lt_pair ju jv)) e0
  have bitEq := (pair_injective hn ip jp p).1
  have digEq := (pair_injective (by positivity) (lt_pair iu iv) (lt_pair ju jv) q).1
  have bd : b=c := by cases b <;> cases c <;> simp [bit] at *
  obtain rfl := Fin.ext digEq; subst c; rfl

def work (n : ℕ) (ks : List Tag) := (ks.map fun k => gridCost n n (cellCost k.1 k.2.1 k.2.2)).sum

/-- A full prefix level, including every child sign and packed partner. -/
theorem stage_runs {W n cutoff : ℕ} (hn : 0< n) (a : Addresses) (ks : List Tag)
    (guard : ∀ i≤ n, Fits W ((i:ℤ)-n))
    (src : a.signs+n*(n*n)≤ cutoff ∧ a.indices+n*(n*n)≤ cutoff)
    (sep : cutoff≤ a.nextSigns ∧ a.nextSigns+(2*n)*(4*(n*n))≤ a.nextIndices)
    (fits : ∀ k : Tag, ∀ z∈points n n, Fits W ((a.signs+oldPos n z.1 z.2.1 z.2.2:ℕ):ℤ) ∧
      Fits W ((a.indices+oldPos n z.1 z.2.1 z.2.2:ℕ):ℤ) ∧ Fits W (target a n k z))
    (m : Memory) (hp : Parameters a n m) :
    ∃ t≤ work n ks, ∃ o, Runs W (commands ks) m t o ∧ Parameters a n o ∧
      (∀ k∈ks, ∀ i∈points n n, o (target a n k i:ℕ)=word a n k i (heap m)) ∧
      (∀ z : ℕ, (∀ k∈ks, ∀ i∈points n n, z≠target a n k i) → o z=m z) ∧ regs (-4) m o := by
  induction ks generalizing m with
  | nil => exact ⟨0,le_rfl,m,.skip _,hp,by simp,(fun _ _ => rfl),fun _ _ _ => rfl⟩
  | cons k ks ih =>
    have above (j : Tag) : cutoff≤ outBank a j.2.2 := by unfold outBank; split <;> omega
    obtain ⟨t,ht,x,first,hit,miss,hx,mx⟩ := pass_run hn a k.1 k.2.1 k.2.2 m hp guard ⟨src.1,src.2,above k⟩ (fits k)
    obtain ⟨v,hv,o,rest,po,hh,ff,xo⟩ := ih x hx
    have keep (z : ℕ) (hz : z< cutoff) : x z=m z := miss _ (by intro i _; unfold position; have := above k; omega)
    have read (j : Tag) (i : Position) (hi : i∈points n n) : word a n j i (heap x)=word a n j i (heap m) := by
      have sm := old_lt hi
      simp only [word,result,heap,keep _ (by omega : a.signs+oldPos n i.1 i.2.1 i.2.2< cutoff),keep _ (by omega : a.indices+oldPos n i.1 i.2.1 i.2.2< cutoff)]
    refine ⟨t+v,by simpa [work] using Nat.add_le_add ht hv,o,.seq first rest,po,?_,?_,fun z lo hi => (xo z lo hi).trans (mx z lo hi)⟩
    · intro j hj i hi
      by_cases inside : j∈ks
      · exact (hh j inside i hi).trans (read j i hi)
      · obtain rfl : j=k := (List.mem_cons.mp hj).resolve_right inside
        exact (ff _ (fun h hh p he eq => inside ((tags_disjoint hn a sep.2 hi he j h eq).symm ▸ hh))).trans (hit i hi)
    · intro z hz
      exact (ff _ (fun j h => hz _ (List.mem_cons_of_mem _ h))).trans (miss _ (hz k (by simp)))

end VWZClique.IntegerRAM.Projected.SupportDP
end

/- NativeProjectionSupportFull -/
section
namespace VWZClique.IntegerRAM.Projected.SupportDP
open Structured Projection UniformFolds TraceDyadic SquareCode.Layout Workspace

def addresses (start h : ℕ) : Addresses where
  signs := level start h
  indices := level start h+8^h
  nextSigns := level start (h+1)
  nextIndices := level start (h+1)+8^(h+1)

theorem sideSquare (h : ℕ) : (2^h:ℕ)*(2^h)=4^h := by rw [←Nat.mul_pow]
theorem sideCube (h : ℕ) : (2^h:ℕ)*(2^h*2^h)=8^h := by
  rw [sideSquare,←Nat.mul_pow]

/-- The prefix scatter writes exactly the mathematical partner and the sign of
the enlarged product basis vector. The middle-label coordinates are recovered
in the proof by Euclidean division; the machine's grid already supplies them. -/
theorem build_next {h : ℕ} {a : Addresses} {m o : Memory}
    (old : BanksAt h a.signs a.indices m)
    (set : ∀ k∈tags, ∀ i∈points (2^h) (2^h), o (target a (2^h) k i:ℕ)=word a (2^h) k i (heap m)) :
    BanksAt (h+1) a.nextSigns a.nextIndices o := by
  have one (j : BasisLabel h) (x : Bits h) (d : Fin 4) (b : Bool) :
      o (a.nextSigns+(wordIndex (h+1) (Fin.cons b x)).val*4^(h+1)+(Butterfly.labelIndex (h+1) (Fin.cons d j)).val:ℕ)=sign (Fin.cons d j) (Fin.cons b x) ∧
      o (a.nextIndices+(wordIndex (h+1) (Fin.cons b x)).val*4^(h+1)+(Butterfly.labelIndex (h+1) (Fin.cons d j)).val:ℕ)=index (Fin.cons d j) (Fin.cons b x) := by
    let n := 2^h
    let l := (Butterfly.labelIndex h j).val
    let v := (wordIndex h x).val
    have pos : 0< n := Nat.pow_pos (by decide)
    have hsq : n*n=4^h := sideSquare h
    have hl : l< n*n := by rw [hsq]; exact (Butterfly.labelIndex h j).isLt
    have reg : (v,l/n,l%n)∈points n n := (points_mem _ _ _).mpr ⟨(wordIndex h x).isLt,
      (Nat.div_lt_iff_lt_mul pos).mpr hl,Nat.mod_lt _ pos⟩
    have decomp : l/n*n+(l%n)=l := by rw [Nat.mul_comm]; exact Nat.div_add_mod .. 
    have os : oldPos n v (l/n) (l%n)=v*4^h+l := by rw [oldPos,decomp,hsq]
    have address : newPos n v (l/n) (l%n) d b = (wordIndex (h+1) (Fin.cons b x)).val*4^(h+1)
      +(Butterfly.labelIndex (h+1) (Fin.cons d j)).val := by
      rw [word_cons,label_cons,newPos,hsq,decomp,pow_succ 4];dsimp [n,v,l];ring
    have s := set (d,b,false) (mem_tags _) _ reg
    have p := set (d,b,true) (mem_tags _) _ reg
    change o (a.nextSigns+newPos n v (l/n) (l%n) d b:ℕ) = coeff d b*m (a.signs+oldPos n v (l/n) (l%n):ℕ) at s
    change o (a.nextIndices+newPos n v (l/n) (l%n) d b:ℕ) = (coeff d b*m (a.signs+oldPos n v (l/n) (l%n):ℕ))*(coeff d b*m (a.signs+oldPos n v (l/n) (l%n):ℕ))*
      ((bit (localPartner d b):ℤ)*n+m (a.indices+oldPos n v (l/n) (l%n):ℕ)) at p
    rw [address,os] at s p
    have left := old.signs j x
    have right := old.partners j x
    change m (a.signs+v*4^h+l:ℕ)=sign j x at left
    change m (a.indices+v*4^h+l:ℕ)=index j x at right
    simp only [←Nat.add_assoc,left,right] at s p
    exact ⟨s.trans (sign_cons j x d b).symm,p.trans (index_cons j x d b).symm⟩
  constructor
  · intro j x
    simpa only [Fin.cons_self_tail] using (one (Fin.tail j) (Fin.tail x) (j 0) (x 0)).1
  · intro j x
    simpa only [Fin.cons_self_tail] using (one (Fin.tail j) (Fin.tail x) (j 0) (x 0)).2

theorem stage_cost (h : ℕ) : work (2^h) tags ≤ constant*8^h := by
  let n := 2^h
  have one : 1≤ n := Nat.one_le_pow _ _ (by decide)
  have sq : n≤ n*n := by simpa only [one_mul] using Nat.mul_le_mul_right n one
  have cb : n*n≤ n*(n*n) := by simpa only [one_mul] using Nat.mul_le_mul_right (n*n) one
  have cost (b : ℕ) : gridCost n n b≤(b+23)*(n*(n*n)) := by
    unfold gridCost
    nlinarith only [one,sq,cb]
  have all (ks : List Tag) : work n ks≤(ks.map fun k => cellCost k.1 k.2.1 k.2.2+23).sum*(n*(n*n)) := by
    induction ks with
    | nil => simp [work]
    | cons k ks ih =>
      simp only [work,List.map_cons,List.sum_cons] at *
      rw [Nat.add_mul]
      exact Nat.add_le_add (cost _) ih
  simpa only [n,constant,sideCube] using all tags

end VWZClique.IntegerRAM.Projected.SupportDP
end

/- NativeProjectionSupportLoop -/
section
namespace VWZClique.IntegerRAM.Projected.SupportDP
open UniformFolds Structured SquareCode.Layout Workspace Butterfly Graph

structure Counter (L h : ℕ) (m : Memory) : Prop where
  ix : m outerI=h
  lim : m total=L
  one : m unit=1

theorem bump {W h start L : ℕ} (m : Memory) (ctl : Counter L h m) (params : Parameters (addresses start h) (2^h) m) :
    ∃ o, Runs W (line bumpBlock) m 10 o ∧ Parameters (addresses start (h+1)) (2^(h+1)) o ∧
      Counter L h o ∧ ∀ z : ℕ, o z=m z := by
  let o := bumpBlock.foldl effect m
  have act : Runs W (line bumpBlock) m 10 o := line_runs _ _ (by simp [bumpBlock,safeLine,Butterfly.safe])
  obtain ⟨n,side,sg,ind,ns,ni⟩ := params
  have u : m (-92)=1 := ctl.one
  refine ⟨o,act,?_,?_,?_⟩
  · constructor <;> simp [o,bumpBlock,effect,update,addresses,Workspace.level,unit,temp,inSign,inIndex,outSign,outIndex,u,
      n,side,ns,ni,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,pow_succ] at * <;> ring
  · constructor <;> simp [o,bumpBlock,effect,update,temp,inSign,inIndex,outSign,outIndex,outerI,total,unit,
      ctl.ix,ctl.lim,ctl.one] at *
  · intro z; simp (disch := omega) [o,bumpBlock,effect,update,temp,inSign,inIndex,outSign,outIndex]

theorem seed {W L start : ℕ} (m : Memory) (hs : m inSign=start) (ml : m 320=L) (above : 320< start)
    (fs : Fits W (start:ℤ)) (fi : Fits W ((start+1:ℕ):ℤ)) :
    ∃ o, Runs W (line initBlock) m 15 o ∧ Parameters (addresses start 0) 1 o ∧
      BanksAt 0 start (start+1) o ∧ Counter L 0 o ∧ o guardReg=(L:ℤ)-1 ∧
      ∀ z : ℕ, z< start ∨ start+2≤ z → o z=m z := by
  let o := initBlock.foldl effect m
  have nr (k : ℤ) (hk : k<0) : k≠(start:ℤ) := by omega
  have ni (k : ℤ) (hk : k<0) : k≠(start:ℤ)+1 := by omega
  have safe : safeLine W m initBlock := by
    simp (disch := decide) [initBlock,safeLine,Butterfly.safe,effect,update,hs,nr,ni,
      inSign,inIndex,outSign,outIndex,unit,zeroR,outerI,total,guardReg,temp,Nat.cast_add] at *
    exact ⟨fs,fi⟩
  refine ⟨o,line_runs _ _ safe,?_,?_,?_,?_,?_⟩
  · constructor <;> simp (disch := decide) [o,initBlock,effect,update,addresses,Workspace.level,hs,nr,ni,
      inSign,inIndex,outSign,outIndex,unit,zeroR,outerI,total,guardReg,temp] at * <;> omega
  · have a : o start=1 := by simp (disch := decide) [o,initBlock,effect,update,hs,nr,ni,
      inSign,inIndex,outSign,outIndex,unit,zeroR,outerI,total,guardReg,temp] at *
    have b : o (start+1:ℕ)=0 := by simp (disch := decide) [o,initBlock,effect,update,hs,nr,ni,show (start:ℤ)+1≠ -93 by omega,
      inSign,inIndex,outSign,outIndex,unit,zeroR,outerI,total,guardReg,temp] at *
    constructor
    · intro j x; have na := (wordIndex 0 x).isLt; have nb := (Butterfly.labelIndex 0 j).isLt
      have i : (wordIndex 0 x).val=0 := by simpa using Nat.eq_zero_of_le_zero (show (wordIndex 0 x).val≤0 by omega)
      have k : (Butterfly.labelIndex 0 j).val=0 := by omega
      simpa [i,k,sign,TraceDyadic.basisInt] using a
    · intro j x; have na := (wordIndex 0 x).isLt; have nb := (Butterfly.labelIndex 0 j).isLt
      have i : (wordIndex 0 x).val=0 := by omega
      have k : (Butterfly.labelIndex 0 j).val=0 := by omega
      have y := (wordIndex 0 (Slices.lookupPartner j x)).isLt
      have ij : (wordIndex 0 (Slices.lookupPartner j x)).val=0 := by omega
      simpa [index,i,k,ij] using b
  · constructor <;> simp (disch := decide) [o,initBlock,effect,update,hs,ml,nr,ni,
      inSign,inIndex,outSign,outIndex,unit,zeroR,outerI,total,guardReg,temp] at * <;> omega
  · simp (disch := decide) [o,initBlock,effect,update,hs,ml,nr,ni,
      inSign,inIndex,outSign,outIndex,unit,zeroR,outerI,total,guardReg,temp] at *
  · intro z hz
    have zl : (z:ℤ)≠(start:ℤ) := by omega
    have zr : (z:ℤ)≠(start:ℤ)+1 := by omega
    simp (disch := omega) [o,initBlock,effect,update,hs,nr,ni,zl,zr,
      inSign,inIndex,outSign,outIndex,unit,zeroR,outerI,total,guardReg,temp] at *

end VWZClique.IntegerRAM.Projected.SupportDP
end

/- NativeProjectionSupportRun -/
section
namespace VWZClique.IntegerRAM.Projected.SupportDP
open Structured SquareCode.Layout Workspace Graph

/-- The complete, uniform support-table construction. The level bound and all
physical addresses are runtime values; no basis vector is supplied as advice. -/
theorem execute_run {W L start M : ℕ} (room : Division.Room W M) (above : 320< start)
    (cap : start+3*8^L≤ M) (m : Memory) (hs : m inSign=start) (ml : m 320=L) :
    ∃ f≤16+L*(constant*8^L+13), ∃ o, Runs W execute m f o ∧
      BanksAt L (level start L) (level start L+8^L) o ∧ o inSign=level start L ∧ o inIndex=((level start L+8^L:ℕ):ℤ) ∧
      ∀ z : ℕ, z< start ∨ level start L+2*8^L≤ z → o z=m z := by
  have eight : 0<8^L := Nat.pow_pos (by decide)
  have length : L≤ M := by
    have a := (Nat.lt_two_pow_self (n:=L)).le
    have b := Nat.pow_le_pow_left (by decide : 2≤8) L
    omega
  have guard (n : ℕ) (hn : n≤ M) (j : ℕ) (hj : j≤ n) : Fits W ((j:ℤ)-n) := room.fits (by omega) (by omega)
  have fit (z : ℕ) (h : z≤ M) : Fits W (z:ℤ) := room.fits (by omega) (by omega)
  obtain ⟨s,init,p0,b0,c0,g0,sf⟩ := seed m hs ml above (fit _ (by omega)) (fit _ (by omega))
  let I := fun h (x : Memory) => Parameters (addresses start h) (2^h) x ∧
    BanksAt h (level start h) (level start h+8^h) x ∧ Counter L h x ∧
    ∀ z : ℕ, z< start ∨ level start h+2*8^h≤ z → x z=m z
  have sI : I 0 s := by simpa only [I,level,pow_zero,Nat.mul_one] using And.intro p0 (And.intro b0 (And.intro c0 sf))
  have action (h : ℕ) (hh : h< L) (x : Memory) (ih : I h x) :
      ∃ f≤ constant*8^L+10, ∃ y, Runs W body x f y ∧ y outerI=h ∧ y unit=1 ∧ y total=L ∧ I (h+1) (nextMemory y outerI guardReg h L) := by
    obtain ⟨params,tables,cnt,frame⟩ := ih
    let a := addresses start h
    let n := 2^h
    have npos : 0< n := Nat.pow_pos (by decide)
    have cube : n*(n*n)=8^h := sideCube h
    have bigCube : (2*n)*(4*(n*n))=8^(h+1) := by rw [pow_succ,←cube];ring
    have size (k : ℕ) (hk : k≤ L) : level start k+2*8^k≤ M :=
      (level_bound start k).trans (by have p := Nat.pow_le_pow_right (by decide : 0<8) hk;omega)
    have pn : n≤8^h := Nat.pow_le_pow_left (by decide) h
    have src : a.signs+n*(n*n)≤ a.nextSigns ∧ a.indices+n*(n*n)≤ a.nextSigns := by
      dsimp [a,addresses,level]; rw [cube]; omega
    have sep : a.nextSigns+(2*n)*(4*(n*n))≤ a.nextIndices := by dsimp [a,addresses]; rw [bigCube]
    have endZ : a.nextIndices+8^(h+1)≤ M := by
      dsimp [a,addresses]; have h := size (h+1) hh;omega
    have upper (k : Tag) (i : Position) (hi : i∈points n n) : target a n k i< a.nextIndices+8^(h+1) := by
      have sm := new_lt hi k.1 k.2.1
      rw [bigCube] at sm
      have ns : a.nextSigns≤ a.nextIndices := by dsimp [a,addresses];omega
      unfold target position outBank
      split <;> omega
    obtain ⟨f,fc,o,run,par,writes,keep,regs⟩ := stage_runs (cutoff:=a.nextSigns) npos a tags
      (guard n (by have bound := size h hh.le;omega)) src ⟨le_rfl,sep⟩
      (fun k i hi => by
        have old := old_lt hi; have ub := upper k i hi
        refine ⟨fit _ (by omega),fit _ (by omega),fit _ (by omega)⟩) x params
    have banks := build_next (a:=a) (m:=x) (o:=o) (h:=h) tables writes
    have ctr : Counter L h o := ⟨(regs _ (by decide) (by decide)).trans cnt.ix,
      (regs _ (by decide) (by decide)).trans cnt.lim,(regs _ (by decide) (by decide)).trans cnt.one⟩
    obtain ⟨y,yr,pp,yc,yf⟩ := bump o ctr par
    have other (z : ℤ) (bi : z≠outerI) (bg : z≠guardReg) : nextMemory y outerI guardReg h L z=y z := by simp [nextMemory,update,bi,bg]
    have heapEq (z : ℕ) : nextMemory y outerI guardReg h L z=o z :=
      (other _ (by dsimp [outerI];omega) (by dsimp [guardReg];omega)).trans (yf z)
    have bound : work n tags≤constant*8^L := (stage_cost h).trans (Nat.mul_le_mul_left constant (Nat.pow_le_pow_right (by decide : 0<8) hh.le))
    refine ⟨_,by omega,y,.seq run yr,yc.ix,yc.one,yc.lim,?_,?_,?_,?_⟩
    · constructor
      · exact (other _ (by decide) (by decide)).trans pp.outer
      · exact (other _ (by decide) (by decide)).trans pp.side
      · exact (other _ (by decide) (by decide)).trans pp.sig
      · exact (other _ (by decide) (by decide)).trans pp.ind
      · exact (other _ (by decide) (by decide)).trans pp.nsig
      · exact (other _ (by decide) (by decide)).trans pp.nind
    · exact ⟨fun j v => (heapEq _).trans (banks.signs j v),fun j v => (heapEq _).trans (banks.partners j v)⟩
    · constructor
      · simp [nextMemory,update,outerI,guardReg]
      · exact (other _ (by decide) (by decide)).trans yc.lim
      · exact (other _ (by decide) (by decide)).trans yc.one
    · intro z hz
      have lo : start≤ a.nextSigns := level_lo start (h+1)
      have targetLo (k : Tag) (i : Position) : a.nextSigns≤ target a n k i := by
        have ns : a.nextSigns≤ a.nextIndices := by dsimp [a,addresses];omega
        unfold target position outBank; split <;> omega
      have vBound : level start (h+1)+2*8^(h+1)=a.nextIndices+8^(h+1) := by dsimp [a,addresses];omega
      exact (heapEq z).trans ((keep z (fun k _ i hi => by have := upper k i hi; have := targetLo k i; omega)).trans (frame z (by
        change z< start ∨ level start h+2*8^h≤ z; change z< start ∨ (level start h+2*8^h)+2*8^(h+1)≤ z at hz;omega)))
  have fg : Fits W (s guardReg) := by rw [g0]; apply room.fits <;> omega
  by_cases z : L=0
  · subst L; exact ⟨16,by decide,s,.seq init (.guard_skip fg (by omega)),sI.2.1,sI.1.sig,sI.1.ind,sI.2.2.2⟩
  · obtain ⟨f,hf,o,act,done⟩ := repeatN_runs (B:=constant*8^L+10) (by omega : 0< L) _
      (by decide : total≠outerI) I (guard L length) action sI
    exact ⟨_,by change f≤L*(constant*8^L+13) at hf; omega,o,.seq init (.guard_take fg (by omega) act),done.2.1,done.1.sig,done.1.ind,done.2.2.2⟩

theorem support_cost (L : ℕ) : 16+L*(constant*8^L+13)≤(constant+30)*(2^L)^5 := by
  let n := 2^L
  have h : L≤n := (Nat.lt_two_pow_self (n:=L)).le
  have n1 : 1≤ n := Nat.one_le_pow _ _ (by decide)
  have p1 : n≤ n^5 := by simpa only [pow_one] using Nat.pow_le_pow_right n1 (by decide : 1≤5)
  have q1 : n^4≤ n^5 := Nat.pow_le_pow_right n1 (by decide)
  have eq : 8^L=n^3 := by dsimp [n]; rw [←pow_mul,Nat.mul_comm L 3,pow_mul];rfl
  have prod : L*(n^3)≤ n^5 := (Nat.mul_le_mul_right (n^3) h).trans (by simpa [pow_succ,Nat.mul_comm] using q1)
  have cost := Nat.mul_le_mul_left constant prod
  rw [eq]
  change 16+L*(constant*n^3+13)≤(constant+30)*n^5
  nlinarith only [n1,p1,h,cost]

end VWZClique.IntegerRAM.Projected.SupportDP
end

/- NativeProjectionSupportHeaders -/
section
namespace VWZClique.IntegerRAM.Projected.SupportDP
open Structured Butterfly Graph Workspace

theorem withHeaders_run {W L start M : ℕ} (room : Division.Room W M) (above : 379<start) (cap : start+3*8^L≤M)
    (m : Memory) (hs : m startHeader=start) (ml : m 320=L) :
    ∃ f≤(constant+35)*(2^L)^5, ∃ o, Runs W withHeaders m f o ∧
      BanksAt L (level start L) (level start L+8^L) o ∧ o signHeader=level start L ∧
      o pairHeader=((level start L+8^L:ℕ):ℤ) ∧
      ∀ z : ℕ, z≠351 → z≠352 → z<start ∨ level start L+2*8^L≤z → o z=m z := by
  let x := readSupport.foldl effect m
  have pre : Runs W (line readSupport) m 2 x := line_runs _ _ (by simp [readSupport,safeLine,Butterfly.safe])
  have old (z : ℕ) : x z=m z := by simp (disch := omega) [x,readSupport,effect,update,unit,inSign]
  have sp : x inSign=start := by simp [x,readSupport,effect,update,unit,inSign,startHeader,hs] at *
  obtain ⟨f,hf,y,act,tables,sg,pr,rest⟩ := execute_run room (by omega) cap x sp ((old 320).trans ml)
  let o := writeSupport.foldl effect y
  have endRun : Runs W (line writeSupport) y 3 o := line_runs _ _ (by simp [writeSupport,safeLine,Butterfly.safe])
  have others (z : ℕ) (p : z≠351) (q : z≠352) : o z=y z := by
    simp (disch := omega) [o,writeSupport,effect,update,unit,inSign,inIndex,signHeader,pairHeader,
      show (z:ℤ)≠351 by omega,show (z:ℤ)≠352 by omega]
  have stageBase := level_lo start L
  have cells (z : ℕ) (hz : level start L≤z) : o z=y z := others z (by omega) (by omega)
  have pow : 1≤(2^L:ℕ)^5 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by decide))
  have bound := hf.trans (support_cost L)
  refine ⟨_,by rw [show constant+35=(constant+30)+5 by omega,Nat.add_mul];omega,o,.seq pre (.seq act endRun),
    ?_,?_,?_,fun z a b h => (others z a b).trans ((rest z h).trans (old z))⟩
  · exact ⟨fun j v => (cells _ (by omega)).trans (tables.signs j v),fun j v => (cells _ (by omega)).trans (tables.partners j v)⟩
  · simp [o,writeSupport,effect,update,unit,inSign,inIndex,signHeader,pairHeader,sg] at *
  · simp [o,writeSupport,effect,update,unit,inSign,inIndex,signHeader,pairHeader,pr] at *

end VWZClique.IntegerRAM.Projected.SupportDP
end

/- NativeSquareDepth -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM

/-- The actual controller computes the first strictly larger radix power
and its associated integer scaling factor. -/
theorem padding_depth {W b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (c : ℤ) (m : IntegerRAM.Memory) (given : m nReg=n)
    (guards : ∀ t ≤ depth b n, Fits W (((b^t:ℕ):ℤ)-(n+1:ℕ))) :
    ∃ out, Runs W (padCommand b c) m (2+(depth b n)*padSteps b c) out ∧
      out (-3)=((b^(depth b n):ℕ):ℤ) ∧ out scaleReg=c^(depth b n) ∧
      ∀ z, floor < z → z≠ -3 → z≠scaleReg → z≠paddingTest → out z=m z := by
  have go (j r : ℕ) (jr : j+r=depth b n) (hr : 0 < r) (x : IntegerRAM.Memory)
      (xn : x nReg=n) (xs : x (-3)=((b^j:ℕ):ℤ)) (xc : x scaleReg=c^j) :
      ∃ out, Runs W (.repeatWhileNegative (padIter b c) paddingTest) x (r*padSteps b c) out ∧
        out (-3)=((b^(depth b n):ℕ):ℤ) ∧ out scaleReg=c^(depth b n) ∧
        ∀ z, floor < z → z≠ -3 → z≠scaleReg → z≠paddingTest → out z=x z := by
    induction r generalizing j x with
    | zero => omega
    | succ r ih =>
      have jj : j+1 ≤ depth b n := by omega
      obtain ⟨y,ry,fy⟩ := assign_run (W:=W) x (by decide : floor < -3) (times side (num b))
        (by simp [times,side,num,Expr.safe,floor])
      have ys : y (-3)=((b^(j+1):ℕ):ℤ) := by simp [fy _ (by decide : floor < -3),times,side,num,Expr.val,xs,pow_succ]
      have ky (z : ℤ) (lo : floor < z) (ne : z≠ -3) := (fy z lo).trans (if_neg ne)
      obtain ⟨v,rv,fv⟩ := assign_run (W:=W) y (by decide : floor < scaleReg) (scaleMultiply c)
        (by simp [scaleMultiply,Expr.safe,floor,scaleReg])
      have vc : v scaleReg=c^(j+1) := by
        simp [fv _ (by decide : floor < scaleReg),scaleMultiply,Expr.val,ky scaleReg (by decide) (by decide),xc,pow_succ]
      have kv (z : ℤ) (lo : floor < z) (ne : z≠scaleReg) := (fv z lo).trans (if_neg ne)
      obtain ⟨a,ra,fa⟩ := assign_run (W:=W) v (by decide : floor < paddingTest) padComparison
        (by simp [padComparison,side,Expr.safe,floor,nReg])
      have ka (z : ℤ) (lo : floor < z) (ne : z≠paddingTest) := (fa z lo).trans (if_neg ne)
      have av : a paddingTest=((b^(j+1):ℕ):ℤ)-(n+1:ℕ) := by
        rw [fa _ (by decide),if_pos rfl]
        simp [padComparison,side,Expr.val,kv (-3) (by decide) (by decide),ys,kv nReg (by decide) (by decide),
          ky nReg (by decide) (by decide),xn]
      have run : Runs W (padIter b c) x _ a := Runs.seq ry (Runs.seq rv ra)
      have sa := (ka (-3) (by decide) (by decide)).trans ((kv (-3) (by decide) (by decide)).trans ys)
      have ca := (ka scaleReg (by decide) (by decide)).trans vc
      have keep (z : ℤ) (lo : floor < z) (n₁ : z≠ -3) (n₂ : z≠scaleReg) (n₃ : z≠paddingTest) :
          a z=x z := (ka z lo n₃).trans ((kv z lo n₂).trans (ky z lo n₁))
      have ha : Fits W (a paddingTest) := av ▸ guards _ jj
      by_cases eq : r=0
      · subst r
        have je : j+1=depth b n := by omega
        have gt := Nat.lt_pow_succ_log_self hb n
        change n < b^(depth b n) at gt
        refine ⟨a,?_,by simpa [je] using sa,by simpa [je] using ca,keep⟩
        simpa [padSteps] using Runs.loop_done run ha (by rw [av,je]; omega)
      · have jlt : j+1 ≤ Nat.log b n := by dsimp [depth] at jr; omega
        have le := (Nat.pow_le_pow_right (by omega : 0 < b) jlt).trans (Nat.pow_log_le_self b (by omega : n≠0))
        obtain ⟨o,ro,so,co,ko⟩ := ih (j+1) (by omega) (by omega) a
          ((keep nReg (by decide) (by decide) (by decide) (by decide)).trans xn) sa ca
        refine ⟨o,?_,so,co,fun z lo n₁ n₂ n₃ => (ko z lo n₁ n₂ n₃).trans (keep z lo n₁ n₂ n₃)⟩
        rw [Nat.succ_mul,Nat.add_comm]
        exact Runs.loop_again run ha (by rw [av]; omega) ro
  let x := update m (-3) 1
  let y := update x scaleReg 1
  obtain ⟨o,r,s,sc,fr⟩ := go 0 (depth b n) (by simp) (by dsimp [depth]; omega) y
    (by simpa [y,x,update,scaleReg,nReg] using given) (by simp [y,x,update,scaleReg]) (by simp [y,update])
  exact ⟨o,by simpa only [padCommand,←Nat.add_assoc] using Runs.seq (.atom (.one m (-3))) (Runs.seq (.atom (.one x scaleReg)) r),
    s,sc,fun z lo a b d => (fr z lo a b d).trans (by simp only [y,x,update,if_neg a,if_neg b])⟩

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeProjectionSmallScale -/
section
namespace VWZClique.IntegerRAM.Projected.SmallScale
open Structured Butterfly Graph BlockMM SquareCode.Layout

/-- Record the scaling factor of every small square before processing the first
label. This control path also executes when the projected label set is empty. -/
theorem calculate_run {W L M b : ℕ} (hb : 2≤b) (c : ℕ) (room : Division.Room W M)
    (space : b*2^L+1≤M) (m : Memory) (dim : m 0=((2^L:ℕ):ℤ)) :
    ∃ f≤6+(L+1)*padSteps b c, ∃ o, Runs W (calculate b c) m f o ∧
      o header=((c^(depth b (2^L)):ℕ):ℤ) ∧ ∀ z : ℕ, z≠367 → o z=m z := by
  let x := loadN.foldl effect m
  have step : Runs W (line loadN) m 2 x := line_runs _ _ (by simp [loadN,safeLine,Butterfly.safe])
  have h : x nReg=((2^L:ℕ):ℤ) := by simp [x,loadN,effect,update,one,nReg,dim]
  have old (z : ℕ) : x z=m z := by simp (disch := omega) [x,loadN,effect,update,one,nReg]
  have hn : 1≤2^L := Nat.one_le_pow _ _ (by decide)
  have bn : 2^L≤b*2^L := by simpa only [one_mul] using Nat.mul_le_mul_right (2^L) (by omega : 1≤b)
  have bd := (depth_bounds hb hn).2
  obtain ⟨y,run,_,scale,frame⟩ := padding_depth hb hn (c:ℤ) x h (fun t ht => by
    have p := (Nat.pow_le_pow_right (by omega : 0<b) ht).trans bd
    apply room.fits <;> omega)
  let o := writeScale.foldl effect y
  have endRun : Runs W (line writeScale) y 2 o := line_runs _ _ (by simp [writeScale,safeLine,Butterfly.safe])
  have lg : Nat.log b (2^L)≤L := by
    simpa only [Nat.log_pow (by decide : 1<(2:ℕ))] using Nat.log_anti_left (n:=2^L) (by decide : 1<(2:ℕ)) hb
  have fuel := Nat.mul_le_mul_right (padSteps b c) (by unfold depth;omega : depth b (2^L)≤L+1)
  refine ⟨_,by omega,o,.seq step (.seq run endRun),?_,?_⟩
  · simp [o,writeScale,effect,update,one,header,SquareCode.Layout.scaleReg,scale,Nat.cast_pow] at *
  · intro z hz
    have eq := frame (z:ℤ) (by unfold floor;omega) (by omega) (by unfold SquareCode.Layout.scaleReg;omega) (by unfold paddingTest;omega)
    simp (disch := omega) [o,writeScale,effect,update,one,header,show (z:ℤ)≠367 by omega,eq,old]

end VWZClique.IntegerRAM.Projected.SmallScale
end

/- NativeProjectionPrepare -/
section
namespace VWZClique.IntegerRAM.Projected.Preparation
open Structured UniformFolds NativeFrame NativeTraversal NativeArena BlockMM

private theorem move_params {n base count : ℕ} {x y : Memory} (p : Init.Params base n count x)
    (fr : ∀ z : ℕ, 350≤ z → z≤380 → z≠351 → z≠352 → z≠367 → y z=x z) :
    Init.Params base n count y := by
  constructor
  · exact (fr 350 (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.weights
  · exact (fr 358 (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.codeBase
  · exact (fr 359 (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.size
  · exact (fr 370 (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.coefficients
  · exact (fr 379 (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.start
  · exact (fr 371 (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.source
  · exact (fr 372 (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.middle
  · exact (fr 373 (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.right
  · exact (fr 374 (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.raw
  · exact (fr 356 (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.smallWork
  · exact (fr 375 (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.wt
  · exact (fr 376 (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.leftPack
  · exact (fr 377 (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.rightPack
  · exact (fr 378 (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.product

theorem verifiedPublicationStep {W M L root output d b c : ℕ} (large : 512≤ root) (hd : d≤36) (hb : 2≤ b)
    (H : SimpleGraph V) (w : WeightKey (2^L)→ℚ) (q : List (NativeTraversal.Slot L)) (m : Memory)
    (room : Graph.Division.Room W M)
    (supportRoom : MaskScan.Arena.slot (atDepth root (2^L) d) (2^L) 7+2+3*8^L≤ M)
    (ratio : 2^(L+1)*(4*windowAt (Nat.card H.edgeSet))≤ M) (padding : b*2^L+1≤ M)
    (src : Repr (layout L root output large) (.input d w::q) m) :
    let base := atDepth root (2^L) d
    let K := windowAt (Nat.card H.edgeSet)
    let count := (RankSwap.outside L (lower K L) (width K L)).card
    ∃ f≤ ticks d K b c L, ∃ o, Runs W (command d K b c) m f o ∧ Ready L K base count b c w o ∧
      ∀ z : ℕ, projectionPrefix base (2^L) z → o z=m z := by
  let n := 2^L
  let base := atDepth root n d
  let K := windowAt (Nat.card H.edgeSet)
  let start := MaskScan.Arena.slot base n 7+2
  have b0 : 512≤ base := (layout L root output large).large d
  have beg : metaBase base n≤ start := by dsimp [metaBase,tableWords,start,MaskScan.Arena.slot,MaskScan.Arena.origin,MaskScan.Arena.span];rw [pow_two];omega
  have extent : base≤ metaBase base n := by dsimp [metaBase];omega
  have cap : start+3*8^L≤ M := supportRoom
  have addr : MaskScan.Arena.slot base n 7+1≤ M := by change MaskScan.Arena.slot base n 7+2+3*8^L≤ M at cap;omega
  obtain ⟨f,hf,x,init,xctx,pre,xfr⟩ := frame_init large hd H w q m room addr ratio src
  obtain ⟨y,head,params,yfr⟩ := Init.run hd b0 x xctx.1.dim xctx.2.1.1 pre room (by change start≤ M;omega)
  have yl : y 320=L := (yfr 320 (Or.inl (by decide))).trans xctx.1.length
  obtain ⟨g,hg,z,make,banks,sg,pr,zfr⟩ := SupportDP.withHeaders_run (start:=start) room (by omega) cap y params.start yl
  have xn : x 0=(n:ℤ) := xctx.1.dim
  have zn : z 0=(n:ℤ) := (zfr 0 (by decide) (by decide) (Or.inl (by omega))).trans ((yfr 0 (Or.inl (by decide))).trans xn)
  obtain ⟨k,hk,o,pad,pow,ofr⟩ := SmallScale.calculate_run hb c room padding z zn
  have oy (i : ℕ) (a : i≠351) (b : i≠352) (c : i≠367) (up : i< start) : o i=y i :=
    (ofr i c).trans (zfr i a b (Or.inl up))
  have keptPrefix (i : ℕ) (h : projectionPrefix base n i) : o i=m i := by
    have old := xfr i h
    rcases h with h|h|h|h
    all_goals
      have bound : i< start := by omega
      exact (oy i (by omega) (by omega) (by omega) bound).trans ((yfr i (by omega)).trans old)
  have ox (i : ℕ) (lo : base ≤ i) (hi : i < start) : o i=x i :=
    (oy i (by omega) (by omega) (by omega) hi).trans (yfr i (Or.inr (by omega)))
  have om : MaskScan.Arena.Prepared L K base o := pre.congr ox
  have height := Workspace.level_lo start L
  have ot : SupportDP.BanksAt L (Workspace.level start L) (Workspace.level start L+8^L) o :=
    ⟨fun j v => (ofr _ (by omega)).trans (banks.signs j v),fun j v => (ofr _ (by omega)).trans (banks.partners j v)⟩
  refine ⟨_,by unfold ticks headerTime;omega,o,.seq init (.seq head (.seq make pad)),?_,keptPrefix⟩
  refine ⟨om,move_params params (fun i lo hi a b c => oy i a b c (by omega)),?_,
    (ofr 0 (by decide)).trans zn,(keptPrefix 320 (Or.inr (Or.inl rfl))).trans src.1.length,
    ot,(ofr 351 (by decide)).trans sg,(ofr 352 (by decide)).trans pr,pow⟩
  intro i
  have h : Graph.Table.wordIndex i<9*n+81*(n*n) := NativeLeaf.index_lt i
  have place : projectionPrefix base n (base+Graph.Table.wordIndex i) :=
    Or.inr (Or.inr (Or.inr ⟨by omega,by dsimp [metaBase,tableWords];omega⟩))
  exact (congrArg (Int.cast : ℤ → ℚ) (keptPrefix _ place)).trans (src.2.1.2 i)

end VWZClique.IntegerRAM.Projected.Preparation
end

open VWZClique VWZClique.IntegerRAM VWZClique.IntegerRAM.Projected VWZClique.IntegerRAM.Projected.Preparation VWZClique.IntegerRAM.Structured VWZClique.UniformFolds VWZClique.IntegerRAM.NativeFrame VWZClique.NativeTraversal VWZClique.IntegerRAM.NativeArena VWZClique.BlockMM
theorem solution {W M L root output d b c : ℕ} (large : 512≤ root) (hd : d≤36) (hb : 2≤ b)
    (H : SimpleGraph V) (w : WeightKey (2^L)→ℚ) (q : List (NativeTraversal.Slot L)) (m : Memory)
    (room : Graph.Division.Room W M)
    (supportRoom : MaskScan.Arena.slot (atDepth root (2^L) d) (2^L) 7+2+3*8^L≤ M)
    (ratio : 2^(L+1)*(4*windowAt (Nat.card H.edgeSet))≤ M) (padding : b*2^L+1≤ M)
    (src : Repr (layout L root output large) (.input d w::q) m) :
    let base := atDepth root (2^L) d
    let K := windowAt (Nat.card H.edgeSet)
    let count := (RankSwap.outside L (lower K L) (width K L)).card
    ∃ f≤ ticks d K b c L, ∃ o, Runs W (command d K b c) m f o ∧ Ready L K base count b c w o ∧
      ∀ z : ℕ, projectionPrefix base (2^L) z → o z=m z
  := @VWZClique.IntegerRAM.Projected.Preparation.verifiedPublicationStep W M L root output d b c large hd hb H w q m room supportRoom ratio padding src
