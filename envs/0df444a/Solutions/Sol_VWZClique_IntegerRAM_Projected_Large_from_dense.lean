-- Prove2me | solution 1 for VWZClique.IntegerRAM.Projected.Large.from_dense
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T14:08:27.933085+00:00
-- url     : https://prove2.me/submissions/5307cc45-ad0a-4d6e-a196-1a3a8ecd7bfd

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

/- NativeSquareGuarded -/
section
namespace VWZClique.IntegerRAM.SquareCode
open Structured

theorem gated_run {W : ℕ} (m : Memory) (d : ℤ) (dst g k value : Expr)
    (ds : dst.safe d W m) (gs : g.safe d W m) (ks : k.safe d W m)
    (vs : 0 ≤ g.val m → 0 ≤ k.val m → value.safe d W m)
    (fd : Fits W (dst.val m)) (fg : Fits W (g.val m)) (fk : Fits W (k.val m)) :
    ∃ t, t ≤ gatedSteps dst g k value ∧ ∃ out, Runs W (gatedWrite d dst g k value) m t out ∧
      ∀ z, d<z → out z=if z=dst.val m then (if 0 ≤ g.val m ∧ 0 ≤ k.val m then value.val m else 0) else m z := by
  let i := d-1
  let j := d-2
  let v := d-3
  obtain ⟨a,ra,da,fa⟩ := dst.run m d ds
  obtain ⟨ge,gs⟩ := carry (show i≤d by dsimp [i]; omega) fa g gs
  obtain ⟨b,rb,gb,fb⟩ := g.run a i gs
  have lowB (z : ℤ) (h : d<z) : b z=m z := (fb z (by dsimp [i]; omega)).trans (fa z h)
  obtain ⟨ke,ks⟩ := carry (show j≤d by dsimp [j]; omega) lowB k ks
  obtain ⟨c,rc,kc,fc⟩ := k.run b j ks
  let x := update c v (c v-c v)
  have lowX (z : ℤ) (h : j<z) : x z=b z := by
    simp only [x,update,if_neg (by dsimp [j,v] at *; omega : z≠v),fc z h]
  have xg : x i=g.val m := (lowX i (by dsimp [i,j]; omega)).trans (gb.trans ge)
  have xk : x j=k.val m := by simpa only [x,update,if_neg (by dsimp [j,v]; omega : j≠v)] using kc.trans ke
  have xd : x d=dst.val m := (lowX d (by dsimp [j]; omega)).trans ((fb d (by dsimp [i]; omega)).trans da)
  have framed (z : ℤ) (h : d<z) : x z=m z := (lowX _ (by dsimp [j]; omega)).trans (lowB _ h)
  have guarded : ∃ s, s ≤ value.steps+2 ∧ ∃ y, Runs W (.whenNonnegative i (.whenNonnegative j (value.code v))) x s y ∧
      y d=dst.val m ∧ (∀ z, d<z → y z=m z) ∧ y v=(if 0 ≤ g.val m ∧ 0 ≤ k.val m then value.val m else 0) := by
    by_cases g₀ : 0 ≤ g.val m
    · by_cases k₀ : 0 ≤ k.val m
      · obtain ⟨given,safe⟩ := carry (show v≤d by dsimp [v]; omega) framed value (vs g₀ k₀)
        obtain ⟨y,run,vy,fy⟩ := value.run x v safe
        exact ⟨1+(1+value.steps),by omega,y,.guard_take (xg ▸ fg) (by rw [xg]; omega) (.guard_take (xk ▸ fk) (by rw [xk]; omega) run),
          (fy _ (by dsimp [v]; omega)).trans xd,fun z zh => (fy z (by dsimp [v]; omega)).trans (framed _ zh),
          by simpa [g₀,k₀] using vy.trans given⟩
      · exact ⟨1+1,by omega,x,.guard_take (xg ▸ fg) (by rw [xg]; omega) (.guard_skip (xk ▸ fk) (by rw [xk]; omega)),
          xd,framed,by simp [x,update,g₀,k₀]⟩
    · exact ⟨1,by omega,x,.guard_skip (xg ▸ fg) (by rw [xg]; omega),xd,framed,by simp [x,update,g₀]⟩
  obtain ⟨s,hs,y,ry,yd,py,vy⟩ := guarded
  have store := Runs.atom (Step.store (W:=W) y d v (yd ▸ fd))
  refine ⟨_,by unfold gatedSteps; omega,_,.seq ra (.seq rb (.seq rc (.seq (.atom (.sub c v v v)) (.seq ry store)))),?_⟩
  intro z hz
  simp [update,yd,vy,py z hz]

end VWZClique.IntegerRAM.SquareCode
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

/- NativeSquareProjectPacking -/
section
namespace VWZClique.IntegerRAM.Projected.Packing
open Structured SquareCode

def index (which : Role) (a b s p r c : ℕ) :=
  match which with
  | .weight => c*a+r
  | .middle => r*(b*s)+(p*s+c)
  | .right => (p*s+r)*a+c

def Inside (role : Role) (a r c : ℕ) :=
  (rowCheck role=true → r<a) ∧ (colCheck role=true → c<a)

def entry (which : Role) (a b s p base row col : ℕ) (m : Memory) : ℤ :=
  if (((rowCheck which)=false ∨ row<a) ∧ ((colCheck which)=false ∨ col<a)) then
    m (base+index which a b s p row col:ℕ) else 0

/-- Native zero-padding, transposition and slice gathering for one of the three
projected tile roles. Registers -51 through -55 hold source, short dimension,
packet count, packet number, and destination, respectively. Raster.lim holds
the square tile side. -/
theorem pack_runs {W M a b s p base output : ℕ} (which : Role) (hs : 0<s) (ha : a ≤ s) (sideM : s ≤ M)
    (cap : ∀ v : ℤ, -(M:ℤ) ≤ v → v ≤ M → Fits W v) (room : output+s*s ≤ M)
    (sourceBelow : ∀ r<s, ∀ c<s, Inside which a r c → base+index which a b s p r c < output)
    (m : Memory) (sw : m Raster.lim=s) (sr : m src=base) (sa : m short=a)
    (sb : m count=b) (sp : m packet=p) (so : m dst=output) :
    ∃ f≤2+s*(1+s*(cellCost which+3)+3), ∃ y, Runs W (pack which) m f y ∧
      Raster.buffer output (fun j => entry which a b s p base (j/s) (j%s) m) m (s*s) y ∧ Raster.saved m y := by
  apply Raster.run_fills hs m sw (fun t ht => cap _ (by omega) (by omega))
  intro r hr c hc x saved old xr xc
  have ref (u : ℤ) (lo : Raster.floor<u) (hi : u<0) (n : ¬Raster.privateReg u) := saved u lo hi n
  have Xs := (ref _ (by decide) (by decide) (by unfold Raster.privateReg; decide : ¬Raster.privateReg Raster.lim)).trans sw
  have Xsrc := (ref _ (by decide) (by decide) (by unfold Raster.privateReg; decide : ¬Raster.privateReg src)).trans sr
  have Xa := (ref _ (by decide) (by decide) (by unfold Raster.privateReg; decide : ¬Raster.privateReg short)).trans sa
  have Xb := (ref _ (by decide) (by decide) (by unfold Raster.privateReg; decide : ¬Raster.privateReg count)).trans sb
  have Xp := (ref _ (by decide) (by decide) (by unfold Raster.privateReg; decide : ¬Raster.privateReg packet)).trans sp
  have Xout := (ref _ (by decide) (by decide) (by unfold Raster.privateReg; decide : ¬Raster.privateReg dst)).trans so
  have addr : (source which).val x=((base+index which a b s p r c:ℕ):ℤ) := by
    cases which <;> simp [source,index,Expr.val,Xsrc,Xa,Xb,Xp,Xs,xr,xc]
  have dstEq : target.val x=((output+(r*s+c):ℕ):ℤ) := by simp [target,Expr.val,Xout,xr,xc,Xs]
  have dBound : output+(r*s+c)<output+s*s := by
    have e := Nat.mul_le_mul_right s hr
    rw [Nat.succ_mul] at e
    omega
  have guardEq (on : Bool) (reg : ℤ) (j : ℕ) (h : x reg=j) :
      (check on reg).val x=(if on then (a:ℤ)-1-j else 0) := by
    cases on <;> simp [check,Expr.val,Xa,h]
  have rg := guardEq (rowCheck which) Raster.row r xr
  have cg := guardEq (colCheck which) Raster.col c xc
  have idxOK (rowG : 0 ≤ (check (rowCheck which) Raster.row).val x) (colG : 0 ≤ (check (colCheck which) Raster.col).val x) :
      Inside which a r c := by
    constructor
    · intro eq; rw [rg,eq] at rowG; simp only [if_true] at rowG; omega
    · intro eq; rw [cg,eq] at colG; simp only [if_true] at colG; omega
  have safeCheck (on : Bool) (reg : ℤ) (regOk : Raster.floor<reg) : (check on reg).safe Raster.floor W x := by
    cases on <;> simp [check,Expr.safe,Raster.floor] at * <;> assumption
  have bound (on : Bool) (j : ℕ) (hj : j<s) : Fits W (if on then (a:ℤ)-1-j else 0) := by
    cases on <;> simp only [Bool.false_eq_true,if_false,if_true] <;> apply cap <;> omega
  obtain ⟨t,hT,y,run,fr⟩ := gated_run (W:=W) x Raster.floor target (check (rowCheck which) Raster.row) (check (colCheck which) Raster.col)
    (.read (source which)) (by simp [target,Expr.safe,Raster.floor]) (safeCheck _ _ (by decide)) (safeCheck _ _ (by decide))
    (fun rg cg => by
      have range := sourceBelow r hr c hc (idxOK rg cg)
      refine ⟨?_,?_,?_⟩
      · cases which <;> simp [source,Expr.safe,Raster.floor]
      · rw [addr]; unfold Raster.floor; omega
      · rw [addr]; apply cap <;> omega)
    (dstEq ▸ cap _ (by omega) (by omega)) (rg ▸ bound _ r hr) (cg ▸ bound _ c hc)
  refine ⟨t,hT,y,run,?_⟩
  intro z lo
  rw [fr z lo,dstEq]
  have div : (r*s+c)/s=r := by rw [Nat.mul_comm r s,Nat.mul_add_div hs,Nat.div_eq_of_lt hc,Nat.add_zero]
  have md : (r*s+c)%s=c := by rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hc]
  rw [div,md]
  have guards : (0 ≤ (check (rowCheck which) Raster.row).val x ∧ 0 ≤ (check (colCheck which) Raster.col).val x) ↔
      (((rowCheck which)=false ∨ r<a) ∧ ((colCheck which)=false ∨ c<a)) := by
    rw [rg,cg]
    cases rowCheck which <;> cases colCheck which <;> simp <;> omega
  by_cases good : (((rowCheck which)=false ∨ r<a) ∧ ((colCheck which)=false ∨ c<a))
  · have gg := guards.mpr good
    have same : (Expr.read (source which)).val x=m (base+index which a b s p r c:ℕ) := by
      simp only [Expr.val,addr]
      exact old _ (sourceBelow _ hr _ hc (idxOK gg.1 gg.2))
    simp only [if_pos gg,entry,if_pos good,same]
  · simp only [if_neg (fun e => good (guards.mp e)),entry,if_neg good]

end VWZClique.IntegerRAM.Projected.Packing
end

/- NativeProjectionTiles -/
section
namespace VWZClique.IntegerRAM.Projected

/-- Extend a short packed array by zeros in the tail of a tile. -/
def pad {a s : ℕ} (f : Fin a → ℤ) (i : Fin s) : ℤ :=
  if h : i.val < a then f ⟨i.val,h⟩ else 0

theorem pad_sum {a s : ℕ} (h : a ≤ s) (f : Fin a → ℤ) :
    ∑ i : Fin s, pad f i = ∑ i : Fin a, f i := by
  classical
  symm
  apply Fintype.sum_of_injective (fun x : Fin a => x.castLE h) (Fin.castLE_injective h)
  · intro i hi
    have hn : ¬i.val < a := fun l => hi ⟨⟨i.val,l⟩,Fin.ext rfl⟩
    simp [pad,hn]
  · intro i
    simp [pad]

def weightTile {a : ℕ} (s : ℕ) (A : Tile a) : Tile s :=
  fun v u => pad (fun j => pad (fun i => A i j) u) v

def midTile {a t s : ℕ} (B : Matrix (Fin a) (Fin t × Fin s) ℤ) (p : Fin t) : Tile s :=
  fun v x => pad (fun j => B j (p,x)) v

def rightTile {a t s : ℕ} (C : Matrix (Fin t × Fin s) (Fin a) ℤ) (p : Fin t) : Tile s :=
  fun x u => pad (fun i => C (p,x) i) u

def dotTile {s : ℕ} (A B : Tile s) : ℤ := ∑ i, ∑ j, A i j * B i j

/-- Multiply each contiguous pair of square tiles, contract it against a single
transposed weight tile, and accumulate one scalar. -/
theorem tile_trace {a t s : ℕ} (h : a ≤ s) (A : Tile a)
    (B : Matrix (Fin a) (Fin t × Fin s) ℤ) (C : Matrix (Fin t × Fin s) (Fin a) ℤ) :
    (∑ p, dotTile (weightTile s A) (midTile B p * rightTile C p)) =
      Matrix.trace (A * (B*C)) := by
  classical
  have tile (p : Fin t) : dotTile (weightTile s A) (midTile B p * rightTile C p) =
      ∑ v : Fin a, ∑ u : Fin a, A u v * ∑ x : Fin s, B v (p,x)*C (p,x) u := by
    unfold dotTile
    rw [← pad_sum h (fun v : Fin a => ∑ u : Fin a, A u v * ∑ x : Fin s, B v (p,x)*C (p,x) u)]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v.val < a
    · simp only [pad,hv,dif_pos]
      rw [← pad_sum h (fun u : Fin a => A u ⟨v.val,hv⟩ *
        ∑ x : Fin s, B ⟨v.val,hv⟩ (p,x)*C (p,x) u)]
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : u.val < a <;>
        simp [pad,weightTile,midTile,rightTile,Matrix.mul_apply,hu,hv]
    · simp [pad,weightTile,hv]
  simp_rw [tile]
  change _ = ∑ u, ∑ v, A u v * ∑ x, B v x * C x u
  simp_rw [Fintype.sum_prod_type,Finset.mul_sum]
  calc
    _ = ∑ v : Fin a, ∑ p : Fin t, ∑ u : Fin a, ∑ x : Fin s,
        A u v * (B v (p,x)*C (p,x) u) := Finset.sum_comm
    _ = ∑ v : Fin a, ∑ u : Fin a, ∑ p : Fin t, ∑ x : Fin s,
        A u v * (B v (p,x)*C (p,x) u) :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

end VWZClique.IntegerRAM.Projected
end

/- WordDot -/
section
namespace VWZClique.IntegerRAM.WordDot
open Structured

/-- The addresses of one arithmetic progression in the nonnegative data area. -/
structure Stream where
  base : ℕ
  stride : ℕ

def Stream.addr (s : Stream) (i : ℕ) : ℕ := s.base + i * s.stride

theorem Stream.addr_succ (s : Stream) (i : ℕ) :
    s.addr (i+1) = s.addr i + s.stride := by
  simp [Stream.addr, Nat.succ_mul, Nat.add_assoc]

namespace Reg
abbrev dest : ℤ := -12
end Reg

/-- The caller supplies the start, stride and term count. The kernel initializes
its accumulator, loop counter, guard, and constant. -/
structure Ready (m : Memory) (l r : Stream) (n : ℕ) : Prop where
  leftPtr : m Reg.leftPtr = l.base
  rightPtr : m Reg.rightPtr = r.base
  leftStride : m Reg.leftStride = l.stride
  rightStride : m Reg.rightStride = r.stride
  length : m Reg.length = n

/-- The integer specification uses an ordinary finite dot product. -/
def dot (m : Memory) (l r : Stream) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, m (l.addr i) * m (r.addr i)

/-- Every address outside the eight scratch registers is preserved. -/
def Framed (origin out : Memory) : Prop :=
  ∀ a : ℤ, a < -8 ∨ 0 ≤ a → out a = origin a

private def started (m : Memory) : Memory :=
  let m₁ := update m Reg.one 1
  let m₂ := update m₁ Reg.acc (m₁ Reg.one - m₁ Reg.one)
  let m₃ := update m₂ Reg.count (m₂ Reg.acc - m₂ Reg.length)
  update m₃ Reg.guard (m₃ Reg.length - m₃ Reg.one)

private def after (m : Memory) : Memory :=
  let m₁ := update m Reg.x (m (m Reg.leftPtr))
  let m₂ := update m₁ Reg.y (m₁ (m₁ Reg.rightPtr))
  let m₃ := update m₂ Reg.x (m₂ Reg.x * m₂ Reg.y)
  let m₄ := update m₃ Reg.acc (m₃ Reg.acc + m₃ Reg.x)
  let m₅ := update m₄ Reg.leftPtr (m₄ Reg.leftPtr + m₄ Reg.leftStride)
  let m₆ := update m₅ Reg.rightPtr (m₅ Reg.rightPtr + m₅ Reg.rightStride)
  update m₆ Reg.count (m₆ Reg.count + m₆ Reg.one)

private theorem init_run {W : ℕ} (m : Memory) : Runs W init m 4 (started m) := by
  unfold init started
  exact .seq (t := 3) (.atom (.one _ _))
    (.seq (t := 2) (.atom (.sub _ _ _ _)) (.seq (.atom (.sub _ _ _ _)) (.atom (.sub _ _ _ _))))

private theorem body_run {W : ℕ} (m : Memory)
    (hl : Fits W (m Reg.leftPtr)) (hr : Fits W (m Reg.rightPtr)) :
    Runs W body m 7 (after m) := by
  unfold body after
  refine .seq (t := 6) (.atom (.load _ _ _ hl)) ?_
  refine .seq (t := 5) (.atom (.load _ _ _ ?_)) ?_
  · simpa [update,Reg.x,Reg.rightPtr] using hr
  exact .seq (t := 4) (.atom (.mul _ _ _ _))
    (.seq (t := 3) (.atom (.add _ _ _ _))
    (.seq (t := 2) (.atom (.add _ _ _ _))
    (.seq (.atom (.add _ _ _ _)) (.atom (.add _ _ _ _)))))

private structure Inv (origin : Memory) (l r : Stream) (n i : ℕ) (m : Memory) : Prop where
  leftPtr : m Reg.leftPtr = l.addr i
  rightPtr : m Reg.rightPtr = r.addr i
  leftStride : m Reg.leftStride = l.stride
  rightStride : m Reg.rightStride = r.stride
  one : m Reg.one = 1
  count : m Reg.count = (i:ℤ) - n
  acc : m Reg.acc = dot origin l r i
  frame : Framed origin m

private theorem starts {m : Memory} {l r : Stream} {n : ℕ} (h : Ready m l r n) :
    Inv m l r n 0 (started m) ∧ started m Reg.guard = (n:ℤ)-1 := by
  obtain ⟨hp,hq,hs,ht,hn⟩ := h
  dsimp only [Reg.leftPtr,Reg.rightPtr,Reg.leftStride,Reg.rightStride,Reg.length] at hp hq hs ht hn
  constructor
  · constructor
    all_goals try simp [started,update,dot,Stream.addr,Reg.leftPtr,Reg.rightPtr,
      Reg.acc,Reg.one,Reg.count,Reg.guard,Reg.leftStride,Reg.rightStride,Reg.length,hp,hq,hs,ht,hn]
    intro a ha
    simp only [update]
    split_ifs <;> first | rfl | omega
  · simp [started,update,Reg.acc,Reg.count,Reg.one,Reg.guard,Reg.length,hn]

private theorem advances {o m : Memory} {l r : Stream} {n i : ℕ} (h : Inv o l r n i m) :
    Inv o l r n (i+1) (after m) := by
  obtain ⟨hp,hq,hs,ht,h1,hc,ha,hf⟩ := h
  have hx := hf (l.addr i) (Or.inr (Int.natCast_nonneg _))
  have hy := hf (r.addr i) (Or.inr (Int.natCast_nonneg _))
  dsimp only [Reg.leftPtr,Reg.rightPtr,Reg.leftStride,Reg.rightStride,Reg.acc,
    Reg.count,Reg.one] at hp hq hs ht h1 hc ha
  constructor
  all_goals try simp (disch := omega) [after,update,Reg.leftPtr,Reg.rightPtr,Reg.x,Reg.y,Reg.acc,
    Reg.one,Reg.count,Reg.leftStride,Reg.rightStride,hp,hq,hs,ht,h1,hc,ha,hx,hy,
    Stream.addr_succ,dot,Finset.sum_range_succ]
  · omega
  · intro a hat
    simp only [update]
    split_ifs <;> first | exact hf a hat | omega

private theorem test_fits {W n i : ℕ} (h : Fits W ((n:ℤ)-1)) (hi : i < n) :
    Fits W (((i+1:ℕ):ℤ) - n) := by
  have hp : (0:ℤ) < 2^(W-1) := by positivity
  unfold Fits at *
  omega

private theorem iterates {W n : ℕ} {o : Memory} {l r : Stream}
    (guardFit : Fits W ((n:ℤ)-1))
    (leftFit : ∀ j < n, Fits W (l.addr j : ℤ)) (rightFit : ∀ j < n, Fits W (r.addr j : ℤ))
    (remaining i : ℕ) (m : Memory) (hlen : i + (remaining+1) = n) (h : Inv o l r n i m) :
    ∃ out, Runs W loop m (8*(remaining+1)) out ∧ Inv o l r n n out := by
  induction remaining generalizing i m with
  | zero =>
    have hi : i < n := by omega
    have act := body_run m (h.leftPtr ▸ leftFit i hi) (h.rightPtr ▸ rightFit i hi)
    have next := advances h
    have endAt : i+1 = n := by omega
    refine ⟨after m,Runs.loop_done act (next.count ▸ test_fits guardFit hi) ?_,endAt ▸ next⟩
    rw [next.count,endAt]
    omega
  | succ remaining ih =>
    have hi : i < n := by omega
    have act := body_run m (h.leftPtr ▸ leftFit i hi) (h.rightPtr ▸ rightFit i hi)
    have next := advances h
    obtain ⟨out,more,done⟩ := ih (i+1) (after m) (by omega) next
    refine ⟨out,?_,done⟩
    rw [show 8*(remaining+1+1) = 7+1+8*(remaining+1) by omega]
    exact Runs.loop_again (reg := Reg.count) act (next.count ▸ test_fits guardFit hi)
      (by rw [next.count]; omega) more

/-- A fixed command computes the strided dot product, including the empty product sum.
Only values used as addresses or branch tests need to fit a signed word. -/
theorem run {W n : ℕ} (m : Memory) (l r : Stream) (ready : Ready m l r n)
    (guardFit : Fits W ((n:ℤ)-1))
    (leftFit : ∀ j < n, Fits W (l.addr j : ℤ)) (rightFit : ∀ j < n, Fits W (r.addr j : ℤ)) :
    ∃ out, Runs W command m (8*n+5) out ∧ out Reg.acc = dot m l r n ∧ Framed m out := by
  obtain ⟨start,guard⟩ := starts ready
  cases n with
  | zero =>
    refine ⟨started m,.seq (s := 4) (t := 1) (init_run m) (.guard_skip (guard ▸ guardFit) ?_),start.acc,start.frame⟩
    rw [guard]
    norm_num
  | succ n =>
    obtain ⟨out,h,done⟩ := iterates guardFit leftFit rightFit n 0 (started m) (by omega) start
    refine ⟨out,?_,done.acc,done.frame⟩
    rw [show 8*(n+1)+5 = 4 + (1+8*(n+1)) by omega]
    exact .seq (init_run m) (.guard_take (guard ▸ guardFit) (by rw [guard]; omega) h)

end VWZClique.IntegerRAM.WordDot
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

def setupMem (m : Memory) : Memory :=
  update (update (update (update (update m Reg.leftPtr (m Cell.wt+m Cell.zero))
    Reg.rightPtr (m Cell.prod+m Cell.zero)) Reg.leftStride 1) Reg.rightStride 1) Reg.length (m Cell.area+m Cell.zero)

private theorem setup_runs (W : ℕ) (m : Memory) : Runs W setupDot m 5 (setupMem m) := by
  unfold setupDot copy setupMem
  exact .seq (t:=4) (.atom (.add _ _ _ _)) (.seq (t:=3) (.atom (.add _ _ _ _))
    (.seq (t:=2) (.atom (.one _ _)) (.seq (.atom (.one _ _)) (.atom (.add _ _ _ _)))))

private theorem setup_frame (m : Memory) (z : ℤ) (hz : z ≤ -30 ∨ 0 ≤ z) : setupMem m z=m z := by
  simp only [setupMem,update,if_neg (by change z≠ -11; omega : z≠Reg.length),
    if_neg (by change z≠ -10; omega : z≠Reg.rightStride),if_neg (by change z≠ -9; omega : z≠Reg.leftStride),
    if_neg (by change z≠ -2; omega : z≠Reg.rightPtr),if_neg (by change z≠ -1; omega : z≠Reg.leftPtr)]

private theorem setup_ready {m : Memory} {l : Layout} {s : ℕ}
    (hz : m Cell.zero=0) (hw : m Cell.wt=l.wt) (hp : m Cell.prod=l.prod)
    (ha : m Cell.area=(s*s:ℕ)) :
    Ready (setupMem m) ⟨l.wt,1⟩ ⟨l.prod,1⟩ (s*s) := by
  constructor <;> simp [setupMem,update,Reg.leftPtr,Reg.rightPtr,Reg.leftStride,Reg.rightStride,
    Reg.length,hz,hw,hp,ha]

private theorem dot_bank {m : Memory} {s : ℕ} (l r : ℕ) (A B : Tile s)
    (left : bank m l A) (right : bank m r B) :
    dot m ⟨l,1⟩ ⟨r,1⟩ (s*s) = dotTile A B := by
  rw [dot,← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : Fin (s*s), flat A i * flat B i :=
      Finset.sum_congr rfl (fun i _ => by simp only [Stream.addr,Nat.mul_one,left i,right i])
    _ = ∑ p : Fin s × Fin s, A p.1 p.2 * B p.1 p.2 :=
      Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_prod_type _

def advanced (m : Memory) : Memory :=
  update (update (update m Cell.acc (m Cell.acc+m Reg.acc)) Cell.lhs (m Cell.lhs+m Cell.area))
    Cell.rhs (m Cell.rhs+m Cell.area)

private theorem advance_runs (W : ℕ) (m : Memory) : Runs W advance m 3 (advanced m) :=
  .seq (t:=2) (.atom (.add _ _ _ _)) (.seq (.atom (.add _ _ _ _)) (.atom (.add _ _ _ _)))

structure Control (m : Memory) (l : Layout) (s t i : ℕ) (z : ℤ) : Prop where
  lhs : m Cell.lhs=(l.lhs+i*(s*s):ℕ)
  rhs : m Cell.rhs=(l.rhs+i*(s*s):ℕ)
  prod : m Cell.prod=l.prod
  wt : m Cell.wt=l.wt
  side : m Cell.side=s
  area : m Cell.area=(s*s:ℕ)
  zero : m Cell.zero=0
  idx : m Cell.idx=i
  one : m Cell.one=1
  lim : m Cell.lim=t
  acc : m Cell.acc=z

private theorem Control.transfer {m m' : Memory} {l s t i z} (h : Control m l s t i z)
    (f : ∀ p : ℤ, -44 ≤ p → p≤ -30 → m' p = m p) : Control m' l s t i z :=
  ⟨(f _ (by decide) (by decide)).trans h.lhs,(f _ (by decide) (by decide)).trans h.rhs,
   (f _ (by decide) (by decide)).trans h.prod,(f _ (by decide) (by decide)).trans h.wt,(f _ (by decide) (by decide)).trans h.side,
   (f _ (by decide) (by decide)).trans h.area,(f _ (by decide) (by decide)).trans h.zero,(f _ (by decide) (by decide)).trans h.idx,
   (f _ (by decide) (by decide)).trans h.one,(f _ (by decide) (by decide)).trans h.lim,(f _ (by decide) (by decide)).trans h.acc⟩

def part {s t} (a : Tile s) (b c : Fin t → Tile s) (i : ℕ) : ℤ :=
  ∑ j ∈ Finset.range i, if h : j < t then dotTile a (b ⟨j,h⟩ * c ⟨j,h⟩) else 0

private theorem Control.advance {m : Memory} {s t i : ℕ} {z : ℤ} {l : Layout}
    (h : Control m l s t i z) :
    Control (nextMemory (advanced m) Cell.idx Cell.flag i t) l s t (i+1) (z+m Reg.acc) := by
  rcases h with ⟨hl,hr,hp,hw,hs,ha,hz,hi,ho,hn,hac⟩
  constructor <;>
    simp [nextMemory,advanced,update,Cell.idx,Cell.flag,Cell.rhs,Cell.lhs,Cell.acc,Cell.area,
      Cell.side,Cell.wt,Cell.prod,Cell.zero,Cell.one,Cell.lim] at * <;>
    simp_all [Nat.succ_mul,Int.natCast_add,Int.natCast_mul] <;> ring

/-- A fixed outer loop evaluates the trace on a stream of packed tiles. Its
instruction count includes square multiplication, both dot-product streams, and
all index/pointer updates. -/
theorem packet_loop_runs {W K s t : ℕ} {μ : ℤ} (ht : 0 < t) (square : Command) (l : Layout)
    (a : Tile s) (b c : Fin t → Tile s) (sq : SquareRun W K μ square l a b c)
    (m : Memory) (tab : Tables m l a b c) (ctl : Control m l s t 0 0)
    (guard : ∀ i ≤ t, Fits W ((i:ℤ)-t)) (lengthFit : Fits W ((s*s:ℕ)-1:ℤ))
    (addrFit : ∀ i < s*s, Fits W ((l.wt+i:ℕ):ℤ) ∧ Fits W ((l.prod+i:ℕ):ℤ)) :
    ∃ f, f ≤ t*(K+8*(s*s)+16) ∧ ∃ out, Runs W (packetLoop square) m f out ∧
      out Cell.acc=μ*(∑ p, dotTile a (b p * c p)) ∧ Tables out l a b c ∧
      (∀ z : ℕ, z<l.preserve → out z=m z) := by
  let inv := fun i x => Control x l s t i (μ*part a b c i) ∧ Tables x l a b c ∧
    ∀ z : ℕ, z<l.preserve → x z=m z
  have init : inv 0 m := ⟨by simpa [part] using ctl,tab,fun _ _ => rfl⟩
  have step (i : ℕ) (hi : i < t) (x : Memory) (hx : inv i x) :
      ∃ f : ℕ, f ≤ K+8*(s*s)+13 ∧ ∃ v : Memory,
        Runs W (onePacket square) x f v ∧ v Cell.idx=i ∧ v Cell.one=1 ∧ v Cell.lim=t ∧
        inv (i+1) (nextMemory v Cell.idx Cell.flag i t) := by
    obtain ⟨ctrl,tables,kept⟩ := hx
    let p : Fin t := ⟨i,hi⟩
    obtain ⟨g,hg,y,mult,prod,ty,pres,save⟩ := sq p x tables ctrl.lhs ctrl.rhs ctrl.prod ctrl.side
    have cy := ctrl.transfer pres
    let y' := setupMem y
    have sy : ∀ v : ℕ, y' v = y v := fun j => setup_frame _ _ (Or.inr (Int.natCast_nonneg _))
    have ry := setup_ready cy.zero cy.wt cy.prod cy.area
    obtain ⟨u,dr,acc,fr⟩ := WordDot.run (W:=W) y' ⟨l.wt,1⟩ ⟨l.prod,1⟩ ry lengthFit
      (fun j hj => by simpa [Stream.addr] using (addrFit j hj).1)
      (fun j hj => by simpa [Stream.addr] using (addrFit j hj).2)
    have ey (v : ℕ) : u v=y v := (fr _ (Or.inr (Int.natCast_nonneg _))).trans (sy v)
    have ctrlU := cy.transfer (fun j _ hj => (fr _ (Or.inl (by omega))).trans (setup_frame _ _ (Or.inl hj)))
    have ed : u Reg.acc=μ*dotTile a (b p * c p) := by
      refine acc.trans ((dot_bank _ _ _ _ (fun j => (sy _).trans (ty.weights j))
        (fun j => (sy _).trans (prod j))).trans ?_)
      simp only [dotTile,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro c _
      ring
    have final : Control (nextMemory (advanced u) Cell.idx Cell.flag i t) l s t (i+1)
        (μ*part a b c (i+1)) := by
      simpa [part,Finset.sum_range_succ,hi,ed,p,mul_add] using ctrlU.advance
    have sam (j : ℕ) : nextMemory (advanced u) Cell.idx Cell.flag i t j = y j := by
      simpa [nextMemory,advanced,update,Cell.idx,Cell.flag,Cell.rhs,Cell.lhs,Cell.acc] using ey j
    refine ⟨g+(5+(8*(s*s)+5+3)),by omega,advanced u,.seq mult (.seq (setup_runs W y) (.seq dr (advance_runs W u))),
      ?_,?_,?_,final,ty.transfer sam,fun z hz => (sam z).trans ((save z hz).trans (kept z hz))⟩
    · simpa [advanced,update,Cell.idx,Cell.rhs,Cell.lhs,Cell.acc] using ctrlU.idx
    · simpa [advanced,update,Cell.one,Cell.rhs,Cell.lhs,Cell.acc] using ctrlU.one
    · simpa [advanced,update,Cell.lim,Cell.rhs,Cell.lhs,Cell.acc] using ctrlU.lim
  obtain ⟨f,hf,o,run,oc,ot,kept⟩ := repeatN_runs (B:=K+8*(s*s)+13) ht _ (by decide) inv guard step init
  refine ⟨f,by simpa [Nat.add_assoc] using hf,o,run,?_,ot,kept⟩
  have last : part a b c t=∑ p, dotTile a (b p*c p) := by
    simp [part,← Fin.sum_univ_eq_sum_range]
  exact oc.acc.trans (congrArg (μ * ·) last)

end VWZClique.IntegerRAM.Projected
end

/- NativeSquareProjectTiles -/
section
namespace VWZClique.IntegerRAM.Projected.Packing
open Structured

def sourceWords (role : Role) (a b s : ℕ) :=
  match role with
  | .weight => a*a | .middle => a*(b*s) | .right => (b*s)*a

theorem source_bound (role : Role) {a b s p r c : ℕ} (hp : p<b) (hr : r<s) (hc : c<s)
    (valid : Inside role a r c) : index role a b s p r c<sourceWords role a b s := by
  have lex {a b i j : ℕ} (hi : i<a) (hj : j<b) : i*b+j<a*b := by
    have x := Nat.mul_le_mul_right b hi
    rw [Nat.succ_mul] at x; omega
  cases role with
  | weight =>
    exact lex (valid.2 rfl) (valid.1 rfl)
  | middle =>
    exact lex (valid.1 rfl) (lex hp hc)
  | right =>
    exact lex (lex hp hr) (valid.2 rfl)

theorem padded_bank {s output : ℕ} {m o : Memory} (v : ℕ → ℕ → ℤ) (A : Tile s)
    (buf : Raster.buffer output (fun j => v (j/s) (j%s)) m (s*s) o)
    (agree : ∀ u w : Fin s, v u w=A u w) : bank o output A := by
  intro i
  obtain ⟨⟨u,w⟩,rfl⟩ := finProdFinEquiv.surjective i
  let q := (finProdFinEquiv (u,w)).val
  have hq : q<s*s := (finProdFinEquiv (u,w)).isLt
  have uq : q=s*u.val+w.val := by simp [q,finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
  have hs : 0<s := Nat.zero_lt_of_lt u.isLt
  have div : q/s=u := by rw [uq,Nat.mul_add_div hs,Nat.div_eq_of_lt w.isLt,Nat.add_zero]
  have md : q%s=w := by rw [uq,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt w.isLt]
  have eq := buf (output+q)
  simp only [if_pos (by omega : output≤output+q ∧ output+q<output+s*s),Nat.add_sub_cancel_left,div,md] at eq
  exact eq.trans (by simpa [flat] using agree u w)

theorem weight_values {a b s p base : ℕ} (A : Tile a) (m : Memory)
    (read : ∀ i j : Fin a, m (base+(i.val*a+j.val):ℕ)=A i j) (r c : Fin s) :
    entry .weight a b s p base r c m=weightTile s A r c := by
  by_cases hr : r.val<a <;> by_cases hc : c.val<a <;>
    simp [entry,rowCheck,colCheck,index,weightTile,pad,hr,hc]
  exact read ⟨c.val,hc⟩ ⟨r.val,hr⟩

theorem mid_values {a b s base : ℕ} (p : Fin b) (B : Matrix (Fin a) (Fin b × Fin s) ℤ) (m : Memory)
    (read : ∀ i : Fin a, ∀ p : Fin b, ∀ c : Fin s, m (base+(i.val*(b*s)+(p.val*s+c.val)):ℕ)=B i (p,c)) (r c : Fin s) :
    entry .middle a b s p base r c m=midTile B p r c := by
  by_cases hr : r.val<a <;> simp [entry,rowCheck,colCheck,index,midTile,pad,hr]
  exact read ⟨r.val,hr⟩ p c

theorem right_values {a b s base : ℕ} (p : Fin b) (C : Matrix (Fin b × Fin s) (Fin a) ℤ) (m : Memory)
    (read : ∀ p : Fin b, ∀ r : Fin s, ∀ c : Fin a, m (base+((p.val*s+r.val)*a+c.val):ℕ)=C (p,r) c) (r c : Fin s) :
    entry .right a b s p base r c m=rightTile C p r c := by
  by_cases hc : c.val<a <;> simp [entry,rowCheck,colCheck,index,rightTile,pad,hc]
  exact read p r ⟨c.val,hc⟩

end VWZClique.IntegerRAM.Projected.Packing
end

/- NativeSquarePackMany -/
section
namespace VWZClique.IntegerRAM.Projected.Packing
open Structured

def PacketFrame (m x : Memory) :=
  ∀ z, Raster.floor<z → z<0 → ¬Raster.privateReg z → z≠dst → z≠areaReg →
    z≠packOne → z≠packet → z≠packFlag → x z=m z

private theorem entry_congr {a b s p base i j : ℕ} {m x : Memory} (role : Role)
    (eq : Inside role a i j → x (base+index role a b s p i j:ℕ)=m (base+index role a b s p i j:ℕ)) :
    entry role a b s p base i j x=entry role a b s p base i j m := by
  unfold entry
  split
  next ok =>
    apply eq
    constructor
    · intro h; rcases ok.1 with no|yes; simp [h] at no; exact yes
    · intro h; rcases ok.2 with no|yes; simp [h] at no; exact yes
  next => rfl

/-- Pack every B or C tile into consecutive destinations. This single native
loop reads the source, short side, packet count, tile side, and destination from
the same registers as a single-packet pack. It initializes the packet counter. -/
theorem packMany_runs {W M a b s base output : ℕ} (role : Role) (hs : 0<s) (hb : 0<b)
    (ha : a ≤ s) (sm : s ≤ M) (bm : b ≤ M)
    (cap : ∀ v : ℤ, -(M:ℤ) ≤ v → v ≤ M → Fits W v)
    (above : base+sourceWords role a b s ≤ output) (room : output+b*(s*s) ≤ M)
    (m : Memory) (sw : m Raster.lim=s) (sr : m src=base) (sa : m short=a) (sb : m count=b) (so : m dst=output) :
    ∃ f ≤ 3+b*((2+s*(1+s*(cellCost role+3)+3))+4), ∃ y, Runs W (packMany role) m f y ∧
      (∀ p<b, ∀ k<s*s, y (output+p*(s*s)+k:ℕ) = entry role a b s p base (k/s) (k%s) m) ∧
      (∀ z : ℕ, z<output ∨ output+b*(s*s) ≤ z → y z=m z) ∧ PacketFrame m y := by
  let K := 2+s*(1+s*(cellCost role+3)+3)
  let I (q : ℕ) (x : Memory) :=
    x packet=q ∧ x dst=(output+q*(s*s):ℕ) ∧ x areaReg=(s*s:ℕ) ∧ x packOne=1 ∧
    PacketFrame m x ∧ (∀ p<q, ∀ k<s*s, x (output+p*(s*s)+k:ℕ)=entry role a b s p base (k/s) (k%s) m) ∧
    ∀ z : ℕ, z<output ∨ output+q*(s*s) ≤ z → x z=m z
  let u := update m areaReg (m Raster.lim*m Raster.lim)
  let v := update u packOne 1
  let w := update v packet (v packet-v packet)
  have init : I 0 w := by
    refine ⟨by simp [w,update],by simpa [w,v,u,update] using so,by simp [w,v,u,update,sw],by simp [w,v,update],?_,by simp,?_⟩
    · intro z _ _ _ _ h₁ h₂ h₃ _
      simp [w,v,u,update,if_neg h₁,if_neg h₂,if_neg h₃]
    · intro z hz
      simp [w,v,u,update,if_neg (by change (z:ℤ)≠ -54; omega : (z:ℤ)≠packet),
        if_neg (by change (z:ℤ)≠ -57; omega : (z:ℤ)≠packOne),if_neg (by change (z:ℤ)≠ -56; omega : (z:ℤ)≠areaReg)]
  have step (p : ℕ) (hp : p<b) (x : Memory) (inv : I p x) :
      ∃ f, f≤K+1 ∧ ∃ y, Runs W (onePacket role) x f y ∧ y packet=p ∧ y packOne=1 ∧ y count=b ∧
      I (p+1) (nextMemory y packet packFlag p b) := by
    obtain ⟨px,dx,ax,ux,fx,prev,remain⟩ := inv
    have get (z : ℤ) (lo : Raster.floor<z) (hi : z<0) (pr : ¬Raster.privateReg z)
        (d : z≠dst) (e : z≠areaReg) (f : z≠packOne) (g : z≠packet) (h : z≠packFlag) := fx z lo hi pr d e f g h
    have X (z : ℤ) (lo : Raster.floor<z) (hi : z<0) (pr : ¬Raster.privateReg z)
        (d : z≠dst) (e : z≠areaReg) (f : z≠packOne) (g : z≠packet) (h : z≠packFlag) := get z lo hi pr d e f g h
    have tileBound := Nat.mul_le_mul_right (s*s) hp
    rw [Nat.succ_mul] at tileBound
    obtain ⟨t,ct,y,ry,fill,fr⟩ := pack_runs (W:=W) role hs ha sm cap (show output+p*(s*s)+s*s ≤ M by omega)
      (fun r hr c hc ok => by have bound := source_bound role hp hr hc ok; omega) x
      ((X _ (by decide) (by decide) (by unfold Raster.privateReg; decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans sw)
      ((X _ (by decide) (by decide) (by unfold Raster.privateReg; decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans sr)
      ((X _ (by decide) (by decide) (by unfold Raster.privateReg; decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans sa)
      ((X _ (by decide) (by decide) (by unfold Raster.privateReg; decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans sb) px dx
    let out := update y dst (y dst+y areaReg)
    let nxt := nextMemory out packet packFlag p b
    have eqO (z : ℤ) (zd : z≠dst) : out z=y z := by simp [out,update,zd]
    have eqN (z : ℤ) (zp : z≠packet) (zf : z≠packFlag) : nxt z=out z := by simp [nxt,nextMemory,update,zp,zf]
    have keep (z : ℕ) : nxt z=y z := (eqN z (by change (z:ℤ)≠ -54; omega) (by change (z:ℤ)≠ -58; omega)).trans
      (eqO z (by change (z:ℤ)≠ -55; omega))
    have dnew : out dst=(output+(p+1)*(s*s):ℕ) := by
      simp [out,update,fr dst (by decide) (by decide) (by unfold Raster.privateReg; decide),
        fr areaReg (by decide) (by decide) (by unfold Raster.privateReg; decide),dx,ax,Nat.succ_mul,add_assoc]
    have yy (z : ℤ) (h₁ : Raster.floor<z) (h₂ : z<0) (h₃ : ¬Raster.privateReg z) (hd : z≠dst) :
        out z=x z := (eqO _ hd).trans (fr _ h₁ h₂ h₃)
    refine ⟨t+1,by omega,out,.seq ry (.atom (.add y dst dst areaReg)),
      (yy _ (by decide) (by decide) (by unfold Raster.privateReg; decide) (by decide)).trans px,
      (yy _ (by decide) (by decide) (by unfold Raster.privateReg; decide) (by decide)).trans ux,
      (yy _ (by decide) (by decide) (by unfold Raster.privateReg; decide) (by decide)).trans
        ((X _ (by decide) (by decide) (by unfold Raster.privateReg; decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans sb),
      by simp [nextMemory,update],(eqN _ (by decide) (by decide)).trans dnew,
      (eqN _ (by decide) (by decide)).trans ((yy _ (by decide) (by decide) (by unfold Raster.privateReg; decide) (by decide)).trans ax),
      (eqN _ (by decide) (by decide)).trans ((yy _ (by decide) (by decide) (by unfold Raster.privateReg; decide) (by decide)).trans ux),?_,?_,?_⟩
    · intro z lo hi pr d e f g h
      exact (eqN _ g h).trans ((yy _ lo hi pr d).trans (fx z lo hi pr d e f g h))
    · intro j hj k hk
      change nxt (output+j*(s*s)+k:ℕ)=_
      rw [keep,fill]
      by_cases same : j=p
      · subst j
        rw [if_pos (by omega),Nat.add_sub_cancel_left]
        apply entry_congr
        intro ok
        have hl : k/s<s := (Nat.div_lt_iff_lt_mul hs).mpr hk
        have bound := source_bound role hp hl (Nat.mod_lt _ hs) ok
        exact remain _ (Or.inl (by omega))
      · have early := Nat.mul_le_mul_right (s*s) (show j+1 ≤ p by omega)
        rw [Nat.succ_mul] at early
        rw [if_neg (by omega)]
        exact prev j (by omega) k hk
    · intro z hz
      change nxt z=_
      rw [keep,fill,if_neg (by rw [Nat.succ_mul] at hz; omega)]
      exact remain z (by rw [Nat.succ_mul] at hz; omega)
  obtain ⟨f,hf,y,run,final⟩ := repeatN_runs hb (onePacket role) (by decide : count≠packet) I
    (fun j hj => cap _ (by omega) (by omega)) step init
  obtain ⟨_,_,_,_,frame,done',remaining⟩ := final
  refine ⟨1+(1+(1+f)),?_,y,.seq (.atom (.mul m areaReg Raster.lim Raster.lim))
    (.seq (.atom (.one u packOne)) (.seq (.atom (.sub v packet packet packet)) run)),done',remaining,frame⟩
  change f ≤ b*((K+1)+3) at hf
  rw [show K+1+3=K+4 by omega] at hf
  change 1+(1+(1+f)) ≤ 3+b*(K+4)
  omega

end VWZClique.IntegerRAM.Projected.Packing
end

/- MMUniform -/
section
namespace VWZClique.BlockMM

theorem depth_bounds {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) :
    n ≤ b^(depth b n) ∧ b^(depth b n) ≤ b*n := by
  refine ⟨(Nat.lt_pow_succ_log_self hb n).le,?_⟩
  rw [depth,pow_succ,Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ (by omega))

noncomputable def padded {I J : Type*} (e : I ↪ J) (A : Square I) : Square J :=
  fun i j => (Function.partialInv e i).elim 0 fun u => (Function.partialInv e j).elim 0 (A u)

theorem padded_product {I J : Type*} [Fintype I] [Fintype J]
    (e : I ↪ J) (A B : Square I) (i j : I) :
    (padded e A * padded e B) (e i) (e j) = (A*B) i j := by
  classical
  simp only [Matrix.mul_apply,padded,Function.partialInv_left e.injective,Option.elim_some]
  let s := Finset.univ.map e
  have hu : s ⊆ Finset.univ := Finset.subset_univ s
  rw [← Finset.sum_subset hu (f := fun k =>
      (Function.partialInv e k).elim 0 (A i) * (Function.partialInv e k).elim 0 (fun u => B u j))
      (by
        intro k _ hk
        cases h : Function.partialInv e k with
        | none => simp
        | some a =>
          exact (hk (by simp [s,← (e.injective.isPartialInv a k).1 h])).elim)]
  simp [s,Function.partialInv_left e.injective]

theorem bound_padding {I J : Type*} (e : I ↪ J) (A : Square I) (U : ℕ)
    (hA : ∀ i j, |A i j| ≤ (U:ℤ)) (u v : J) : |padded e A u v| ≤ (U:ℤ) := by
  cases h : Function.partialInv e u <;> cases k : Function.partialInv e v <;>
    simp [padded,h,k,hA]

private theorem pow_swap (x : ℝ) (hx : 0 ≤ x) (α : ℝ) (h : ℕ) :
    (x^α)^h = (x^h)^α := by
  rw [← Real.rpow_natCast_mul hx, mul_comm, Real.rpow_mul_natCast hx]

end VWZClique.BlockMM
end

/- MMWordLayoutRun -/
section
namespace VWZClique.BlockMM.WordLayout

theorem size_le_space (b r h N : ℕ) : size b h N ≤ space b r h N := by
  cases h <;> simp [space]

end VWZClique.BlockMM.WordLayout
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

private theorem quotient_iterate {W d : ℕ} (num : ℤ) (hn : -4 < num) (hn' : num < 0)
    (hd : 0 < d) (q : ℕ) (hq : 0 < q) (m : IntegerRAM.Memory) (given : m num=((q*d:ℕ):ℤ))
    (kReg : m divK=d) (oneReg : m divOne=1)
    (room : ∀ j : ℕ, j ≤ q*d → Fits W (-(j:ℤ))) :
    ∃ out, Runs W (.repeatWhileNegative (quotientIter num) divTest) m (5*q) out ∧
      out num=0 ∧ out divQ=m divQ+q ∧ ∀ z, z≠num → z≠divQ → z≠divTest → out z=m z := by
  induction q generalizing m with
  | zero => omega
  | succ q ih =>
    let a := update m num (m num-m divK)
    let b := update a divQ (a divQ+a divOne)
    let c := update b divTest (b divTest-b divTest)
    let y := update c divTest (c divTest-c num)
    have exec : Runs W (quotientIter num) m 4 y :=
      Runs.seq (Runs.seq (.atom (.sub m num num divK))
        (Runs.seq (.atom (.add a divQ divQ divOne)) (.atom (.sub b divTest divTest divTest))))
        (.atom (.sub c divTest divTest num))
    have calcN : m num-m divK=((q*d:ℕ):ℤ) := by
      rw [given,kReg,Nat.succ_mul,Int.natCast_add]
      omega
    have newN : y num=((q*d:ℕ):ℤ) := by
      simp [y,c,b,a,update,show num≠divTest by unfold divTest; omega,
        show num≠divQ by unfold divQ; omega,calcN]
    have newQ : y divQ=m divQ+1 := by
      simp [y,c,b,a,update,divTest,divQ,divOne,if_neg (by omega : (-12:ℤ)≠num),
        if_neg (by omega : (-10:ℤ)≠num),show m (-10)=1 from oneReg]
    have test : y divTest= -((q*d:ℕ):ℤ) := by
      simp [y,c,b,a,update,show num≠divTest by unfold divTest; omega,
        show num≠divQ by unfold divQ; omega,calcN]
    have fr (z : ℤ) (hnz : z≠num) (hqz : z≠divQ) (htz : z≠divTest) : y z=m z := by
      simp [y,c,b,a,update,hnz,hqz,htz]
    have small : q*d ≤ (q+1)*d := by rw [Nat.add_mul]; omega
    have fit : Fits W (y divTest) := test ▸ room _ small
    by_cases done : q=0
    · subst q
      exact ⟨y,by simpa using Runs.loop_done exec fit (by simp [test]),by simpa using newN,
        by simpa using newQ,fr⟩
    · have pos : 0 < q*d := Nat.mul_pos (by omega) hd
      obtain ⟨out,more,n',q',f'⟩ := ih (by omega) y newN
        ((fr divK (by unfold divK; omega) (by decide) (by decide)).trans kReg)
        ((fr divOne (by unfold divOne; omega) (by decide) (by decide)).trans oneReg)
        (fun j hj => room j (Nat.le_trans hj small))
      have both := Runs.loop_again exec fit (by rw [test]; omega) more
      refine ⟨out,?_,n',?_,fun z h₁ h₂ h₃ => (f' z h₁ h₂ h₃).trans (fr z h₁ h₂ h₃)⟩
      · simpa [Nat.mul_add,Nat.add_comm,Nat.add_left_comm] using both
      · simp [q',newQ,Int.natCast_succ]; omega

/-- Destructive division by a fixed constant on a positive exact multiple.
Scratch is disjoint from the root-side and caller argument registers. -/
theorem quotient_run {W d q : ℕ} (hd : 0 < d) (hq : 0 < q) (num : ℤ) (hn : -4 < num) (hn' : num < 0)
    (m : IntegerRAM.Memory) (given : m num=((q*d:ℕ):ℤ))
    (room : ∀ j : ℕ, j ≤ q*d → Fits W (-(j:ℤ))) :
    ∃ o, Runs W (quotientCmd d num) m ((Expr.num d).steps+2 + (1+(1+(5*q+4)))) o ∧ o num=q ∧
      ∀ z, floor < z → z≠num → z≠divOne → z≠divK → z≠divQ → z≠divTest → o z=m z := by
  obtain ⟨a,ra,va⟩ := assign_run (W:=W) m (by decide : floor < divK) (Expr.num d) (Expr.num_safe ..)
  let b := update a divOne 1
  let c := update b divQ (b divQ-b divQ)
  have ck : c divK=d := by simp [c,b,update,divK,divQ,divOne,va _ (by decide : floor <  -11),Expr.num_val]
  have c1 : c divOne=1 := by simp [c,b,update,divQ,divOne]
  have cq : c divQ=0 := by simp [c,update]
  have cn : c num=((q*d:ℕ):ℤ) := by
    simp only [c,b,update,if_neg (by unfold divQ; omega : num≠divQ),if_neg (by unfold divOne; omega : num≠divOne),
      va num (by unfold floor; omega),if_neg (by unfold divK; omega : num≠divK),given]
  obtain ⟨y,rr,_,yy,fr⟩ := quotient_iterate num hn hn' hd q hq c cn ck c1 room
  obtain ⟨o,ro,vo⟩ := assign_run y (by unfold floor; omega : floor < num) (.reg divQ)
    (show (Expr.reg divQ).safe floor W y from (by decide : floor < divQ))
  refine ⟨o,Runs.seq ra (Runs.seq (.atom (.one a divOne)) (Runs.seq (.atom (.sub b divQ divQ divQ)) (Runs.seq rr ro))),?_,?_⟩
  · rw [vo _ (by unfold floor; omega),if_pos rfl]; simpa [Expr.val,yy,cq]
  · intro z hz h1 h2 h3 h4 h5
    rw [vo _ hz,if_neg h1,fr _ h1 h4 h5]
    simp only [c,b,update,if_neg h4,if_neg h2,va _ hz,if_neg h3]

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareFlight -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

theorem size_ge {b : ℕ} (hb : 0 < b) (h N : ℕ) (hn : 0 < N) :
    b^h ≤ WordLayout.size b h N ∧ N ≤ WordLayout.size b h N := by
  have a : 1 ≤ b^h := Nat.pow_pos hb
  have c : b^h ≤ b^h*b^h := by simpa using Nat.mul_le_mul_left (b^h) a
  have e : b^h*b^h ≤ N*(b^h*b^h) := by simpa using Nat.mul_le_mul_right (b^h*b^h) hn
  have x := Nat.mul_le_mul_left N (show 1 ≤ b^h*b^h by omega)
  simp only [Nat.mul_one] at x
  unfold WordLayout.size plane
  omega

def DownTrace {b r : ℕ} (S : Scheme b r) (W h : ℕ) (m : IntegerRAM.Memory) (t : ℕ) (x : IntegerRAM.Memory) :=
  if h=0 then t=0 ∧ x=m else Runs W (.repeatWhileNegative (downStep S) flag) m t x

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareSetup -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured

def setupEval : Setup → IntegerRAM.Memory → IntegerRAM.Memory
  | [],m => m
  | (i,e)::xs,m => setupEval xs (update m i (e.val m))
def setupSafe (W : ℕ) : Setup → IntegerRAM.Memory → Prop
  | [],_ => True
  | (i,e)::xs,m => floor < i ∧ e.safe floor W m ∧ setupSafe W xs (update m i (e.val m))

/-- Set several registers, with the ordinary sequential functional meaning on
every observable cell. All temporary writes stay below the scratch boundary. -/
theorem setup_runs {W : ℕ} (l : Setup) (m : IntegerRAM.Memory) (safe : setupSafe W l m) :
    ∃ o, Runs W (setupCode l) m (setupCost l) o ∧ ∀ z, floor < z → o z=setupEval l m z := by
  suffices go : ∀ (x : IntegerRAM.Memory), (∀ z, floor < z → x z=m z) →
      ∃ o, Runs W (setupCode l) x (setupCost l) o ∧ ∀ z, floor < z → o z=setupEval l m z from go m (fun _ _ => rfl)
  induction l generalizing m with
  | nil => exact fun x agree => ⟨x,.skip _,agree⟩
  | cons item xs ih =>
    obtain ⟨i,e⟩ := item
    intro x agree
    obtain ⟨ev,es⟩ := carry (le_refl floor) agree e safe.2.1
    obtain ⟨y,run,write⟩ := assign_run x safe.1 e es
    obtain ⟨o,rest,fr⟩ := ih _ safe.2.2 y (fun z hz => by
      rw [write z hz,ev]; unfold update; split <;> simp_all)
    exact ⟨o,.seq run rest,fr⟩

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeProjectPackBanks -/
section
namespace VWZClique.IntegerRAM.Projected.Large
open Structured SquareCode SquareCode.Layout Packing

structure Shape (m : Memory) (a b s : ℕ) : Prop where
  aEq : m short=a
  bEq : m Packing.count=b
  sEq : m Raster.lim=s

theorem select_run {W a b s : ℕ} (m : Memory) (d : Shape m a b s) (ins outs : ℕ) :
    ∃ o, Runs W (setupCode (select ins outs)) m (setupCost (select ins outs)) o ∧
      o src=m ins ∧ o dst=m outs ∧ o packet=0 ∧ Shape o a b s ∧ ∀ z : ℕ, o z=m z := by
  obtain ⟨o,r,f⟩ := SquareCode.Layout.setup_runs (select ins outs) m (W:=W) (by
    simp [select,setupSafe,Expr.safe,floor] <;> omega)
  have atAny (z : ℤ) (h : floor<z) : o z=update (update (update m src (m ins)) dst (m outs)) packet 0 z := by
    rw [f _ h]
    simp [select,setupEval,Expr.val,update,if_neg (by change (outs:ℤ)≠ -51; omega : (outs:ℤ)≠src)]
  refine ⟨o,r,by simp [atAny src (by decide),update],by simp [atAny dst (by decide),update],
    by simp [atAny packet (by decide),update],⟨by simpa [atAny short (by decide),update] using d.aEq,
    by simpa [atAny Packing.count (by decide),update] using d.bEq,by simpa [atAny Raster.lim (by decide),update] using d.sEq⟩,?_⟩
  intro z; rw [atAny _ (by unfold floor; omega)]
  simp only [update,if_neg (by change (z:ℤ)≠ -54; omega : (z:ℤ)≠packet),
    if_neg (by change (z:ℤ)≠ -55; omega : (z:ℤ)≠dst),if_neg (by change (z:ℤ)≠ -51; omega : (z:ℤ)≠src)]

private theorem Shape.packetFrame {m o : Memory} {a b s : ℕ} (h : Shape m a b s) (f : PacketFrame m o) : Shape o a b s := by
  constructor <;>
    first | exact (f _ (by decide) (by decide) (by unfold Raster.privateReg; decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)).trans h.aEq
          | exact (f _ (by decide) (by decide) (by unfold Raster.privateReg; decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)).trans h.bEq
          | exact (f _ (by decide) (by decide) (by unfold Raster.privateReg; decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)).trans h.sEq

private theorem Shape.rasterFrame {m o : Memory} {a b s : ℕ} (h : Shape m a b s) (f : Raster.saved m o) : Shape o a b s :=
  ⟨(f _ (by decide) (by decide) (by unfold Raster.privateReg; decide)).trans h.aEq,
    (f _ (by decide) (by decide) (by unfold Raster.privateReg; decide)).trans h.bEq,
    (f _ (by decide) (by decide) (by unfold Raster.privateReg; decide)).trans h.sEq⟩

private theorem entry_heap {role : Role} {a b s p bse i j : ℕ} {m x : Memory}
    (he : ∀ z : ℕ, x z=m z) : entry role a b s p bse i j x=entry role a b s p bse i j m := by
  unfold entry; split <;> first | exact he _ | rfl

theorem bank_run {W M a b s source dest : ℕ} (role : Role) (ins outs : ℕ) (m : Memory)
    (d : Shape m a b s) (ia : m ins=source) (ob : m outs=dest)
    (hs : 0<s) (hb : 0<b) (ha : a ≤ s) (sm : s ≤ M) (bm : b ≤ M) (cap : SquareCode.Layout.Room W M)
    (apart : source+sourceWords role a b s ≤ dest) (room : dest+b*(s*s) ≤ M) :
    ∃ t ≤ bankCost role ins outs b s, ∃ o, Runs W (packBank role ins outs) m t o ∧ Shape o a b s ∧
      (∀ p<b, ∀ k<s*s, o (dest+p*(s*s)+k:ℕ)=entry role a b s p source (k/s) (k%s) m) ∧
      ∀ z : ℕ, z<dest ∨ dest+b*(s*s) ≤ z → o z=m z := by
  obtain ⟨x,rx,sc,ds,_,sx,fx⟩ := select_run (W:=W) m d ins outs
  obtain ⟨t,ct,o,ro,values,frame,regs⟩ := packMany_runs role hs hb ha sm bm cap apart room x
    sx.sEq (sc.trans ia) sx.aEq sx.bEq (ds.trans ob)
  exact ⟨_,Nat.add_le_add_left ct _,o,.seq rx ro,sx.packetFrame regs,
    fun p hp k hk => (values p hp k hk).trans (entry_heap fx),fun z hz => (frame z hz).trans (fx _)⟩

theorem weight_run {W M a b s source dest : ℕ} (m : Memory) (d : Shape m a b s)
    (ia : m 371=source) (ob : m 375=dest) (hs : 0<s) (hb : 0<b) (ha : a ≤ s) (sm : s ≤ M)
    (cap : SquareCode.Layout.Room W M) (apart : source+a*a ≤ dest) (room : dest+s*s ≤ M) :
    ∃ t ≤ setupCost (select 371 375)+planeCost .weight s, ∃ o, Runs W packOneW m t o ∧ Shape o a b s ∧
      (∀ k<s*s, o (dest+k:ℕ)=entry .weight a b s 0 source (k/s) (k%s) m) ∧
      ∀ z : ℕ, z<dest ∨ dest+s*s ≤ z → o z=m z := by
  obtain ⟨x,rx,sc,ds,pk,sx,fx⟩ := select_run (W:=W) m d 371 375
  obtain ⟨t,ct,o,ro,values,regs⟩ := pack_runs .weight hs ha sm cap room (fun r hr c hc ok =>
    (Nat.add_lt_add_left (source_bound .weight hb hr hc ok) source).trans_le apart) x sx.sEq (sc.trans ia) sx.aEq sx.bEq pk (ds.trans ob)
  refine ⟨_,Nat.add_le_add_left ct _,o,.seq rx ro,sx.rasterFrame regs,?_,?_⟩
  · intro k hk
    have eq : o (dest+k:ℕ)=entry .weight a b s 0 source (k/s) (k%s) x := by
      simpa [hk,if_pos (by omega : dest ≤ dest+k ∧ dest+k<dest+s*s)] using values (dest+k)
    exact eq.trans (entry_heap fx)
  · intro z hz
    have eq : o z=x z := by simpa [if_neg (by omega : ¬(dest ≤ z ∧ z<dest+s*s))] using values z
    exact eq.trans (fx _)

end VWZClique.IntegerRAM.Projected.Large
end

/- NativeProjectPacked -/
section
namespace VWZClique.IntegerRAM.Projected.Large
open Structured Packing

def Banks.layout (l : Banks) : Projected.Layout := ⟨l.left,l.right,l.output,l.w,l.w⟩

theorem Sources.transfer {a b s} {m o : Memory} {l : Banks} {A B C} (h : Sources (a:=a) (b:=b) (s:=s) m l A B C)
    (bound : l.bound s a b) (same : ∀ z : ℕ, z<l.w → o z=m z) : Sources o l A B C := by
  rcases bound with ⟨w,mid,right,_,_,_⟩
  refine ⟨fun i j => (same _ ?_).trans (h.weight i j),fun i p c => (same _ ?_).trans (h.middle i p c),
    fun p r i => (same _ ?_).trans (h.right p r i)⟩
  · have le := Nat.mul_le_mul_right a i.isLt; rw [Nat.succ_mul] at le
    have := j.isLt; omega
  · have hp := Nat.mul_le_mul_right s p.isLt; rw [Nat.succ_mul] at hp
    have hc := c.isLt
    have inner : p.val*s+c.val < b*s := by omega
    have le := Nat.mul_le_mul_right (b*s) i.isLt; rw [Nat.succ_mul] at le
    omega
  · have hp := Nat.mul_le_mul_right s p.isLt
    rw [Nat.succ_mul] at hp
    have ir := r.isLt; have ii := i.isLt
    have long : p.val*s+r.val < b*s := by omega
    have le := Nat.mul_le_mul_right a long; rw [Nat.succ_mul] at le
    omega

private theorem bankOf {s : ℕ} {m : Memory} {base : ℕ} (tile : Tile s) {f : ℕ → ℕ → ℤ}
    (values : ∀ j<s*s,m (base+j:ℕ)=f (j/s) (j%s)) (correct : ∀ i j : Fin s, f i j=tile i j) :
    bank m base tile := by
  intro j
  obtain ⟨⟨i,k⟩,rfl⟩ := finProdFinEquiv.surjective j
  let v := (finProdFinEquiv (i,k)).val
  have idx : v=s*i.val+k.val := by simp [v,finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
  have hs := Nat.zero_lt_of_lt i.isLt
  have div : v/s=i := by rw [idx,Nat.mul_add_div hs,Nat.div_eq_of_lt k.isLt,Nat.add_zero]
  have md : v%s=k := by rw [idx,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt k.isLt]
  exact (values v (finProdFinEquiv (i,k)).isLt).trans (by simpa [div,md,flat] using correct i k)

private theorem keepBank {s : ℕ} {m o : Memory} {tile : Tile s} {base cutoff : ℕ} (banked : bank m base tile)
    (below : base+s*s ≤ cutoff) (frame : ∀ z : ℕ, z<cutoff → o z=m z) : bank o base tile := by
  intro j
  exact (frame _ (by have := j.isLt; omega)).trans (banked j)

theorem all_runs {W M a b s : ℕ} (m : Memory) (l : Banks) (param : Pointers m l) (d : Shape m a b s)
    (A : Tile a) (B : Matrix (Fin a) (Fin b × Fin s) ℤ) (C : Matrix (Fin b × Fin s) (Fin a) ℤ) (src : Sources m l A B C)
    (hs : 0<s) (hb : 0<b) (ha : a ≤ s) (sm : s ≤ M) (bm : b ≤ M) (cap : SquareCode.Layout.Room W M)
    (bounds : l.bound s a b) (head : 378<l.w) (room : l.output ≤ M) :
    ∃ t ≤ allCost s b, ∃ o, Runs W allPacks m t o ∧ Shape o a b s ∧
      Tables o l.layout (weightTile s A) (midTile B) (rightTile C) ∧ ∀ z : ℕ, z<l.w → o z=m z := by
  have all := bounds
  obtain ⟨wa,lb,rb,wl,lr,rp⟩ := bounds
  have span := Nat.mul_le_mul_right (s*s) hb
  simp only [Nat.one_mul] at span
  obtain ⟨t,ct,x,rx,dx,wt,fx⟩ := weight_run m d param.A param.w hs hb ha sm cap wa (by omega)
  have fx' (z : ℕ) (h : z<l.w) := fx z (Or.inl h)
  have ix (i : ℕ) (hi : i ≤ 378) := fx' i (by omega)
  have sx := src.transfer all fx'
  obtain ⟨u,cu,y,ry,dy,mid,fy⟩ := bank_run .middle 372 376 x dx ((ix _ (by decide)).trans param.B)
    ((ix _ (by decide)).trans param.left) hs hb ha sm bm cap (by change l.B+a*(b*s) ≤ l.left; omega) (by omega)
  have fy' (z : ℕ) (h : z<l.left) := fy z (Or.inl h)
  have fxy (z : ℕ) (h : z<l.w) := (fy' z (by omega)).trans (fx' z h)
  have sy := src.transfer all fxy
  obtain ⟨v,cv,o,ro,do',rhs,fo⟩ := bank_run .right 373 377 y dy ((fxy _ (by omega)).trans param.C)
    ((fxy _ (by omega)).trans param.right) hs hb ha sm bm cap (by change l.C+(b*s)*a ≤ l.right; omega) (by omega)
  have fo' (z : ℕ) (h : z<l.right) := fo z (Or.inl h)
  refine ⟨_,Nat.add_le_add ct (Nat.add_le_add cu cv),o,.seq rx (.seq ry ro),do',⟨?_,?_,?_⟩,
    fun z hz => (fo' z (by omega)).trans (fxy z hz)⟩
  · have weight : bank x l.w (weightTile s A) := bankOf (base:=l.w)
        (f:=fun i j => entry .weight a b s 0 l.A i j m) _ wt (weight_values (s:=s) (p:=0) (b:=b) A m src.weight)
    exact keepBank (keepBank weight wl fy') (by omega : l.w+s*s ≤ l.right) fo'
  · intro p
    have span' := Nat.mul_le_mul_right (s*s) p.isLt
    rw [Nat.succ_mul] at span'
    have by' : bank y (l.left+p.val*(s*s)) (midTile B p) :=
      bankOf (f:=fun i j => entry .middle a b s p.val l.B i j x) _ (mid p p.isLt) (mid_values p B x sx.middle)
    exact keepBank by' (by omega : l.left+p.val*(s*s)+s*s ≤ l.right) fo'
  · intro p
    exact bankOf (base:=l.right+p.val*(s*s)) (f:=fun i j => entry .right a b s p.val l.C i j y) _ (rhs p p.isLt) (right_values p C y sy.right)

end VWZClique.IntegerRAM.Projected.Large
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

/- NativeProjectPacketInit -/
section
namespace VWZClique.IntegerRAM.Projected.Large
open Structured SquareCode SquareCode.Layout BlockMM

theorem scaleSetup_run {b W M a n s : ℕ} (hb : 2 ≤ b) (hs : 1 ≤ s) (sm : b^(depth b s) ≤ M) (c : ℤ)
    (cap : Room W M) (l : Banks) (low : 378<l.temp) (high : l.temp<l.w) (wM : l.w ≤ M)
    (m : Memory) (d : Shape m a n s) (ptr : Pointers m l) :
    ∃ o, Runs W (scaleSetup b c) m (setupCost setSide+((2+depth b s*padSteps b c)+1)) o ∧
      o Cell.side=s ∧ o Packing.count=n ∧ o l.temp=c^(depth b s) ∧
      ∀ z : ℕ, z≠l.temp → o z=m z := by
  obtain ⟨x,rx,fx⟩ := SquareCode.Layout.setup_runs setSide m (W:=W) (by simp [setSide,setupSafe,Expr.safe,floor,nReg])
  have desc (z : ℤ) (lo : floor<z) : x z=update m nReg (s:ℤ) z := by
    rw [fx _ lo]; simp only [setSide,setupEval,Expr.val,d.sEq]
  have capS := (depth_bounds hb hs).1.trans sm
  obtain ⟨y,ry,_,scale,fy⟩ := padding_depth hb hs c x (by simp [desc nReg (by decide),update]) (fun j hj => by
    have mono := Nat.pow_le_pow_right (by omega : 0<b) hj
    have one := Nat.pow_pos (by omega : 0<b) (n:=j)
    exact cap _ (by omega) (by omega))
  have pos (z : ℕ) : y z=m z := (fy z (by unfold floor; omega) (by omega) (by unfold SquareCode.Layout.scaleReg; omega)
    (by unfold paddingTest; omega)).trans ((desc _ (by unfold floor; omega)).trans (if_neg (by unfold nReg; omega)))
  have yptr : y 374=l.temp := (pos 374).trans ptr.temp
  have store := Runs.atom (Step.store (W:=W) y 374 SquareCode.Layout.scaleReg (yptr ▸ cap _ (by omega) (by omega)))
  let out := update y (y 374) (y SquareCode.Layout.scaleReg)
  have yside := (fy nReg (by decide) (by decide) (by decide) (by decide)).trans ((desc nReg (by decide)).trans (if_pos rfl))
  have yc := (fy Packing.count (by decide) (by decide) (by decide) (by decide)).trans
    (((desc Packing.count (by decide)).trans (if_neg (by decide))).trans d.bEq)
  refine ⟨out,.seq rx (.seq ry store),by simpa [out,update,yptr,if_neg (by change (-34:ℤ)≠l.temp; omega : Cell.side≠(l.temp:ℤ))] using (show y Cell.side=(s:ℤ) from yside),
    by simpa [out,update,yptr,if_neg (by change (-53:ℤ)≠l.temp; omega : Packing.count≠(l.temp:ℤ))] using yc,
    by simp [out,update,yptr,scale],?_⟩
  intro z nz
  simpa [out,update,yptr,Int.natCast_inj,nz] using pos z

theorem controls_run {s n W : ℕ} (l : Banks) (m : Memory) (ptr : Pointers m l) (side : m Cell.side=s)
    (packets : m Packing.count=n) :
    ∃ o, Runs W (setupCode controls) m (setupCost controls) o ∧
      Control o l.layout s n 0 0 ∧ ∀ z : ℕ, o z=m z := by
  obtain ⟨o,run,fr⟩ := SquareCode.Layout.setup_runs controls m (W:=W) (by simp [controls,setupSafe,Expr.safe,floor])
  have frame (z : ℕ) : o z=m z := by
    rw [fr _ (by unfold floor; omega)]
    simp only [controls,setupEval,update,Cell.lhs,Cell.rhs,Cell.prod,Cell.wt,Cell.area,Cell.zero,Cell.idx,Cell.one,Cell.lim,Cell.acc]
    simp only [if_neg (by omega : (z:ℤ)≠ -30),if_neg (by omega : (z:ℤ)≠ -31),if_neg (by omega : (z:ℤ)≠ -32),if_neg (by omega : (z:ℤ)≠ -33),if_neg (by omega : (z:ℤ)≠ -35),if_neg (by omega : (z:ℤ)≠ -36),if_neg (by omega : (z:ℤ)≠ -40),if_neg (by omega : (z:ℤ)≠ -41),if_neg (by omega : (z:ℤ)≠ -42),if_neg (by omega : (z:ℤ)≠ -44)]
  refine ⟨o,run,?_,frame⟩
  constructor <;> 
    first | rw [fr Cell.lhs (by decide)] | rw [fr Cell.rhs (by decide)] | rw [fr Cell.prod (by decide)]
          | rw [fr Cell.wt (by decide)] | rw [fr Cell.side (by decide)] | rw [fr Cell.area (by decide)]
          | rw [fr Cell.zero (by decide)] | rw [fr Cell.idx (by decide)] | rw [fr Cell.one (by decide)]
          | rw [fr Cell.lim (by decide)] | rw [fr Cell.acc (by decide)]
  all_goals simp [controls,setupEval,Expr.val,update,Banks.layout,Cell.lhs,Cell.rhs,Cell.prod,Cell.wt,Cell.side,Cell.area,Cell.one,Cell.zero,Cell.idx,Cell.lim,Cell.acc,Packing.count,ptr.output,ptr.w,ptr.left,ptr.right,show m (-34)=(s:ℤ) from side,show m (-53)=(n:ℤ) from packets]

theorem Pointers.keep {m o : Memory} {l : Banks} (ptr : Pointers m l) (same : ∀ z : ℕ, z≤378 → o z=m z) :
    Pointers o l :=
  ⟨(same 371 (by decide)).trans ptr.A,(same 372 (by decide)).trans ptr.B,(same 373 (by decide)).trans ptr.C,
   (same 374 (by decide)).trans ptr.temp,(same 375 (by decide)).trans ptr.w,(same 376 (by decide)).trans ptr.left,
   (same 377 (by decide)).trans ptr.right,(same 378 (by decide)).trans ptr.output⟩

end VWZClique.IntegerRAM.Projected.Large
end

/- NativeProjectPower -/
section
namespace VWZClique.IntegerRAM.Projected.Power
open Structured

def scratch (z : ℤ) := z=pos ∨ z=one ∨ z=flag ∨ z=test

theorem run {W n : ℕ} (base exponent : ℤ) (ne : base≠exponent)
    (bp : ¬scratch base) (ep : ¬scratch exponent) (m : Memory) (hn : m exponent=n)
    (len : Fits W ((n:ℤ)-1)) (guards : ∀ j≤n, Fits W ((j:ℤ)-n)) :
    ∃ f≤5+4*n, ∃ out, Runs W (code base exponent) m f out ∧ out base=((2:ℕ)^n:ℕ) ∧
      ∀ z, z≠base → ¬scratch z → out z=m z := by
  let a := update m base 1
  let b := update a one 1
  let c := update b pos (b pos-b pos)
  let d := update c test (c exponent-c one)
  have fit (z : ℤ) (e : ¬scratch z) : z≠pos ∧ z≠one ∧ z≠flag ∧ z≠test := by
    simpa [scratch,not_or] using e
  have fix (z : ℤ) (nb : z≠base) (ns : ¬scratch z) : d z=m z := by
    obtain ⟨np,no,_,nt⟩ := fit z ns
    simp [d,c,b,a,update,np,no,nt,nb]
  have E : d exponent=n := (fix _ (Ne.symm ne) ep).trans hn
  have B : d base=1 := by
    obtain ⟨np,no,_,nt⟩ := fit base bp
    simp [d,c,b,a,update,np,no,nt]
  have X : d test=(n:ℤ)-1 := by
    obtain ⟨np,no,_,nt⟩ := fit exponent ep
    simp [d,c,b,a,update,np,no,Ne.symm ne,hn]
  have first (s : ℕ) (o : Memory) (r : Runs W (.whenNonnegative test (repeatN (.atom (.add base base base)) pos one exponent flag)) d s o) :
      Runs W (code base exponent) m (1+(1+(1+(1+s)))) o :=
    .seq (.atom (.one ..)) (.seq (.atom (.one ..)) (.seq (.atom (.sub ..)) (.seq (.atom (.sub ..)) r)))
  by_cases hn0 : n=0
  · subst n
    exact ⟨5,by omega,d,first _ _ (.guard_skip (X ▸ len) (by rw [X]; norm_num)),by simpa using B,fix⟩
  let I (j : ℕ) (x : Memory) := x pos=j ∧ x one=1 ∧ x exponent=n ∧ x base=((2:ℕ)^j:ℕ) ∧
    ∀ z, z≠base → ¬scratch z → x z=m z
  have init : I 0 d := ⟨by simp [d,c,update],by simp [d,c,b,update],E,by simpa using B,fix⟩
  have body (j : ℕ) (_ : j<n) (x : Memory) (ok : I j x) :
      ∃ f≤1, ∃ o, Runs W (.atom (.add base base base)) x f o ∧ o pos=j ∧ o one=1 ∧ o exponent=n ∧
        I (j+1) (nextMemory o pos flag j n) := by
    let y := update x base (x base+x base)
    have okp : pos≠base := Ne.symm (fit _ bp).1
    have oko : one≠base := Ne.symm (fit _ bp).2.1
    have yj : y pos=j := by simpa [y,update,okp] using ok.1
    have yo : y one=1 := by simpa [y,update,oko] using ok.2.1
    have ye : y exponent=n := by simpa [y,update,Ne.symm ne] using ok.2.2.1
    refine ⟨1,le_rfl,y,.atom (.add ..),yj,yo,ye,by simp [nextMemory,update],by simpa [nextMemory,update] using yo,?_,?_,?_⟩
    · obtain ⟨np,_,nf,_⟩ := fit _ ep
      simpa [nextMemory,update,np,nf] using ye
    · obtain ⟨np,_,nf,_⟩ := fit _ bp
      simp [nextMemory,update,np,nf,y,ok.2.2.2.1,pow_succ]; ring
    · intro z nb ns
      obtain ⟨np,_,nf,_⟩ := fit _ ns
      simpa [nextMemory,update,np,nf,y,nb] using ok.2.2.2.2 z nb ns
  obtain ⟨s,cs,o,rs,final⟩ := repeatN_runs (by omega : 0<n) _ (fit _ ep).1 I guards body init
  exact ⟨_,by omega,o,first _ _ (.guard_take (X ▸ len) (by rw [X]; omega) rs),final.2.2.2.1,final.2.2.2.2⟩

end VWZClique.IntegerRAM.Projected.Power
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

/-- Every exact multiple recovers its original signed factor. -/
theorem exact_runs {W h M : ℕ} (hh : 0<h) (hM : h≤M) (room : Graph.Division.Room W M)
    {d : ℕ} (hd : 0<d) (z : ℤ) (hz : |z|<(2:ℤ)^h)
    (capacity : (2:ℤ)^h*d≤(M:ℤ)) (m : Memory) (mv : m value=z*d)
    (md : m divisor=d) (mh : m length=h) :
    ∃ f out, f≤13*h+11 ∧ Runs W command m f out ∧ Frame m out ∧ out result=z := by
  have dp : (0:ℤ)<d := by exact_mod_cast hd
  have ab : |m value|=|z| * d := by rw [mv,abs_mul,abs_of_pos dp]
  obtain ⟨f,out,cost,run,fr,answer⟩ := divide_runs hh hM room hd capacity m
    (by rw [ab]; exact mul_lt_mul_of_pos_right hz dp) md mh
  refine ⟨f,out,cost,run,fr,?_⟩
  rw [answer,ab,Int.mul_ediv_cancel _ (ne_of_gt dp),mv]
  by_cases hneg : z<0
  · rw [if_pos (mul_neg_of_neg_of_pos hneg dp),abs_of_neg hneg]; ring
  · rw [if_neg (not_lt_of_ge (mul_nonneg (by omega) dp.le)),abs_of_nonneg (by omega)]; ring

/-- For nonnegative indexing operands the caller obtains both Euclidean outputs.
The two extra instructions reconstruct the remainder from the quotient. -/
def divmod : Command := .seq command
  (.seq (.atom (.mul remn result divisor)) (.atom (.sub remn value remn)))

theorem divmod_runs {W h M : ℕ} (hh : 0<h) (hM : h≤M) (room : Graph.Division.Room W M)
    {a d : ℕ} (hd : 0<d) (bound : (a:ℤ)<(2:ℤ)^h*d) (capacity : (2:ℤ)^h*d≤(M:ℤ))
    (m : Memory) (mv : m value=a) (md : m divisor=d) (mh : m length=h) :
    ∃ f out, f≤13*h+13 ∧ Runs W divmod m f out ∧ Frame m out ∧
      out result=((a/d:ℕ):ℤ) ∧ out remn=((a%d:ℕ):ℤ) := by
  have nonneg : 0 ≤ m value := by rw [mv]; exact Int.natCast_nonneg a
  obtain ⟨f,x,b,run,fr,res⟩ := divide_runs hh hM room hd capacity m
    (by rwa [abs_of_nonneg nonneg,mv]) md mh
  have q : x result=((a/d:ℕ):ℤ) := by
    rw [if_neg (not_lt_of_ge nonneg),abs_of_nonneg nonneg,mv,mul_one] at res
    simpa using res
  have xd := (fr divisor (by decide)).trans md
  have xv := (fr value (by decide)).trans mv
  let y := update x remn (x result*x divisor)
  let out := update y remn (y value-y remn)
  have last : Runs W (.seq (.atom (.mul remn result divisor)) (.atom (.sub remn value remn))) x 2 out :=
    .seq (.atom (.mul ..)) (.atom (.sub ..))
  refine ⟨f+2,out,by omega,.seq run last,frame_trans fr ?_,?_,?_⟩
  · intro j hj
    have ne : j≠remn := by rcases hj with h|h <;> norm_num [signReg,remn] at * <;> omega
    simp [out,y,update,ne]
  · simpa [out,y,update,result,remn] using q
  · have eq : (a:ℤ)=(a/d:ℕ)*(d:ℤ)+(a%d:ℕ) := by
      have hx : (a/d)*d+a%d=a := by rw [Nat.mul_comm (a/d) d,Nat.div_add_mod]
      exact_mod_cast hx.symm
    simp [out,y,update,remn,value,xv,xd,q] at *; omega

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

/- UniformProjectionBudget -/
section
namespace VWZClique.UniformFolds

/-- Every actual basis set fits the selected schedule, including all small lengths. -/
theorem projectionShape_all {L : ℕ} (q : ℕ) (S : Finset (BasisLabel L)) :
    let t := effectiveTile q L S.card
    S.card*2^L ≤ Double.IntegerTiling.side L t ∧
      Double.IntegerTiling.blocks L t * Double.IntegerTiling.side L t = (2^L)^3 := by
  refine ⟨?_,Double.IntegerTiling.exact_shape L _⟩
  unfold effectiveTile
  split
  · assumption
  · have hs : S.card ≤ 4^L := by simpa [BasisLabel] using Finset.card_le_univ S
    calc
      _ ≤ 4^L*2^L := Nat.mul_le_mul_right _ hs
      _ = 2^(3*L) := by rw [show (4:ℕ) = 2^2 by decide,←pow_mul,←pow_add]; congr 1; omega
      _ = _ := by simp [Double.IntegerTiling.side]

end VWZClique.UniformFolds
end

/- NativeProjectShape -/
section
namespace VWZClique.IntegerRAM.Projected.Shape
open Structured SquareCode SquareCode.Layout UniformFolds Double

private theorem quotient_run {W M L : ℕ} (q : ℕ) (cap : Graph.Division.Room W M) (lim : 2^(L+1)*q ≤ M)
    (m : Memory) (given : m WindowInit.Lreg=L) :
    ∃ f≤13*(L+1)+q+17, ∃ x, Runs W (quotient q) m f x ∧ x SignedDivision.result=((L/q:ℕ):ℤ) ∧
      ∀ z : ℤ, SignedDivision.value<z → x z=m z := by
  by_cases z : q=0
  · subst q
    refine ⟨1,by omega,_,.atom (.sub ..),by simp [update],?_⟩
    intro z h; simp only [update,if_neg (by unfold SignedDivision.value SignedDivision.result at *; omega : z≠SignedDivision.result)]
  · obtain ⟨f,x,hf,run,val,fr⟩ := WindowInit.ratio_runs 1 q (by omega) (by omega) cap lim m given
    exact ⟨f,by omega,x,by simpa [quotient,z] using run,by simpa using val,fun z hz => fr z (Or.inl hz)⟩

theorem run {W M L labels : ℕ} (q : ℕ) (cap : Graph.Division.Room W M)
    (lim : 2^(L+1)*q ≤ M) (sizeOK : (2^L)^3+1 ≤ M) (nlabels : labels*2^L ≤ M)
    (clock : 3*L+1 ≤ M) (m : Memory) (N : m 0=((2^L:ℕ):ℤ)) (len : m 320=L) (cnt : m 359=labels) :
    let t := effectiveTile q L labels
    ∃ f ≤ amount q L, ∃ o, Runs W (code q) m f o ∧ o short=((labels*2^L:ℕ):ℤ) ∧
      o side=(IntegerTiling.side L t:ℤ) ∧ o count=(IntegerTiling.blocks L t:ℤ) ∧
      ∀ z : ℕ, o z=m z := by
  dsimp only
  let ns := labels*2^L
  let e := L/q
  let g := 3*L-e
  have he : e ≤ L := Nat.div_le_self _ _
  have hg : g ≤ 3*L := Nat.sub_le .. 
  have subE : e ≤ 3*L := by omega
  have positive : 0 < (2:ℕ)^g := by positivity
  have siM : (2:ℕ)^g < M := (Nat.pow_le_pow_right (by decide) hg).trans_lt (by
    rw [Nat.mul_comm 3 L,pow_mul]; omega)
  have gs (n : ℕ) (hn : n ≤ 3*L) : ∀ j ≤ n, Fits W ((j:ℤ)-n) := fun j hj => cap.fits (by omega) (by omega)
  have lenF (n : ℕ) (hn : n ≤ 3*L) : Fits W ((n:ℤ)-1) := cap.fits (by omega) (by omega)
  obtain ⟨x,rx,fx⟩ := SquareCode.Layout.setup_runs header m (W:=W) (by simp [header,setupSafe,Expr.safe,floor,WindowInit.Lreg,short])
  have xL : x WindowInit.Lreg=L := by simp [fx WindowInit.Lreg (by decide),header,setupEval,update,Expr.val,len]
  have xs : x short=(ns:ℤ) := by simp [fx short (by decide),header,setupEval,update,Expr.val,WindowInit.Lreg,N,cnt,ns]
  have hx (z : ℕ) : x z=m z := by
    rw [fx z (by unfold floor; omega)]
    simp only [header,setupEval,update,if_neg (by change (z:ℤ)≠ -52; omega : (z:ℤ)≠short),
      if_neg (by change (z:ℤ)≠ -12; omega : (z:ℤ)≠WindowInit.Lreg)]
  obtain ⟨f,hf,y,ry,yr,fy⟩ := quotient_run q cap lim x xL
  have hlo (z : ℕ) : y z=m z := (fy _ (by unfold SignedDivision.value; omega)).trans (hx _)
  have ys := (fy short (by decide)).trans xs
  obtain ⟨v,rv,fv⟩ := SquareCode.Layout.setup_runs exponents y (W:=W) (by simp [exponents,setupSafe,Expr.safe,floor,eCount,eSide,SignedDivision.result])
  have vv (z : ℤ) (lo : floor<z) : v z=update (update y eCount (e:ℤ)) eSide (g:ℤ) z := by
    rw [fv z lo]
    have w320 : y 320=(L:ℤ) := (hlo 320).trans len
    simp [exponents,setupEval,Expr.val,update,yr,e,g,eCount,w320,Int.ofNat_sub subE]
  have ve : v eCount=e := by simp [vv eCount (by decide),update]
  have vg : v eSide=g := by simp [vv eSide (by decide),update]
  have vk (z : ℤ) (lo : floor<z) (ne : z≠eCount) (ne' : z≠eSide) : v z=y z := by simp [vv z lo,update,ne,ne']
  obtain ⟨l,hl,a,ra,ab,fa⟩ := Power.run (W:=W) count eCount (by decide) (by unfold Power.scratch; decide)
    (by unfold Power.scratch; decide) v ve (lenF _ subE) (gs _ subE)
  have ag := (fa eSide (by decide) (by unfold Power.scratch; decide)).trans vg
  obtain ⟨s,hs,w,rw',ws,fw⟩ := Power.run (W:=W) side eSide (by decide) (by unfold Power.scratch; decide)
    (by unfold Power.scratch; decide) a ag (lenF _ hg) (gs _ hg)
  have wc := (fw count (by decide) (by unfold Power.scratch; decide)).trans ab
  have wk (z : ℤ) (lo : -52 ≤ z) (ne : z≠side) : w z=y z := by
    exact (fw _ ne (by unfold Power.scratch; dsimp only [Power.pos,Power.one,Power.flag,Power.test]; omega)).trans
      ((fa _ (by change z≠ -53; omega) (by unfold Power.scratch; dsimp only [Power.pos,Power.one,Power.flag,Power.test]; omega)).trans
        (vk _ (by unfold floor; omega) (by change z≠ -61; omega) (by change z≠ -62; omega)))
  have wshort := (wk short (by decide) (by decide)).trans ys
  have wh (z : ℕ) : w z=m z := (wk z (by omega) (by change (z:ℤ)≠ -3; omega)).trans (hlo _)
  obtain ⟨v',rg,fg⟩ := SquareCode.Layout.setup_runs chooseGap w (W:=W) (by simp [chooseGap,setupSafe,Expr.safe,floor,short,side,gap])
  have fg' (z : ℤ) (lo : floor<z) (ne : z≠gap) : v' z=w z := by simp [fg _ lo,chooseGap,setupEval,update,ne]
  have vh (z : ℕ) : v' z=m z := (fg' z (by unfold floor; omega) (by change (z:ℤ)≠ -67; omega)).trans (wh _)
  have vv' : v' gap=(ns:ℤ)-((2^g:ℕ):ℤ)-1 := by simp [fg gap (by decide),chooseGap,setupEval,update,Expr.val,ws,wshort]
  have gfit : Fits W (v' gap) := by
    rw [vv']; apply cap.fits <;> dsimp only [ns] <;> omega
  have chain {o t} (finish : Runs W (.whenNonnegative gap (setupCode fallback)) v' t o) :
      Runs W (code q) m _ o := Runs.seq rx (.seq ry (.seq rv (.seq ra (.seq rw' (.seq rg finish)))))
  by_cases keep : ns ≤ 2^g
  · refine ⟨_,?_,v',chain (.guard_skip gfit (by rw [vv']; omega)),(fg' _ (by decide) (by decide)).trans wshort,?_,?_,vh⟩
    · dsimp [amount]; omega
    · change v' side=((2^(3*L-L/(if ns ≤ 2^g then q else 0)):ℕ):ℤ)
      rw [if_pos keep]; exact (fg' _ (by decide) (by decide)).trans ws
    · change v' count=((2^(L/(if ns ≤ 2^g then q else 0)):ℕ):ℤ)
      rw [if_pos keep]; exact (fg' _ (by decide) (by decide)).trans wc
  · obtain ⟨o,ro,fo⟩ := SquareCode.Layout.setup_runs fallback v' (W:=W) (by simp [fallback,setupSafe,long,Expr.safe,floor,count,side])
    have full : (2^L:ℕ)*(2^L*2^L)=2^(3*L) := by rw [←pow_add,←pow_add]; congr 1; omega
    refine ⟨_,?_,o,chain (.guard_take gfit (by rw [vv']; omega) ro),?_,?_,?_,?_⟩
    · dsimp [amount]; omega
    · simpa [fo short (by decide),fallback,setupEval,update,ns] using (fg' short (by decide) (by decide)).trans wshort
    · change o side=((2^(3*L-L/(if ns ≤ 2^g then q else 0)):ℕ):ℤ)
      have w0 : v' 0=((2^L:ℕ):ℤ) := (vh 0).trans N
      rw [if_neg keep]; simp [fo side (by decide),fallback,setupEval,update,long,Expr.val,w0,←full]
    · change o count=((2^(L/(if ns ≤ 2^g then q else 0)):ℕ):ℤ)
      rw [if_neg keep]; simp [fo count (by decide),fallback,setupEval,update,Expr.val]
    · intro z
      rw [fo _ (by unfold floor; omega)]
      simpa [fallback,setupEval,update,if_neg (by change (z:ℤ)≠ -3; omega : (z:ℤ)≠side),
        if_neg (by change (z:ℤ)≠ -53; omega : (z:ℤ)≠count)] using vh z

end VWZClique.IntegerRAM.Projected.Shape
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

theorem shortTrace {L} (S : Finset (BasisLabel L)) (K q : ℕ) (w : ChannelKey L → ℚ) :
    Matrix.trace (shortWeight S K w * (middle S q w * right S q w)) = numerator S S K K w := by
  change (∑ u, ∑ v, shortWeight S K w u v * ∑ c, middle S q w v c * right S q w c u) =
    ∑ u, ∑ v, leftTable S S K K w u v * ∑ c, midTable S w v c * rightTable S w c u
  apply Fintype.sum_equiv (nodeNumber S).symm
  intro u
  apply Fintype.sum_equiv (nodeNumber S).symm
  intro v
  apply congrArg (leftTable S S K K w _ _ * ·)
  exact Fintype.sum_equiv (blockNumber L q).symm _ _ (fun _ => rfl)

/-- Native evaluation of the projected integer numerator from its three
projected tables. It invokes a square product once per tile; the outer loop,
dot products, and pointer management are generated by one fixed command. -/
theorem native_numerator {L W K C q : ℕ} (S : Finset (BasisLabel L)) (w : ChannelKey L → ℚ)
    (μ : ℤ) (square : Command) (l : Layout) (m : Memory) :
    let t := effectiveTile q L S.card
    let s := IntegerTiling.side L t
    let b := blocks L t
    let A := weightTile s (shortWeight S K w)
    let B := midTile (middle S t w)
    let E := rightTile (right S t w)
    SquareRun W C μ square l A B E → Tables m l A B E → Control m l s b 0 0 →
      (∀ i ≤ b, Fits W ((i:ℤ)-b)) → Fits W ((s*s:ℕ)-1:ℤ) →
      (∀ i < s*s, Fits W ((l.wt+i:ℕ):ℤ) ∧ Fits W ((l.prod+i:ℕ):ℤ)) →
      ∃ f, f ≤ b*(C+8*(s*s)+16) ∧ ∃ out, Runs W (packetLoop square) m f out ∧
        out Cell.acc=μ*numerator S S K K w ∧ (∀ z : ℕ, z < l.preserve → out z=m z) := by
  dsimp only
  intro sq tables ctl guard len addr
  let t := effectiveTile q L S.card
  have hpos : 0 < blocks L t := by unfold blocks; positivity
  obtain ⟨f,time,o,run,result,_,kept⟩ := packet_loop_runs hpos square l _ _ _ sq m tables ctl guard len addr
  refine ⟨f,time,o,run,result.trans ?_,kept⟩
  exact congrArg (μ * ·) ((tile_trace (projectionShape_all q S).1 _ _ _).trans (shortTrace S K t w))

def withDot (mm : ℕ → ℕ) (s : ℕ) := mm s + 8*(s*s)+16

theorem kernel_fits_projection (mm : ℕ → ℕ) (q L a T : ℕ) :
    let e := effectiveTile q L a
    let s := IntegerTiling.side L e
    blocks L e * (mm s + 8*(s*s)+16) ≤ projectionWork (withDot mm) T q L a := by
  let n := 2^L
  let e := effectiveTile q L a
  let s := IntegerTiling.side L e
  have h := Nat.mul_le_mul_left (blocks L e) (Nat.le_add_right (withDot mm s) ((a*n)*(a*n)))
  change blocks L e * withDot mm s ≤ _
  apply h.trans
  dsimp only [projectionWork,Double.budget,n,e,s]
  omega

theorem withDot_rate {ω σ M : ℝ} (hw : 2 ≤ ω) (hσ : 0 ≤ σ) (mm : ℕ → ℕ)
    (hmm : ∀ s : ℕ, 1 ≤ s → (mm s:ℝ) ≤ M*(s:ℝ)^(ω+σ)) :
    ∀ s : ℕ, 1 ≤ s → (withDot mm s:ℝ) ≤ (M+24)*(s:ℝ)^(ω+σ) := by
  intro s hs
  have base : (1:ℝ) ≤ s := by exact_mod_cast hs
  have sq : (s:ℝ)*(s:ℝ) ≤ (s:ℝ)^(ω+σ) := by
    rw [← pow_two,← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le base (by linarith)
  have one : (1:ℝ) ≤ (s:ℝ)^(ω+σ) := Real.one_le_rpow base (by linarith)
  have cost := hmm s hs
  simp only [withDot,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [cost,sq,one]

end VWZClique.IntegerRAM.Projected
end

/- NativeProjectionTileScale -/
section
namespace VWZClique.IntegerRAM.Projected

theorem scaleMat_mul {I J K : Type*} [Fintype J] (a b : ℤ) (A : Matrix I J ℤ) (B : Matrix J K ℤ) :
    scaleMat a A * scaleMat b B = scaleMat (a*b) (A*B) := by
  funext i k
  simp only [scaleMat,Matrix.mul_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _; ring

theorem scaleMat_trace {I : Type*} [Fintype I] (c : ℤ) (A : Matrix I I ℤ) :
    Matrix.trace (scaleMat c A)=c*Matrix.trace A := by simp [Matrix.trace,Matrix.diag,scaleMat,Finset.mul_sum]

end VWZClique.IntegerRAM.Projected
end

/- NativeProjectionScaled -/
section
namespace VWZClique.IntegerRAM.Projected
open Structured UniformFolds TraceDyadic Double Double.IntegerTiling

/-- Denominators from bilinear square schemes are common across all packets
of a given side. The entire contraction has one factor msmall³*mbig, so it
can be normalized with one signed exact division after the last packet. -/
theorem native_scaled_numerator {L W K C q : ℕ} (S : Finset (BasisLabel L)) (w : ChannelKey L → ℚ)
    (msmall mbig : ℤ) (square : Command) (l : Layout) (m : Memory) :
    let t := effectiveTile q L S.card
    let s := IntegerTiling.side L t
    let b := blocks L t
    let A := weightTile s (scaleMat msmall (shortWeight S K w))
    let B := midTile (scaleMat msmall (middle S t w))
    let E := rightTile (scaleMat msmall (right S t w))
    SquareRun W C mbig square l A B E → Tables m l A B E → Control m l s b 0 0 →
      (∀ i ≤ b, Fits W ((i:ℤ)-b)) → Fits W ((s*s:ℕ)-1:ℤ) →
      (∀ i < s*s, Fits W ((l.wt+i:ℕ):ℤ) ∧ Fits W ((l.prod+i:ℕ):ℤ)) →
      ∃ f ≤ b*(C+8*(s*s)+16), ∃ out, Runs W (packetLoop square) m f out ∧
        out Cell.acc=(msmall^3*mbig)*numerator S S K K w ∧ (∀ z : ℕ, z < l.preserve → out z=m z) := by
  dsimp only
  intro sq tables ctl guard len addr
  let t := effectiveTile q L S.card
  have hpos : 0 < blocks L t := by unfold blocks; positivity
  obtain ⟨f,time,o,run,result,_,kept⟩ := packet_loop_runs hpos square l _ _ _ sq m tables ctl guard len addr
  refine ⟨f,time,o,run,result.trans ?_,kept⟩
  rw [tile_trace (projectionShape_all q S).1,scaleMat_mul,scaleMat_mul,scaleMat_trace,shortTrace]
  ring

end VWZClique.IntegerRAM.Projected
end

/- NativeProjectLarge -/
section
namespace VWZClique.IntegerRAM.Projected.Large
open Structured SquareCode SquareCode.Layout BlockMM BlockMM.WordLayout UniformFolds TraceDyadic Double IntegerTiling

private theorem tables_modified_before {m o : IntegerRAM.Memory} {l : Banks} {n a s : ℕ} {A : Tile s} {B C : Fin n → Tile s}
    (tab : Tables m l.layout A B C) (bounds : l.bound s a n) (before : l.temp<l.w)
    (same : ∀ z : ℕ, z≠l.temp → o z=m z) : Tables o l.layout A B C := by
  rcases bounds with ⟨_,_,_,w,left,_⟩
  exact ⟨fun i => (same _ (by dsimp only [Banks.layout]; omega)).trans (tab.weights i),
    fun p i => (same _ (by dsimp only [Banks.layout]; omega)).trans (tab.left p i),
    fun p i => (same _ (by dsimp only [Banks.layout]; omega)).trans (tab.right p i)⟩

/-- From the dense scaled channels, compute the projected trace in the native
accumulator. The only private positive word before the packed tiles is the
now-dead transform word at l.temp. Every earlier address is preserved. -/
theorem verifiedPublicationStep {base rank q W M L : ℕ} (S : Scheme base rank) (hb : 2 ≤ base) (hr : 0<rank)
    (labels : Finset (BasisLabel L)) (w : ChannelKey L → ℚ) (small : ℤ) (K : ℕ)
    (l : Banks) (m : IntegerRAM.Memory) (ptr : Pointers m l)
    (room : Graph.Division.Room W M) (N : m 0=((2^L:ℕ):ℤ)) (len : m 320=L) (card : m 359=labels.card) :
    let shape := effectiveTile q L labels.card
    let s := IntegerTiling.side L shape
    let n := blocks L shape
    let A := scaleMat small (shortWeight labels K w)
    let B := scaleMat small (middle labels shape w)
    let C := scaleMat small (Projected.right labels shape w)
    Limits base rank q L labels.card s n l M → Sources m l A B C →
      ∃ f≤cost q S L s n, ∃ o, Runs W (code q S) m f o ∧
        o Cell.acc=(small^3*S.scale^(depth base s))*numerator labels labels K K w ∧
        o SquareCode.Layout.scaleReg=S.scale^(depth base s) ∧ ∀ z : ℕ, z<l.temp → o z=m z := by
  intro shape s n A B C lim sources
  let lyt := l.layout
  have sv : 0<s := by dsimp [s,IntegerTiling.side]; positivity
  have nc : 0<n := by dsimp [n,blocks]; positivity
  have sizeAll := projectionShape_all q labels
  have shortSide : labels.card*2^L ≤ s := sizeAll.1
  have blocksEq : n*s=(2^L)^3 := sizeAll.2
  have nM : n ≤ M := by
    have e := Nat.mul_le_mul_left n sv
    simp only [Nat.mul_one,blocksEq] at e
    have := lim.side; omega
  have sM : s ≤ M := by
    have e := Nat.mul_le_mul_right s nc
    simp only [Nat.one_mul,blocksEq] at e
    have := lim.side; omega
  have cap : Room W M := fun _ lo hi => room.fits lo hi
  obtain ⟨f,cf,x,one,short,side,count,fx⟩ := Projected.Shape.run q room lim.ratio lim.side lim.short lim.clock m N len card
  have hdr := lim.header
  have temp := lim.temp
  have bounds := lim.banks
  have outBound := lim.workspace
  obtain ⟨p,cp,y,two,yd,tab,fy⟩ := all_runs x l (ptr.keep (fun z _ => fx z)) ⟨short,count,side⟩ A B C
    (sources.transfer bounds (fun z _ => fx z)) sv nc shortSide sM nM cap bounds (by omega) (by omega)
  have yframe (z : ℕ) (hz : z<l.w) : y z=m z := (fy _ hz).trans (fx _)
  have yp := ptr.keep (fun z hz => yframe z (by omega))
  have Dfit : base^(depth base s) ≤ M := by
    have a := (size_ge (b:=base) (by omega) (depth base s) 1 (by decide)).1
    have b := size_le_space base rank (depth base s) 1
    omega
  obtain ⟨z,three,zs,zn,ztemp,fz⟩ := scaleSetup_run hb sv Dfit S.scale cap l hdr temp
    (by have h := bounds.2.2.2; omega) y yd yp
  obtain ⟨v,four,ctl,fv⟩ := controls_run (W:=W) l z (yp.keep (fun j hj => fz j (by omega))) zs zn
  have tv := (tables_modified_before tab bounds temp fz).transfer fv
  obtain ⟨wa,lb,rb,wl,lr,rp⟩ := bounds
  have sq := SquareCaller.square_run (s:=s) (t:=n) S hb hr sv cap lyt (weightTile s A) (midTile B) (rightTile C)
    (by dsimp [lyt,Banks.layout]; omega) (by exact rp) (by dsimp [lyt,Banks.layout]; omega) (by dsimp [lyt,Banks.layout]; omega) outBound
  have guard (j : ℕ) (le : j ≤ n) : Fits W ((j:ℤ)-n) := cap _ (by omega) (by omega)
  have sz : s*s ≤ M := by omega
  have lenFit : Fits W ((s*s:ℕ)-1:ℤ) := cap _ (by omega) (by omega)
  have addresses (i : ℕ) (hi : i<s*s) : Fits W ((l.w+i:ℕ):ℤ) ∧ Fits W ((l.output+i:ℕ):ℤ) :=
    ⟨cap _ (by omega) (by omega),cap _ (by omega) (by omega)⟩
  obtain ⟨j,cj,u,five,num,fu⟩ := native_scaled_numerator (W:=W) (K:=K) (q:=q) labels w small (S.scale^(depth base s))
    (multiply S) lyt v sq tv ctl guard lenFit addresses
  have up (j : ℕ) (hj : j<l.w) : u j=z j := (fu j hj).trans (fv j)
  have ut : u l.temp=S.scale^(depth base s) := (up _ temp).trans ztemp
  have us (j : ℕ) (hj : j<l.temp) : u j=m j := (up _ (by omega)).trans ((fz j (by omega)).trans (yframe j (by omega)))
  have pointer : u 374=l.temp := (us 374 (by omega)).trans ptr.temp
  have load := Runs.atom (Step.load (W:=W) u SquareCode.Layout.scaleReg 374 (pointer ▸ cap _ (by omega) (by omega)))
  refine ⟨_,Nat.add_le_add cf (Nat.add_le_add cp (Nat.add_le_add_left (Nat.add_le_add_left
    (Nat.add_le_add_right cj 1) _) _)),_,.seq one (.seq two (.seq three (.seq four (.seq five load)))),?_,?_,?_⟩
  · simpa [update,SquareCode.Layout.scaleReg] using num
  · simp [update,pointer,ut]
  · intro z hz; simpa [update,if_neg (by unfold SquareCode.Layout.scaleReg; omega : (z:ℤ)≠SquareCode.Layout.scaleReg)] using us z hz

end VWZClique.IntegerRAM.Projected.Large
end

open VWZClique VWZClique.IntegerRAM VWZClique.BlockMM VWZClique.BlockMM.WordLayout VWZClique.IntegerRAM.Structured VWZClique.IntegerRAM.Projected VWZClique.IntegerRAM.SquareCode VWZClique.IntegerRAM.SquareCode.Layout VWZClique.UniformFolds VWZClique.TraceDyadic VWZClique.Double VWZClique.Double.IntegerTiling VWZClique.IntegerRAM.Projected.Large
/-- From the dense scaled channels, compute the projected trace in the native
accumulator. The only private positive word before the packed tiles is the
now-dead transform word at l.temp. Every earlier address is preserved. -/
theorem solution {base rank q W M L : ℕ} (S : Scheme base rank) (hb : 2 ≤ base) (hr : 0<rank)
    (labels : Finset (BasisLabel L)) (w : ChannelKey L → ℚ) (small : ℤ) (K : ℕ)
    (l : Banks) (m : IntegerRAM.Memory) (ptr : Pointers m l)
    (room : VWZClique.IntegerRAM.Graph.Division.Room W M) (N : m 0=((2^L:ℕ):ℤ)) (len : m 320=L) (card : m 359=labels.card) :
    let shape := effectiveTile q L labels.card
    let s := IntegerTiling.side L shape
    let n := blocks L shape
    let A := scaleMat small (shortWeight labels K w)
    let B := scaleMat small (middle labels shape w)
    let C := scaleMat small (Projected.right labels shape w)
    Limits base rank q L labels.card s n l M → Sources m l A B C →
      ∃ f≤cost q S L s n, ∃ o, Runs W (VWZClique.IntegerRAM.Projected.Large.code q S) m f o ∧
        o VWZClique.IntegerRAM.Projected.Cell.acc=(small^3*S.scale^(depth base s))*numerator labels labels K K w ∧
        o VWZClique.IntegerRAM.SquareCode.Layout.scaleReg=S.scale^(depth base s) ∧ ∀ z : ℕ, z<l.temp → o z=m z
  := by apply VWZClique.IntegerRAM.Projected.Large.verifiedPublicationStep <;> assumption
