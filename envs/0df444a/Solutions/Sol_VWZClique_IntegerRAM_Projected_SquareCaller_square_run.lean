-- Prove2me | solution 1 for VWZClique.IntegerRAM.Projected.SquareCaller.square_run
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T14:03:52.311015+00:00
-- url     : https://prove2.me/submissions/9ec6ec54-d2f8-44b6-9497-0885d0186443

import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_VWZClique_Contraction
import Definitions.Def_VWZClique_Count
import Definitions.Def_VWZClique_NativeCliqueCompiler
import Definitions.Def_VWZClique_NativeProjectionContract
import Definitions.Def_VWZClique_Weighted
import Mathlib
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

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

/- CliqueBlockMM -/
section
/-! Fixed integer-coefficient bilinear schemes recursively multiply arbitrary
    tensor powers of their base dimension. Clearing the base coefficients'
    denominators introduces just one fixed scale factor per level. -/

namespace VWZClique.BlockMM
open scoped BigOperators

/-- Apply one coefficient vector to the blocks of a matrix. -/
def collect {I : Type*} {b : ℕ} (L : Square (Fin b)) (A : Square (Fin b × I)) : Square I :=
  fun u v => linear L (fun i j => A (i,u) (j,v))

/-- The scalar scheme is valid with integer matrices as its entries. -/
theorem scheme_blocks {I : Type*} [Fintype I] {b r : ℕ} (S : Scheme b r)
    (A B : Square (Fin b × I)) (i j : Fin b) (u v : I) :
    (∑ s, S.out i j s * (collect (S.left s) A * collect (S.right s) B) u v) =
      S.scale * (A*B) (i,u) (j,v) := by
  calc
    _ = ∑ x : I, ∑ s, S.out i j s *
          (collect (S.left s) A u x * collect (S.right s) B x v) := by
      simp only [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ x : I, S.scale * (∑ q : Fin b, A (i,u) (q,x) * B (q,x) (j,v)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact S.correct (fun p q => A (p,u) (q,x)) (fun p q => B (p,x) (q,v)) i j
    _ = _ := by
      rw [← Finset.mul_sum, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]

/-- Matrix index at recursion depth `h`. -/
def Index (b : ℕ) : ℕ → Type
  | 0 => Unit
  | h+1 => Fin b × Index b h

instance indexFintype (b : ℕ) : (h : ℕ) → Fintype (Index b h)
  | 0 => inferInstanceAs (Fintype Unit)
  | h+1 => @instFintypeProd _ _ (inferInstanceAs (Fintype (Fin b))) (indexFintype b h)

theorem card_index (b h : ℕ) : Fintype.card (Index b h) = b^h := by
  induction h with
  | zero => change Fintype.card Unit = _; simp
  | succ h ih =>
    change Fintype.card (Fin b × Index b h) = _
    simp [ih, pow_succ, Nat.mul_comm]

/-- A fixed recursion on the depth, using exactly the same three coefficient tables at every node. -/
def product {b r : ℕ} (S : Scheme b r) :
    (h : ℕ) → Square (Index b h) → Square (Index b h) → Square (Index b h)
  | 0, A, B => fun i j => A i () * B () j
  | h+1, A, B => fun i j => ∑ s, S.out i.1 j.1 s *
      product S h (collect (S.left s) A) (collect (S.right s) B) i.2 j.2

theorem product_exact {b r : ℕ} (S : Scheme b r) (h : ℕ)
    (A B : Square (Index b h)) (u v : Index b h) :
    product S h A B u v = S.scale^h * (A*B) u v := by
  induction h with
  | zero =>
    change A u () * B () v = S.scale^0 * (∑ j : Unit, A u j * B j v)
    simp
  | succ h ih =>
    obtain ⟨i,u⟩ := u
    obtain ⟨j,v⟩ := v
    change (∑ s, S.out i j s * product S h (collect (S.left s) A) (collect (S.right s) B) u v) = _
    calc
      _ = S.scale^h *
          (∑ s, S.out i j s * (collect (S.left s) A * collect (S.right s) B) u v) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [ih]
        ring
      _ = S.scale^h * (S.scale * (A*B) (i,u) (j,v)) :=
        congrArg (fun z : ℤ => S.scale^h*z) (scheme_blocks (I := Index b h) S A B i j u v)
      _ = _ := by rw [pow_succ]; ring

/-- Scalar budget for the tabulated schedule. A node forms the two sets of
    `r` block combinations and the `b²` output combinations, with at most
    `6rb²` coefficient products/additions per entry of a block. -/
def scalarBudget (b r : ℕ) : ℕ → ℕ
  | 0 => 1
  | h+1 => r*scalarBudget b r h + 6*r*b^2*(b^2)^h

theorem scalarBudget_le {b r : ℕ} (hr : b^2 ≤ r) (h : ℕ) :
    scalarBudget b r h ≤ (1+6*b^2*h)*r^h := by
  induction h with
  | zero => simp [scalarBudget]
  | succ h ih =>
    calc
      _ ≤ r*((1+6*b^2*h)*r^h) + 6*r*b^2*r^h := by
        exact Nat.add_le_add (Nat.mul_le_mul_left _ ih)
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr h))
      _ = _ := by ring

/-- The magnitude of an intermediate block combination. -/
theorem linear_bound {b C U : ℕ} (L A : Square (Fin b))
    (hL : ∀ i j, |L i j| ≤ (C:ℤ)) (hA : ∀ i j, |A i j| ≤ (U:ℤ)) :
    |linear L A| ≤ ((b^2*C*U : ℕ):ℤ) := by
  unfold linear
  calc
    _ ≤ ∑ i, |∑ j, L i j * A i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin b, ∑ _ : Fin b, (C:ℤ)*U := by
      apply Finset.sum_le_sum
      intro i _
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_mul (hL i j) (hA i j) (abs_nonneg _) (by positivity)
    _ = _ := by simp; ring

/-- Every recursive product has polynomially bounded numerators. The displayed
    base of the exponential in the depth depends only on the fixed scheme. -/
theorem product_bound {b r C : ℕ} (S : Scheme b r)
    (hL : ∀ s i j, |S.left s i j| ≤ (C:ℤ))
    (hR : ∀ s i j, |S.right s i j| ≤ (C:ℤ))
    (hO : ∀ i j s, |S.out i j s| ≤ (C:ℤ))
    (h U V : ℕ) (A B : Square (Index b h))
    (hA : ∀ i j, |A i j| ≤ (U:ℤ)) (hB : ∀ i j, |B i j| ≤ (V:ℤ))
    (u v : Index b h) :
    |product S h A B u v| ≤ ((U*V*(r*C*(b^2*C)^2)^h : ℕ):ℤ) := by
  induction h generalizing U V with
  | zero =>
    change |A u () * B () v| ≤ _
    rw [abs_mul]
    simpa using mul_le_mul (hA u ()) (hB () v) (abs_nonneg _) (by positivity)
  | succ h ih =>
    obtain ⟨i,u⟩ := u
    obtain ⟨j,v⟩ := v
    let M := b^2*C
    let γ := r*C*M^2
    have recbound (s : Fin r) :
        |product S h (collect (S.left s) A) (collect (S.right s) B) u v| ≤
          ((M*U*(M*V)*γ^h : ℕ):ℤ) :=
      ih (M*U) (M*V) _ _ (fun p q => linear_bound _ _ (hL s) (fun a a' => hA (a,p) (a',q)))
        (fun p q => linear_bound _ _ (hR s) (fun a a' => hB (a,p) (a',q))) _ _
    change |∑ s, S.out i j s *
      product S h (collect (S.left s) A) (collect (S.right s) B) u v| ≤ _
    calc
      _ ≤ ∑ s, |S.out i j s * product S h (collect (S.left s) A) (collect (S.right s) B) u v| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin r, (C:ℤ)*((M*U*(M*V)*γ^h : ℕ):ℤ) := by
        apply Finset.sum_le_sum
        intro s _
        rw [abs_mul]
        exact mul_le_mul (hO i j s) (recbound s) (abs_nonneg _) (by positivity)
      _ = _ := by simp [γ,M,pow_succ]; ring

/-- For a fixed base and coefficient bound, exponential growth in the recursion
    depth is polynomial in the matrix dimension. -/
theorem depth_power_polynomial {b : ℕ} (hb : 2 ≤ b) (γ h : ℕ) :
    γ^h ≤ (b^h)^γ := by
  have hγ : γ ≤ b^γ := (Nat.lt_two_pow_self (n := γ)).le.trans (Nat.pow_le_pow_left hb _)
  calc
    γ^h ≤ (b^γ)^h := Nat.pow_le_pow_left hγ h
    _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

end VWZClique.BlockMM
end

/- MMUniform -/
section
namespace VWZClique.BlockMM

theorem depth_bounds {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) :
    n ≤ b^(depth b n) ∧ b^(depth b n) ≤ b*n := by
  refine ⟨(Nat.lt_pow_succ_log_self hb n).le,?_⟩
  rw [depth,pow_succ,Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ (by omega))

/-- Positional numbering of the recursively blocked index. -/
def radix (b : ℕ) : (h : ℕ) → Index b h ≃ Fin (b^h)
  | 0 => finOneEquiv.symm
  | h+1 => ((Equiv.prodCongr (Equiv.refl (Fin b)) (radix b h)).trans finProdFinEquiv).trans
      (finCongr (by rw [pow_succ,Nat.mul_comm]))

def includeIndex {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) : Fin n ↪ Index b (depth b n) :=
  (Fin.castLEEmb (depth_bounds hb hn).1).trans (radix b _).symm.toEmbedding

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

/-- Result of applying the one fixed scheme at every node of the uniformly padded recursion. -/
noncomputable def scaled {b r n : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hn : 1 ≤ n)
    (A B : Square (Fin n)) : Square (Fin n) :=
  let e := includeIndex hb hn
  fun i j => product S (depth b n) (padded e A) (padded e B) (e i) (e j)

theorem scaled_exact {b r n : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hn : 1 ≤ n)
    (A B : Square (Fin n)) (i j : Fin n) :
    scaled S hb hn A B i j = S.scale^(depth b n) * (A*B) i j := by
  simp only [scaled,product_exact,padded_product]

theorem scaled_div {b r n : ℕ} (S : Scheme b r) (hs : S.scale ≠ 0)
    (hb : 2 ≤ b) (hn : 1 ≤ n) (A B : Square (Fin n)) (i j : Fin n) :
    scaled S hb hn A B i j / S.scale^(depth b n) = (A*B) i j := by
  rw [scaled_exact,Int.mul_ediv_cancel_left _ (pow_ne_zero _ hs)]

theorem depth_poly {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (γ : ℕ) :
    γ^(depth b n) ≤ (b*n)^γ :=
  (depth_power_polynomial hb _ _).trans (Nat.pow_le_pow_left (depth_bounds hb hn).2 _)

theorem bound_padding {I J : Type*} (e : I ↪ J) (A : Square I) (U : ℕ)
    (hA : ∀ i j, |A i j| ≤ (U:ℤ)) (u v : J) : |padded e A u v| ≤ (U:ℤ) := by
  cases h : Function.partialInv e u <;> cases k : Function.partialInv e v <;>
    simp [padded,h,k,hA]

theorem scaled_bound {b r n : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hn : 1 ≤ n)
    (C U V : ℕ) (hL : ∀ s i j, |S.left s i j| ≤ (C:ℤ))
    (hR : ∀ s i j, |S.right s i j| ≤ (C:ℤ)) (hO : ∀ i j s, |S.out i j s| ≤ (C:ℤ))
    (A B : Square (Fin n)) (hA : ∀ i j, |A i j| ≤ (U:ℤ)) (hB : ∀ i j, |B i j| ≤ (V:ℤ))
    (u v : Fin n) :
    |scaled S hb hn A B u v| ≤ ((U*V*(b*n)^(r*C*(b^2*C)^2) : ℕ):ℤ) := by
  let e := includeIndex hb hn
  apply (product_bound S hL hR hO _ U V _ _ (bound_padding e A U hA) (bound_padding e B V hB)
    (e u) (e v)).trans
  exact_mod_cast Nat.mul_le_mul_left (U*V) (depth_poly hb hn _)

private theorem pow_swap (x : ℝ) (hx : 0 ≤ x) (α : ℝ) (h : ℕ) :
    (x^α)^h = (x^h)^α := by
  rw [← Real.rpow_natCast_mul hx, mul_comm, Real.rpow_mul_natCast hx]

end VWZClique.BlockMM
end

/- MMUniformRadix -/
section
namespace VWZClique.BlockMM

/-- Reject padding positions by comparing their positional index to the original side. -/
def decodeIndex {b h : ℕ} (n : ℕ) (a : Index b h) : Option (Fin n) :=
  if ha : ((radix b h) a).val < n then some ⟨((radix b h) a).val,ha⟩ else none

theorem decodeIndex_eq {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (a : Index b (depth b n)) :
    decodeIndex n a = Function.partialInv (includeIndex hb hn) a := by
  let e := includeIndex hb hn
  have back (x : Fin n) : ((radix b _) (e x)).val = x.val := by simp [e,includeIndex]
  by_cases h : ((radix b _) a).val < n
  · let i : Fin n := ⟨((radix b _) a).val,h⟩
    have he : e i = a := (radix b _).injective (Fin.ext (back i))
    simpa only [decodeIndex,dif_pos h] using ((e.injective.isPartialInv i a).2 he).symm
  · rw [decodeIndex,dif_neg h]
    cases hq : Function.partialInv e a with
    | none => rfl
    | some i =>
      have hh := (e.injective.isPartialInv i a).1 hq
      exact (h (by rw [← hh,back]; exact i.isLt)).elim

def padRadix {b h n : ℕ} (A : Square (Fin n)) : Square (Index b h) :=
  fun i j => (decodeIndex n i).elim 0 fun x => (decodeIndex n j).elim 0 (A x)

/-- Concrete evaluation using recursive radix addresses and bounded integer comparisons. -/
def runRadix {b r n : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hn : 1 ≤ n)
    (A B : Square (Fin n)) (i j : Fin n) : ℤ :=
  product S (depth b n) (padRadix A) (padRadix B) (includeIndex hb hn i) (includeIndex hb hn j)

theorem runRadix_eq {b r n : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hn : 1 ≤ n)
    (A B : Square (Fin n)) (i j : Fin n) : runRadix S hb hn A B i j = scaled S hb hn A B i j := by
  have hpad (M : Square (Fin n)) : padRadix (h := depth b n) M = padded (includeIndex hb hn) M := by
    funext u v
    simp only [padRadix,padded,decodeIndex_eq hb hn]
  simp only [runRadix,scaled,hpad]

theorem runRadix_div {b r n : ℕ} (S : Scheme b r) (hs : S.scale ≠ 0)
    (hb : 2 ≤ b) (hn : 1 ≤ n) (A B : Square (Fin n)) (i j : Fin n) :
    runRadix S hb hn A B i j / S.scale^depth b n = (A*B) i j := by
  rw [runRadix_eq,scaled_div S hs]

end VWZClique.BlockMM
end

/- MMWordLayout -/
section
namespace VWZClique.BlockMM.WordLayout

abbrev Memory := ℕ → ℤ

abbrev Cell (b h N : ℕ) := Fin 3 × Fin N × Index b h × Index b h

def packing (b h N : ℕ) : Cell b h N ≃ Fin (size b h N) :=
  let mat := (Equiv.prodCongr (radix b h) (radix b h)).trans finProdFinEquiv
  let node := (Equiv.prodCongr (Equiv.refl (Fin N)) mat).trans finProdFinEquiv
  (Equiv.prodCongr (Equiv.refl (Fin 3)) node).trans finProdFinEquiv

def addr (base : ℕ) {b h N : ℕ} (x : Cell b h N) := base + ((packing b h N) x).val

theorem address_formula (base : ℕ) {b h N : ℕ} (k : Fin 3) (p : Fin N) (i j : Index b h) :
    addr base (k,p,i,j) = base + ((k.val*N+p.val)*b^h+((radix b h) i).val)*b^h+((radix b h) j).val := by
  change base + (((radix b h) j).val+b^h*((radix b h) i).val+
    (b^h*b^h)*p.val+(N*(b^h*b^h))*k.val) = _
  ring

theorem addr_range (base : ℕ) {b h N : ℕ} (x : Cell b h N) :
    base ≤ addr base x ∧ addr base x < base + size b h N :=
  ⟨Nat.le_add_right _ _, Nat.add_lt_add_left ((packing b h N) x).isLt _⟩

theorem addr_injective (base b h N : ℕ) : Function.Injective (addr (b:=b) (h:=h) (N:=N) base) := by
  intro x y hxy
  exact (packing b h N).injective (Fin.ext (Nat.add_left_cancel hxy))

theorem levels_disjoint {base next b h N b' h' M : ℕ} (hnext : base + size b h N ≤ next)
    (x : Cell b h N) (y : Cell b' h' M) : addr base x < addr next y :=
  ((addr_range base x).2.trans_le hnext).trans_le (addr_range next y).1

/-- Rank-r child slot, with integer number p*r+s and division/remainder inverse. -/
def child {N r : ℕ} (p : Fin N) (s : Fin r) : Fin (N*r) := finProdFinEquiv (p,s)

theorem child_number {N r : ℕ} (p : Fin N) (s : Fin r) : (child p s).val = p.val*r+s.val := by
  change s.val+r*p.val = _
  ring

theorem child_inverse {N r : ℕ} (p : Fin N) (s : Fin r) :
    (finProdFinEquiv.symm (child p s)).1 = p ∧ (finProdFinEquiv.symm (child p s)).2 = s := by
  simp [child]

theorem child_decode {N r : ℕ} (v : Fin (N*r)) :
    ((finProdFinEquiv.symm v).1.val,(finProdFinEquiv.symm v).2.val) = (v.val/r,v.val%r) := rfl

theorem block_number {b h : ℕ} (i : Fin b) (u : Index b h) :
    ((radix b (h+1)) (i,u)).val = i.val*b^h + ((radix b h) u).val := by
  change ((radix b h) u).val+b^h*i.val = _
  ring

def get (m : Memory) (base b h N : ℕ) (k : Fin 3) (p : Fin N) : Square (Index b h) :=
  fun i j => m (addr base (k,p,i,j))

/-- Functional semantics for writing a contiguous level in increasing physical address order. -/
def put (m : Memory) (base b h N : ℕ) (v : Fin 3 → Fin N → Square (Index b h)) : Memory := fun a =>
  if ha : base ≤ a ∧ a < base+size b h N then
    let x := (packing b h N).symm ⟨a-base, by omega⟩
    v x.1 x.2.1 x.2.2.1 x.2.2.2
  else m a

@[simp] theorem get_put (m : Memory) (base b h N : ℕ) (v : Fin 3 → Fin N → Square (Index b h))
    (k : Fin 3) (p : Fin N) (i j : Index b h) :
    get (put m base b h N v) base b h N k p i j = v k p i j := by
  change put m base b h N v (addr base (k,p,i,j)) = _
  rw [put,dif_pos (addr_range base (k,p,i,j))]
  have he : (⟨addr base (k,p,i,j)-base,by have := addr_range base (k,p,i,j); omega⟩ : Fin (size b h N)) =
      (packing b h N) (k,p,i,j) := Fin.ext (Nat.add_sub_cancel_left _ _)
  simp only [he,Equiv.symm_apply_apply]

theorem put_outside (m : Memory) (base b h N : ℕ) (v : Fin 3 → Fin N → Square (Index b h))
    (a : ℕ) (ha : a<base ∨ base+size b h N ≤ a) : put m base b h N v a = m a := by
  exact dif_neg (by omega)

/-- Count each written cell, each coefficient term in either direction, and each leaf scalar multiply. -/
def iterations (b r : ℕ) : (h N : ℕ) → ℕ
  | 0,N => size b 0 N + N
  | h+1,N => size b h (N*r) + 2*plane b h (N*r)*b^2 + iterations b r h (N*r) +
      size b (h+1) N + plane b (h+1) N*r

private theorem square_power (b h : ℕ) : b^h*b^h = (b^2)^h := by rw [←mul_pow,pow_two]
private theorem plane_succ (b h N : ℕ) : plane b (h+1) N = N*b^2*(b^2)^h := by
  rw [plane,square_power,pow_succ]; ring
private theorem plane_eq (b h N : ℕ) : plane b h N = N*(b^2)^h := by rw [plane,square_power]

theorem space_bound {b r : ℕ} (hr : 1 ≤ r) (h N : ℕ) :
    space b r h N ≤ 3*N*scalarBudget b r h := by
  induction h generalizing N with
  | zero => simp [space,size,plane,scalarBudget]
  | succ h ih =>
    simp only [space,size,plane_succ,scalarBudget]
    have hc := Nat.mul_le_mul_right (N*b^2*(b^2)^h) hr
    calc
      _ ≤ 3*(N*b^2*(b^2)^h) + 3*(N*r)*scalarBudget b r h := Nat.add_le_add_left (ih (N*r)) _
      _ ≤ _ := by
        have hz := Nat.zero_le (N*r*b^2*(b^2)^h)
        ring_nf at hc hz ⊢
        omega

theorem iteration_bound {b r : ℕ} (hb : 1≤b) (hr : 1≤r) (h N : ℕ) :
    iterations b r h N ≤ 4*N*scalarBudget b r h := by
  induction h generalizing N with
  | zero => simp [iterations,size,plane,scalarBudget]; omega
  | succ h ih =>
    simp only [iterations,size,plane_succ,plane_eq,scalarBudget]
    have hb2 : 1 ≤ b^2 := Nat.one_le_pow _ _ hb
    have hcost := ih (N*r)
    have hc := Nat.mul_le_mul_right (N*b^2*(b^2)^h) hr
    have hd := Nat.mul_le_mul_right (N*r*(b^2)^h) hb2
    have hz := Nat.zero_le (N*r*b^2*(b^2)^h)
    ring_nf at hcost hc hd hz ⊢
    omega

end VWZClique.BlockMM.WordLayout
end

/- MMWordLayoutRun -/
section
namespace VWZClique.BlockMM.WordLayout

/-- All (parent,rank) children of an entire level receive their two block combinations together. -/
def down {b r : ℕ} (S : Scheme b r) (h N base : ℕ) (m : Memory) : Memory :=
  put m (base+size b (h+1) N) b h (N*r) fun k v =>
    let ps := finProdFinEquiv.symm v
    if k=0 then collect (S.left ps.2) (get m base b (h+1) N 0 ps.1) else
    if k=1 then collect (S.right ps.2) (get m base b (h+1) N 1 ps.1) else 0

theorem down_left {b r : ℕ} (S : Scheme b r) (h N base : ℕ) (m : Memory) (p : Fin N) (s : Fin r) :
    get (down S h N base m) (base+size b (h+1) N) b h (N*r) 0 (child p s) =
      collect (S.left s) (get m base b (h+1) N 0 p) := by
  funext i j
  rw [down,get_put]
  simp [child]

theorem down_right {b r : ℕ} (S : Scheme b r) (h N base : ℕ) (m : Memory) (p : Fin N) (s : Fin r) :
    get (down S h N base m) (base+size b (h+1) N) b h (N*r) 1 (child p s) =
      collect (S.right s) (get m base b (h+1) N 1 p) := by
  funext i j
  rw [down,get_put]
  simp [child]

/-- The exact addresses read to form one left input of a child. -/
theorem down_left_addresses {b r : ℕ} (S : Scheme b r) (h N base : ℕ) (m : Memory)
    (p : Fin N) (s : Fin r) (u v : Index b h) :
    down S h N base m (addr (base+size b (h+1) N) (0,child p s,u,v)) =
      ∑ a : Fin b, ∑ d : Fin b, S.left s a d * m (addr (b:=b) (h:=h+1) base (0,p,(a,u),(d,v))) := by
  exact congrFun (congrFun (down_left S h N base m p s) u) v

def leafValue (b N base : ℕ) (m : Memory) (k : Fin 3) (p : Fin N) : Square (Index b 0) :=
  fun i j => if k=2 then get m base b 0 N 0 p i () * get m base b 0 N 1 p () j else get m base b 0 N k p i j

/-- The last level multiplies two individual integer words at each node. -/
def leaf (b N base : ℕ) (m : Memory) : Memory := put m base b 0 N (leafValue b N base m)

/-- Read the children's result bank and assemble all entries of the parent result bank. -/
def upValue {b r : ℕ} (S : Scheme b r) (h N base : ℕ) (m : Memory) (k : Fin 3) (p : Fin N) :
    Square (Index b (h+1)) := fun i j =>
    if k=2 then ∑ s : Fin r, S.out i.1 j.1 s * get m (base+size b (h+1) N) b h (N*r) 2 (child p s) i.2 j.2
    else get m base b (h+1) N k p i j

def up {b r : ℕ} (S : Scheme b r) (h N base : ℕ) (m : Memory) : Memory :=
  put m base b (h+1) N (upValue S h N base m)

theorem up_addresses {b r : ℕ} (S : Scheme b r) (h N base : ℕ) (m : Memory)
    (p : Fin N) (i j : Fin b) (u v : Index b h) :
    up S h N base m (addr (b:=b) (h:=h+1) base (2,p,(i,u),(j,v))) =
      ∑ s : Fin r, S.out i j s * m (addr (base+size b (h+1) N) (2,child p s,u,v)) := by
  change get (up S h N base m) base b (h+1) N 2 p (i,u) (j,v) = _
  exact get_put m base b (h+1) N (upValue S h N base m) 2 p (i,u) (j,v)

/-- Breadth-first descent and ascent. Each call processes all N nodes of one level. -/
def run {b r : ℕ} (S : Scheme b r) : (h N base : ℕ) → Memory → Memory
  | 0,N,base,m => leaf b N base m
  | h+1,N,base,m => up S h N base
      (run S h (N*r) (base+size b (h+1) N) (down S h N base m))

theorem run_result {b r : ℕ} (S : Scheme b r) (h N base : ℕ) (m : Memory)
    (p : Fin N) (i j : Index b h) :
    get (run S h N base m) base b h N 2 p i j =
      product S h (get m base b h N 0 p) (get m base b h N 1 p) i j := by
  induction h generalizing N base m with
  | zero => rw [run,leaf,get_put,leafValue,if_pos rfl]; rfl
  | succ h ih =>
    rcases i with ⟨i,u⟩
    rcases j with ⟨j,v⟩
    let next := base+size b (h+1) N
    let d := down S h N base m
    let m' := run S h (N*r) next d
    calc
      _ = ∑ s, S.out i j s * get m' next b h (N*r) 2 (child p s) u v := up_addresses S h N base m' p i j u v
      _ = ∑ s, S.out i j s * product S h (collect (S.left s) (get m base b (h+1) N 0 p))
          (collect (S.right s) (get m base b (h+1) N 1 p)) u v := by
        apply Finset.sum_congr rfl
        intro s _
        apply congrArg (S.out i j s * ·)
        have hx := ih (N*r) next d (child p s) u v
        change get m' next b h (N*r) 2 (child p s) u v = _
        exact hx.trans (congrArg₂ (fun A B => product S h A B u v) (down_left S h N base m p s)
          (down_right S h N base m p s))
      _ = _ := rfl

theorem size_le_space (b r h N : ℕ) : size b h N ≤ space b r h N := by
  cases h <;> simp [space]

theorem run_frame {b r : ℕ} (S : Scheme b r) (h N base : ℕ) (m : Memory) (a : ℕ)
    (ha : a<base ∨ base + space b r h N ≤ a) : run S h N base m a = m a := by
  induction h generalizing N base m with
  | zero => rw [run,leaf]; exact put_outside _ _ _ _ _ _ _ (by simpa [space] using ha)
  | succ h ih =>
    rw [space] at ha
    have htail := size_le_space b r h (N*r)
    have hs : a<base ∨ base+size b (h+1) N ≤ a := by omega
    have hchild : a<base+size b (h+1) N ∨ base+size b (h+1) N + space b r h (N*r) ≤ a := by omega
    rw [run,up,put_outside _ _ _ _ _ _ _ hs,ih _ _ _ hchild,down]
    exact put_outside _ _ _ _ _ _ _ (by omega)

def start (base b h : ℕ) (m : Memory) (A B : Square (Index b h)) : Memory :=
  put m base b h 1 fun k _ => if k=0 then A else if k=1 then B else 0

/-- Run the integer array implementation on arbitrary original matrix dimensions with zero padding. -/
def execute {b r n : ℕ} (S : Scheme b r) (base : ℕ) (m : Memory) (A B : Square (Fin n)) : Memory :=
  let h := depth b n
  run S h 1 base (start base b h m (padRadix A) (padRadix B))

theorem execute_exact {b r n : ℕ} (S : Scheme b r) (hb : 2≤b) (hn : 1≤n)
    (base : ℕ) (m : Memory) (A B : Square (Fin n)) (i j : Fin n) :
    execute S base m A B (addr base (2,(0:Fin 1),includeIndex hb hn i,includeIndex hb hn j)) =
      S.scale^(depth b n) * (A*B) i j := by
  let h := depth b n
  let e := includeIndex hb hn
  let init := start base b h m (padRadix A) (padRadix B)
  change get (run S h 1 base init) base b h 1 2 0 (e i) (e j) = _
  rw [run_result]
  have left : get init base b h 1 0 0 = padRadix A := by funext u v; simp [init,start]
  have right : get init base b h 1 1 0 = padRadix B := by funext u v; simp [init,start]
  rw [left,right]
  exact (runRadix_eq S hb hn A B i j).trans (scaled_exact S hb hn A B i j)

end VWZClique.BlockMM.WordLayout
end

/- NativeSquareCell -/
section
namespace VWZClique.IntegerRAM.SquareCode
open Structured
open VWZClique.BlockMM
namespace Layout
open VWZClique.BlockMM.WordLayout

structure Context {b h N : ℕ} (baseVal : ℕ) (p : Fin N) (u v : Index b h)
    (m : IntegerRAM.Memory) : Prop where
  base_eq : m (-1)=baseVal
  nodes_eq : m (-2)=N
  side_eq : m (-3)=b^h
  node_eq : m (-4)=p.val
  row_eq : m (-5)=((radix b h) u).val
  col_eq : m (-6)=((radix b h) v).val

private theorem par_val {b h N baseVal : ℕ} {p : Fin N} {u v : Index b h} {m : IntegerRAM.Memory}
    (c : Context baseVal p u v m) (k : Fin 3) (a d : Fin b) :
    (parentCell k a d).val m = (addr (h:=h+1) baseVal (k,p,(a,u),(d,v)) : ℕ) := by
  rw [address_formula (h:=h+1) baseVal k p (a,u) (d,v),block_number a u,block_number d v,pow_succ]
  simp only [parentCell,atWord,parentSide,num,plus,times,base,nodes,side,node,row,col,Expr.val,
    Expr.num_val,c.base_eq,c.nodes_eq,c.side_eq,c.node_eq,c.row_eq,c.col_eq,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
  ring

private theorem kid_val {b r h N baseVal : ℕ} {p : Fin N} {u v : Index b h} {m : IntegerRAM.Memory}
    (c : Context baseVal p u v m) (k : Fin 3) (s : Fin r) :
    (childCell b r k s).val m = (addr (baseVal+WordLayout.size b (h+1) N) (k,child p s,u,v) : ℕ) := by
  rw [address_formula,child_number]
  simp only [childCell,atWord,parentSide,next,num,plus,times,base,nodes,side,node,row,col,Expr.val,
    Expr.num_val,c.base_eq,c.nodes_eq,c.side_eq,c.node_eq,c.row_eq,c.col_eq,WordLayout.size,plane,pow_succ,
    Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

private theorem par_safe {b : ℕ} (k : Fin 3) (a d : Fin b) (W : ℕ) (m : IntegerRAM.Memory) :
    (parentCell k a d).safe floor W m := by
  simp [parentCell,atWord,parentSide,num,plus,times,base,nodes,side,node,row,col,Expr.safe,floor]
private theorem kid_safe {r : ℕ} (b : ℕ) (k : Fin 3) (s : Fin r) (W : ℕ) (m : IntegerRAM.Memory) :
    (childCell b r k s).safe floor W m := by
  simp [childCell,atWord,parentSide,next,num,plus,times,base,nodes,side,node,row,col,Expr.safe,floor]

theorem sumFin_val (n : ℕ) (f : Fin n → Expr) (m : IntegerRAM.Memory) :
    (sumFin n f).val m = ∑ i, (f i).val m := by
  induction n with
  | zero => simp [sumFin,Expr.val]
  | succ n ih => rw [Fin.sum_univ_succ,sumFin,Expr.val,ih]

theorem sumFin_safe {n : ℕ} (f : Fin n → Expr) {W : ℕ} {m : IntegerRAM.Memory}
    (hf : ∀ i, (f i).safe floor W m) : (sumFin n f).safe floor W m := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨hf 0,ih _ (fun i => hf i.succ)⟩

def natMem (m : IntegerRAM.Memory) : WordLayout.Memory := fun n => m n

theorem downCode_runs {b r h N baseVal W : ℕ} (p : Fin N) (u v : Index b h)
    (m : IntegerRAM.Memory) (c : Context baseVal p u v m) (k : Fin 3) (s : Fin r) (w : Square (Fin b))
    (fitP : ∀ x : Cell b (h+1) N, Fits W (addr baseVal x))
    (fitC : ∀ x : Cell b h (N*r), Fits W (addr (baseVal+WordLayout.size b (h+1) N) x)) :
    ∃ out, Runs W (downCode k s w) m ((childCell b r k s).steps+((downVal k w).steps+1)) out ∧
      ∀ z, floor < z → out z = if z=(addr (baseVal+WordLayout.size b (h+1) N) (k,child p s,u,v):ℕ)
        then collect w (WordLayout.get (natMem m) baseVal b (h+1) N k p) u v else m z := by
  have safe : (downVal k w).safe floor W m := by
    apply sumFin_safe
    intro a
    apply sumFin_safe
    intro d
    refine ⟨Expr.int_safe ..,par_safe _ _ _ _ _,?_,?_⟩
    · rw [par_val c]; unfold floor; omega
    · rw [par_val c]; apply fitP
  have val : (downVal k w).val m = collect w (WordLayout.get (natMem m) baseVal b (h+1) N k p) u v := by
    simp only [downVal,sumFin_val,times,Expr.val,Expr.int_val,par_val c,collect,linear,WordLayout.get,natMem]
  obtain ⟨out,run,correct⟩ := write_run m floor _ _ (kid_safe b k s W m) safe
    (show Fits W ((childCell b r k s).val m) by rw [kid_val c]; apply fitC)
  exact ⟨out,run,fun z hz => by simpa only [kid_val c,val] using correct z hz⟩

theorem upCode_runs {b r h N baseVal W : ℕ} (S : Scheme b r) (p : Fin N) (u v : Index b h)
    (m : IntegerRAM.Memory) (c : Context baseVal p u v m) (a d : Fin b)
    (fitP : ∀ x : Cell b (h+1) N, Fits W (addr baseVal x))
    (fitC : ∀ x : Cell b h (N*r), Fits W (addr (baseVal+WordLayout.size b (h+1) N) x)) :
    ∃ out, Runs W (upCode S a d) m ((parentCell 2 a d).steps+((upVal S a d).steps+1)) out ∧
      ∀ z, floor < z → out z = if z=(addr (h:=h+1) baseVal (2,p,(a,u),(d,v)):ℕ)
        then ∑ s : Fin r, S.out a d s * WordLayout.get (natMem m) (baseVal+WordLayout.size b (h+1) N) b h (N*r) 2 (child p s) u v
        else m z := by
  have safe : (upVal S a d).safe floor W m := by
    apply sumFin_safe
    intro s
    refine ⟨Expr.int_safe ..,kid_safe _ _ _ _ _,?_,?_⟩
    · rw [kid_val c]; unfold floor; omega
    · rw [kid_val c]; apply fitC
  have val : (upVal S a d).val m = ∑ s : Fin r, S.out a d s *
      WordLayout.get (natMem m) (baseVal+WordLayout.size b (h+1) N) b h (N*r) 2 (child p s) u v := by
    simp only [upVal,sumFin_val,times,Expr.val,Expr.int_val,kid_val c,WordLayout.get,natMem]
  obtain ⟨out,run,correct⟩ := write_run m floor _ _ (par_safe 2 a d W m) safe
    (show Fits W ((parentCell 2 a d).val m) by rw [par_val c]; apply fitP)
  exact ⟨out,run,fun z hz => by simpa only [par_val c,val] using correct z hz⟩

end Layout
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

/- NativeSquarePass -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

abbrev Batch (b h N : ℕ) := Fin N × Index b h × Index b h

def unpackPos {b h N : ℕ} (nPos : 0 < N) (dPos : 0 < b^h) (x : Position) : Batch b h N :=
  (⟨x.1%N,Nat.mod_lt _ nPos⟩,(radix b h).symm ⟨x.2.1%(b^h),Nat.mod_lt _ dPos⟩,
    (radix b h).symm ⟨x.2.2%(b^h),Nat.mod_lt _ dPos⟩)

def packPos {b h N : ℕ} (x : Batch b h N) : Position :=
  (x.1.val,((radix b h) x.2.1).val,((radix b h) x.2.2).val)

theorem pack_mem {b h N : ℕ} (x : Batch b h N) : packPos x∈points N (b^h) :=
  (points_mem ..).2 ⟨x.1.isLt,((radix b h) x.2.1).isLt,((radix b h) x.2.2).isLt⟩

theorem unpack_pack {b h N : ℕ} (hn : 0 < N) (hd : 0 < b^h) (x : Batch b h N) :
    unpackPos hn hd (packPos x)=x := by
  rcases x with ⟨p,u,v⟩
  have eq {k : ℕ} (i : Fin k) : (i:ℕ)%k=i := Nat.mod_eq_of_lt i.isLt
  simp [unpackPos,packPos,eq]

theorem pack_unpack {b h N : ℕ} (hn : 0 < N) (hd : 0 < b^h) (x : Position) (hx : x∈points N (b^h)) :
    packPos (unpackPos hn hd x)=x := by
  obtain ⟨hp,hu,hv⟩ := (points_mem ..).1 hx
  simp [unpackPos,packPos,Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt hu,Nat.mod_eq_of_lt hv]

/-- Turn any verified single-cell kernel into one complete pass over nodes and
submatrix indices. The pass may visit cells far apart in physical memory. -/
theorem batch_run {b h N baseVal W B : ℕ} (hn : 0 < N) (hd : 0 < b^h)
    (m : IntegerRAM.Memory) (hb : m (-1)=baseVal) (hN : m (-2)=N) (hD : m (-3)=b^h)
    (guardN : ∀ j : ℕ, j ≤ N → Fits W ((j:ℤ)-N))
    (guardD : ∀ j : ℕ, j ≤ b^h → Fits W ((j:ℤ)-b^h))
    (cmd : Command) (dst : Batch b h N → ℕ) (value : Batch b h N → Heap → ℤ)
    (src : ℕ → Prop) (disj : ∀ t, ¬ src (dst t)) (inj : Function.Injective dst)
    (reads : ∀ t, ∀ x y : Heap, (∀ z, src z → x z=y z) → value t x=value t y)
    (one : ∀ (t : Batch b h N) (x : IntegerRAM.Memory), Context baseVal t.1 t.2.1 t.2.2 x →
      ∃ out, Runs W cmd x B out ∧ ∀ z, floor < z → out z =
        if z=(dst t:ℤ) then value t (heap x) else x z) :
    ∃ steps, steps ≤ gridCost N (b^h) B ∧ ∃ out, Runs W (grid cmd) m steps out ∧
      (∀ t, out (dst t:ℤ)=value t (heap m)) ∧
      (∀ z : ℕ, (∀ t, z≠dst t) → out z=m z) ∧ regs (-4) m out := by
  let dec := unpackPos hn hd
  let dest (x : Position) := dst (dec x)
  let val (x : Position) := value (dec x)
  let f (p u v : ℕ) := scatter dest val (p,u,v)
  have step (p : ℕ) (hp : p < N) (u : ℕ) (hu : u < b^h) (v : ℕ) (hv : v < b^h)
      (x : IntegerRAM.Memory) (root : regs (-4) m x) (h₁ : x (-4)=p) (h₂ : x (-5)=u) (h₃ : x (-6)=v)
      (h7 : x (-7)=1) :
      ∃ t, t ≤ B ∧ ∃ out, Runs W cmd x t out ∧ heap out=f p u v (heap x) ∧ regs (-7) x out ∧ out (-7)=1 := by
    let j : Position := (p,u,v)
    have hc : Context baseVal (dec j).1 (dec j).2.1 (dec j).2.2 x := by
      refine ⟨(root _ (by decide) (by decide)).trans hb,(root _ (by decide) (by decide)).trans hN,
        (root _ (by decide) (by decide)).trans hD,?_,?_,?_⟩
      · simpa [dec,unpackPos,j,Nat.mod_eq_of_lt hp] using h₁
      · simpa [dec,unpackPos,j,Nat.mod_eq_of_lt hu] using h₂
      · simpa [dec,unpackPos,j,Nat.mod_eq_of_lt hv] using h₃
    obtain ⟨out,run,ans⟩ := one (dec j) x hc
    refine ⟨B,le_rfl,out,run,?_,?_,?_⟩
    · funext z
      simpa [f,scatter,heap,dest,val,j] using ans (z:ℤ) (by unfold floor; omega)
    · intro z hlo hhi
      exact (ans z (by unfold floor at *; omega)).trans (if_neg (by omega))
    · exact ((ans (-7) (by decide)).trans (if_neg (by omega))).trans h7
  obtain ⟨steps,estimate,out,run,res,frame,_⟩ := grid_run hn hd m hN hD guardN guardD cmd f step
  have sc := scatter_result (points N (b^h)) (heap m) dest val src
    (fun x _ => disj _) (fun x _ => reads _) (fun x hx y hy eq => by
      have de := inj eq
      exact (pack_unpack hn hd x hx).symm.trans ((congrArg packPos de).trans (pack_unpack hn hd y hy)))
  rw [gridFold_list] at res
  refine ⟨steps,estimate,out,run,?_,?_,frame⟩
  · intro t
    change heap out (dst t) = _
    have answer := sc.1 (packPos t) (pack_mem t)
    simpa only [dest,val,dec,unpack_pack] using (congrFun res (dest (packPos t))).trans answer
  · intro z hz
    exact (congrFun res z).trans (sc.2 z (fun x _ => hz (dec x)))

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareLeaf -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured

private theorem levelAddr_val {baseVal N q : ℕ} {m : IntegerRAM.Memory}
    (hb : m (-1)=baseVal) (hn : m (-2)=N) (hp : m (-4)=q) (k : ℕ) :
    (levelAddr k).val m = ((baseVal+k*N+q:ℕ):ℤ) := by
  simp only [levelAddr,plus,times,num,base,nodes,node,Expr.val,Expr.num_val,hb,hn,hp,Int.natCast_add,Int.natCast_mul]
  omega

private theorem levelAddr_safe (k W : ℕ) (m : IntegerRAM.Memory) : (levelAddr k).safe floor W m := by
  simp [levelAddr,plus,times,num,base,nodes,node,Expr.safe,floor]

theorem leafBody_runs {baseVal N q W : ℕ} (m : IntegerRAM.Memory)
    (hb : m (-1)=baseVal) (hn : m (-2)=N) (hp : m (-4)=q)
    (fit : ∀ k < 3, Fits W ((baseVal+k*N+q:ℕ):ℤ)) :
    ∃ out, Runs W leafBody m leafBodySteps out ∧ ∀ i, floor < i → out i =
      if i=((baseVal+2*N+q:ℕ):ℤ) then m (baseVal+q:ℕ)*m (baseVal+N+q:ℕ) else m i := by
  have addr := levelAddr_val hb hn hp
  have safe (k : ℕ) (hk : k < 3) : (Expr.read (levelAddr k)).safe floor W m := by
    refine ⟨levelAddr_safe ..,?_,?_⟩
    · rw [addr]; unfold floor; omega
    · rw [addr]; exact fit k hk
  obtain ⟨out,h,e⟩ := write_run m floor _ _ (levelAddr_safe 2 W m)
    (show levelProd.safe floor W m from ⟨safe 0 (by decide),safe 1 (by decide)⟩)
    (show Fits W ((levelAddr 2).val m) by rw [addr]; exact fit 2 (by decide))
  refine ⟨out,h,fun i hi => ?_⟩
  simpa [levelProd,times,Expr.val,addr] using e i hi

/-- Value of the sequential output bank after the first q scalar multiplications. -/
def leafPrefix (baseVal N q : ℕ) (m : IntegerRAM.Memory) (z : ℕ) : ℤ :=
  if baseVal+2*N ≤ z ∧ z < baseVal+2*N+q then
    m ((z-2*N:ℕ):ℤ)*m ((z-N:ℕ):ℤ) else m z

theorem leafLayer_runs {baseVal N W : ℕ} (hn : 0 < N) (m : IntegerRAM.Memory)
    (hb : m (-1)=baseVal) (hN : m (-2)=N)
    (fit : ∀ a < baseVal+3*N, Fits W (a:ℤ))
    (guardFit : ∀ q : ℕ, q ≤ N → Fits W ((q:ℤ)-N)) :
    ∃ t, t ≤ 2+N*(leafBodySteps+3) ∧ ∃ out, Runs W leafLayer m t out ∧
      (∀ z : ℕ, out z=leafPrefix baseVal N N m z) ∧
      ∀ z : ℤ, floor < z → z < 0 → z≠ -4 → z≠ -7 → z≠ -8 → out z=m z := by
  let I (q : ℕ) (x : IntegerRAM.Memory) :=
    x (-4)=q ∧ x (-7)=1 ∧ x (-1)=baseVal ∧ x (-2)=N ∧
    (∀ z : ℕ, x z=leafPrefix baseVal N q m z) ∧
    ∀ z : ℤ, floor < z → z < 0 → z≠ -4 → z≠ -7 → z≠ -8 → x z=m z
  let s := update m (-7) 1
  let ini := update s (-4) (s (-4)-s (-4))
  have ih0 : I 0 ini := by
    dsimp [I,ini,s]
    refine ⟨by simp [update],by simp [update],by simpa [update] using hb,by simpa [update] using hN,?_,?_⟩
    · intro z
      have h4 : (z:ℤ) ≠ -4 := by omega
      have h7 : (z:ℤ) ≠ -7 := by omega
      simp [update,h4,h7,leafPrefix] <;> omega
    · intro z _ _ h4 h7 _
      simp [update,h4,h7]
  have action (q : ℕ) (hq : q < N) (x : IntegerRAM.Memory) (ix : I q x) :
      ∃ t, t ≤ leafBodySteps ∧ ∃ out, Runs W leafBody x t out ∧
        out (-4)=q ∧ out (-7)=1 ∧ out (-2)=N ∧ I (q+1) (nextMemory out (-4) (-8) q N) := by
    obtain ⟨idx,one,bv,lim,data,regs⟩ := ix
    obtain ⟨o,run,v⟩ := leafBody_runs x bv lim idx (fun k hk => fit _ (by
      have h : k*N ≤ 2*N := Nat.mul_le_mul_right N (by omega)
      omega))
    have reg (z : ℤ) (hz : floor < z) (hnz : z < 0) : o z=x z := by
      rw [v z hz,if_neg (by omega)]
    have v0 : o (-4)=q := (reg _ (by decide) (by decide)).trans idx
    have v1 : o (-7)=1 := (reg _ (by decide) (by decide)).trans one
    have vN : o (-2)=N := (reg _ (by decide) (by decide)).trans lim
    refine ⟨_,Nat.le_refl _,o,run,v0,v1,vN,?_,?_,?_,?_,?_,?_⟩
    · simp [nextMemory,update]
    · simpa [nextMemory,update] using v1
    · simpa [nextMemory,update] using (reg _ (by decide : floor <  -1) (by decide)).trans bv
    · simpa [nextMemory,update] using vN
    · intro z
      have h4 : (z:ℤ) ≠ -4 := by omega
      have h8 : (z:ℤ) ≠ -8 := by omega
      simp only [nextMemory,update,if_neg h8,if_neg h4]
      rw [v z (by unfold floor; omega)]
      by_cases hz : z=baseVal+2*N+q
      · subst z
        rw [if_pos rfl,data,data]
        simp only [leafPrefix]
        rw [if_neg (by omega),if_neg (by omega),if_pos (by omega)]
        rw [show baseVal+2*N+q-2*N=baseVal+q by omega,show baseVal+2*N+q-N=baseVal+N+q by omega]
      · rw [if_neg (by omega),data]
        unfold leafPrefix
        have eq : (baseVal+2*N ≤ z ∧ z < baseVal+2*N+q) ↔ (baseVal+2*N ≤ z ∧ z < baseVal+2*N+(q+1)) := by omega
        simp [eq]
    · intro z lo hi h4 h7 h8
      simp only [nextMemory,update,if_neg h8,if_neg h4,reg z lo hi,regs z lo hi h4 h7 h8]
  obtain ⟨t,ht,o,run,done'⟩ := repeatN_runs hn leafBody (by decide : (-2:ℤ)≠ -4) I guardFit action ih0
  refine ⟨1+(1+t),by omega,o,Runs.seq (.atom (.one m (-7))) (Runs.seq (.atom (.sub s (-4) (-4) (-4))) run),done'.2.2.2.2.1,done'.2.2.2.2.2⟩

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareLayer -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

def downDst {b h N r : ℕ} (baseVal : ℕ) (k : Fin 3) (s : Fin r) (t : Batch b h N) :=
  addr (baseVal+WordLayout.size b (h+1) N) (k,child t.1 s,t.2.1,t.2.2)

def downResult {b h N : ℕ} (baseVal : ℕ) (k : Fin 3) (w : Square (Fin b)) (t : Batch b h N) (H : Heap) :=
  collect w (WordLayout.get H baseVal b (h+1) N k t.1) t.2.1 t.2.2

private theorem down_inj {b h N r : ℕ} (baseVal : ℕ) (k : Fin 3) (s : Fin r) :
    Function.Injective (downDst (b:=b) (h:=h) (N:=N) baseVal k s) := by
  rintro ⟨p,u,v⟩ ⟨p',u',v'⟩ eq
  obtain eq := addr_injective _ _ _ _ eq
  change (k,child p s,u,v)=(k,child p' s,u',v') at eq
  have hc := congrArg (fun x : Cell b h (N*r) => x.2.1) eq
  have ep := congrArg (fun i : Fin (N*r) => (finProdFinEquiv.symm i).1) hc
  simp [child] at ep
  exact Prod.ext ep (congrArg (fun x : Cell b h (N*r) => x.2.2) eq)

theorem down_pass {b r h N baseVal W : ℕ} (hn : 0 < N) (hd : 0 < b^h)
    (m : IntegerRAM.Memory) (hb : m (-1)=baseVal) (hN : m (-2)=N) (hD : m (-3)=b^h)
    (guardN : ∀ j : ℕ, j ≤ N → Fits W ((j:ℤ)-N))
    (guardD : ∀ j : ℕ, j ≤ b^h → Fits W ((j:ℤ)-b^h))
    (fitP : ∀ x : Cell b (h+1) N, Fits W (addr baseVal x))
    (fitC : ∀ x : Cell b h (N*r), Fits W (addr (baseVal+WordLayout.size b (h+1) N) x))
    (k : Fin 3) (s : Fin r) (w : Square (Fin b)) :
    ∃ steps, steps ≤ gridCost N (b^h) ((childCell b r k s).steps+((downVal k w).steps+1)) ∧
      ∃ out, Runs W (grid (downCode k s w)) m steps out ∧
        (∀ t : Batch b h N, out (downDst baseVal k s t : ℤ)=downResult baseVal k w t (heap m)) ∧
        (∀ z : ℕ, (∀ t : Batch b h N, z≠downDst baseVal k s t) → out z=m z) ∧ regs (-4) m out := by
  apply batch_run hn hd m hb hN hD guardN guardD _ _ _ (fun z => z < baseVal+WordLayout.size b (h+1) N)
  · intro t
    exact Nat.not_lt.mpr (addr_range _ _).1
  · exact down_inj _ _ _
  · intro t x y he
    have vals : WordLayout.get x baseVal b (h+1) N k t.1=WordLayout.get y baseVal b (h+1) N k t.1 := by
      funext i j
      exact he _ (addr_range _ _).2
    simp only [downResult,vals]
  · intro t x cx
    exact downCode_runs t.1 t.2.1 t.2.2 x cx k s w fitP fitC

def upDst {b h N : ℕ} (baseVal : ℕ) (a d : Fin b) (t : Batch b h N) :=
  addr (b:=b) (h:=h+1) baseVal (2,t.1,(a,t.2.1),(d,t.2.2))

def upResult {b r h N : ℕ} (baseVal : ℕ) (S : Scheme b r) (a d : Fin b) (t : Batch b h N) (H : Heap) :=
  ∑ s : Fin r, S.out a d s * WordLayout.get H (baseVal+WordLayout.size b (h+1) N) b h (N*r) 2 (child t.1 s) t.2.1 t.2.2

private theorem up_inj {b h N : ℕ} (baseVal : ℕ) (a d : Fin b) :
    Function.Injective (upDst (h:=h) (N:=N) baseVal a d) := by
  rintro ⟨p,u,v⟩ ⟨p',u',v'⟩ eq
  obtain he := addr_injective _ _ _ _ eq
  exact congrArg (fun x : Cell b (h+1) N => (x.2.1,x.2.2.1.2,x.2.2.2.2)) he

theorem up_pass {b r h N baseVal W : ℕ} (hn : 0 < N) (hd : 0 < b^h)
    (m : IntegerRAM.Memory) (hb : m (-1)=baseVal) (hN : m (-2)=N) (hD : m (-3)=b^h)
    (guardN : ∀ j : ℕ, j ≤ N → Fits W ((j:ℤ)-N))
    (guardD : ∀ j : ℕ, j ≤ b^h → Fits W ((j:ℤ)-b^h))
    (fitP : ∀ x : Cell b (h+1) N, Fits W (addr baseVal x))
    (fitC : ∀ x : Cell b h (N*r), Fits W (addr (baseVal+WordLayout.size b (h+1) N) x))
    (S : Scheme b r) (a d : Fin b) :
    ∃ steps, steps ≤ gridCost N (b^h) ((parentCell 2 a d).steps+((upVal S a d).steps+1)) ∧
      ∃ out, Runs W (grid (upCode S a d)) m steps out ∧
        (∀ t : Batch b h N, out (upDst baseVal a d t : ℤ)=upResult baseVal S a d t (heap m)) ∧
        (∀ z : ℕ, (∀ t : Batch b h N, z≠upDst baseVal a d t) → out z=m z) ∧ regs (-4) m out := by
  apply batch_run hn hd m hb hN hD guardN guardD _ _ _ (fun z => baseVal+WordLayout.size b (h+1) N ≤ z)
  · intro t
    exact Nat.not_le.mpr (addr_range _ _).2
  · exact up_inj _ _ _
  · intro t x y he
    apply Finset.sum_congr rfl
    intro s _
    exact congrArg (S.out a d s * ·) (he _ (addr_range _ _).1)
  · intro t x cx
    exact upCode_runs S t.1 t.2.1 t.2.2 x cx a d fitP fitC

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareCatalog -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

@[simp] theorem mem_all {I : Type*} [Fintype I] (j : I) : j∈all I := by simp [all]

theorem run_many {I : Type*} (W : ℕ) (l : List I) (cmd : I → Command) (cost : I → ℕ)
    (P : IntegerRAM.Memory → Prop) (target : Heap) (hit : I → ℕ → Prop)
    (pass : ∀ j∈l, ∀ x, P x → ∃ t, t ≤ cost j ∧ ∃ out, Runs W (cmd j) x t out ∧ P out ∧
      (∀ z : ℕ, hit j z → out z=target z) ∧ (∀ z : ℕ, ¬hit j z → out z=x z))
    (m : IntegerRAM.Memory) (good : P m) :
    ∃ t, t ≤ (l.map cost).sum ∧ ∃ out, Runs W (codes cmd l) m t out ∧ P out ∧
      (∀ z : ℕ, (∃ j∈l, hit j z) → out z=target z) ∧
      (∀ z : ℕ, (∀ j∈l, ¬hit j z) → out z=m z) := by
  induction l generalizing m with
  | nil => exact ⟨0,by simp,m,.skip _,good,by simp,by simp⟩
  | cons j js ih =>
    obtain ⟨t,ct,x,r₁,g,h,miss⟩ := pass j (by simp) m good
    obtain ⟨s,cs,o,r₂,g',h',miss'⟩ := ih (fun i hi => pass i (List.mem_cons_of_mem _ hi)) x g
    refine ⟨t+s,by simpa using Nat.add_le_add ct cs,o,.seq r₁ r₂,g',?_,?_⟩
    · intro z hz
      by_cases found : ∃ i∈js, hit i z
      · exact h' z found
      · obtain ⟨i,hi,ok⟩ := hz
        obtain eq|rest := List.mem_cons.mp hi
        · subst i
          exact (miss' z (fun i hi hh => found ⟨i,hi,hh⟩)).trans (h z ok)
        · exact False.elim <| found ⟨i,rest,ok⟩
    · intro z avoid
      exact (miss' z (fun i hi => avoid i (List.mem_cons_of_mem _ hi))).trans (miss z (avoid j (by simp)))

theorem grid_cost_bound {N D : ℕ} (hn : 1 ≤ N) (hd : 1 ≤ D) (B : ℕ) :
    gridCost N D B ≤ (B+15)*(N*D*D) := by
  have hD : N ≤ N*D := by simpa using Nat.mul_le_mul_left N hd
  have hD' : N*D ≤ N*D*D := by simpa using Nat.mul_le_mul_left (N*D) hd
  unfold gridCost
  ring_nf at hD hD' ⊢
  omega

def lowOK (baseVal N D : ℕ) (m : IntegerRAM.Memory) :=
  m (-1)=baseVal ∧ m (-2)=N ∧ m (-3)=D

private theorem lowOK_kept {baseVal N D : ℕ} {x y : IntegerRAM.Memory} (hx : lowOK baseVal N D x)
    (fr : regs (-4) x y) : lowOK baseVal N D y :=
  ⟨(fr _ (by decide) (by decide)).trans hx.1,(fr _ (by decide) (by decide)).trans hx.2.1,
    (fr _ (by decide) (by decide)).trans hx.2.2⟩

private theorem down_get {b r h N baseVal : ℕ} (S : Scheme b r) (H : Heap)
    (j : Fin 3 × Fin r) (t : Batch b h N) :
    down S h N baseVal H (downDst baseVal j.1 j.2 t) = downResult baseVal j.1 (weightDown S j) t H := by
  change WordLayout.get (down S h N baseVal H) _ _ _ _ _ _ _ _ = _
  rw [down,get_put]
  by_cases e : j.1=0
  · simp [e,child,downResult,weightDown]
  by_cases e' : j.1=1
  · simp [e,e',child,downResult,weightDown]
  · simp [e,e',downResult,weightDown,collect,linear]

theorem downLevel_run {b r h N baseVal W : ℕ} (S : Scheme b r) (hn : 0 < N) (hd : 0 < b^h)
    (m : IntegerRAM.Memory) (ready : lowOK baseVal N (b^h) m)
    (gN : ∀ j : ℕ, j ≤ N → Fits W ((j:ℤ)-N)) (gD : ∀ j : ℕ, j ≤ b^h → Fits W ((j:ℤ)-b^h))
    (fp : ∀ x : Cell b (h+1) N, Fits W (addr baseVal x))
    (fc : ∀ x : Cell b h (N*r), Fits W (addr (baseVal+WordLayout.size b (h+1) N) x)) :
    ∃ t, t ≤ ((all (Fin 3 × Fin r)).map (fun j => gridCost N (b^h) (downBatchCost S j))).sum ∧
      ∃ o, Runs W (downLevel S) m t o ∧ lowOK baseVal N (b^h) o ∧ regs (-4) m o ∧ heap o=down S h N baseVal (heap m) := by
  let next := baseVal+WordLayout.size b (h+1) N
  let P (x : IntegerRAM.Memory) := lowOK baseVal N (b^h) x ∧ regs (-4) m x ∧ ∀ z : ℕ, z < next → x z=m z
  let hit (j : Fin 3 × Fin r) (z : ℕ) := ∃ t : Batch b h N, z=downDst baseVal j.1 j.2 t
  let target := down S h N baseVal (heap m)
  have pass (j : Fin 3 × Fin r) (_ : j∈all _) (x : IntegerRAM.Memory) (px : P x) :
      ∃ t, t ≤ gridCost N (b^h) (downBatchCost S j) ∧ ∃ o, Runs W (downBatchCode S j) x t o ∧ P o ∧
        (∀ z : ℕ, hit j z → o z=target z) ∧ (∀ z : ℕ, ¬hit j z → o z=x z) := by
    obtain ⟨t,ht,o,run,values,miss,fr⟩ := down_pass hn hd x px.1.1 px.1.2.1 px.1.2.2 gN gD fp fc
      j.1 j.2 (weightDown S j)
    refine ⟨t,ht,o,run,⟨lowOK_kept px.1 fr,(fun z h h' => (fr z h h').trans (px.2.1 z h h')),?_⟩,?_,?_⟩
    · intro z hz
      apply (miss z _).trans (px.2.2 z hz)
      intro a eq
      have lower : next ≤ downDst baseVal j.1 j.2 a := (addr_range _ _).1
      omega
    · rintro _ ⟨a,rfl⟩
      rw [values]
      change _=down S h N baseVal (heap m) (downDst baseVal j.1 j.2 a)
      rw [down_get]
      have eq : WordLayout.get (heap x) baseVal b (h+1) N j.1 a.1=WordLayout.get (heap m) baseVal b (h+1) N j.1 a.1 := by
        funext z z'
        exact px.2.2 _ (addr_range _ _).2
      simp only [downResult,eq]
    · exact fun z hz => miss z (fun a eq => hz ⟨a,eq⟩)
  obtain ⟨s,hs,o,run,good,values,miss⟩ := run_many W _ _ _ P target hit pass m ⟨ready,(fun _ _ _ => rfl),fun _ _ => rfl⟩
  refine ⟨s,hs,o,run,good.1,good.2.1,?_⟩
  funext z
  by_cases inside : next ≤ z ∧ z < next+WordLayout.size b h (N*r)
  · let i : Fin (WordLayout.size b h (N*r)) := ⟨z-next,by omega⟩
    obtain ⟨⟨k,v,u,v'⟩,e⟩ := (packing b h (N*r)).surjective i
    obtain ⟨⟨p,a⟩,rfl⟩ := finProdFinEquiv.surjective v
    apply values
    refine ⟨(k,a),mem_all _,(p,u,v'),?_⟩
    have he := congrArg Fin.val e
    change _ = z-next at he
    change z=next+((packing b h (N*r)) (k,finProdFinEquiv (p,a),u,v')).val
    omega
  · have outside : z < next ∨ next+WordLayout.size b h (N*r) ≤ z := by omega
    have e : target z=m z := put_outside _ _ _ _ _ _ _ outside
    apply (miss z _).trans e.symm
    rintro j _ ⟨a,rfl⟩
    exact inside (addr_range _ _)

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareAscent -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

theorem upLevel_run {b r h N baseVal W : ℕ} (S : Scheme b r) (hn : 0 < N) (hd : 0 < b^h)
    (m : IntegerRAM.Memory) (ready : lowOK baseVal N (b^h) m)
    (gN : ∀ j : ℕ, j ≤ N → Fits W ((j:ℤ)-N)) (gD : ∀ j : ℕ, j ≤ b^h → Fits W ((j:ℤ)-b^h))
    (fp : ∀ x : Cell b (h+1) N, Fits W (addr baseVal x))
    (fc : ∀ x : Cell b h (N*r), Fits W (addr (baseVal+WordLayout.size b (h+1) N) x)) :
    ∃ t, t ≤ ((all (Fin b × Fin b)).map (fun j => gridCost N (b^h) (upBatchCost S j))).sum ∧
      ∃ o, Runs W (upLevel S) m t o ∧ lowOK baseVal N (b^h) o ∧ regs (-4) m o ∧ heap o=up S h N baseVal (heap m) := by
  let next := baseVal+WordLayout.size b (h+1) N
  let P (x : IntegerRAM.Memory) := lowOK baseVal N (b^h) x ∧ regs (-4) m x ∧ ∀ z : ℕ, next ≤ z → x z=m z
  let hit (j : Fin b × Fin b) (z : ℕ) := ∃ t : Batch b h N, z=upDst baseVal j.1 j.2 t
  let target := up S h N baseVal (heap m)
  have pass (j : Fin b × Fin b) (_ : j∈all _) (x : IntegerRAM.Memory) (px : P x) :
      ∃ t, t ≤ gridCost N (b^h) (upBatchCost S j) ∧ ∃ o, Runs W (upBatchCode S j) x t o ∧ P o ∧
        (∀ z : ℕ, hit j z → o z=target z) ∧ (∀ z : ℕ, ¬hit j z → o z=x z) := by
    obtain ⟨t,ht,o,run,values,miss,fr⟩ := up_pass hn hd x px.1.1 px.1.2.1 px.1.2.2 gN gD fp fc S j.1 j.2
    refine ⟨t,ht,o,run,⟨⟨(fr _ (by decide) (by decide)).trans px.1.1,
      (fr _ (by decide) (by decide)).trans px.1.2.1,(fr _ (by decide) (by decide)).trans px.1.2.2⟩,(fun z h h' => (fr z h h').trans (px.2.1 z h h')),?_⟩,?_,?_⟩
    · intro z hz
      apply (miss z _).trans (px.2.2 z hz)
      intro a eq
      have lt : upDst baseVal j.1 j.2 a < next := (addr_range _ _).2
      omega
    · rintro _ ⟨a,rfl⟩
      rw [values]
      change _=up S h N baseVal (heap m) (addr (h:=h+1) baseVal (2,a.1,(j.1,a.2.1),(j.2,a.2.2)))
      rw [up_addresses]
      apply Finset.sum_congr rfl
      intro s _
      exact congrArg (S.out j.1 j.2 s * ·) (px.2.2 _ (addr_range _ _).1)
    · exact fun z hz => miss z (fun a eq => hz ⟨a,eq⟩)
  obtain ⟨s,hs,o,run,good,values,miss⟩ := run_many W _ _ _ P target hit pass m ⟨ready,(fun _ _ _ => rfl),fun _ _ => rfl⟩
  refine ⟨s,hs,o,run,good.1,good.2.1,?_⟩
  funext z
  by_cases hitZ : ∃ j∈all _, hit j z
  · exact values z hitZ
  have unchanged : o z=m z := miss _ (fun j hj h => hitZ ⟨j,hj,h⟩)
  apply unchanged.trans
  symm
  by_cases inside : baseVal ≤ z ∧ z < next
  · let f : Fin (WordLayout.size b (h+1) N) := ⟨z-baseVal,by dsimp [next] at inside; omega⟩
    obtain ⟨⟨k,p,i,d⟩,he⟩ := (packing b (h+1) N).surjective f
    have addrZ : z=addr baseVal (k,p,i,d) := by
      have e := congrArg Fin.val he
      change _ = z-baseVal at e
      change z=baseVal+_
      omega
    subst z
    change WordLayout.get (up S h N baseVal (heap m)) baseVal b (h+1) N k p i d=_
    rcases i with ⟨a,u⟩
    rcases d with ⟨c,v⟩
    have hk : k≠2 := by
      rintro rfl
      exact hitZ ⟨(a,c),mem_all _,(p,u,v),rfl⟩
    exact (get_put (heap m) baseVal b (h+1) N (upValue S h N baseVal (heap m)) k p (a,u) (c,v)).trans (if_neg hk)
  · exact put_outside _ _ _ _ _ _ _ (by dsimp [next] at inside; omega)

private theorem listRate {I : Type*} (l : List I) (cost : I → ℕ) {N D : ℕ} (hn : 1 ≤ N) (hd : 1 ≤ D) :
    (l.map (fun j => gridCost N D (cost j))).sum ≤ (l.map (fun j => cost j+15)).sum*(N*D*D) := by
  induction l with
  | nil => simp
  | cons j js ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [Nat.add_mul]
    exact Nat.add_le_add (grid_cost_bound hn hd _) ih

/-- Native instruction count for an entire downward or upward layer, with one
constant independent of the number of nodes and their matrix dimensions. -/
theorem layer_time {b r : ℕ} (S : Scheme b r) :
    ∃ C : ℕ, ∀ N D : ℕ, 0 < N → 0 < D →
      ((all (Fin 3 × Fin r)).map (fun j => gridCost N D (downBatchCost S j))).sum
      + ((all (Fin b × Fin b)).map (fun j => gridCost N D (upBatchCost S j))).sum ≤ C*(N*D*D) := by
  let left := ((all (Fin 3 × Fin r)).map (fun j => downBatchCost S j+15)).sum
  let right := ((all (Fin b × Fin b)).map (fun j => upBatchCost S j+15)).sum
  refine ⟨left+right,?_⟩
  intro N D hn hd
  rw [Nat.add_mul]
  exact Nat.add_le_add (listRate _ _ hn hd) (listRate _ _ hn hd)

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

/- NativeSquareAdvance -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

/-- Runtime arguments and caller-owned counters live between the expression
scratch and the controller's working registers. -/
def CallerFrame (m out : IntegerRAM.Memory) : Prop := ∀ z, floor < z → z < -14 → out z=m z

theorem CallerFrame.trans {m x o : IntegerRAM.Memory} (a : CallerFrame m x) (b : CallerFrame x o) :
    CallerFrame m o := fun z lo hi => (b z lo hi).trans (a z lo hi)

private theorem gridFrame {m o : IntegerRAM.Memory} (a : regs (-4) m o) : CallerFrame m o :=
  fun z lo hi => a z (Or.inr ⟨lo,by omega⟩) (by omega)

private theorem quotFrame {m o : IntegerRAM.Memory} {num : ℤ} (hn : -4 < num)
    (a : ∀ z, floor < z → z≠num → z≠divOne → z≠divK → z≠divQ → z≠divTest → o z=m z) : CallerFrame m o := by
  intro z lo hi
  apply a z lo <;> (try simp only [divOne,divK,divQ,divTest]) <;> omega

private theorem heap_copy (m o : IntegerRAM.Memory) (e : Expr) {reg : ℤ} (hr : reg < 0)
    (fr : ∀ z, floor < z → o z=if z=reg then e.val m else m z) : heap o=heap m := by
  funext z
  exact (fr z (by unfold floor; omega)).trans (if_neg (by omega))

private theorem downAdj_run {b r h N baseVal W : ℕ} (m : IntegerRAM.Memory) (ready : lowOK baseVal N (b^h) m) :
    ∃ o, Runs W (downAdj b r) m (downAdjTime b r) o ∧ lowOK (baseVal+WordLayout.size b (h+1) N) (N*r) (b^h) o ∧
      heap o=heap m ∧ o rootReg=m rootReg ∧ CallerFrame m o := by
  obtain ⟨x,ra,va⟩ := assign_run (W:=W) m (by decide : floor <  -1) (next b) (by
    simp [next,parentSide,base,nodes,side,times,plus,num,Expr.safe,floor])
  have keep (z : ℤ) (hz : floor < z) (hd : z≠ -1) : x z=m z := (va z hz).trans (if_neg hd)
  have nval : (next b).val m=(baseVal+WordLayout.size b (h+1) N:ℕ) := by
    simp [next,parentSide,base,nodes,side,times,plus,num,Expr.val,ready.1,ready.2.1,ready.2.2,WordLayout.size,plane,pow_succ]
    ring
  obtain ⟨o,rb,vb⟩ := assign_run (W:=W) x (by decide : floor <  -2) (times nodes (num r))
    (by simp [times,nodes,num,Expr.safe,floor])
  have keep' (z : ℤ) (hz : floor < z) (hd : z≠ -2) : o z=x z := (vb z hz).trans (if_neg hd)
  have vals : (times nodes (num r)).val x=((N*r:ℕ):ℤ) := by
    simp [times,nodes,num,Expr.val,keep _ (by decide : floor <  -2) (by decide),ready.2.1]
  refine ⟨o,Runs.seq ra rb,⟨?_,?_,?_⟩,(heap_copy x o _ (by decide : (-2:ℤ) < 0) vb).trans
    (heap_copy m x _ (by decide : (-1:ℤ) < 0) va),?_,?_⟩
  · rw [keep' _ (by decide) (by decide),va _ (by decide),if_pos rfl,nval]
  · rw [vb _ (by decide),if_pos rfl,vals]
  · exact (keep' _ (by decide) (by decide)).trans ((keep _ (by decide) (by decide)).trans ready.2.2)
  · exact (keep' _ (by decide) (by decide)).trans (keep _ (by decide) (by decide))

  · exact fun z lo hi => (keep' z lo (by omega)).trans (keep z lo (by omega))

/-- The whole downward update, including dynamic division to recover the
child side, all coefficient combinations, and advancement of the memory base. -/
theorem downOnce_run {b r h N baseVal W : ℕ} (S : Scheme b r) (hb : 0 < b) (hn : 0 < N)
    (m : IntegerRAM.Memory) (ready : lowOK baseVal N (b^(h+1)) m)
    (gN : ∀ j : ℕ, j ≤ N → Fits W ((j:ℤ)-N)) (gD : ∀ j : ℕ, j ≤ b^h → Fits W ((j:ℤ)-b^h))
    (divFit : ∀ j : ℕ, j ≤ b^h*b → Fits W (-(j:ℤ)))
    (fp : ∀ x : Cell b (h+1) N, Fits W (addr baseVal x))
    (fc : ∀ x : Cell b h (N*r), Fits W (addr (baseVal+WordLayout.size b (h+1) N) x)) :
    ∃ t, t ≤ downTime S h N ∧ ∃ o, Runs W (downOnce S) m t o ∧
      lowOK (baseVal+WordLayout.size b (h+1) N) (N*r) (b^h) o ∧ heap o=down S h N baseVal (heap m) ∧
      o rootReg=m rootReg ∧ CallerFrame m o := by
  have hd := Nat.pow_pos hb (n:=h)
  obtain ⟨x,rx,xd,fr⟩ := quotient_run hb hd (-3) (by decide) (by decide) m (by simpa [pow_succ] using ready.2.2) divFit
  have ready' : lowOK baseVal N (b^h) x := ⟨(fr _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans ready.1,(fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.2.1,xd⟩
  have rh : heap x=heap m := by
    funext z
    apply fr <;> (try simp only [floor,divOne,divQ,divK,divTest]) <;> omega
  obtain ⟨s,cs,y,ry,cy,fy,hy⟩ := downLevel_run S hn hd x ready' gN gD fp fc
  obtain ⟨o,ro,co,ho,fo,caller⟩ := downAdj_run (b:=b) (r:=r) (W:=W) y cy
  refine ⟨_,Nat.add_le_add_left (Nat.add_le_add_right cs _) _,o,.seq rx (.seq ry ro),co,?_,?_,?_⟩
  · rw [ho,hy,rh]
  · exact fo.trans ((fy rootReg (by decide) (by decide)).trans (fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))

  · exact ((quotFrame (by decide) fr).trans (gridFrame fy)).trans caller

/-- The upward update decodes the parent node count, moves back one level,
combines the child's output words and restores the parent side. -/
theorem upOnce_run {b r h N baseVal W : ℕ} (S : Scheme b r) (hb : 0 < b) (hr : 0 < r) (hn : 0 < N)
    (m : IntegerRAM.Memory) (ready : lowOK (baseVal+WordLayout.size b (h+1) N) (N*r) (b^h) m)
    (gN : ∀ j : ℕ, j ≤ N → Fits W ((j:ℤ)-N)) (gD : ∀ j : ℕ, j ≤ b^h → Fits W ((j:ℤ)-b^h))
    (divFit : ∀ j : ℕ, j ≤ N*r → Fits W (-(j:ℤ)))
    (fp : ∀ x : Cell b (h+1) N, Fits W (addr baseVal x))
    (fc : ∀ x : Cell b h (N*r), Fits W (addr (baseVal+WordLayout.size b (h+1) N) x)) :
    ∃ t, t ≤ upTime S h N ∧ ∃ o, Runs W (upOnce S) m t o ∧ lowOK baseVal N (b^(h+1)) o ∧
      heap o=up S h N baseVal (heap m) ∧ o rootReg=m rootReg ∧ CallerFrame m o := by
  have hd := Nat.pow_pos hb (n:=h)
  obtain ⟨x,rx,xn,fr⟩ := quotient_run hr hn (-2) (by decide) (by decide) m ready.2.1 divFit
  have xd : x (-3)=((b^h:ℕ):ℤ) := (fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.2.2
  have xb : x (-1)=((baseVal+WordLayout.size b (h+1) N:ℕ):ℤ) := (fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.1
  have xh : heap x=heap m := by funext z; apply fr <;> (try simp only [floor,divOne,divQ,divK,divTest]) <;> omega
  obtain ⟨y,ry,vy⟩ := assign_run (W:=W) x (by decide : floor <  -1) (back b) (by simp [back,parentSide,num,base,nodes,side,times,Expr.safe,floor])
  have backVal : (back b).val x=baseVal := by
    simp [back,parentSide,base,nodes,side,times,num,Expr.val,xb,xn,xd,WordLayout.size,plane,pow_succ]
    ring
  have ky (z : ℤ) (hz : floor < z) (d : z≠ -1) : y z=x z := (vy z hz).trans (if_neg d)
  have cy : lowOK baseVal N (b^h) y := ⟨by rw [vy _ (by decide),if_pos rfl,backVal],
    (ky _ (by decide) (by decide)).trans xn,(ky _ (by decide) (by decide)).trans xd⟩
  obtain ⟨s,cs,a,ra,ca,fa,ha⟩ := upLevel_run S hn hd y cy gN gD fp fc
  obtain ⟨o,ro,vo⟩ := assign_run (W:=W) a (by decide : floor <  -3) (parentSide b) (by simp [parentSide,times,num,side,Expr.safe,floor])
  have sizeVal : (parentSide b).val a=((b^(h+1):ℕ):ℤ) := by simp [parentSide,times,num,side,Expr.val,ca.2.2,pow_succ,mul_comm]
  have ko (z : ℤ) (hz : floor < z) (d : z≠ -3) : o z=a z := (vo z hz).trans (if_neg d)
  refine ⟨_,Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_right cs _) _) _,o,.seq rx (.seq ry (.seq ra ro)),
    ⟨(ko _ (by decide) (by decide)).trans ca.1,(ko _ (by decide) (by decide)).trans ca.2.1,
      by rw [vo _ (by decide),if_pos rfl,sizeVal]⟩,?_,?_,?_⟩
  · rw [heap_copy a o _ (by decide : (-3:ℤ) < 0) vo,ha,heap_copy x y _ (by decide : (-1:ℤ) < 0) vy,xh]
  · exact (ko _ (by decide) (by decide)).trans ((fa _ (by decide) (by decide)).trans ((ky _ (by decide) (by decide)).trans
      (fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))))

  · have c₁ : CallerFrame x y := fun z lo hi => ky z lo (by omega)
    have c₂ : CallerFrame a o := fun z lo hi => ko z lo (by omega)
    exact ((((quotFrame (by decide) fr).trans c₁).trans (gridFrame fa)).trans c₂)

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareTrace -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured

/-- A sequence of completed iterations with the test checked after each one.
The test is negative at each internal join. -/
inductive LoopTrace (W : ℕ) (c : Command) (g : ℤ) (m : IntegerRAM.Memory) :
    ℕ → IntegerRAM.Memory → Prop where
  | nil : LoopTrace W c g m 0 m
  | snoc {q s x y} : LoopTrace W c g m q x → (q=0 ∨ x g < 0) →
      Runs W c x s y → Fits W (y g) → LoopTrace W c g m (q+(s+1)) y

theorem LoopTrace.prefix {W c g m q x} (h : LoopTrace W c g m q x) (neg : q=0 ∨ x g < 0)
    {r y} (tail : Runs W (.repeatWhileNegative c g) x r y) :
    Runs W (.repeatWhileNegative c g) m (q+r) y := by
  induction h generalizing r y with
  | nil => simpa using tail
  | @snoc q s x v prior first run fit ih =>
    have last : v g < 0 := neg.resolve_left (by omega)
    have rest := ih first (Runs.loop_again run fit last tail)
    simpa [Nat.add_assoc] using rest

theorem LoopTrace.close {W c g m q x} (h : LoopTrace W c g m q x) (hq : 0 < q) (last : ¬ x g < 0) :
    Runs W (.repeatWhileNegative c g) m q x := by
  cases h with
  | nil => omega
  | snoc head neg run fit => exact head.prefix neg (Runs.loop_done run fit last)

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

private theorem leafPrefix_eq (baseVal b N : ℕ) (m : IntegerRAM.Memory) :
    leafPrefix baseVal N N m=leaf b N baseVal (heap m) := by
  funext z
  by_cases hz : baseVal ≤ z ∧ z < baseVal+WordLayout.size b 0 N
  · let t : Fin (WordLayout.size b 0 N) := ⟨z-baseVal,by omega⟩
    obtain ⟨⟨k,p,i,j⟩,hk⟩ := (packing b 0 N).surjective t
    have loc : z=addr baseVal (k,p,i,j) := by
      have e := congrArg Fin.val hk
      change _=z-baseVal at e
      change z=baseVal+_
      omega
    subst z
    change _=WordLayout.get (leaf b N baseVal (heap m)) baseVal b 0 N k p i j
    rw [leaf,get_put,leafValue]
    have e (k : Fin 3) (i j : Index b 0) :
        addr baseVal (k,p,i,j)=baseVal+k.val*N+p.val := by
      rw [address_formula]
      have ei : ((radix b 0) i).val=0 := by have bound : ((radix b 0) i).val < 1 := ((radix b 0) i).isLt; omega
      have ej : ((radix b 0) j).val=0 := by have bound : ((radix b 0) j).val < 1 := ((radix b 0) j).isLt; omega
      simp [ei,ej,Nat.add_assoc]
    rw [e k i j]
    by_cases hk : k=2
    · subst k
      rw [if_pos rfl]
      change leafPrefix baseVal N N m (baseVal+2*N+p.val)=m (addr (b:=b) (h:=0) baseVal (0,p,i,()))*m (addr (b:=b) (h:=0) baseVal (1,p,(),j))
      rw [e 0 i (),e 1 () j]
      change leafPrefix baseVal N N m (baseVal+2*N+p.val)=m (baseVal+0*N+p.val:ℕ)*m (baseVal+1*N+p.val:ℕ)
      have hp := p.isLt
      rw [leafPrefix,if_pos (by omega)]
      congr 2 <;> omega
    · rw [if_neg hk]
      change leafPrefix baseVal N N m (baseVal+k.val*N+p.val)=m (addr baseVal (k,p,i,j))
      rw [e k i j,leafPrefix,if_neg]
      have kp : k.val ≤ 1 := by have := k.isLt; have neq : k.val≠2 := fun hh => hk (Fin.ext hh); omega
      have bound := Nat.mul_le_mul_right N kp
      have hp := p.isLt
      simp only [Nat.one_mul] at bound
      omega
  · have no : ¬(baseVal+2*N ≤ z ∧ z < baseVal+2*N+N) := by simp [WordLayout.size,plane] at hz; omega
    exact (if_neg no).trans (put_outside (heap m) baseVal b 0 N (leafValue b N baseVal (heap m)) z (by omega)).symm

private theorem marker {W : ℕ} {e : Expr} {baseVal N D : ℕ} (m : IntegerRAM.Memory) (ctx : lowOK baseVal N D m)
    (safe : e.safe floor W m) :
    ∃ o, Runs W (assign flag e) m (e.steps+2) o ∧ lowOK baseVal N D o ∧
      o rootReg=m rootReg ∧ heap o=heap m ∧ o flag=e.val m ∧ CallerFrame m o := by
  obtain ⟨o,r,f⟩ := assign_run m (by decide : floor < flag) e safe
  have keep (i : ℤ) (hlo : floor < i) (h : i≠flag) : o i=m i := (f i hlo).trans (if_neg h)
  exact ⟨o,r,⟨(keep _ (by decide) (by decide)).trans ctx.1,(keep _ (by decide) (by decide)).trans ctx.2.1,
    (keep _ (by decide) (by decide)).trans ctx.2.2⟩,keep _ (by decide) (by decide),
    funext (fun z : ℕ => keep z (by unfold floor; omega) (by unfold flag; omega)),
    (f _ (by decide)).trans (if_pos rfl),fun z lo hi => keep z lo (by unfold flag; omega)⟩

def DownTrace {b r : ℕ} (S : Scheme b r) (W h : ℕ) (m : IntegerRAM.Memory) (t : ℕ) (x : IntegerRAM.Memory) :=
  if h=0 then t=0 ∧ x=m else Runs W (.repeatWhileNegative (downStep S) flag) m t x

/-- One down-pass, one leaf pass, and one up-pass. The native code for each
phase depends on S alone; h only appears in the calling convention. -/
theorem flight {b r : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hr : 0 < r) (W M : ℕ) (cap : Room W M)
    (h N baseVal root : ℕ) (hn : 0 < N) (hroot : b^h ≤ root) (hrM : root ≤ M)
    (bound : baseVal+space b r h N ≤ M) (m : IntegerRAM.Memory)
    (ctx : lowOK baseVal N (b^h) m) (rootEq : m rootReg=root) :
    ∃ d l u : ℕ, d+l+u ≤ charge S h N ∧
    ∃ x y o : IntegerRAM.Memory, DownTrace S W h m d x ∧ Runs W leafLayer x l y ∧
      LoopTrace W (upStep S) flag y u o ∧ lowOK baseVal N (b^h) o ∧ o rootReg=root ∧
      heap o=run S h N baseVal (heap m) ∧
      CallerFrame m o ∧ (h=0 → u=0) ∧ (0 < h → 0 < u ∧ o flag=(b^h:ℕ)- (root:ℤ)) := by
  induction h generalizing N baseVal m with
  | zero =>
    have tail : baseVal+3*N ≤ M := by simpa [space,WordLayout.size,plane] using bound
    have nM : N ≤ M := by omega
    obtain ⟨l,cl,o,leafRun,res,fr⟩ := leafLayer_runs hn m ctx.1 ctx.2.1
      (fun a ha => cap _ (by omega) (by omega)) (fun j hj => cap _ (by omega) (by omega))
    have ready : lowOK baseVal N (b^0) o :=
      ⟨(fr _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans ctx.1,
       (fr _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans ctx.2.1,
       (fr _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans ctx.2.2⟩
    exact ⟨0,l,0,by simpa [charge] using cl,m,o,o,by simp [DownTrace],leafRun,.nil,ready,
      (fr _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans rootEq,
      (funext res).trans (leafPrefix_eq _ _ _ _),(fun z lo hi => fr z lo (by omega) (by omega) (by omega) (by omega)),fun _ => rfl,by omega⟩
  | succ h ih =>
    let next := baseVal+WordLayout.size b (h+1) N
    have splitB : next+space b r h (N*r) ≤ M := by simpa [next,space,Nat.add_assoc] using bound
    have nk := Nat.mul_pos hn hr
    have hbh : 0 < b^h := Nat.pow_pos (by omega)
    have hD : b^h < b^(h+1) := by rw [pow_succ]; nlinarith
    have boundParent := size_le_space b r (h+1) N
    have boundChild := size_le_space b r h (N*r)
    have pM := size_ge (b:=b) (by omega) (h+1) N hn
    have kM := size_ge (b:=b) (by omega) h (N*r) nk
    have p : baseVal+WordLayout.size b (h+1) N ≤ M := by omega
    have c : next+WordLayout.size b h (N*r) ≤ M := by omega
    have nM : N ≤ M := by omega
    have nrM : N*r ≤ M := by omega
    have dM : b^h ≤ M := by omega
    have bdM : b^h*b ≤ M := by simpa [pow_succ] using hroot.trans hrM
    have gN (j : ℕ) (hj : j ≤ N) := cap ((j:ℤ)-N) (by omega) (by omega)
    have gD (j : ℕ) (hj : j ≤ b^h) := cap ((j:ℤ)-((b^h:ℕ):ℤ)) (by omega) (by omega)
    have fp (z : Cell b (h+1) N) : Fits W (addr baseVal z) :=
      cap _ (by omega) (by have := (addr_range baseVal z).2; omega)
    have fc (z : Cell b h (N*r)) : Fits W (addr next z) :=
      cap _ (by omega) (by have := (addr_range next z).2; omega)
    obtain ⟨a,ca,v,ra,cv,hv,rv,f₁⟩ := downOnce_run S (by omega) hn m ctx gN (by simpa using gD)
      (fun j hj => cap _ (by omega) (by omega)) fp fc
    obtain ⟨w,rw',cw,rwRoot,hw,fw,f₂⟩ := marker (W:=W) (e:=downTest) v cv (by simp [downTest,side,Expr.safe,floor])
    have stepDown : Runs W (downStep S) m (a+(downTest.steps+2)) w := .seq ra rw'
    have flagW : w flag=1-((b^h:ℕ):ℤ) := by simpa [downTest,Expr.val,side,cv.2.2] using fw
    have fitW : Fits W (w flag) := flagW ▸ cap _ (by omega) (by omega)
    obtain ⟨d,l,u,budget,x,y,z,down,leafRun,up,cz,rz,hz,f₃,nilU,lastU⟩ :=
      ih (N:=N*r) (baseVal:=next) nk (hD.le.trans hroot) splitB w cw (rwRoot.trans (rv.trans rootEq))
    obtain ⟨a',ca',v',ra',cv',hv',rv',f₄⟩ := upOnce_run S (by omega) hr hn z cz gN (by simpa using gD)
      (fun j hj => cap _ (by omega) (by omega)) fp fc
    obtain ⟨o,r',co,ro,ho,fo,f₅⟩ := marker (W:=W) (e:=upTest) v' cv' (by simp [upTest,side,Expr.safe,floor,rootReg])
    have stepUp : Runs W (upStep S) z (a'+(upTest.steps+2)) o := .seq ra' r'
    have flagO : o flag=((b^(h+1):ℕ):ℤ)-root := by
      simpa [upTest,Expr.val,side,cv'.2.2,rv',rz] using fo
    have fitO : Fits W (o flag) := flagO ▸ cap _ (by omega) (by omega)
    have openUp : u=0 ∨ z flag < 0 := by
      by_cases zero : h=0
      · exact Or.inl (nilU zero)
      · obtain ⟨_,ff⟩ := lastU (by omega)
        exact Or.inr (by rw [ff]; omega)
    let d' := (a+(downTest.steps+2))+1+d
    let u' := u+((a'+(upTest.steps+2))+1)
    refine ⟨d',l,u',?_,x,y,o,?_,leafRun,up.snoc openUp stepUp fitO,co,ro.trans (rv'.trans rz),?_,((((f₁.trans f₂).trans f₃).trans f₄).trans f₅),by omega,?_⟩
    · dsimp [d',u']; simp only [charge]; omega
    · simp only [DownTrace,Nat.succ_ne_zero,if_false]
      by_cases z₀ : h=0
      · obtain ⟨hd,hx⟩ : d=0 ∧ x=w := by simpa [DownTrace,z₀] using down
        subst d; subst x
        simpa [d'] using Runs.loop_done stepDown fitW (by simp [flagW,z₀])
      · have cDown : Runs W (.repeatWhileNegative (downStep S) flag) w d x := by simpa only [DownTrace,if_neg z₀] using down
        have hp : 1 < b^h := Nat.one_lt_pow (by omega) (by omega)
        exact Runs.loop_again stepDown fitW (by rw [flagW]; omega) cDown
    · rw [ho,hv',hz,hw,hv,run]
    · exact fun _ => ⟨by dsimp [u']; omega,by simpa using flagO⟩

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- MMWordLayoutRate -/
section
open OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.BlockMM.WordLayout

/-- Include root padding writes and harvesting all n² requested output entries. -/
def totalWork (b r n : ℕ) := size b (depth b n) 1 + iterations b r (depth b n) 1 + n^2

theorem rank_pos {b r : ℕ} (S : Scheme b r) (hb : 0<b) (hs : 0<S.scale) : 0<r := by
  by_contra! h
  obtain rfl : r=0 := by omega
  let i : Fin b := ⟨0,hb⟩
  have he := S.correct (1 : Square (Fin b)) 1 i i
  simp at he
  omega

theorem address_root_output {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (base : ℕ) (i j : Fin n) :
    addr base (2,(0:Fin 1),includeIndex hb hn i,includeIndex hb hn j) =
      base + (2*b^(depth b n)+i.val)*b^(depth b n)+j.val := by
  rw [address_formula]
  simp [includeIndex]

theorem size_and_work {b r n : ℕ} (hb : 2≤b) (hr : 1≤r) (hn : 1≤n) :
    space b r (depth b n) 1 + totalWork b r n ≤ 13*scalarBudget b r (depth b n) := by
  let h := depth b n
  have hs := space_bound (b:=b) hr h 1
  have ht := iteration_bound (b:=b) (by omega) hr h 1
  have hw := size_le_space b r h 1
  have hp := Nat.pow_le_pow_left (depth_bounds hb hn).1 2
  have ha : n^2 ≤ size b h 1 := by
    calc n^2 ≤ (b^h)^2 := hp
         _ ≤ _ := by simp [size,plane,pow_two]; omega
  change space b r h 1 + (size b h 1 + iterations b r h 1 + n^2) ≤ 13*scalarBudget b r h
  simp only [Nat.mul_one] at hs ht
  omega

theorem execute_frame {b r n : ℕ} (S : Scheme b r) (base : ℕ) (m : Memory) (A B : Square (Fin n))
    (a : ℕ) (ha : a<base ∨ base+space b r (depth b n) 1 ≤ a) : execute S base m A B a = m a := by
  rw [execute,run_frame _ _ _ _ _ _ ha,start]
  apply put_outside
  have hh := size_le_space b r (depth b n) 1
  omega

end VWZClique.BlockMM.WordLayout
end

/- NativeSquareRate -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout OAI.MatrixMultiplication.Arithmetic

/-- A single machine program for every positive recursion height. Its three
phases use two actual loops, independently of the input side. -/
theorem core_runs {b r : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hr : 0 < r) {W M : ℕ}
    (room : Room W M) {h N baseVal : ℕ} (hh : 0 < h) (hn : 0 < N) (spaceFit : baseVal+space b r h N ≤ M)
    (m : IntegerRAM.Memory) (ctx : lowOK baseVal N (b^h) m) :
    ∃ t, t ≤ 4+charge S h N ∧ ∃ o, Runs W (core S) m t o ∧ heap o=run S h N baseVal (heap m) ∧ CallerFrame m o := by
  obtain ⟨s,rs,fs⟩ := assign_run (W:=W) m (by decide : floor < rootReg) side (by decide : floor < (-3:ℤ))
  have keep (z : ℤ) (hz : floor < z) (ne : z≠rootReg) : s z=m z := (fs z hz).trans (if_neg ne)
  have ct : lowOK baseVal N (b^h) s := ⟨(keep _ (by decide) (by decide)).trans ctx.1,
    (keep _ (by decide) (by decide)).trans ctx.2.1,(keep _ (by decide) (by decide)).trans ctx.2.2⟩
  have init : s rootReg=(b^h:ℕ) := ((fs _ (by decide)).trans (if_pos rfl)).trans ctx.2.2
  have sizeM : b^h ≤ M := by
    have h1 := (size_ge (b:=b) (by omega) h N hn).1
    have h2 := size_le_space b r h N
    omega
  obtain ⟨d,l,u,ctot,x,y,o,dr,lr,ur,_,_,result,caller,_,last⟩ := flight S hb hr W M room h N baseVal
    (b^h) hn le_rfl sizeM spaceFit s ct init
  have downR : Runs W (.repeatWhileNegative (downStep S) flag) s d x := by simpa only [DownTrace,if_neg (Nat.ne_of_gt hh)] using dr
  obtain ⟨hu,flagEq⟩ := last hh
  have upR := ur.close hu (by rw [flagEq]; simp)
  refine ⟨4+(d+(l+u)),by omega,o,Runs.seq rs (Runs.seq downR (.seq lr upR)),?_,(fun z lo hi => (caller z lo hi).trans (keep z lo (by unfold rootReg; omega)))⟩
  rw [result]
  congr 1
  funext z
  apply keep <;> simp only [floor,rootReg] <;> omega

/-- Sum the actual instruction charges over all levels of the rank-r tree. -/
theorem charge_bound {b r : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hr : 0 < r) :
    ∃ C : ℕ, ∀ h N : ℕ, 0 < N → charge S h N ≤ C*N*scalarBudget b r h := by
  obtain ⟨P,hP⟩ := layer_time S
  let K := (Expr.num b).steps+(Expr.num r).steps+downAdjTime b r+(back b).steps+(parentSide b).steps+
    downTest.steps+upTest.steps+50
  let C := P+K+leafBodySteps+20
  refine ⟨C,?_⟩
  intro h
  induction h with
  | zero =>
    intro N hn
    simp only [charge,scalarBudget,Nat.mul_one]
    have H := Nat.mul_le_mul_right N (show leafBodySteps+5 ≤ C by dsimp [C]; omega)
    rw [Nat.add_mul] at H
    rw [Nat.mul_add]
    nlinarith
  | succ h ih =>
    intro N hn
    let D := b^h
    have hd : 0 < D := Nat.pow_pos (by omega)
    have hp := hP N D hn hd
    have old := ih (N*r) (Nat.mul_pos hn hr)
    have hnD : N ≤ N*D := by simpa using Nat.mul_le_mul_left N hd
    have hD : D ≤ N*D := by simpa using Nat.mul_le_mul_right D hn
    have hdD : N*D ≤ N*D*D := by simpa using Nat.mul_le_mul_left (N*D) hd
    have oneD : 1 ≤ N*D*D := (show 1 ≤ N from hn).trans (hnD.trans hdD)
    have costK : K ≤ K*(N*D*D) := by simpa using Nat.mul_le_mul_left K oneD
    have extra : 5*N+5*D ≤ 10*(N*D*D) := by omega
    have eqPow : (b^2)^h=D*D := by dsimp [D]; rw [←mul_pow,pow_two]
    have cb : P+K+10 ≤ C := by dsimp [C]; omega
    have blow : 1 ≤ 6*r*b^2 := by change 0 < 6*r*b^2; positivity
    let L := ((all (Fin 3 × Fin r)).map (fun j => gridCost N D (downBatchCost S j))).sum
    let R := ((all (Fin b × Fin b)).map (fun j => gridCost N D (upBatchCost S j))).sum
    have sumP : L+R ≤ P*(N*D*D) := hp
    have fixed : downTime S h N + (downTest.steps+3) + upTime S h N + (upTest.steps+3) ≤ L+R+K+(5*N+5*D) := by
      dsimp only [downTime,upTime,quotTime,K,L,R,D]
      omega
    have chargeLocal := fixed.trans (Nat.add_le_add (Nat.add_le_add sumP costK) extra)
    have local' : downTime S h N + (downTest.steps+3) + upTime S h N + (upTest.steps+3) ≤ C*(N*D*D) := by
      have bound := Nat.mul_le_mul_right (N*D*D) cb
      rw [Nat.add_mul,Nat.add_mul] at bound
      exact chargeLocal.trans bound
    have higher := Nat.mul_le_mul_left (C*(N*D*D)) blow
    simp only [Nat.mul_one] at higher
    calc
      _ = charge S h (N*r)+(downTime S h N+(downTest.steps+3)+upTime S h N+(upTest.steps+3)) := by rw [charge]; omega
      _ ≤ C*(N*r)*scalarBudget b r h + C*(N*D*D)*(6*r*b^2) :=
        Nat.add_le_add old (local'.trans higher)
      _ = _ := by rw [scalarBudget,eqPow]; ring

end VWZClique.IntegerRAM.SquareCode.Layout
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

/- NativeSquareTransfer -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured

def offset (pointer stride i j : ℕ) := pointer+(stride*i+j)

theorem offset_inj {ptr stride i i' j j' : ℕ} (h : j<stride) (h' : j'<stride)
    (he : offset ptr stride i j=offset ptr stride i' j') : i=i' ∧ j=j' := by
  have eq : stride*i+j=stride*i'+j' := Nat.add_left_cancel he
  have a := congrArg (· / stride) eq
  have b := congrArg (· % stride) eq
  have hs : 0 < stride := by omega
  simp only [Nat.mul_add_div hs,Nat.div_eq_of_lt h,Nat.div_eq_of_lt h',Nat.add_zero] at a
  simp only [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt h,Nat.mod_eq_of_lt h'] at b
  exact ⟨a,b⟩

/-- Copy one row-major square between arbitrary row strides, or fill the
destination square with zero. It touches only the addressed destination
entries, and retains rows of the source not covered by the destination. -/
theorem tilePass_run {W D srcBase fs dest ds : ℕ} (copy : Bool) (hd : 0 < D) (stride : D ≤ ds)
    (m : IntegerRAM.Memory) (nodes : m (-2)=1) (side : m (-3)=D)
    (rf : m srcPointer=srcBase) (sf : m srcStride=fs) (rd : m dstPointer=dest) (sd : m dstStride=ds)
    (guard : ∀ j : ℕ, j ≤ D → Fits W ((j:ℤ)-D))
    (unit : ∀ j : ℕ, j ≤ 1 → Fits W ((j:ℤ)-1))
    (fitD : ∀ i<D, ∀ j<D, Fits W (offset dest ds i j))
    (fitS : copy=true → ∀ i<D, ∀ j<D, Fits W (offset srcBase fs i j))
    (apart : copy=true → ∀ i<D, ∀ j<D, ∀ u<D, ∀ v<D, offset dest ds i j ≠ offset srcBase fs u v) :
    ∃ t, t ≤ gridCost 1 D (tileSteps copy) ∧ ∃ out, Runs W (tilePass copy) m t out ∧
      (∀ i<D, ∀ j<D, out (offset dest ds i j) = if copy then m (offset srcBase fs i j) else 0) ∧
      (∀ z : ℕ, (∀ i<D, ∀ j<D, z≠offset dest ds i j) → out z=m z) ∧ regs (-4) m out := by
  let dst (p : Position) := offset dest ds p.2.1 p.2.2
  let val (p : Position) (H : Heap) := if copy then H (offset srcBase fs p.2.1 p.2.2) else 0
  let f (p i j : ℕ) := scatter dst val (p,i,j)
  have cell (p : ℕ) (_ : p<1) (i : ℕ) (hi : i<D) (j : ℕ) (hj : j<D) (x : IntegerRAM.Memory)
      (fr : regs (-4) m x) (_ : x (-4)=p) (xi : x (-5)=i) (xj : x (-6)=j) (one : x (-7)=1) :
      ∃ t, t ≤ tileSteps copy ∧ ∃ o, Runs W (tileStore copy) x t o ∧ heap o=f p i j (heap x) ∧
        regs (-7) x o ∧ o (-7)=1 := by
    have F := (fr srcPointer (by decide) (by decide)).trans rf
    have FS := (fr srcStride (by decide) (by decide)).trans sf
    have T := (fr dstPointer (by decide) (by decide)).trans rd
    have TS := (fr dstStride (by decide) (by decide)).trans sd
    have ptr (a s : ℤ) (A B : ℕ) (aa : x a=A) (bb : x s=B) :
        (tileAddr a s).val x=(offset A B i j:ℤ) := by
      simp only [tileAddr,plus,times,row,col,Expr.val,aa,bb,xi,xj,offset,Int.natCast_add,Int.natCast_mul]
    have pf := ptr _ _ _ _ F FS
    have pt := ptr _ _ _ _ T TS
    have read : (tileLoad copy).safe floor W x := by
      cases copy with
      | false => trivial
      | true =>
        refine ⟨by simp [tileAddr,plus,times,row,col,Expr.safe,floor],?_,?_⟩
        · rw [pf]; unfold floor; omega
        · rw [pf]; exact fitS rfl i hi j hj
    obtain ⟨o,ro,ko⟩ := write_run x floor (tileAddr dstPointer dstStride) (tileLoad copy)
      (by simp [tileAddr,plus,times,row,col,Expr.safe,floor]) read (pt ▸ fitD i hi j hj)
    refine ⟨_,le_rfl,o,ro,?_,?_,?_⟩
    · funext z
      have h := ko (z:ℤ) (by unfold floor; omega)
      cases copy <;> simpa [heap,f,scatter,val,dst,tileLoad,Expr.val,pf,pt] using h
    · intro z h n
      exact (ko z (by unfold floor at *; omega)).trans (if_neg (by rw [pt]; omega))
    · exact ((ko (-7) (by decide)).trans (if_neg (by rw [pt]; omega))).trans one
  obtain ⟨t,ct,o,run,values,frame,_⟩ := grid_run (by decide : 0<1) hd m nodes side unit guard _ f cell
  let src (z : ℕ) := copy=true ∧ ∃ i<D, ∃ j<D, z=offset srcBase fs i j
  have sc := scatter_result (points 1 D) (heap m) dst val src (by
    rintro p mem ⟨c,i,hi,j,hj,he⟩
    obtain ⟨_,a,b⟩ := (points_mem ..).1 mem
    exact apart c _ a _ b _ hi _ hj he) (by
    intro p mem x y eq
    obtain ⟨_,a,b⟩ := (points_mem ..).1 mem
    cases c : copy
    · simp [val,c]
    · simp only [val,c,if_true]
      exact eq _ ⟨c,p.2.1,a,p.2.2,b,rfl⟩) (by
    rintro ⟨p,i,j⟩ hp ⟨q,u,v⟩ hq eq
    obtain ⟨p0,_,jD⟩ := (points_mem ..).1 hp
    obtain ⟨q0,_,vD⟩ := (points_mem ..).1 hq
    obtain ⟨rfl,rfl⟩ := offset_inj (jD.trans_le stride) (vD.trans_le stride) eq
    change p<1 at p0
    change q<1 at q0
    congr 1 <;> omega)
  rw [gridFold_list] at values
  refine ⟨t,ct,o,run,?_,?_,frame⟩
  · intro i hi j hj
    exact (congrFun values _).trans (sc.1 (0,i,j) ((points_mem ..).2 ⟨show 0<1 by decide,hi,hj⟩))
  · intro z hz
    exact (congrFun values z).trans (sc.2 z (fun p hp => hz _ ((points_mem ..).1 hp).2.1 _ ((points_mem ..).1 hp).2.2))

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

/- NativeSquareJob -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured

def Origin.val (a : Anchors) : Origin → ℕ
  | .left => a.lhs | .right => a.rhs | .result => a.result
  | .bank k => a.work+k*(a.pad*a.pad)

def Anchors.ready (a : Anchors) (m : IntegerRAM.Memory) :=
  m rawSide=a.raw ∧ m padSide=a.pad ∧ m workPtr=a.work ∧ m lhsPtr=a.lhs ∧ m rhsPtr=a.rhs ∧ m resultPtr=a.result

private theorem width_val (d : Width) {a : Anchors} {m : IntegerRAM.Memory} (ok : a.ready m) :
    d.expr.val m=d.val a := by cases d <;> simp_all [Anchors.ready,Width.expr,Width.val,Expr.val]

private theorem origin_val (d : Origin) {a : Anchors} {m : IntegerRAM.Memory} (ok : a.ready m) :
    d.expr.val m=d.val a := by
  cases d <;> simp_all [Anchors.ready,Origin.expr,Origin.val,Expr.val,plus,num,times]

private theorem width_safe (d : Width) (m : IntegerRAM.Memory) (W : ℕ) : d.expr.safe floor W m := by
  cases d <;> simp [Width.expr,Expr.safe,floor]

private theorem origin_safe (d : Origin) (m : IntegerRAM.Memory) (W : ℕ) : d.expr.safe floor W m := by
  cases d <;> simp [Origin.expr,Expr.safe,num,times,plus,floor]

private theorem ready_write {a : Anchors} {m : IntegerRAM.Memory} (ok : a.ready m)
    (r : ℤ) (lo : -20 ≤ r) (ne : r ≠ -16) (v : ℤ) : a.ready (update m r v) := by
  simpa only [Anchors.ready,update,if_neg (by change (-34:ℤ)≠r; omega : rawSide≠r),
    if_neg (by change (-16:ℤ)≠r; omega : padSide≠r),if_neg (by change (-21:ℤ)≠r; omega : workPtr≠r),
    if_neg (by change (-30:ℤ)≠r; omega : lhsPtr≠r),if_neg (by change (-31:ℤ)≠r; omega : rhsPtr≠r),
    if_neg (by change (-32:ℤ)≠r; omega : resultPtr≠r)] using ok

def Persistent (m o : IntegerRAM.Memory) := ∀ z, floor < z → (z ≤ -21 ∨ z= -16 ∨ z= -15) → o z=m z

theorem Anchors.of_persistent (a : Anchors) {m o : IntegerRAM.Memory} (p : Persistent m o) (h : a.ready m) : a.ready o := by
  rcases h with ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
  exact ⟨(p _ (by decide) (by decide)).trans h₁,(p _ (by decide) (by decide)).trans h₂,
    (p _ (by decide) (by decide)).trans h₃,(p _ (by decide) (by decide)).trans h₄,
    (p _ (by decide) (by decide)).trans h₅,(p _ (by decide) (by decide)).trans h₆⟩

/-- Set the six working registers and execute one rectangular-stride copy or zero fill. -/
theorem Job.run {W : ℕ} (q : Job) (a : Anchors) (m : IntegerRAM.Memory) (ready : a.ready m)
    (D : ℕ) (dEq : q.dim.val a=D) (hd : 0 < D) (stride : D ≤ q.dstStep.val a)
    (guard : ∀ j : ℕ, j ≤ D → Fits W ((j:ℤ)-D)) (unit : ∀ j : ℕ, j ≤ 1 → Fits W ((j:ℤ)-1))
    (fitD : ∀ i<D, ∀ j<D, Fits W (offset (q.dst.val a) (q.dstStep.val a) i j))
    (fitS : q.copy=true → ∀ i<D, ∀ j<D, Fits W (offset (q.src.val a) (q.srcStep.val a) i j))
    (apart : q.copy=true → ∀ i<D, ∀ j<D, ∀ u<D, ∀ v<D,
       offset (q.dst.val a) (q.dstStep.val a) i j ≠ offset (q.src.val a) (q.srcStep.val a) u v) :
    ∃ t, t ≤ q.cost a ∧ ∃ out, Runs W q.cmd m t out ∧
      (∀ i<D, ∀ j<D, out (offset (q.dst.val a) (q.dstStep.val a) i j) =
        if q.copy then m (offset (q.src.val a) (q.srcStep.val a) i j) else 0) ∧
      (∀ z : ℕ, (∀ i<D, ∀ j<D, z≠offset (q.dst.val a) (q.dstStep.val a) i j) → out z=m z) ∧ Persistent m out := by
  let m1 := update m (-2) 1
  let m2 := update m1 (-3) (q.dim.expr.val m1)
  let m3 := update m2 srcPointer (q.src.expr.val m2)
  let m4 := update m3 srcStride (q.srcStep.expr.val m3)
  let m5 := update m4 dstPointer (q.dst.expr.val m4)
  have a1 : a.ready m1 := ready_write ready _ (by decide) (by decide) _
  have a2 : a.ready m2 := ready_write a1 _ (by decide) (by decide) _
  have a3 : a.ready m3 := ready_write a2 _ (by decide) (by decide) _
  have a4 : a.ready m4 := ready_write a3 _ (by decide) (by decide) _
  have a5 : a.ready m5 := ready_write a4 _ (by decide) (by decide) _
  have safe : setupSafe W q.setup m := by
    exact ⟨by decide,trivial,by decide,width_safe ..,by decide,origin_safe ..,by decide,width_safe ..,
      by decide,origin_safe ..,by decide,width_safe ..,trivial⟩
  obtain ⟨x,run,fx⟩ := setup_runs q.setup m safe
  have vals (z : ℤ) (lo : floor < z) : x z =
      update (update (update (update (update (update m (-2) 1) (-3) D) srcPointer (q.src.val a))
      srcStride (q.srcStep.val a)) dstPointer (q.dst.val a)) dstStride (q.dstStep.val a) z := by
    rw [fx z lo]
    change update m5 dstStride (q.dstStep.expr.val m5) z=_
    rw [width_val q.dstStep a5]; dsimp only [m5]; rw [origin_val q.dst a4]
    dsimp only [m4]; rw [width_val q.srcStep a3]; dsimp only [m3]; rw [origin_val q.src a2]
    dsimp only [m2]; rw [width_val q.dim a1,dEq]
  have keep (z : ℤ) (lo : floor < z) (hi : z ≤ -21 ∨ z= -16 ∨ z= -15 ∨ 0 ≤ z) : x z=m z := by
    rw [vals _ lo]; simp only [update,srcPointer,srcStride,dstPointer,dstStride]
    split_ifs <;> omega
  obtain ⟨t,ct,o,rt,hit,miss,fr⟩ := tilePass_run q.copy hd stride x
    (by simp [vals (-2) (by decide),update]) (by simp [vals (-3) (by decide),update])
    (by simp [vals srcPointer (by decide),update]) (by simp [vals srcStride (by decide),update])
    (by simp [vals dstPointer (by decide),update]) (by simp [vals dstStride (by decide),update])
    guard unit fitD fitS apart
  refine ⟨_,by simpa [Job.cost,dEq] using Nat.add_le_add_left ct (setupCost q.setup),o,.seq run rt,?_,?_,?_⟩
  · intro i hi j hj
    rw [hit i hi j hj]
    exact congrArg (fun y : ℤ => if q.copy then y else 0) (keep _ (by unfold floor; omega) (by omega))
  · intro z outside
    exact (miss z outside).trans (keep _ (by unfold floor; omega) (by omega))
  · intro z lo hi
    exact (fr z (Or.inr ⟨lo,by omega⟩) (by omega)).trans (keep _ lo (by omega))

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareBoundary -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

def lookup {n : ℕ} (A : Square (Fin n)) (i j : ℕ) : ℤ :=
  if hi : i<n then if hj : j<n then A ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0

def TileAt (m : IntegerRAM.Memory) (base stride D : ℕ) (f : ℕ → ℕ → ℤ) :=
  ∀ i<D, ∀ j<D, m (offset base stride i j)=f i j

def Outside (m o : IntegerRAM.Memory) (base length : ℕ) :=
  ∀ z : ℕ, z<base ∨ base+length ≤ z → o z=m z

theorem offset_range {base stride D i j : ℕ} (hi : i<D) (hj : j<stride) :
    base ≤ offset base stride i j ∧ offset base stride i j<base+stride*D := by
  have h := Nat.mul_le_mul_left stride hi
  rw [Nat.mul_succ] at h
  dsimp [offset]
  omega

theorem Persistent.trans {m x o : IntegerRAM.Memory} (h₁ : Persistent m x) (h₂ : Persistent x o) :
    Persistent m o := fun z lo hi => (h₂ z lo hi).trans (h₁ z lo hi)

theorem Outside.trans {m x o : IntegerRAM.Memory} {base length : ℕ} (h₁ : Outside m x base length)
    (h₂ : Outside x o base length) : Outside m o base length := fun z hz => (h₂ z hz).trans (h₁ z hz)

theorem fitsGuard {W M D : ℕ} (cap : Room W M) (hd : D ≤ M) :
    ∀ j : ℕ, j ≤ D → Fits W ((j:ℤ)-D) := fun _ _ => cap _ (by omega) (by omega)

theorem fitsAddr {W M D base stride : ℕ} (cap : Room W M) (strideOk : D ≤ stride)
    (hi : base+stride*D ≤ M) : ∀ i<D, ∀ j<D, Fits W (offset base stride i j) := by
  intro i iD j jD
  have hh := (offset_range (base:=base) iD (jD.trans_le strideOk)).2
  exact cap _ (by omega) (by omega)

theorem ingest_run {W M : ℕ} (cap : Room W M) (a : Anchors) (m : IntegerRAM.Memory) (ready : a.ready m)
    (rawPos : 0<a.raw) (lePad : a.raw ≤ a.pad) (padM : a.pad ≤ M) (src : Origin) (k : ℕ)
    (A : Square (Fin a.raw)) (input : TileAt m (src.val a) a.raw a.raw (lookup A))
    (below : src.val a+a.raw*a.raw ≤ (Origin.bank k).val a)
    (room : (Origin.bank k).val a+a.pad*a.pad ≤ M) :
    ∃ t, t ≤ (fillBank k).cost a+(copyInto src k).cost a ∧ ∃ out, Runs W (ingest src k) m t out ∧
      a.ready out ∧ Persistent m out ∧ TileAt out ((Origin.bank k).val a) a.pad a.pad (lookup A) ∧
      Outside m out ((Origin.bank k).val a) (a.pad*a.pad) := by
  let base := (Origin.bank k).val a
  have hp := rawPos.trans_le lePad
  have unit := fitsGuard (D:=1) cap (by omega)
  have fD := fitsAddr cap (le_refl a.pad) room
  have fS := fitsAddr cap (le_refl a.raw) (below.trans (show (Origin.bank k).val a ≤ M by omega))
  obtain ⟨t,ct,x,rx,write,mx,px⟩ := (fillBank k).run a m ready a.pad rfl hp le_rfl
    (fitsGuard cap padM) unit fD (by simp [fillBank]) (by simp [fillBank])
  have outsideX : Outside m x base (a.pad*a.pad) := by
    intro z hz
    apply mx
    intro i hi j hj
    have h := offset_range (base:=base) hi hj
    change z≠offset base a.pad i j
    omega
  have sourceX : TileAt x (src.val a) a.raw a.raw (lookup A) := by
    intro i hi j hj
    exact (outsideX _ (Or.inl ((offset_range hi hj).2.trans_le below))).trans (input i hi j hj)
  obtain ⟨s,cs,o,ro,copy,miss,po⟩ := (copyInto src k).run a x (a.of_persistent px ready) a.raw rfl rawPos lePad
    (fitsGuard cap (lePad.trans padM)) unit (fun i hi j hj => fD i (hi.trans_le lePad) j (hj.trans_le lePad))
    (fun _ => fS) (by
      intro _ i hi j hj u hu v hv eq
      exact (not_lt_of_ge (offset_range (base:=base) (hi.trans_le lePad) (hj.trans_le lePad)).1)
        (eq ▸ (offset_range (base:=src.val a) hu hv).2.trans_le below))
  have both := px.trans po
  refine ⟨_,Nat.add_le_add ct cs,o,.seq rx ro,a.of_persistent both ready,both,?_,outsideX.trans ?_⟩
  · intro i hi j hj
    by_cases inRaw : i<a.raw ∧ j<a.raw
    · exact (copy i inRaw.1 j inRaw.2).trans (sourceX i inRaw.1 j inRaw.2)
    · have keep := miss (offset base a.pad i j) (fun u hu v hv eq => by
        obtain ⟨rfl,rfl⟩ := offset_inj hj (hv.trans_le lePad) eq
        exact inRaw ⟨hu,hv⟩)
      have zero : x (offset base a.pad i j)=0 := write i hi j hj
      rw [keep,zero]
      simp only [lookup]
      split_ifs <;> simp_all
  · intro z hz
    apply miss
    intro i hi j hj
    have h := offset_range (base:=base) (hi.trans_le lePad) (hj.trans_le lePad)
    change z≠offset base a.pad i j
    omega

theorem get_padded {b h n base : ℕ} (k : Fin 3) (A : Square (Fin n)) (m : IntegerRAM.Memory)
    (loaded : TileAt m (base+k.val*(b^h*b^h)) (b^h) (b^h) (lookup A)) :
    WordLayout.get (heap m) base b h 1 k 0=padRadix A := by
  funext i j
  let u := ((radix b h) i).val
  let v := ((radix b h) j).val
  change m (addr base (k,(0:Fin 1),i,j))=_
  rw [address_formula]
  have eq : base+((k.val*1+0)*(b^h)+u)*(b^h)+v = offset (base+k.val*(b^h*b^h)) (b^h) u v := by
    dsimp only [offset]; ring
  change m ((base+((k.val*1+0)*(b^h)+u)*(b^h)+v:ℕ):ℤ)=_
  rw [eq,loaded _ ((radix b h) i).isLt _ ((radix b h) j).isLt]
  dsimp only [lookup,padRadix,decodeIndex,u,v]
  split_ifs <;> rfl

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareBootstrap -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

def outerFrame (m x : IntegerRAM.Memory) := ∀ z : ℤ, -44 ≤ z → z ≤ -30 → x z=m z

theorem startSquare_run {W M b : ℕ} (cap : Room W M) (hb : 2 ≤ b) (s : ℤ)
    (a : Anchors) (hn : 1 ≤ a.raw) (dim : a.pad=b^(depth b a.raw)) (work : a.work=a.result+a.raw*a.raw)
    (room : a.pad ≤ M) (m : IntegerRAM.Memory)
    (nreg : m rawSide=a.raw) (lhs : m lhsPtr=a.lhs) (rhs : m rhsPtr=a.rhs) (res : m resultPtr=a.result) :
    ∃ o, Runs W (startSquare b s) m ((2+(depth b a.raw)*padSteps b s)+setupCost chooseArea) o ∧
      a.ready o ∧ heap o=heap m ∧ outerFrame m o ∧ o scaleReg=s^(depth b a.raw) := by
  have leD := (depth_bounds hb hn).1
  obtain ⟨x,r,xs,xc,fr⟩ := padding_depth hb hn s m nreg (fun j hj => by
    have up := Nat.pow_le_pow_right (by omega : 0 < b) hj
    have pos : 0 < b^j := Nat.pow_pos (by omega)
    apply cap <;> omega)
  obtain ⟨o,ro,fo⟩ := setup_runs chooseArea x (W:=W) (by
    simp [chooseArea,setupSafe,Expr.safe,plus,times,floor])
  have desc (z : ℤ) (lo : floor < z) : o z=update (update x padSide (a.pad:ℤ)) workPtr (a.work:ℤ) z := by
    rw [fo _ lo]
    simp [chooseArea,setupEval,Expr.val,plus,times,fr resultPtr (by decide) (by decide) (by decide) (by decide),
      fr rawSide (by decide) (by decide) (by decide) (by decide),nreg,res,update,xs,dim,work]
  have keep (z : ℤ) (lo : floor < z) (skip₁ : z≠padSide) (skip₂ : z≠workPtr) : o z=x z := by
    simp only [desc z lo,update,if_neg skip₁,if_neg skip₂]
  have whole (z : ℤ) (lo : floor < z) (away : z ≤ -30 ∨ 0 ≤ z) : o z=m z := by
    exact (keep _ lo (by change z≠ -16; omega) (by change z≠ -21; omega)).trans
      (fr _ lo (by omega) (by unfold scaleReg; omega) (by unfold paddingTest; omega))
  refine ⟨o,.seq r ro,⟨(whole _ (by decide) (by decide)).trans nreg,?_,?_,
    (whole _ (by decide) (by decide)).trans lhs,(whole _ (by decide) (by decide)).trans rhs,
    (whole _ (by decide) (by decide)).trans res⟩,funext (fun z : ℕ => whole z (by unfold floor; omega) (by omega)),
    (fun z lo hi => whole z (by unfold floor; omega) (Or.inl hi)),(keep _ (by decide) (by decide) (by decide)).trans xc⟩
  · simp [desc _ (by decide : floor < padSide),update]
  · simp [desc _ (by decide : floor < workPtr),update]

theorem pointCore_run {W : ℕ} (a : Anchors) (m : IntegerRAM.Memory) (h : a.ready m) :
    ∃ o, Runs W (setupCode pointCore) m (setupCost pointCore) o ∧
      lowOK a.work 1 a.pad o ∧ heap o=heap m ∧ Persistent m o := by
  obtain ⟨o,run,fr⟩ := setup_runs pointCore m (W:=W) (by simp [pointCore,setupSafe,Expr.safe,floor])
  have eq (z : ℤ) (lo : floor < z) : o z=update (update (update m (-1) (a.work:ℤ)) (-2) 1) (-3) (a.pad:ℤ) z := by
    rw [fr _ lo]; simp [pointCore,setupEval,Expr.val,update,h.2.2.1,h.2.1]
  refine ⟨o,run,⟨by simp [eq (-1) (by decide),update],by simp [eq (-2) (by decide),update],by simp [eq (-3) (by decide),update]⟩,?_,?_⟩
  · funext z
    rw [heap,heap,eq _ (by unfold floor; omega)]
    simp only [update,if_neg (by omega : (z:ℤ)≠ -3),if_neg (by omega : (z:ℤ)≠ -2),if_neg (by omega : (z:ℤ)≠ -1)]
  · intro z lo hi
    rw [eq _ lo]
    simp only [update,if_neg (by omega : z≠ -3),if_neg (by omega : z≠ -2),if_neg (by omega : z≠ -1)]

def Persistent.outer {m o : IntegerRAM.Memory} (p : Persistent m o) : outerFrame m o :=
  fun z lo hi => p z (by unfold floor; omega) (Or.inl (by omega))

def CallerFrame.persistent {m o : IntegerRAM.Memory} (p : CallerFrame m o) : Persistent m o :=
  fun z lo hi => p z lo (by omega)

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareMultiply -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

/-- One fixed native instruction program for ordinary contiguous row-major matrices.
Place the output after both inputs and the reusable workspace immediately after it. -/
theorem multiply_run {b r W M : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hr : 0<r) (cap : Room W M)
    (a : Anchors) (hn : 1 ≤ a.raw) (dim : a.pad=b^(depth b a.raw)) (area : a.work=a.result+a.raw*a.raw)
    (leftBefore : a.lhs+a.raw*a.raw ≤ a.result) (rightBefore : a.rhs+a.raw*a.raw ≤ a.result)
    (spaceFit : a.work+space b r (depth b a.raw) 1 ≤ M) (m : IntegerRAM.Memory)
    (nreg : m rawSide=a.raw) (lhs : m lhsPtr=a.lhs) (rhs : m rhsPtr=a.rhs) (res : m resultPtr=a.result)
    (A B : Square (Fin a.raw)) (left : TileAt m a.lhs a.raw a.raw (lookup A))
    (right : TileAt m a.rhs a.raw a.raw (lookup B)) :
    ∃ t, t ≤ runtimeCost S a ∧ ∃ o, Runs W (multiply S) m t o ∧
      (∀ i j : Fin a.raw, o (offset a.result a.raw i j)=S.scale^(depth b a.raw)*(A*B) i j) ∧
      (∀ z : ℕ, z<a.result → o z=m z) ∧ outerFrame m o ∧ o scaleReg=S.scale^(depth b a.raw) := by
  let h := depth b a.raw
  change a.work+space b r h 1 ≤ M at spaceFit
  have lePad : a.raw ≤ a.pad := dim ▸ (depth_bounds hb hn).1
  have ds : a.work+3*(a.pad*a.pad) ≤ M := by
    have sz := size_le_space b r h 1
    simp only [WordLayout.size,plane,Nat.one_mul] at sz
    change a.pad=b^h at dim
    rw [←dim] at sz
    omega
  have pm : a.pad ≤ M := by
    have sz := (size_ge (b:=b) (by omega) h 1 (by decide)).1
    have sp := size_le_space b r h 1
    change a.pad=b^h at dim
    rw [←dim] at sz
    omega
  obtain ⟨x,rx,cx,fx,outer,scale⟩ := startSquare_run cap hb S.scale a hn dim area pm m nreg lhs rhs res
  have passLeft : TileAt x a.lhs a.raw a.raw (lookup A) := fun i hi j hj =>
    (congrFun fx _).trans (left i hi j hj)
  obtain ⟨l,cl,y,ry,cy,py,ly,fy⟩ := ingest_run cap a x cx hn lePad pm .left 0 A passLeft
    (by simp [Origin.val]; omega) (by simp [Origin.val]; omega)
  have pastY (z : ℕ) (hz : z<a.work) : y z=m z :=
    (fy z (Or.inl (by simpa [Origin.val] using hz))).trans (congrFun fx z)
  have passRight : TileAt y a.rhs a.raw a.raw (lookup B) := fun i hi j hj =>
    (pastY _ (by have := (offset_range (base:=a.rhs) hi hj).2; omega)).trans (right i hi j hj)
  obtain ⟨s,cs,v,rv,cv,pv,bv,fv⟩ := ingest_run cap a y cy hn lePad pm .right 1 B passRight
    (by simp [Origin.val]; omega) (by simp [Origin.val]; omega)
  have pastV (z : ℕ) (hz : z<a.work+a.pad*a.pad) : v z=y z :=
    fv z (Or.inl (by simpa [Origin.val] using hz))
  obtain ⟨w,rw',cw,fw,pw⟩ := pointCore_run (W:=W) a v cv
  have al : TileAt w (a.work+0*(b^h*b^h)) (b^h) (b^h) (lookup A) := by
    change a.pad=b^h at dim
    rw [←dim]
    intro i hi j hj
    have hloc := (offset_range (base:=(Origin.bank 0).val a) hi hj).2
    simp only [Origin.val,Nat.zero_mul,Nat.add_zero] at hloc ⊢
    exact (congrFun fw _).trans ((pastV _ hloc).trans (by simpa [Origin.val] using ly i hi j hj))
  have bl : TileAt w (a.work+1*(b^h*b^h)) (b^h) (b^h) (lookup B) := by
    change a.pad=b^h at dim
    rw [←dim]
    exact fun i hi j hj => (congrFun fw _).trans (bv i hi j hj)
  have la := get_padded (b:=b) (h:=h) (base:=a.work) (0:Fin 3) A w al
  have lb := get_padded (b:=b) (h:=h) (base:=a.work) (1:Fin 3) B w bl
  have hh : 0<h := by dsimp [h,depth]; omega
  obtain ⟨c,cc,z,rz,hz,pz⟩ := core_runs S hb hr cap hh (by decide : 0<1) spaceFit w (dim ▸ cw)
  have prior := ((py.trans pv).trans pw).trans pz.persistent
  have cz := a.of_persistent prior cx
  have zp (i j : Fin a.raw) : z (offset ((Origin.bank 2).val a) a.pad i j)=S.scale^h*(A*B) i j := by
    have loc : offset ((Origin.bank 2).val a) a.pad i j = addr a.work (2,(0:Fin 1),includeIndex hb hn i,includeIndex hb hn j) := by
      rw [address_root_output hb hn]; simp only [Origin.val,offset,dim]; ring
    rw [loc]
    change heap z _=_
    rw [hz]
    change WordLayout.get (BlockMM.WordLayout.run S h 1 a.work (heap w)) a.work b h 1 2 0 (includeIndex hb hn i) (includeIndex hb hn j)=_
    rw [run_result,la,lb]
    exact (runRadix_eq S hb hn A B i j).trans (scaled_exact S hb hn A B i j)
  have fD := fitsAddr cap (le_refl a.raw) (show a.result+a.raw*a.raw ≤ M by omega)
  have fS := fitsAddr cap lePad (show (Origin.bank 2).val a+a.pad*a.raw ≤ M by
    have e := Nat.mul_le_mul_left a.pad lePad; dsimp [Origin.val]; omega)
  obtain ⟨u,cu,o,ru,hit,miss,po⟩ := emitJob.run a z cz a.raw rfl hn le_rfl
    (fitsGuard cap (lePad.trans pm)) (fitsGuard cap (hn.trans (lePad.trans pm))) fD (fun _ => fS)
    (by
      intro _ i hi j hj p hp q hq eq
      have d := (offset_range (base:=a.result) hi hj).2
      have s := (offset_range (base:=(Origin.bank 2).val a) hp (hq.trans_le lePad)).1
      change offset a.result a.raw i j=offset ((Origin.bank 2).val a) a.pad p q at eq
      dsimp only [Origin.val] at s eq
      omega)
  refine ⟨_,Nat.add_le_add_left (Nat.add_le_add cl (Nat.add_le_add cs (Nat.add_le_add_left
    (Nat.add_le_add cc cu) _))) _,o,.seq rx (.seq ry (.seq rv (.seq rw' (.seq rz ru)))),?_,?_,?_,?_⟩
  · intro i j
    exact (hit i i.isLt j j.isLt).trans (zp i j)
  · intro p hp
    have hz0 := (congrFun hz p).trans (run_frame S h 1 a.work (heap w) p (Or.inl (by omega)))
    exact (miss p (fun i hi j hj eq => by have := (offset_range (base:=a.result) hi hj).1; change p=offset a.result a.raw i j at eq; omega)).trans
      (hz0.trans ((congrFun fw p).trans ((pastV p (by omega)).trans (pastY p (by omega)))))
  · exact fun q lo hi => ((prior.trans po).outer q lo hi).trans (outer q lo hi)
  · exact ((prior.trans po) scaleReg (by decide) (by decide)).trans scale

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareProjectionCall -/
section
namespace VWZClique.IntegerRAM.Projected
open Structured BlockMM BlockMM.WordLayout
namespace SquareCaller
open SquareCode.Layout

private theorem flat_index {s : ℕ} (i j : Fin s) : (finProdFinEquiv (i,j)).val=s*i.val+j.val := by
  simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]

theorem tiled {s base : ℕ} {A : Tile s} {m : IntegerRAM.Memory} (h : bank m base A) : TileAt m base s s (lookup A) := by
  intro i hi j hj
  let u : Fin s := ⟨i,hi⟩
  let v : Fin s := ⟨j,hj⟩
  have eq := h (finProdFinEquiv (u,v))
  simpa [flat_index,offset,flat,u,v,lookup,hi,hj,add_comm] using eq

private theorem bank_kept {s base bound : ℕ} (A : Tile s) {m x : IntegerRAM.Memory} (source : bank m base A)
    (below : base+s*s ≤ bound) (fr : ∀ z : ℕ, z<bound → x z=m z) : bank x base A := by
  intro i
  exact (fr _ (by have := i.isLt; omega)).trans (source i)

/-- Discharge the concrete square-call interface for the projected contraction. -/
theorem verifiedPublicationStep {b r W M s t : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hr : 0<r)
    (hs : 1 ≤ s) (room : Room W M) (l : Projected.Layout) (A : Tile s) (B C : Fin t → Tile s)
    (leftB : l.lhs+t*(s*s) ≤ l.prod) (rightB : l.rhs+t*(s*s) ≤ l.prod)
    (weightB : l.wt+s*s ≤ l.prod) (keep : l.preserve ≤ l.prod)
    (workspace : l.prod+s*s+space b r (depth b s) 1 ≤ M) :
    SquareRun W (duration S s) (S.scale^(depth b s)) (multiply S) l A B C := by
  intro p m tables lhs rhs prod side
  let a : Anchors := ⟨s,b^(depth b s),l.prod+s*s,l.lhs+p.val*(s*s),l.rhs+p.val*(s*s),l.prod⟩
  have ptr (base : ℕ) (all : base+t*(s*s) ≤ l.prod) (p : Fin t) : base+p.val*(s*s)+s*s ≤ l.prod := by
    have eq := Nat.mul_le_mul_right (s*s) p.isLt
    rw [Nat.succ_mul] at eq
    omega
  obtain ⟨f,hf,x,run,values,frame,reg,_⟩ := multiply_run S hb hr room a hs rfl rfl
    (ptr _ leftB p) (ptr _ rightB p) workspace m side lhs rhs prod (B p) (C p)
    (tiled (tables.left p)) (tiled (tables.right p))
  refine ⟨f,hf,x,run,?_,⟨bank_kept A tables.weights weightB frame,
    fun q => bank_kept (B q) (tables.left q) (ptr _ leftB q) frame,
    fun q => bank_kept (C q) (tables.right q) (ptr _ rightB q) frame⟩,reg,fun z hz => frame z (hz.trans_le keep)⟩
  intro i
  obtain ⟨⟨u,v⟩,rfl⟩ := finProdFinEquiv.surjective i
  simpa [flat_index,flat,offset,a,add_comm] using values u v

end SquareCaller
end VWZClique.IntegerRAM.Projected
end

open VWZClique VWZClique.IntegerRAM VWZClique.BlockMM VWZClique.BlockMM.WordLayout VWZClique.IntegerRAM.Structured VWZClique.IntegerRAM.Projected VWZClique.IntegerRAM.SquareCode VWZClique.IntegerRAM.SquareCode.Layout VWZClique.IntegerRAM.Projected.SquareCaller
/-- Discharge the concrete square-call interface for the projected contraction. -/
theorem solution {b r W M s t : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hr : 0<r)
    (hs : 1 ≤ s) (room : VWZClique.IntegerRAM.SquareCode.Layout.Room W M) (l : Projected.Layout) (A : Tile s) (B C : Fin t → Tile s)
    (leftB : l.lhs+t*(s*s) ≤ l.prod) (rightB : l.rhs+t*(s*s) ≤ l.prod)
    (weightB : l.wt+s*s ≤ l.prod) (keep : l.preserve ≤ l.prod)
    (workspace : l.prod+s*s+space b r (depth b s) 1 ≤ M) :
    SquareRun W (duration S s) (S.scale^(depth b s)) (multiply S) l A B C
  := by apply VWZClique.IntegerRAM.Projected.SquareCaller.verifiedPublicationStep <;> assumption
