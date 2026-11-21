-- Prove2me | solution 1 for VWZClique.scaled_matrix_multiplication_word_ram
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T13:25:45.07318+00:00
-- url     : https://prove2.me/submissions/efc1fac3-aac2-4b04-b58d-b20f96b92f70

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_TrulySubcubicAPSP_WordRAM

/- CliqueVM -/
section

/-! Simulation of bounded integer arithmetic, indirect addressing and branches on
    the fixed-width instruction interpreter used for clique counting. -/

namespace VWZClique.IntegerRAM
open TrulySubcubicAPSP

abbrev Memory := ℤ → ℤ

/-- Exact signed-word representability at positive width. -/
def Fits (W : ℕ) (x : ℤ) : Prop := -(2 : ℤ)^(W-1) ≤ x ∧ x < (2 : ℤ)^(W-1)

instance (W : ℕ) (x : ℤ) : Decidable (Fits W x) := inferInstanceAs (Decidable (_ ∧ _))

def update (m : Memory) (i x : ℤ) : Memory := fun a => if a = i then x else m a

def encode (W : ℕ) (m : Memory) : ℤ → BitVec W := fun a => BitVec.ofInt W (m a)

def input (ws : List ℤ) : Memory := fun a => if a < 0 then 0 else ws.getD a.toNat 0

/-- Execute the same instruction list with exact integer arithmetic. A signed
    indirect address or branch test must fit the target word. Arithmetic
    temporaries are unrestricted until used in one of these ways. -/
def checked (P : List Instr) (W : ℕ) : ℕ → ℕ → Memory → Option (Bool × Memory)
  | 0, _, _ => none
  | t+1, pc, m =>
    let write i x := checked P W t (pc+1) (update m i x)
    match P.getD pc .reject with
    | .one i => write i 1
    | .add i j k => write i (m j + m k)
    | .sub i j k => write i (m j - m k)
    | .mul i j k => write i (m j * m k)
    | .load i j => if Fits W (m j) then write i (m (m j)) else none
    | .store i j => if Fits W (m i) then write (m i) (m j) else none
    | .bltz i target =>
      if Fits W (m i) then checked P W t (if m i < 0 then target else pc+1) m else none
    | .accept => some (true,m)
    | .reject => some (false,m)

theorem encode_input (W : ℕ) (ws : List ℤ) : encode W (input ws) = loadWords W ws := by
  funext a
  by_cases h : a < 0 <;> simp [encode, input, loadWords, h]

theorem encode_update (W : ℕ) (m : Memory) (i x : ℤ) :
    encode W (update m i x) = fun a => if a = i then BitVec.ofInt W x else encode W m a := by
  funext a
  by_cases h : a = i <;> simp [encode, update, h]

theorem decode_fits {W : ℕ} (hw : 0 < W) {x : ℤ} (h : Fits W x) :
    (BitVec.ofInt W x).toInt = x := BitVec.toInt_ofInt_eq_self hw h.1 h.2

private theorem encode_sub (W : ℕ) (x y : ℤ) :
    BitVec.ofInt W (x-y) = BitVec.ofInt W x - BitVec.ofInt W y := by
  rw [sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

/-- A successful checked run has exactly the same fuel bound in the actual VM.
    The VM stores each exact integer modulo its word size. -/
theorem simulate {P : List Instr} {W : ℕ} (hw : 0 < W) {t pc : ℕ} {m out : Memory}
    {b : Bool} (h : checked P W t pc m = some (b,out)) :
    exec P t pc (encode W m) = some (b,encode W out) := by
  induction t generalizing pc m with
  | zero => simp [checked] at h
  | succ t ih =>
    cases hi : P.getD pc .reject with
    | one i =>
      have hr := ih (by simpa only [checked, hi] using h)
      simpa only [exec, hi, encode_update, BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat] using hr
    | add i j k =>
      have hr := ih (by simpa only [checked, hi] using h)
      simpa only [exec, hi, encode_update, BitVec.ofInt_add, encode] using hr
    | sub i j k =>
      have hr := ih (by simpa only [checked, hi] using h)
      simpa only [exec, hi, encode_update, encode_sub, encode] using hr
    | mul i j k =>
      have hr := ih (by simpa only [checked, hi] using h)
      simpa only [exec, hi, encode_update, BitVec.ofInt_mul, encode] using hr
    | load i j =>
      by_cases hf : Fits W (m j)
      · have hr := ih (by simpa only [checked, hi, if_pos hf] using h)
        simpa only [exec, hi, encode_update, encode, decode_fits hw hf] using hr
      · simp only [checked, hi, if_neg hf, reduceCtorEq] at h
    | store i j =>
      by_cases hf : Fits W (m i)
      · have hr := ih (by simpa only [checked, hi, if_pos hf] using h)
        simpa only [exec, hi, encode_update, encode, decode_fits hw hf] using hr
      · simp only [checked, hi, if_neg hf, reduceCtorEq] at h
    | bltz i target =>
      by_cases hf : Fits W (m i)
      · have hr := ih (by simpa only [checked, hi, if_pos hf] using h)
        simpa only [exec, hi, encode, decode_fits hw hf] using hr
      · simp only [checked, hi, if_neg hf, reduceCtorEq] at h
    | accept =>
      simp only [checked, hi, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      simp only [exec, hi]
    | reject =>
      simp only [checked, hi, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      simp only [exec, hi]

end VWZClique.IntegerRAM
end

/- LoopCompiler -/
section

open TrulySubcubicAPSP
namespace VWZClique.IntegerRAM.Structured

inductive Atom where
  | one (dst : ℤ)
  | add (dst a b : ℤ)
  | sub (dst a b : ℤ)
  | mul (dst a b : ℤ)
  | load (dst ptr : ℤ)
  | store (ptr src : ℤ)

def Atom.instruction : Atom → Instr
  | .one d => .one d
  | .add d a b => .add d a b
  | .sub d a b => .sub d a b
  | .mul d a b => .mul d a b
  | .load d p => .load d p
  | .store p s => .store p s

inductive Step (W : ℕ) : Atom → Memory → Memory → Prop where
  | one (m d) : Step W (.one d) m (update m d 1)
  | add (m d a b) : Step W (.add d a b) m (update m d (m a + m b))
  | sub (m d a b) : Step W (.sub d a b) m (update m d (m a - m b))
  | mul (m d a b) : Step W (.mul d a b) m (update m d (m a * m b))
  | load (m d p) (fit : Fits W (m p)) : Step W (.load d p) m (update m d (m (m p)))
  | store (m p s) (fit : Fits W (m p)) : Step W (.store p s) m (update m (m p) (m s))

inductive Command where
  | skip
  | atom (a : Atom)
  | seq (c d : Command)
  | whenNonnegative (reg : ℤ) (body : Command)
  | repeatWhileNegative (body : Command) (reg : ℤ)

def size : Command → ℕ
  | .skip => 0
  | .atom _ => 1
  | .seq c d => size c + size d
  | .whenNonnegative _ c => 1 + size c
  | .repeatWhileNegative c _ => size c + 1

/-- Compile one fixed loop body for all memory sizes. Branch targets are absolute. -/
def emit : Command → ℕ → List Instr
  | .skip, _ => []
  | .atom a, _ => [a.instruction]
  | .seq c d, pc => emit c pc ++ emit d (pc + size c)
  | .whenNonnegative reg c, pc => .bltz reg (pc + (1 + size c)) :: emit c (pc+1)
  | .repeatWhileNegative c reg, pc => emit c pc ++ [.bltz reg pc]

theorem emit_length (c : Command) (pc : ℕ) : (emit c pc).length = size c := by
  induction c generalizing pc <;> simp_all [size,emit,Nat.add_comm]

/-- Structured integer computation. The index counts primitive machine instructions,
including each guard or loop test. -/
inductive Runs (W : ℕ) : Command → Memory → ℕ → Memory → Prop where
  | skip (m) : Runs W .skip m 0 m
  | atom {a m m'} (s : Step W a m m') : Runs W (.atom a) m 1 m'
  | seq {c d m x out s t} (h : Runs W c m s x) (k : Runs W d x t out) :
      Runs W (.seq c d) m (s+t) out
  | guard_skip {reg c m} (hf : Fits W (m reg)) (hn : m reg < 0) :
      Runs W (.whenNonnegative reg c) m 1 m
  | guard_take {reg c m out t} (hf : Fits W (m reg)) (hn : ¬ m reg < 0)
      (run : Runs W c m t out) : Runs W (.whenNonnegative reg c) m (1+t) out
  | loop_done {reg c m out t} (run : Runs W c m t out) (hf : Fits W (out reg))
      (hn : ¬ out reg < 0) : Runs W (.repeatWhileNegative c reg) m (t+1) out
  | loop_again {reg c m x out s t} (body : Runs W c m s x) (hf : Fits W (x reg))
      (hn : x reg < 0) (more : Runs W (.repeatWhileNegative c reg) x t out) :
      Runs W (.repeatWhileNegative c reg) m (s+1+t) out

def At (p : List Instr) (pc : ℕ) (xs : List Instr) : Prop :=
  ∀ (i : ℕ) (hi : i < xs.length), p.getD (pc+i) .reject = xs[i]

private theorem at_left {p a b : List Instr} {pc} (h : At p pc (a++b)) : At p pc a := by
  intro i hi
  exact (h i (by simp; omega)).trans (List.getElem_append_left' hi b).symm

private theorem at_right {p a b : List Instr} {pc} (h : At p pc (a++b)) :
    At p (pc+a.length) b := by
  intro i hi
  have hh := (h (i+a.length) (by simp; omega)).trans (List.getElem_append_right' a hi).symm
  rwa [show pc+(i+a.length) = pc+a.length+i by omega] at hh

private theorem at_head {p xs : List Instr} {pc a} (h : At p pc (a::xs)) :
    p.getD pc .reject = a := by
  have hh := h 0 (by simp)
  rw [Nat.add_zero] at hh
  exact hh

private theorem at_tail {p xs : List Instr} {pc a} (h : At p pc (a::xs)) :
    At p (pc+1) xs := by
  intro i hi
  have hh := h (i+1) (by simp; omega)
  rw [show pc+(i+1) = pc+1+i by omega] at hh
  exact hh

private theorem step_run {W pc fuel : ℕ} {p : List Instr} {a m out}
    (h : Step W a m out) (hi : p.getD pc .reject = a.instruction) :
    checked p W (fuel+1) pc m = checked p W fuel (pc+1) out := by
  cases h <;> simp_all [checked,Atom.instruction]

/-- Compositional execution with exact step count, even when code is embedded
in a larger instruction list or a loop branches backwards. -/
theorem sound {W : ℕ} {c m out t} (h : Runs W c m t out) :
    ∀ {p : List Instr} (pc : ℕ), At p pc (emit c pc) → ∀ fuel : ℕ,
      checked p W (t+fuel) pc m = checked p W fuel (pc+size c) out := by
  induction h with
  | skip m => intro p pc hp fuel; simp [size]
  | atom hs =>
    intro p pc hp fuel
    simpa [size,Nat.add_comm 1 fuel] using step_run (fuel:=fuel) hs (at_head hp)
  | @seq c d m x o s t h k ih ik =>
    intro p pc hp fuel
    have ha : At p pc (emit c pc ++ emit d (pc+size c)) := hp
    have right := at_right ha
    rw [emit_length] at right
    rw [Nat.add_assoc,ih pc (at_left ha),ik _ right]
    simp [size,Nat.add_assoc]
  | @guard_skip reg c m hf hn =>
    intro p pc hp fuel
    have head := at_head hp
    rw [Nat.add_comm 1 fuel]
    simp only [checked,head,if_pos hf,if_pos hn,size]
  | @guard_take reg c m o t hf hn run ih =>
    intro p pc hp fuel
    have head := at_head hp
    have tail := at_tail hp
    rw [show 1+t+fuel = (t+fuel)+1 by omega]
    simp only [checked,head,if_pos hf,if_neg hn]
    rw [ih _ tail]
    simp [size,Nat.add_assoc]
  | @loop_done reg c m o t run hf hn ih =>
    intro p pc hp fuel
    have ha : At p pc (emit c pc ++ [.bltz reg pc]) := hp
    have right := at_right ha
    rw [emit_length] at right
    have head := at_head right
    rw [show t+1+fuel=t+(fuel+1) by omega, ih pc (at_left ha)]
    simp only [checked,head,if_pos hf,if_neg hn]
    simp [size,Nat.add_assoc]
  | @loop_again reg c m x o s t body hf hn more ih ik =>
    intro p pc hp fuel
    have ha : At p pc (emit c pc ++ [.bltz reg pc]) := hp
    have right := at_right ha
    rw [emit_length] at right
    have head := at_head right
    rw [show s+1+t+fuel=s+((t+fuel)+1) by omega,ih pc (at_left ha)]
    simp only [checked,head,if_pos hf,if_pos hn]
    exact ik pc hp fuel

def program (c : Command) := emit c 0 ++ [.accept]

/-- The final accepting instruction costs one further step. -/
theorem completes {W : ℕ} {c m t out} (h : Runs W c m t out) :
    checked (program c) W (t+1) 0 m = some (true,out) := by
  have whole : At (program c) 0 (emit c 0 ++ [.accept]) := by
    intro i hi
    simp [program,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
  have right := at_right whole
  rw [emit_length, Nat.zero_add] at right
  rw [sound h 0 (at_left whole), Nat.zero_add, checked, at_head right]

/-- The very same fixed native program runs in the published word model. -/
theorem word_program {W : ℕ} (hW : 0<W) {c m t out} (h : Runs W c m t out) :
    exec (program c) (t+1) 0 (encode W m) = some (true,encode W out) :=
  simulate hW (completes h)

end VWZClique.IntegerRAM.Structured
end

/- NativeSquareExpr -/
section

namespace VWZClique.IntegerRAM.SquareCode
open Structured

/-- Straight-line formulas for one kernel write, with address arithmetic and
indirect loads. Registers and heap cells above the scratch area are readable. -/
inductive Expr where
  | zero | one | reg (i : ℤ) | read (a : Expr)
  | add (a b : Expr) | sub (a b : Expr) | mul (a b : Expr)
deriving Inhabited

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

def binary (a b : Command) (op : Atom) := Command.seq a (.seq b (.atom op))

def Expr.code (d : ℤ) : Expr → Command
  | .zero => .atom (.sub d d d)
  | .one => .atom (.one d)
  | .reg i => .seq (.atom (.sub d d d)) (.atom (.add d d i))
  | .read a => .seq (a.code d) (.atom (.load d d))
  | .add a b => binary (a.code d) (b.code (d-1)) (.add d d (d-1))
  | .sub a b => binary (a.code d) (b.code (d-1)) (.sub d d (d-1))
  | .mul a b => binary (a.code d) (b.code (d-1)) (.mul d d (d-1))

def Expr.steps : Expr → ℕ
  | .zero | .one => 1
  | .reg _ => 2
  | .read a => a.steps+1
  | .add a b | .sub a b | .mul a b => a.steps+(b.steps+1)

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

def Expr.num : ℕ → Expr
  | 0 => .zero
  | n+1 => .add (num n) .one

def Expr.int : ℤ → Expr
  | .ofNat n => num n
  | .negSucc n => .sub .zero (num (n+1))

@[simp] theorem Expr.num_val (m : Memory) (n : ℕ) : (num n).val m=n := by
  induction n <;> simp_all [num,val]

@[simp] theorem Expr.int_val (m : Memory) (z : ℤ) : (int z).val m=z := by
  cases z <;> simp [int,val] <;> omega

@[simp] theorem Expr.num_safe (m : Memory) (d : ℤ) (W n : ℕ) : (num n).safe d W m := by
  induction n <;> simp_all [num,safe]

@[simp] theorem Expr.int_safe (m : Memory) (d : ℤ) (W : ℕ) (z : ℤ) : (int z).safe d W m := by
  cases z <;> simp [int,safe]

/-- Compute the destination and value independently then store one word.
The negative scratch segment may be overwritten. -/
def write (d : ℤ) (addr value : Expr) : Command :=
  .seq (addr.code d) (.seq (value.code (d-1)) (.atom (.store d (d-1))))

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

/- NativeSquareRegs -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout

/-- Read the data registers for one (parent, child-row, child-column) kernel.
All compiled formulas use scratch at or below register -128. -/
def base := Expr.reg (-1)
def nodes := Expr.reg (-2)
def side := Expr.reg (-3)
def node := Expr.reg (-4)
def row := Expr.reg (-5)
def col := Expr.reg (-6)
def floor : ℤ := -128

def num := Expr.num
def plus := Expr.add
def times := Expr.mul

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- CliqueBlockMM -/
section

/-! Fixed integer-coefficient bilinear schemes recursively multiply arbitrary
    tensor powers of their base dimension. Clearing the base coefficients'
    denominators introduces just one fixed scale factor per level. -/

namespace VWZClique.BlockMM
open scoped BigOperators

abbrev Square (I : Type*) := Matrix I I ℤ

def linear {b : ℕ} (L A : Square (Fin b)) : ℤ := ∑ i, ∑ j, L i j * A i j

/-- An integer bilinear multiplication scheme, possibly representing a rational
    scheme whose fixed denominators have been cleared. -/
structure Scheme (b r : ℕ) where
  left : Fin r → Square (Fin b)
  right : Fin r → Square (Fin b)
  out : Fin b → Fin b → Fin r → ℤ
  scale : ℤ
  correct : ∀ (A B : Square (Fin b)) (i j : Fin b),
    (∑ s, out i j s * (linear (left s) A * linear (right s) B)) = scale * (A*B) i j

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

/- DoubleEstimates -/
section

open VWZClique Real

namespace VWZClique.Double

theorem length_bound (σ : ℝ) (hσ : 0 < σ) :
    ∃ H : ℝ, 0 < H ∧ ∀ L : ℕ, (L:ℝ)+1 ≤ H * (((2:ℝ)^L)^σ) := by
  let a : ℝ := (2 : ℝ)^σ
  have ha : 1 < a := Real.one_lt_rpow (by norm_num) hσ
  have hd : 0 < a-1 := by linarith
  refine ⟨1+1/(a-1),by positivity,?_⟩
  intro L
  have hL := one_add_mul_sub_le_pow (by linarith : -1 ≤ a) L
  have haL : 1 ≤ a^L := one_le_pow₀ ha.le
  have hs : ((2 : ℝ)^L)^σ = a^L := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul_natCast (by norm_num)]
  rw [hs, add_mul, one_mul,one_div_mul_eq_div]
  have hfrac : (L : ℝ) ≤ a^L/(a-1) := (le_div_iff₀ hd).mpr (by linarith)
  linarith

end VWZClique.Double
end

/- MMUniform -/
section

namespace VWZClique.BlockMM

/-- Least upper-power padding is unnecessary: this explicit depth pads by at most a factor b. -/
def depth (b n : ℕ) : ℕ := Nat.log b n + 1

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

/-- For every exponent bounding the fixed rank, the shared block schedule at
arbitrary side n satisfies the positive-slack cost bound. -/
theorem uniform_budget {b r : ℕ} (hb : 2 ≤ b) (hr : b^2 ≤ r)
    (τ : ℝ) (hτ : 0 ≤ τ) (hrate : (r:ℝ) ≤ (b:ℝ)^τ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (scalarBudget b r (depth b n) : ℝ) ≤ C*(n:ℝ)^(τ+ε) := by
  obtain ⟨H,hH,hH'⟩ := Double.length_bound ε hε
  let D : ℝ := 1+6*(b:ℝ)^2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D*H*(b:ℝ)^(τ+ε),by positivity,?_⟩
  intro n hn
  let h := depth b n
  have hp : (b^h:ℕ) ≤ b*n := (depth_bounds hb hn).2
  have hp' : (b:ℝ)^h ≤ (b:ℝ)*n := by exact_mod_cast hp
  have htwo : (2:ℝ)^h ≤ (b:ℝ)^h := by gcongr; exact_mod_cast hb
  have hlin : 1+6*(b:ℝ)^2*h ≤ D*(H*((b:ℝ)^h)^ε) := by
    calc
      _ ≤ D*((h:ℝ)+1) := by dsimp [D]; nlinarith [sq_nonneg (b:ℝ), Nat.cast_nonneg (α := ℝ) h]
      _ ≤ _ := mul_le_mul_of_nonneg_left ((hH' h).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) htwo hε.le) hH.le)) hD.le
  have hpow : (r:ℝ)^h ≤ ((b:ℝ)^h)^τ := by
    rw [← pow_swap _ (by positivity)]
    exact pow_le_pow_left₀ (by positivity) hrate h
  have hs := scalarBudget_le hr h
  have hs' : (scalarBudget b r h : ℝ) ≤ (1+6*(b:ℝ)^2*h)*(r:ℝ)^h := by exact_mod_cast hs
  calc
    _ ≤ _ := hs'.trans (mul_le_mul hlin hpow (by positivity) (by positivity))
    _ = D*H*(((b:ℝ)^h)^(τ+ε)) := by
      rw [Real.rpow_add (by positivity)]; ring
    _ ≤ D*H*(((b:ℝ)*n)^(τ+ε)) := by
      gcongr
    _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring

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

/-- One level contains three contiguous banks, each storing N row-major square matrices. -/
def plane (b h N : ℕ) := N*(b^h*b^h)
def size (b h N : ℕ) := 3*plane b h N

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

/-- Number of cells in all breadth-first layers. -/
def space (b r : ℕ) : (h N : ℕ) → ℕ
  | 0,N => size b 0 N
  | h+1,N => size b (h+1) N + space b r h (N*r)

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

/- MMWordLayoutSweep -/
section

namespace VWZClique.BlockMM.WordLayout

/-- A single mutable-word write in the mathematical memory model. -/
def store (m : Memory) (a : ℕ) (z : ℤ) : Memory := fun t => if t=a then z else m t

/-- Sequential increasing-address sweep. Each right hand side reads the current memory. -/
def sweep (base : ℕ) (image : Memory → Memory) : ℕ → Memory → Memory
  | 0,m => m
  | q+1,m => let cur := sweep base image q m
             store cur (base+q) (image cur (base+q))

/-- Invariant after one prefix of a same-level sweep. -/
def written (m target : Memory) (base count : ℕ) : Memory := fun a =>
  if base≤a ∧ a<base+count then target a else m a

theorem written_out (m target : Memory) (base q a : ℕ) (ha : a<base ∨ base+q≤a) :
    written m target base q a = m a := if_neg (by omega)

theorem written_same (m target : Memory) (base count a : ℕ) (hh : target a = m a) :
    written m target base count a = m a := by simp [written,hh]

private theorem sweep_written (image : Memory → Memory) (base len : ℕ) (m : Memory)
    (stable : ∀ q < len, image (written m (image m) base q) (base+q) = image m (base+q)) :
    sweep base image len m = written m (image m) base len := by
  induction len with
  | zero => funext a; simp [sweep,written]
  | succ n ih =>
    rw [sweep,ih (fun q hq => stable q (by omega)),stable n (by omega)]
    funext a
    by_cases ha : a=base+n
    · subst a
      simp [store,written]
    · have hiff : (base≤a ∧ a<base+n+1) ↔ (base≤a ∧ a<base+n) := by omega
      simp only [store,if_neg ha,written,Nat.add_succ,hiff]

/-- A packed layer can be written word by word if each word retains its value under the preceding writes. -/
theorem sweep_put (base b h N : ℕ) (g : Memory → Fin 3 → Fin N → Square (Index b h)) (m : Memory)
    (stable : ∀ (k : Fin 3) (p : Fin N) (i j : Index b h),
      g (written m (put m base b h N (g m)) base ((packing b h N) (k,p,i,j)).val) k p i j = g m k p i j) :
    sweep base (fun cur => put cur base b h N (g cur)) (size b h N) m = put m base b h N (g m) := by
  let image (cur : Memory) := put cur base b h N (g cur)
  have step (q : ℕ) (hq : q<size b h N) :
      image (written m (image m) base q) (base+q)=image m (base+q) := by
    obtain ⟨⟨k,p,i,j⟩,hx⟩ := (packing b h N).surjective (⟨q,hq⟩ : Fin (size b h N))
    have he : ((packing b h N) (k,p,i,j)).val=q := congrArg Fin.val hx
    subst q
    let cur := written m (image m) base ((packing b h N) (k,p,i,j)).val
    exact (get_put cur base b h N (g cur) k p i j).trans
      ((stable k p i j).trans (get_put m base b h N (g m) k p i j).symm)
  rw [sweep_written image base _ m step]
  funext a
  by_cases ha : base≤a ∧ a<base+size b h N
  · simp [written,ha,image]
  · have hf : image m a=m a := put_outside _ _ _ _ _ _ _ (by omega)
    simp [written,ha,image] at hf ⊢
    exact hf.symm

end VWZClique.BlockMM.WordLayout
end

/- NativeSquareSweep -/
section

namespace VWZClique.BlockMM.WordLayout

theorem down_sweep {b r : ℕ} (S : Scheme b r) (h N base : ℕ) (m : Memory) :
    sweep (base+size b (h+1) N) (down S h N base) (size b h (N*r)) m = down S h N base m := by
  unfold down
  apply sweep_put
  intro k p i j
  have eq (t : Fin 3) (v : Fin N) (a d : Index b (h+1)) (q : ℕ) (target : Memory) :
      get (written m target (base+size b (h+1) N) q) base b (h+1) N t v a d =
        get m base b (h+1) N t v a d := written_out _ _ _ _ _ (Or.inl (addr_range _ _).2)
  have eq' (t : Fin 3) (v : Fin N) (q : ℕ) (target : Memory) :
      get (written m target (base+size b (h+1) N) q) base b (h+1) N t v =
        get m base b (h+1) N t v := by funext a d; exact eq t v a d q target
  simp only [eq']

theorem leaf_sweep (b N base : ℕ) (m : Memory) :
    sweep base (leaf b N base) (size b 0 N) m = leaf b N base m := by
  unfold leaf
  apply sweep_put
  intro k p i j
  have preserved (t : Fin 3) (ht : t ≠ 2) (a d : Index b 0) (q : ℕ) :
      get (written m (leaf b N base m) base q) base b 0 N t p a d = get m base b 0 N t p a d := by
    apply written_same
    change get (leaf b N base m) base b 0 N t p a d = _
    rw [leaf,get_put,leafValue,if_neg ht]
    rfl
  change leafValue b N base (written m (leaf b N base m) base _) k p i j = _
  by_cases hk : k=2
  · simp only [leafValue,if_pos hk]
    exact congrArg₂ (·*·) (preserved 0 (by decide) i () _) (preserved 1 (by decide) () j _)
  · simp only [leafValue,if_neg hk,preserved k hk]

theorem up_sweep {b r : ℕ} (S : Scheme b r) (h N base : ℕ) (m : Memory) :
    sweep base (up S h N base) (size b (h+1) N) m = up S h N base m := by
  unfold up
  apply sweep_put
  intro k p i j
  let q := ((packing b (h+1) N) (k,p,i,j)).val
  let next := base+size b (h+1) N
  have hq : q ≤ size b (h+1) N := ((packing b (h+1) N) (k,p,i,j)).isLt.le
  have children (s : Fin r) :
      get (written m (up S h N base m) base q) next b h (N*r) 2 (child p s) i.2 j.2 =
        get m next b h (N*r) 2 (child p s) i.2 j.2 :=
    written_out _ _ _ _ _ (Or.inr ((Nat.add_le_add_left hq base).trans (addr_range _ _).1))
  change upValue S h N base (written m (up S h N base m) base q) k p i j = _
  by_cases hk : k=2
  · simp only [upValue,if_pos hk]
    exact Finset.sum_congr rfl fun s _ => congrArg (S.out i.1 j.1 s * ·) (children s)
  · simp only [upValue,if_neg hk]
    apply written_same
    change get (up S h N base m) base b (h+1) N k p i j = _
    rw [up,get_put,upValue,if_neg hk]
    rfl

/-- Recursive square multiplication with each level update executed as
a sequence of single writes that reads its current memory. -/
def mutableRun {b r : ℕ} (S : Scheme b r) : (h N base : ℕ) → Memory → Memory
  | 0,N,base,m => sweep base (leaf b N base) (size b 0 N) m
  | h+1,N,base,m =>
      let next := base+size b (h+1) N
      let kids := sweep next (down S h N base) (size b h (N*r)) m
      sweep base (up S h N base) (size b (h+1) N) (mutableRun S h (N*r) next kids)

theorem mutableRun_eq {b r : ℕ} (S : Scheme b r) (h N base : ℕ) (m : Memory) :
    mutableRun S h N base m = run S h N base m := by
  induction h generalizing N base m with
  | zero => exact leaf_sweep _ _ _ _
  | succ h ih => simp only [mutableRun,up_sweep,down_sweep,ih,run]

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

/-- Address in bank-major, node-major, row-major order. -/
def atWord (start count len bank p i j : Expr) : Expr :=
  plus start (plus (times (plus (times (plus (times bank count) p) len) i) len) j)

def parentSide (b : ℕ) := times (num b) side
def next (b : ℕ) := plus base (times (times (times (num 3) nodes) (parentSide b)) (parentSide b))
def parentCell {b : ℕ} (k : Fin 3) (a d : Fin b) : Expr :=
  atWord base nodes (parentSide b) (num k) node (plus (times (num a) side) row)
    (plus (times (num d) side) col)
def childCell (b r : ℕ) (k : Fin 3) (s : Fin r) : Expr :=
  atWord (next b) (times nodes (num r)) side (num k) (plus (times node (num r)) (num s)) row col

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

def sumFin : (n : ℕ) → (Fin n → Expr) → Expr
  | 0,_ => .zero
  | n+1,f => .add (f 0) (sumFin n (fun i => f i.succ))

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

def downVal {b : ℕ} (k : Fin 3) (w : Square (Fin b)) :=
  sumFin b fun a => sumFin b fun d => times (.int (w a d)) (.read (parentCell k a d))
def upVal {b r : ℕ} (S : Scheme b r) (a d : Fin b) :=
  sumFin r fun s => times (.int (S.out a d s)) (.read (childCell b r 2 s))

def natMem (m : IntegerRAM.Memory) : WordLayout.Memory := fun n => m n

/-- The code for one transformed child input is a fixed instruction sequence
depending only on scheme coefficients and the bank and rank slot. -/
def downCode {b r : ℕ} (k : Fin 3) (s : Fin r) (w : Square (Fin b)) :=
  write floor (childCell b r k s) (downVal k w)

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

def upCode {b r : ℕ} (S : Scheme b r) (a d : Fin b) :=
  write floor (parentCell 2 a d) (upVal S a d)

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

/- CliqueStructured -/
section

/-! Composition of fixed, bounded integer loops for the published clique VM. -/

namespace VWZClique.IntegerRAM.Structured
open TrulySubcubicAPSP

/-- Advance a counter and test whether the next iteration is still below the limit. -/
def tick (i one limit test : ℤ) : Command :=
  .seq (.atom (.add i i one)) (.atom (.sub test i limit))

def nextMemory (m : Memory) (i test : ℤ) (q N : ℕ) : Memory :=
  update (update m i ((q:ℤ)+1)) test (((q:ℤ)+1)-N)

theorem tick_runs {W : ℕ} {i one limit test : ℤ} {q N : ℕ} {m : Memory}
    (hneq : limit ≠ i) (hi : m i = (q:ℤ)) (h1 : m one = 1) (hn : m limit = (N:ℤ)) :
    Runs W (tick i one limit test) m 2 (nextMemory m i test q N) := by
  have hs := Runs.seq (Runs.atom (Step.add (W := W) m i i one))
    (Runs.atom (Step.sub (W := W) (update m i (m i+m one)) test i limit))
  simpa only [tick,nextMemory,hi,h1,update,if_pos rfl,if_true,if_neg hneq,hn] using hs

/-- A fixed ascending for-loop. The caller initializes the counter and the input limit. -/
def repeatN (body : Command) (i one limit test : ℤ) : Command :=
  .repeatWhileNegative (.seq body (tick i one limit test)) test

/-- With a per-iteration body bound `B`, the compiled loop uses at most
    `N(B+3)` instructions, charging the two counter updates and the backward test. -/
theorem repeatN_runs {W N B : ℕ} (hN : 0 < N) (body : Command) {i one limit test : ℤ}
    (hneq : limit ≠ i) (inv : ℕ → Memory → Prop)
    (fits : ∀ q : ℕ, q ≤ N → Fits W ((q:ℤ)-N))
    (step : ∀ q : ℕ, q < N → ∀ m : Memory, inv q m →
      ∃ t : ℕ, t ≤ B ∧ ∃ x : Memory, Runs W body m t x ∧
        x i = (q:ℤ) ∧ x one = 1 ∧ x limit = (N:ℤ) ∧ inv (q+1) (nextMemory x i test q N))
    {m : Memory} (hm : inv 0 m) :
    ∃ t : ℕ, t ≤ N*(B+3) ∧ ∃ out, Runs W (repeatN body i one limit test) m t out ∧ inv N out := by
  have go (r q : ℕ) (he : q+r=N) (hr : 0<r) (m : Memory) (hin : inv q m) :
      ∃ t : ℕ, t ≤ r*(B+3) ∧ ∃ out,
        Runs W (repeatN body i one limit test) m t out ∧ inv N out := by
    induction r generalizing q m with
    | zero => omega
    | succ r ih =>
      obtain ⟨s,hs,x,hx,hxi,hx1,hxN,hin'⟩ := step q (by omega) m hin
      let y := nextMemory x i test q N
      have run : Runs W (.seq body (tick i one limit test)) m (s+2) y :=
        Runs.seq hx (tick_runs hneq hxi hx1 hxN)
      have htest : y test = ((q:ℤ)+1)-N := by simp [y,nextMemory,update]
      have hfit : Fits W (y test) := by
        rw [htest]
        exact_mod_cast fits (q+1) (by omega)
      by_cases hz : r=0
      · subst r
        have hqn : q+1=N := by omega
        refine ⟨(s+2)+1,by omega,y,Runs.loop_done run hfit ?_,hqn ▸ hin'⟩
        rw [htest]
        exact_mod_cast (show ¬ ((q:ℤ)+1-(N:ℤ))<0 by omega)
      · obtain ⟨t,ht,out,ho,final⟩ := ih (q+1) (by omega) (by omega) y hin'
        refine ⟨(s+2)+1+t,?_,out,Runs.loop_again run hfit ?_ ho,final⟩
        · rw [Nat.succ_mul]
          omega
        · rw [htest]
          omega
  exact go N 0 (by omega) hN m hm

end VWZClique.IntegerRAM.Structured


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

def loop (i lim : ℤ) (body : Command) := Command.seq (.atom (.one (-7))) <|
  .seq (.atom (.sub i i i)) (repeatN body i (-7) lim (-8))

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

/-- Parent, row and column are generated by three nested loops, with no
division or remainder operations for unpacking a linear address. -/
def grid (body : Command) := loop (-4) (-2) (loop (-5) (-3) (loop (-6) (-3) body))

def gridCost (N side B : ℕ) := 2+N*((2+side*((2+side*(B+3))+3))+3)

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

def levelAddr (k : ℕ) := plus base (plus (times (num k) nodes) node)
def levelProd := times (.read (levelAddr 0)) (.read (levelAddr 1))
def leafBody := write floor (levelAddr 2) levelProd
def leafBodySteps := (levelAddr 2).steps+(levelProd.steps+1)

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

/-- All scalar products on one bottom layer, measured from arbitrary input memory. -/
def leafLayer := Command.seq (.atom (.one (-7))) <| .seq (.atom (.sub (-4) (-4) (-4)))
  (repeatN leafBody (-4) (-7) (-2) (-8))

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

def codes {I : Type*} (cmd : I → Command) : List I → Command
  | [] => .skip
  | j::js => .seq (cmd j) (codes cmd js)

noncomputable def all (I : Type*) [Fintype I] : List I := Finset.univ.toList
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

def weightDown {b r : ℕ} (S : Scheme b r) (j : Fin 3 × Fin r) : Square (Fin b) :=
  if j.1=0 then S.left j.2 else if j.1=1 then S.right j.2 else 0

def downBatchCode {b r : ℕ} (S : Scheme b r) (j : Fin 3 × Fin r) :=
  grid (downCode j.1 j.2 (weightDown S j))

noncomputable def downLevel {b r : ℕ} (S : Scheme b r) := codes (downBatchCode S) (all (Fin 3 × Fin r))

def downBatchCost {b r : ℕ} (S : Scheme b r) (j : Fin 3 × Fin r) :=
  (childCell b r j.1 j.2).steps+((downVal j.1 (weightDown S j)).steps+1)

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

def upBatchCode {b r : ℕ} (S : Scheme b r) (j : Fin b × Fin b) := grid (upCode S j.1 j.2)
def upBatchCost {b r : ℕ} (S : Scheme b r) (j : Fin b × Fin b) :=
  (parentCell 2 j.1 j.2).steps+((upVal S j.1 j.2).steps+1)
noncomputable def upLevel {b r : ℕ} (S : Scheme b r) := codes (upBatchCode S) (all (Fin b × Fin b))

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

/-- Assign a register using the expression scratch segment. -/
def assign (reg : ℤ) (e : Expr) := Command.seq (e.code floor)
  (.seq (.atom (.sub reg reg reg)) (.atom (.add reg reg floor)))

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

def divOne : ℤ := -10
def divK : ℤ := -11
def divQ : ℤ := -12
def divTest : ℤ := -13

def quotientBody (num : ℤ) := Command.seq (.atom (.sub num num divK))
  (.seq (.atom (.add divQ divQ divOne)) (.atom (.sub divTest divTest divTest)))

-- A negative remainder is the loop guard, so an exact positive multiple
-- performs precisely q subtraction rounds.
def quotientIter (num : ℤ) := Command.seq (quotientBody num) (.atom (.sub divTest divTest num))

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

def quotientCmd (d : ℕ) (num : ℤ) := Command.seq (assign divK (Expr.num d))
  (.seq (.atom (.one divOne))
  (.seq (.atom (.sub divQ divQ divQ))
  (.seq (.repeatWhileNegative (quotientIter num) divTest)
    (assign num (.reg divQ)))))

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

def rootReg : ℤ := -9

def downAdj (b r : ℕ) := Command.seq (assign (-1) (next b)) (assign (-2) (times nodes (num r)))
def back (b : ℕ) := Expr.sub base (times (times (times (num 3) nodes) (parentSide b)) (parentSide b))
def grow (b : ℕ) := assign (-3) (parentSide b)
noncomputable def downOnce {b r : ℕ} (S : Scheme b r) :=
  Command.seq (quotientCmd b (-3)) (.seq (downLevel S) (downAdj b r))
noncomputable def upOnce {b r : ℕ} (S : Scheme b r) :=
  Command.seq (quotientCmd r (-2)) (.seq (assign (-1) (back b)) (.seq (upLevel S) (grow b)))

def downAdjTime (b r : ℕ) := ((next b).steps+2)+((times nodes (num r)).steps+2)
def quotTime (d q : ℕ) := (Expr.num d).steps+2+(1+(1+(5*q+4)))
noncomputable def downTime {b r : ℕ} (S : Scheme b r) (h N : ℕ) := quotTime b (b^h) +
    (((all (Fin 3 × Fin r)).map (fun j => gridCost N (b^h) (downBatchCost S j))).sum+downAdjTime b r)
noncomputable def upTime {b r : ℕ} (S : Scheme b r) (h N : ℕ) := quotTime r N + ((back b).steps+2+
    (((all (Fin b × Fin b)).map (fun j => gridCost N (b^h) (upBatchCost S j))).sum+((parentSide b).steps+2)))

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

def flag : ℤ := -14
def downTest := Expr.sub .one side
def upTest := Expr.sub side (.reg rootReg)
noncomputable def downStep {b r : ℕ} (S : Scheme b r) := Command.seq (downOnce S) (assign flag downTest)
noncomputable def upStep {b r : ℕ} (S : Scheme b r) := Command.seq (upOnce S) (assign flag upTest)

noncomputable def charge {b r : ℕ} (S : Scheme b r) : (h N : ℕ) → ℕ
  | 0,N => 2+N*(leafBodySteps+3)
  | h+1,N => downTime S h N + (downTest.steps+3) + charge S h (N*r) + upTime S h N + (upTest.steps+3)

def Room (W M : ℕ) := ∀ x : ℤ, -(M:ℤ) ≤ x → x ≤ M → Fits W x

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

/- MMUniformField -/
section

namespace VWZClique.BlockMM

/-- Three coefficient arrays with common rank index. -/
structure Factors (F I R : Type*) where
  left : R → I → I → F
  right : R → I → I → F
  out : I → I → R → F

namespace Factors
variable {F I R J Q : Type*} [Field F]

open Classical in
def Valid [Fintype R] (T : Factors F I R) : Prop :=
  ∀ i j a d e f : I,
    (∑ s, T.out i j s * T.left s a d * T.right s e f) =
      if i=a ∧ d=e ∧ f=j then 1 else 0

def reindex (T : Factors F I R) (u : J ≃ I) (v : Q ≃ R) : Factors F J Q where
  left s a d := T.left (v s) (u a) (u d)
  right s a d := T.right (v s) (u a) (u d)
  out i j s := T.out (u i) (u j) (v s)

theorem reindex_valid [Fintype R] [Fintype Q] (T : Factors F I R) (h : T.Valid)
    (u : J ≃ I) (v : Q ≃ R) : (T.reindex u v).Valid := by
  classical
  intro i j a d e f
  change (∑ s : Q, T.out _ _ (v s) * T.left (v s) _ _ * T.right (v s) _ _) = _
  rw [v.sum_comp (fun s => T.out (u i) (u j) s * T.left s (u a) (u d) * T.right s (u e) (u f)),h]
  simp

def power (T : Factors F I R) (h : ℕ) : Factors F (Fin h → I) (Fin h → R) where
  left s a d := ∏ k, T.left (s k) (a k) (d k)
  right s e f := ∏ k, T.right (s k) (e k) (f k)
  out i j s := ∏ k, T.out (i k) (j k) (s k)

theorem power_valid [Fintype R] (T : Factors F I R) (hT : T.Valid) (h : ℕ) : (T.power h).Valid := by
  classical
  intro i j a d e f
  simp only [power,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k s => T.out (i k) (j k) s * T.left s (a k) (d k) * T.right s (e k) (f k))]
  have step (k : Fin h) := hT (i k) (j k) (a k) (d k) (e k) (f k)
  simp_rw [step]
  by_cases hx : i=a ∧ d=e ∧ f=j
  · rcases hx with ⟨rfl,rfl,rfl⟩
    simp
  · rw [if_neg hx]
    have hh : ∃ k, ¬ (i k=a k ∧ d k=e k ∧ f k=j k) := by
      by_contra! hf
      exact hx ⟨funext (fun k => (hf k).1),funext (fun k => (hf k).2.1),funext (fun k => (hf k).2.2)⟩
    obtain ⟨k,hk⟩ := hh
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

section Rational
variable {E D : Type*} [Field E] [Algebra ℚ E] [Fintype D]

private theorem linear_expansion (B : Module.Basis D ℚ E) (p : E →ₗ[ℚ] ℚ) (z x y : E) :
    (∑ a, ∑ d, p (z * B a * B d) * B.repr x a * B.repr y d) = p (z*x*y) := by
  have hx : p (z*x*y) = ∑ a, B.repr x a * p (z*B a*y) := by
    conv_lhs => rw [← B.sum_repr x]
    simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,map_sum,map_smul,smul_eq_mul]
  have hy (a : D) : p (z*B a*y) = ∑ d, B.repr y d * p (z*B a*B d) := by
    conv_lhs => rw [← B.sum_repr y]
    simp only [Finset.mul_sum,mul_smul_comm,map_sum,map_smul,smul_eq_mul]
  rw [hx]
  apply Finset.sum_congr rfl
  intro a _
  rw [hy,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Passing once to rational coordinates costs a fixed factor d² in rank,
independent of the tensor power to which this operation is applied. -/
noncomputable def rational (B : Module.Basis D ℚ E) (p : E →ₗ[ℚ] ℚ) (T : Factors E I R) :
    Factors ℚ I (R × D × D) where
  left s a d := B.repr (T.left s.1 a d) s.2.1
  right s e f := B.repr (T.right s.1 e f) s.2.2
  out i j s := p (T.out i j s.1 * B s.2.1 * B s.2.2)

theorem rational_valid [Fintype R] (B : Module.Basis D ℚ E) (p : E →ₗ[ℚ] ℚ) (hp : p 1 = 1)
    (T : Factors E I R) (hT : T.Valid) : (rational B p T).Valid := by
  classical
  intro i j a d e f
  simp only [rational,Fintype.sum_prod_type,linear_expansion]
  rw [← map_sum p,hT i j a d e f]
  by_cases h : i=a ∧ d=e ∧ f=j <;> simp [h,hp]

theorem exists_projection : ∃ p : E →ₗ[ℚ] ℚ, p 1 = 1 := by
  let incl := Algebra.linearMap ℚ E
  obtain ⟨p,h⟩ := incl.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (RingHom.injective _))
  refine ⟨p,?_⟩
  simpa [incl] using LinearMap.congr_fun h (1:ℚ)

end Rational

theorem rational_power {E : Type*} [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    {b r : ℕ} (T : Factors E (Fin b) (Fin r)) (hT : T.Valid) (h : ℕ) :
    ∃ Q : Factors ℚ (Fin (b^h)) (Fin (r^h * (Module.finrank ℚ E)^2)), Q.Valid := by
  classical
  let d := Module.finrank ℚ E
  let u : (Fin h → Fin b) ≃ Fin (b^h) := Fintype.equivFinOfCardEq (by simp)
  let v : ((Fin h → Fin r) × Fin d × Fin d) ≃ Fin (r^h*d^2) :=
    Fintype.equivFinOfCardEq (by simp [pow_two])
  obtain ⟨p,hp⟩ := exists_projection (E := E)
  let B := Module.finBasis ℚ E
  exact ⟨_,reindex_valid _ (rational_valid B p hp (T.power h) (power_valid T hT h)) u.symm v.symm⟩

end Factors
end VWZClique.BlockMM
end

/- MMUniformInteger -/
section

namespace VWZClique.BlockMM

/-- Clear every denominator in one finite rational table using a positive common integer. -/
theorem commonDen {X : Type*} [Fintype X] (f : X → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ z : X → ℤ, ∀ x, (z x : ℚ) = (D:ℚ)*f x := by
  classical
  let den (x : X) := (f x).den
  refine ⟨∏ x, den x,Finset.prod_pos (fun x _ => (f x).den_pos),fun x =>
    ((∏ y ∈ Finset.univ.erase x, den y : ℕ):ℤ)*(f x).num,?_⟩
  intro x
  have hd : (den x : ℚ)*f x = (f x).num := by
    calc
      _ = (den x:ℚ)*((f x).num/(den x:ℚ)) := congrArg ((den x : ℚ) * ·) (f x).num_div_den.symm
      _ = _ := by
        have hn : (den x : ℚ) ≠ 0 := by exact_mod_cast (f x).den_nz
        field_simp
  rw [← Finset.prod_erase_mul Finset.univ den (Finset.mem_univ x)]
  push_cast
  rw [mul_assoc,hd]

private theorem expand_products {G I J R : Type*} [CommRing G] [Fintype I] [Fintype J] [Fintype R]
    (l : R → I → G) (t : R → J → G) (o : R → G) (a : I → G) (b : J → G) :
    (∑ s, o s * ((∑ p, l s p*a p)*(∑ q, t s q*b q))) =
    ∑ p, ∑ q, (∑ s, o s*l s p*t s q)*(a p*b q) := by
  classical
  calc
    _ = ∑ s, ∑ p, ∑ q, (o s*l s p*t s q)*(a p*b q) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]

theorem schemeOfIdentities {b r : ℕ}
    (L R : Fin r → Square (Fin b)) (O : Fin b → Fin b → Fin r → ℤ) (D : ℤ)
    (h : ∀ i j a d e f : Fin b, (∑ s, O i j s * L s a d * R s e f) =
      D * (if i=a ∧ d=e ∧ f=j then 1 else 0)) :
    ∃ S : Scheme b r, S.scale = D := by
  classical
  refine ⟨⟨L,R,O,D,?_⟩,rfl⟩
  intro A B i j
  have he := expand_products (fun s (p : Fin b × Fin b) => L s p.1 p.2)
    (fun s (p : Fin b × Fin b) => R s p.1 p.2) (O i j)
    (fun p => A p.1 p.2) (fun p => B p.1 p.2)
  simp only [Fintype.sum_prod_type] at he
  calc
    _ = _ := he
    _ = _ := by
      simp_rw [h]
      have step (a d e f : Fin b) :
          D * (if i=a ∧ d=e ∧ f=j then (1:ℤ) else 0) * (A a d * B e f) =
          if a=i then if e=d then if f=j then D*(A a d * B e f) else 0 else 0 else 0 := by
        by_cases h₁ : a=i
        · subst a
          by_cases h₂ : e=d
          · subst e
            by_cases h₃ : f=j <;> simp [h₃]
          · simp [h₂,Ne.symm h₂]
        · simp [h₁,Ne.symm h₁]
      simp_rw [step]
      simp [Matrix.mul_apply,Finset.sum_ite_irrel,Finset.mul_sum]

theorem Factors.integerScheme {b r : ℕ} (T : Factors ℚ (Fin b) (Fin r)) (hT : T.Valid) :
    ∃ S : Scheme b r, 0 < S.scale := by
  obtain ⟨L,hL,l,hl⟩ := commonDen (fun (x : Fin r × Fin b × Fin b) => T.left x.1 x.2.1 x.2.2)
  obtain ⟨R,hR,q,hq⟩ := commonDen (fun (x : Fin r × Fin b × Fin b) => T.right x.1 x.2.1 x.2.2)
  obtain ⟨O,hO,o,ho⟩ := commonDen (fun (x : Fin b × Fin b × Fin r) => T.out x.1 x.2.1 x.2.2)
  let scale : ℤ := (O:ℤ)*L*R
  obtain ⟨S,hS⟩ := schemeOfIdentities
    (fun s i j => l (s,i,j)) (fun s i j => q (s,i,j)) (fun i j s => o (i,j,s)) scale (by
      intro i j a d e f
      apply Int.cast_injective (α := ℚ)
      push_cast
      simp only [hl,hq,ho]
      calc
        _ = (O*(L*R):ℚ) * ∑ s, T.out i j s*T.left s a d*T.right s e f := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
        _ = _ := by
          rw [hT]
          by_cases h : i=a ∧ d=e ∧ f=j
          · simp [scale,h]; ring
          · simp [h])
  exact ⟨S,hS ▸ (by dsimp [scale]; positivity)⟩

/-- A fixed complex-to-number-field specialization can be descended to an
integer scheme after any tensor power, with a single d² rational-coordinate factor. -/
theorem integerPower {E : Type*} [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    {b r : ℕ} (T : Factors E (Fin b) (Fin r)) (hT : T.Valid) (h : ℕ) :
    ∃ S : Scheme (b^h) (r^h * (Module.finrank ℚ E)^2), 0 < S.scale := by
  obtain ⟨Q,hQ⟩ := T.rational_power hT h
  exact Q.integerScheme hQ

end VWZClique.BlockMM
end

/- MMUniformRate -/
section

namespace VWZClique.BlockMM

private theorem positive_power_padding (b : ℕ) (hb : 2 ≤ b) (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℕ, 0 < h ∧ (D:ℝ) ≤ ((b:ℝ)^h)^ε := by
  have hb' : (1:ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have ht := Real.one_lt_rpow hb' hε
  obtain ⟨h,hh⟩ := pow_unbounded_of_one_lt (D:ℝ) ht
  refine ⟨h+1,by omega,?_⟩
  have hp : (D:ℝ) ≤ ((b:ℝ)^ε)^(h+1) :=
    hh.le.trans (pow_le_pow_right₀ ht.le (by omega))
  convert! hp using 1
  rw [← Real.rpow_natCast_mul (by positivity), mul_comm, Real.rpow_mul_natCast (by positivity)]

/-- Rational-coordinate expansion of a fixed algebraic scheme can use arbitrarily little
slack, even if the degree of its number field is very large. -/
theorem fixed_integer_scheme {E : Type*} [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    {b r : ℕ} (T : Factors E (Fin b) (Fin r)) (hT : T.Valid) (hb : 2 ≤ b)
    (τ : ℝ) (hr : (r:ℝ) ≤ (b:ℝ)^τ) (ε : ℝ) (hε : 0 < ε) :
    ∃ B R : ℕ, 2 ≤ B ∧ (R:ℝ) ≤ (B:ℝ)^(τ+ε) ∧
      ∃ S : Scheme B R, 0 < S.scale := by
  let d := Module.finrank ℚ E
  obtain ⟨h,hh,hd⟩ := positive_power_padding b hb (d^2) ε hε
  obtain ⟨S,hS⟩ := integerPower T hT h
  have hb' : 1 ≤ b := by omega
  refine ⟨b^h,r^h*d^2,?_,?_,S,hS⟩
  · exact hb.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hb' (show 1 ≤ h by omega))
  · push_cast at hd ⊢
    rw [Real.rpow_add (by positivity)]
    apply mul_le_mul _ hd (by positivity) (by positivity)
    have hrh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ r) hr h
    convert! hrh using 1
    rw [← Real.rpow_natCast_mul (by positivity), mul_comm, Real.rpow_mul_natCast (by positivity)]

theorem scalarBudget_mono {b r R : ℕ} (h : r ≤ R) (n : ℕ) :
    scalarBudget b r n ≤ scalarBudget b R n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [scalarBudget]
    gcongr

/-- Matrix multiplication with a fixed positive integer scale and a single
recursion for all dimensions. Its scalar budget meets every positive slack. -/
theorem fixed_uniform {E : Type*} [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    {b r : ℕ} (T : Factors E (Fin b) (Fin r)) (hT : T.Valid) (hb : 2 ≤ b)
    (τ : ℝ) (hτ : 2 ≤ τ) (hr : (r:ℝ) ≤ (b:ℝ)^τ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (B R : ℕ) (hb' : 2 ≤ B) (S : Scheme B R), 0 < S.scale ∧
      (∀ n : ℕ, ∀ hn : 1 ≤ n, ∀ A B' : Square (Fin n), ∀ i j,
        scaled S hb' hn A B' i j / S.scale^depth B n = (A*B') i j) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        (scalarBudget B R (depth B n) : ℝ) ≤ C*(n:ℝ)^(τ+ε) := by
  obtain ⟨B,R,hB,hR,S,hS⟩ := fixed_integer_scheme T hT hb τ hr (ε/2) (by linarith)
  have hB' : (1:ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hs : ((B^2 : ℕ):ℝ) ≤ (B:ℝ)^(τ+ε/2) := by
    push_cast
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hB'
      (show (2:ℝ) ≤ τ+ε/2 by linarith)
  let r' := max R (B^2)
  have hr' : (r':ℝ) ≤ (B:ℝ)^(τ+ε/2) := by
    exact_mod_cast (show (max (R:ℝ) (B^2:ℕ)) ≤ (B:ℝ)^(τ+ε/2) from max_le hR hs)
  obtain ⟨C,hC,hbudget⟩ := uniform_budget hB (show B^2 ≤ r' from le_max_right _ _)
    (τ+ε/2) (by linarith) hr' (ε/2) (by linarith)
  refine ⟨B,R,hB,S,hS,fun n hn A B' i j => scaled_div S hS.ne' hB hn A B' i j,C,hC,?_⟩
  intro n hn
  have hh := hbudget n hn
  rw [show τ+ε/2+ε/2=τ+ε by ring] at hh
  exact le_trans (by exact_mod_cast scalarBudget_mono (b := B) (le_max_left R (B^2)) (depth B n)) hh

end VWZClique.BlockMM
end

/- CircuitBuild -/
section

open VWZClique OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.Circuit

/-- Extend any straight-line program, retaining all previous values. -/
def Build {F I : Type*} [Field F] (f : (I → F) → F) (b : ℕ) : Prop :=
  ∀ (r : ℕ) (p : Program F I r), ∃ (n : ℕ) (q : Program F I n) (out : Fin n) (old : Fin r → Fin n),
    q.cost ≤ p.cost + b ∧ (∀ w, q.eval w out = f w) ∧ ∀ w i, q.eval w (old i) = p.eval w i

variable {F I : Type*} [Field F]

theorem cost_mono {f : (I → F) → F} {a b : ℕ} (h : Build f a) (hab : a ≤ b) : Build f b := by
  intro r p
  obtain ⟨n,q,out,old,hc,ho,hi⟩ := h r p
  exact ⟨n,q,out,old,by omega,ho,hi⟩

theorem const (c : F) : Build (fun _ : I → F => c) 0 := by
  intro r p
  exact ⟨r+1,.step p (.constant c),0,Fin.succ,by simp [Program.cost,Gate.cost],fun _ => rfl,fun _ _ => rfl⟩

theorem read (i : I) : Build (fun w : I → F => w i) 0 := by
  intro r p
  exact ⟨r+1,.step p (.input i),0,Fin.succ,by simp [Program.cost,Gate.cost],fun _ => rfl,fun _ _ => rfl⟩

theorem binary {f g : (I → F) → F} {a b : ℕ} (hf : Build f a) (hg : Build g b)
    (fn : F → F → F) (gate : ∀ {n : ℕ}, Fin n → Fin n → Gate F I (Fin n))
    (cost : ∀ {n : ℕ} (i j : Fin n), (gate i j).cost ≤ 1)
    (eval : ∀ {n : ℕ} (w : I → F) (v : Fin n → F) i j, (gate i j).eval w v = fn (v i) (v j)) :
    Build (fun w => fn (f w) (g w)) (a+b+1) := by
  intro r p
  obtain ⟨r₁,p₁,o₁,old₁,h₁,e₁,l₁⟩ := hf r p
  obtain ⟨r₂,p₂,o₂,old₂,h₂,e₂,l₂⟩ := hg r₁ p₁
  let g' := gate (old₂ o₁) o₂
  refine ⟨r₂+1,.step p₂ g',0,fun i => (old₂ (old₁ i)).succ,?_,?_,?_⟩
  · have hc := cost (old₂ o₁) o₂
    change p₂.cost + (gate (old₂ o₁) o₂).cost ≤ _
    omega
  · intro w
    change (gate _ _).eval _ _ = _
    rw [eval,l₂,e₁,e₂]
  · intro w i
    exact (l₂ w _).trans (l₁ w _)

theorem add {f g : (I → F) → F} {a b : ℕ} (hf : Build f a) (hg : Build g b) :
    Build (fun w => f w + g w) (a+b+1) :=
  binary hf hg (·+·) Gate.add (fun _ _ => le_rfl) (fun _ _ _ _ => rfl)

theorem mul {f g : (I → F) → F} {a b : ℕ} (hf : Build f a) (hg : Build g b) :
    Build (fun w => f w * g w) (a+b+1) :=
  binary hf hg (·*·) Gate.mul (fun _ _ => le_rfl) (fun _ _ _ _ => rfl)

theorem sum {J : Type*} (s : Finset J) (f : J → (I → F) → F) (b : ℕ)
    (h : ∀ j ∈ s, Build (f j) b) :
    Build (fun w => ∑ j ∈ s, f j w) (s.card * (b+1)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (I := I) (0:F))
  | @insert j s hj ih =>
    have h' := add (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [hj,Finset.card_insert_of_notMem, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'

theorem prod {J : Type*} (s : Finset J) (f : J → (I → F) → F) (b : ℕ)
    (h : ∀ j ∈ s, Build (f j) b) :
    Build (fun w => ∏ j ∈ s, f j w) (s.card * (b+1)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (I := I) (1:F))
  | @insert j s hj ih =>
    have h' := mul (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [hj,Finset.card_insert_of_notMem, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'

end VWZClique.Circuit
end

/- GraphWeights -/
section

open VWZClique OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.FoldProof

/-- Compute every member of a finite table, retaining its output register. -/
theorem tabulate {F I J : Type*} [Field F] [Fintype J] (f : J → (I → F) → F) (b : ℕ)
    (h : ∀ j, Circuit.Build (f j) b) :
    ∃ (r : ℕ) (p : Program F I r) (out : J → Fin r),
      p.cost ≤ Fintype.card J * b ∧ ∀ w j, p.eval w (out j) = f j w := by
  classical
  have part (s : Finset J) : ∃ (r : ℕ) (p : Program F I r) (out : (j:J) → j ∈ s → Fin r),
      p.cost ≤ s.card*b ∧ ∀ w j hj, p.eval w (out j hj) = f j w := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨0,.nil,fun _ h => False.elim (by simp at h),by simp [Program.cost],fun _ _ h => False.elim (by simp at h)⟩
    | @insert j s hj ih =>
      obtain ⟨n,p,out,hc,he⟩ := ih
      obtain ⟨r,q,o,old,hc',ho,hold⟩ := h j n p
      refine ⟨r,q,fun i hi => if h : i=j then o else old (out i (by simpa [h] using hi)), ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hj,Nat.succ_mul]
        omega
      · intro w i hi
        by_cases hij : i=j
        · subst i; simpa using ho w
        · simpa [hij,hold] using he w i (by simpa [hij] using hi)
  obtain ⟨r,p,out,hc,he⟩ := part Finset.univ
  exact ⟨r,p,fun j => out j (Finset.mem_univ _),hc,fun w j => he w j _⟩

end VWZClique.FoldProof
end

/- MMOmega -/
section

open OAI.MatrixMultiplication.Arithmetic Filter
namespace VWZClique.MM

private def price {F I : Type*} : {r : ℕ} → Program F I r → Fin r → ℕ
  | 0, .nil => Fin.elim0
  | _+1, .step p g => Fin.cases g.cost (price p)

private theorem sum_price {F I : Type*} {r : ℕ} (p : Program F I r) :
    ∑ i, price p i = p.cost := by
  induction p with
  | nil => simp [Program.cost]
  | step p g ih => rw [Fin.sum_univ_succ]; simpa [price,Program.cost,add_comm] using congrArg (g.cost + ·) ih

private theorem register_kind {F I : Type*} [Field F] {r : ℕ} (p : Program F I r) (i : Fin r) :
    price p i = 1 ∨ (∃ c : F, ∀ w, p.eval w i = c) ∨ ∃ k : I, ∀ w, p.eval w i = w k := by
  induction p with
  | nil => exact Fin.elim0 i
  | step p g ih =>
    refine Fin.cases ?_ (fun i => ih i) i
    cases g with
    | constant c => exact Or.inr (Or.inl ⟨c,fun _ => rfl⟩)
    | input k => exact Or.inr (Or.inr ⟨k,fun _ => rfl⟩)
    | _ => exact Or.inl rfl

theorem square_output_lower_bound {F : Type*} [Field F] {n : ℕ}
    (P : MatrixAlgorithm F n n n) (hc : P.Correct) : n^2 ≤ P.cost := by
  classical
  let out (ij : Fin n × Fin n) := P.output ij.1 ij.2
  have ev (ij : Fin n × Fin n) (A B : Matrix (Fin n) (Fin n) F) :
      P.program.eval (matrixInputs A B) (out ij) = (A*B) ij.1 ij.2 :=
    congrFun (congrFun (hc A B) ij.1) ij.2
  let ones : Matrix (Fin n) (Fin n) F := fun _ _ => 1
  have active (ij : Fin n × Fin n) : price P.program (out ij) = 1 := by
    rcases register_kind P.program (out ij) with h | ⟨c,h⟩ | ⟨k,h⟩
    · exact h
    · have hz := ev ij 0 0
      have ho := ev ij ones 1
      rw [h,Matrix.zero_mul] at hz
      rw [h,Matrix.mul_one] at ho
      exact (zero_ne_one ((show c = 0 from hz).symm.trans (show c=1 from ho))).elim
    · rcases k with ⟨i,j⟩ | ⟨i,j⟩
      · have he := ev ij ones 0
        rw [h,Matrix.mul_zero] at he
        exact (one_ne_zero (show (1:F)=0 from he)).elim
      · have he := ev ij 0 ones
        rw [h,Matrix.zero_mul] at he
        exact (one_ne_zero (show (1:F)=0 from he)).elim
  have inject : Function.Injective out := by
    intro x y he
    by_contra hne
    let A : Matrix (Fin n) (Fin n) F := fun i j => if (i,j)=x then 1 else 0
    have hx := ev x A 1
    have hy := ev y A 1
    rw [he,hy,Matrix.mul_one] at hx
    simp [A,Ne.symm hne] at hx
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (Finset.univ.image out))
      (f := price P.program) (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_image (fun _ _ _ _ h => inject h), sum_price] at hsum
  simpa [MatrixAlgorithm.cost,active,pow_two] using hsum

theorem cubic_algorithm (F : Type*) [Field F] (n : ℕ) :
    ∃ P : MatrixAlgorithm F n n n, P.Correct ∧ P.cost ≤ 2*n^3 := by
  let f := fun (v : Fin n × Fin n) (w : MatrixInput n n n → F) => ∑ k : Fin n, w (.inl (v.1,k)) * w (.inr (k,v.2))
  have build (v : Fin n × Fin n) : Circuit.Build (f v) (n*2) := by
    have h := Circuit.sum Finset.univ
      (fun k : Fin n => fun w : MatrixInput n n n → F => w (.inl (v.1,k))*w (.inr (k,v.2))) 1
      (fun k _ => Circuit.mul (Circuit.read _) (Circuit.read _))
    simpa [f] using h
  obtain ⟨r,p,out,hc,he⟩ := FoldProof.tabulate f _ build
  refine ⟨⟨r,p,fun i j => out (i,j)⟩,?_,?_⟩
  · intro A B
    ext i j
    exact he (matrixInputs A B) (i,j)
  · change p.cost ≤ _
    calc p.cost ≤ _ := hc
         _ = _ := by simp [Fintype.card_prod]; ring

theorem cubic_admissible (F : Type*) [Field F] : AdmissibleExponent F 3 := by
  intro ε hε
  refine ⟨2,by norm_num,?_⟩
  intro n hn
  obtain ⟨P,hc,hp⟩ := cubic_algorithm F n
  refine ⟨P,hc,?_⟩
  calc
    (P.cost : ℝ) ≤ 2*(n:ℝ)^3 := by exact_mod_cast hp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num; linarith)

theorem admissible_ge_two {F : Type*} [Field F] {τ : ℝ} (hτ : AdmissibleExponent F τ) : 2 ≤ τ := by
  by_contra! h
  let ε := (2-τ)/2
  have he : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C,hC,h⟩ := hτ ε he
  have lim := (tendsto_rpow_atTop he).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ev : ∀ᶠ n : ℕ in atTop, C < (n:ℝ)^ε := lim.eventually_gt_atTop C
  obtain ⟨n,hn,hn'⟩ := ((eventually_ge_atTop 1).and ev).exists
  obtain ⟨P,hp,hpc⟩ := h n hn
  have hb := square_output_lower_bound P hp
  have hpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have heq : (n:ℝ)^2 = (n:ℝ)^ε * (n:ℝ)^(τ+ε) := by
    rw [← Real.rpow_add hpos, show ε+(τ+ε)=2 by dsimp [ε]; ring]
    norm_num
  have hlow : (n:ℝ)^2 ≤ P.cost := by exact_mod_cast hb
  rw [heq] at hlow
  exact (not_lt_of_ge (hlow.trans hpc)) (mul_lt_mul_of_pos_right hn' (Real.rpow_pos_of_pos hpos _))

theorem omega_two_le (F : Type*) [Field F] : 2 ≤ omega F :=
  le_csInf ⟨3,cubic_admissible F⟩ (fun _ ht => admissible_ge_two ht)

theorem omega_le_three (F : Type*) [Field F] : omega F ≤ 3 :=
  csInf_le ⟨2,fun _ h => admissible_ge_two h⟩ (cubic_admissible F)

theorem omega_admissible (F : Type*) [Field F] : AdmissibleExponent F (omega F) := by
  intro ε hε
  obtain ⟨t,ht,hlt⟩ := exists_lt_of_csInf_lt (s := {t : ℝ | AdmissibleExponent F t})
    ⟨3,cubic_admissible F⟩ (show omega F < omega F + ε/2 by linarith)
  obtain ⟨C,hC,hP⟩ := ht (ε/2) (by linarith)
  refine ⟨C,hC,?_⟩
  intro n hn
  obtain ⟨P,hp,hpc⟩ := hP n hn
  exact ⟨P,hp,hpc.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)) hC.le)⟩

end VWZClique.MM
end

/- BilinearExtraction -/
section

open OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.BilinearExtraction

structure Semantics (F I A : Type*) where
  const : F → A
  input : I → A
  add : A → A → A
  sub : A → A → A
  mul : A → A → A

variable {F I J A B : Type*}

private def gate (m : Semantics F I A) {r : ℕ} (z : Fin r → A) : Gate F I (Fin r) → A
  | .constant c => m.const c
  | .input i => m.input i
  | .add i j => m.add (z i) (z j)
  | .sub i j => m.sub (z i) (z j)
  | .mul i j => m.mul (z i) (z j)

def run (m : Semantics F I A) : {r : ℕ} → Program F I r → Fin r → A
  | _, .nil => Fin.elim0
  | _, .step p g => Fin.cases (gate m (run m p) g) (run m p)

private theorem simulate (m : Semantics F I A) (n : Semantics F I B) (R : A → B → Prop)
    (hc : ∀ c, R (m.const c) (n.const c)) (hi : ∀ i, R (m.input i) (n.input i))
    (ha : ∀ a b u v, R a u → R b v → R (m.add a b) (n.add u v))
    (hs : ∀ a b u v, R a u → R b v → R (m.sub a b) (n.sub u v))
    (hm : ∀ a b u v, R a u → R b v → R (m.mul a b) (n.mul u v))
    {r : ℕ} (p : Program F I r) (i : Fin r) : R (run m p i) (run n p i) := by
  induction p with
  | nil => exact i.elim0
  | step p g ih =>
    refine Fin.cases ?_ (fun j => ih j) i
    cases g with
    | constant c => exact hc c
    | input j => exact hi j
    | add j k => exact ha _ _ _ _ (ih j) (ih k)
    | sub j k => exact hs _ _ _ _ (ih j) (ih k)
    | mul j k => exact hm _ _ _ _ (ih j) (ih k)

variable [Field F]

abbrev Form (F I : Type*) [Field F] := (I → F) →ₗ[F] F
abbrev Term (F I J : Type*) [Field F] := Form F I × Form F J

def rankOne (s : Term F I J) (x : I → F) (y : J → F) : F := s.1 x * s.2 y

structure Jet (F I J : Type*) [Field F] where
  constant : F
  left : Form F I
  right : Form F J
  mixed : (I → F) → (J → F) → F

def jets : Semantics F (I ⊕ J) (Jet F I J) where
  const c := ⟨c,0,0,0⟩
  input := Sum.elim (fun i => ⟨0,LinearMap.proj i,0,0⟩) (fun j => ⟨0,0,LinearMap.proj j,0⟩)
  add p q := ⟨p.constant + q.constant,p.left + q.left,p.right + q.right,p.mixed + q.mixed⟩
  sub p q := ⟨p.constant - q.constant,p.left - q.left,p.right - q.right,p.mixed - q.mixed⟩
  mul p q := ⟨p.constant * q.constant, p.constant • q.left + q.constant • p.left,
    p.constant • q.right + q.constant • p.right,
    p.constant • q.mixed + q.constant • p.mixed + rankOne (p.left,q.right) + rankOne (q.left,p.right)⟩

def generated (s : Finset (Term F I J)) : Submodule F ((I→F) → (J→F) → F) :=
  Submodule.span F (Set.range fun t : s => rankOne t.val)

private theorem generated_mono {s t : Finset (Term F I J)} (h : s ⊆ t) : generated s ≤ generated t := by
  apply Submodule.span_mono
  rintro _ ⟨q,rfl⟩
  exact ⟨⟨q.val,h q.property⟩,rfl⟩

private theorem rankOne_mem {s : Finset (Term F I J)} {u : Term F I J} (hu : u ∈ s) :
    rankOne u ∈ generated s := Submodule.subset_span ⟨⟨u,hu⟩,rfl⟩

/-- A single common set of separated products spans all mixed register coefficients. -/
theorem program_span {r : ℕ} (p : Program F (I ⊕ J) r) :
    ∃ s : Finset (Term F I J), s.card ≤ 2*p.cost ∧ ∀ i, (run jets p i).mixed ∈ generated s := by
  classical
  induction p with
  | nil => exact ⟨∅,by simp [Program.cost],fun i => i.elim0⟩
  | @step r p g ih =>
    obtain ⟨s,hs,hp⟩ := ih
    have extend (t : Finset (Term F I J)) (hst : s ⊆ t) (hc : t.card ≤ 2*(p.step g).cost)
        (hnew : (gate jets (run jets p) g).mixed ∈ generated t) :
        ∃ t : Finset (Term F I J), t.card ≤ 2*(p.step g).cost ∧
          ∀ i, (run jets (p.step g) i).mixed ∈ generated t :=
      ⟨t,hc,fun i => Fin.cases hnew (fun j => generated_mono hst (hp j)) i⟩
    cases g with
    | constant c => exact extend s (by rfl) (by simpa [Program.cost,Gate.cost] using hs) (generated s).zero_mem
    | input k =>
      apply extend s (by rfl) (by simpa [Program.cost,Gate.cost] using hs)
      cases k <;> exact (generated s).zero_mem
    | add i j =>
      exact extend s (by rfl) (by simp [Program.cost,Gate.cost]; omega) ((generated s).add_mem (hp i) (hp j))
    | sub i j =>
      exact extend s (by rfl) (by simp [Program.cost,Gate.cost]; omega) ((generated s).sub_mem (hp i) (hp j))
    | mul i j =>
      let u := run jets p i
      let v := run jets p j
      let first : Term F I J := (u.left,v.right)
      let second : Term F I J := (v.left,u.right)
      let t := insert first (insert second s)
      have hst : s ⊆ t := fun _ h => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
      apply extend t hst
      · have h₁ := Finset.card_insert_le second s
        have h₂ := Finset.card_insert_le first (insert second s)
        simp only [t,Program.cost,Gate.cost]
        omega
      · apply (generated t).add_mem
        · apply (generated t).add_mem
          · exact (generated t).add_mem ((generated t).smul_mem _ (generated_mono hst (hp j)))
              ((generated t).smul_mem _ (generated_mono hst (hp i)))
          · exact rankOne_mem (show first ∈ t by simp [t])
        · exact rankOne_mem (show second ∈ t by simp [t])

open Polynomial
abbrev Bivar (F : Type*) [Field F] := Polynomial (Polynomial F)

noncomputable def polys (x : I → F) (y : J → F) : Semantics F (I ⊕ J) (Bivar F) :=
  ⟨fun c => C (C c), Sum.elim (fun i => C (C (x i) * X)) (fun j => C (C (y j)) * X),
   (·+·), (·-·), (·*·)⟩

def coeffAgrees (x : I → F) (y : J → F) (q : Bivar F) (z : Jet F I J) : Prop :=
  (q.coeff 0).coeff 0 = z.constant ∧ (q.coeff 0).coeff 1 = z.left x ∧
    (q.coeff 1).coeff 0 = z.right y ∧ (q.coeff 1).coeff 1 = z.mixed x y

/-- The four jet entries agree with the coefficients in the two formal scaling variables. -/
theorem program_coeff {r : ℕ} (p : Program F (I ⊕ J) r) (i : Fin r) (x : I → F) (y : J → F) :
    coeffAgrees x y (run (polys x y) p i) (run jets p i) := by
  apply simulate (polys x y) jets (coeffAgrees x y) _ _ _ _ _ p i
  · intro c; simp [coeffAgrees,polys,jets,Polynomial.coeff_C]
  · rintro (i|j) <;> simp [coeffAgrees,polys,jets,Polynomial.coeff_C]
  · rintro a b u v ⟨ha,hl,hr,hm⟩ ⟨ha',hl',hr',hm'⟩
    simp [coeffAgrees,polys,jets,ha,hl,hr,hm,ha',hl',hr',hm']
  · rintro a b u v ⟨ha,hl,hr,hm⟩ ⟨ha',hl',hr',hm'⟩
    simp [coeffAgrees,polys,jets,ha,hl,hr,hm,ha',hl',hr',hm']
  · rintro a b u v ⟨ha,hl,hr,hm⟩ ⟨ha',hl',hr',hm'⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      simp [polys,jets,Polynomial.mul_coeff_one,ha,hl,hr,hm,ha',hl',hr',hm',rankOne] <;> ring

private def scalars (w : I → F) : Semantics F I F := ⟨id,w,(·+·),(·-·),(·*·)⟩

private theorem run_scalars {r : ℕ} (p : Program F I r) (w : I → F) (i : Fin r) :
    run (scalars w) p i = p.eval w i := by
  induction p with
  | nil => exact i.elim0
  | step p g ih =>
    refine Fin.cases ?_ (fun j => ih j) i
    cases g with
    | constant c => rfl
    | input k => rfl
    | add j k => exact congrArg₂ (·+·) (ih j) (ih k)
    | sub j k => exact congrArg₂ (·-·) (ih j) (ih k)
    | mul j k => exact congrArg₂ (·*·) (ih j) (ih k)

private noncomputable def specialize (s t : F) : Bivar F →+* F :=
  (evalRingHom t).comp (mapRingHom (evalRingHom s))

private theorem specialize_run {r : ℕ} (p : Program F (I ⊕ J) r) (i : Fin r)
    (x : I → F) (y : J → F) (s t : F) :
    specialize s t (run (polys x y) p i) =
      p.eval (Sum.elim (fun i => x i*s) (fun j => y j*t)) i := by
  rw [← run_scalars]
  apply simulate (polys x y) (scalars _) (fun p c => specialize s t p = c) _ _ _ _ _ p i
  · intro c; simp [polys,scalars,specialize]
  · rintro (i|j) <;> simp [polys,scalars,specialize]
  · intro a b u v hu hv; exact (map_add _ _ _).trans (congrArg₂ (·+·) hu hv)
  · intro a b u v hu hv; exact (map_sub _ _ _).trans (congrArg₂ (·-·) hu hv)
  · intro a b u v hu hv; exact (map_mul _ _ _).trans (congrArg₂ (·*·) hu hv)

private theorem bivar_ext [Infinite F] {p q : Bivar F}
    (h : ∀ s t : F, specialize s t p = specialize s t q) : p = q := by
  apply Polynomial.ext
  intro k
  apply Polynomial.funext
  intro s
  have hp : p.map (evalRingHom s) = q.map (evalRingHom s) := Polynomial.funext (h s)
  simpa only [coeff_map,coe_evalRingHom] using congrArg (fun z : Polynomial F => z.coeff k) hp

/-- Matrix correctness over an infinite field identifies the mixed coefficient exactly. -/
theorem matrix_mixed [Infinite F] {a b c : ℕ} (P : MatrixAlgorithm F a b c) (hP : P.Correct)
    (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) (i : Fin a) (k : Fin c) :
    (run jets P.program (P.output i k)).mixed (fun u => A u.1 u.2) (fun v => B v.1 v.2) =
      (A*B) i k := by
  let x (u : Fin a × Fin b) := A u.1 u.2
  let y (v : Fin b × Fin c) := B v.1 v.2
  have hpoly : run (polys x y) P.program (P.output i k) = C (C ((A*B) i k) * X) * X := by
    apply bivar_ext
    intro s t
    rw [specialize_run]
    let A' : Matrix (Fin a) (Fin b) F := fun l j => A l j*s
    let B' : Matrix (Fin b) (Fin c) F := fun j l => B j l*t
    have hinput : Sum.elim (fun u => x u*s) (fun v => y v*t) = matrixInputs A' B' := by
      funext u; rcases u with ⟨_,_⟩|⟨_,_⟩ <;> rfl
    rw [hinput]
    calc
      _ = (A'*B') i k := congrFun (congrFun (hP A' B') i) k
      _ = (A*B) i k * s * t := by
        change (∑ j, (A i j*s)*(B j k*t)) = (∑ j, A i j*B j k)*s*t
        rw [Finset.sum_mul,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _; ring
      _ = _ := by simp [specialize]
  have h := (program_coeff P.program (P.output i k) x y).2.2.2
  rw [hpoly] at h
  simpa [x,y] using h.symm

private theorem form_coeff [Fintype I] [DecidableEq I] (l : Form F I) (x : I → F) :
    l x = ∑ i, l (Pi.single i 1) * x i := by
  have hx : (∑ i, x i • Pi.single i (1 : F)) = x := by
    ext j
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  calc
    l x = l (∑ i, x i • Pi.single i (1 : F)) := congrArg l hx.symm
    _ = _ := by simp [smul_eq_mul,mul_comm]

/-- The same rank-one products serve every output of a rectangular matrix program. -/
theorem matrix_algorithm [Infinite F] {a b c : ℕ} (P : MatrixAlgorithm F a b c) (hP : P.Correct) :
    ∃ R : ℕ, R ≤ 2*P.cost ∧
      ∃ (U : Fin R → Fin a × Fin b → F) (V : Fin R → Fin b × Fin c → F)
        (W : Fin a → Fin c → Fin R → F),
      ∀ (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) (i : Fin a) (k : Fin c),
        (A * B) i k = ∑ q, W i k q * (∑ u, U q u * A u.1 u.2) * (∑ v, V q v * B v.1 v.2) := by
  classical
  obtain ⟨S,hS,hm⟩ := program_span P.program
  let e : ↥S ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
  have weights (i : Fin a) (k : Fin c) : ∃ w : S → F,
      ∑ u, w u • rankOne u.val = (run jets P.program (P.output i k)).mixed :=
    (Submodule.mem_span_range_iff_exists_fun F).mp (hm _)
  choose w hw using weights
  refine ⟨S.card,hS,fun q u => (e.symm q).val.1 (Pi.single u 1),
    fun q v => (e.symm q).val.2 (Pi.single v 1),fun i k q => w i k (e.symm q),?_⟩
  intro A B i k
  let x (u : Fin a × Fin b) := A u.1 u.2
  let y (v : Fin b × Fin c) := B v.1 v.2
  have h := congrFun (congrFun (hw i k) x) y
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,rankOne] at h
  change _ = (run jets P.program (P.output i k)).mixed (fun u => A u.1 u.2) (fun v => B v.1 v.2) at h
  rw [matrix_mixed P hP] at h
  rw [← h, ← e.sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Equiv.symm_apply_apply]
  rw [form_coeff q.val.1 x,form_coeff q.val.2 y]
  exact (mul_assoc _ _ _).symm

/-- Coefficients of the matrix multiplication tensor on pairs of elementary matrices. -/
theorem matrix_structure_constants [Infinite F] {n : ℕ} (P : MatrixAlgorithm F n n n) (hP : P.Correct) :
    ∃ R : ℕ, R ≤ 2*P.cost ∧
      ∃ (U V : Fin R → Fin n × Fin n → F) (W : Fin n → Fin n → Fin R → F),
      ∀ i j a d e f : Fin n,
        ∑ q, W i j q * U q (a,d) * V q (e,f) = if i=a ∧ d=e ∧ f=j then 1 else 0 := by
  classical
  obtain ⟨R,hR,U,V,W,h⟩ := matrix_algorithm P hP
  refine ⟨R,hR,U,V,W,?_⟩
  intro i j a d e f
  let A : Matrix (Fin n) (Fin n) F := fun u v => if (u,v)=(a,d) then 1 else 0
  let B : Matrix (Fin n) (Fin n) F := fun u v => if (u,v)=(e,f) then 1 else 0
  have hU (q : Fin R) : (∑ u : Fin n × Fin n, U q u * A u.1 u.2) = U q (a,d) := by
    change (∑ u, U q u * (if u=(a,d) then 1 else 0)) = _
    simp [mul_ite]
  have hV (q : Fin R) : (∑ u : Fin n × Fin n, V q u * B u.1 u.2) = V q (e,f) := by
    change (∑ u, V q u * (if u=(e,f) then 1 else 0)) = _
    simp [mul_ite]
  have hm := h A B i j
  simp only [hU,hV] at hm
  rw [← hm,Matrix.mul_apply]
  by_cases hi : i=a
  · subst a
    by_cases hf : f=j
    · subst f
      simp [A,B]
      by_cases hde : d = e
      · simp [hde]
      · simp [hde,Ne.symm hde]
    · simp [A,B,hf,Ne.symm hf]
  · simp [A,B,hi]

theorem square_tables [Infinite F] {n : ℕ} (P : MatrixAlgorithm F n n n) (hP : P.Correct) :
    ∃ R : ℕ, R ≤ 2*P.cost ∧ ∃ x : Fin 3 × Fin R × Fin n × Fin n → F,
      ∀ i j a d e f : Fin n, ∑ q, x (2,q,i,j) * x (0,q,a,d) * x (1,q,e,f) =
        if i=a ∧ d=e ∧ f=j then 1 else 0 := by
  obtain ⟨R,hR,U,V,W,h⟩ := matrix_structure_constants P hP
  let x : Fin 3 × Fin R × Fin n × Fin n → F := fun z =>
    if z.1=0 then U z.2.1 z.2.2 else if z.1=1 then V z.2.1 z.2.2 else W z.2.2.1 z.2.2.2 z.2.1
  exact ⟨R,hR,x,h⟩

end VWZClique.BilinearExtraction
end

/- CliqueSpecialize -/
section

/-! A finite list of complex constants subject to rational polynomial identities
    can be replaced by elements of one fixed number field while preserving all
    the identities. Applied to the cubic equations of bilinear multiplication,
    this preserves the base dimension and the number of products. -/

namespace VWZClique.Specialization

open MvPolynomial
noncomputable section

theorem finite_extension {σ : Type*} [Finite σ] (x : σ → ℂ) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
      ∃ y : σ → E, ∀ p : MvPolynomial σ ℚ, aeval x p = 0 → aeval y p = 0 := by
  let I : Ideal (MvPolynomial σ ℚ) := vanishingIdeal ℚ {x}
  have hprime : I.IsPrime := by dsimp [I]; infer_instance
  have hI : I ≠ ⊤ := hprime.ne_top
  obtain ⟨J,hJ,hIJ⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨z,hz⟩ := eq_vanishingIdeal_singleton_of_isMaximal (AlgebraicClosure ℚ) hJ
  let E := IntermediateField.adjoin ℚ (Set.range z)
  let y : σ → E := fun i => ⟨z i, IntermediateField.subset_adjoin ℚ (Set.range z) ⟨i,rfl⟩⟩
  have ha : ∀ a : AlgebraicClosure ℚ, IsAlgebraic ℚ a := by
    intro a
    convert! (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic a using 1
  have hfinite : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin (fun a _ => (ha a).isIntegral)
  refine ⟨E,hfinite,y,?_⟩
  have embed : E.val.comp (aeval (R := ℚ) y) = aeval z := by
    ext i
    simp [y]
  intro p hp
  have hpI : p ∈ I := (mem_vanishingIdeal_singleton_iff _ _).mpr hp
  have hh := hIJ hpI
  rw [hz, mem_vanishingIdeal_singleton_iff] at hh
  apply E.val.injective
  rw [map_zero]
  exact (DFunLike.congr_fun embed p).trans hh

abbrev Coeff (b r : ℕ) := Fin 3 × Fin r × Fin b × Fin b

/-- Coefficient identities characterizing an exact bilinear matrix product. -/
def Bilinear {F : Type*} [Field F] {b r : ℕ} (x : Coeff b r → F) : Prop :=
  ∀ i j a d e f : Fin b,
    (∑ s : Fin r, x (2,s,i,j) * x (0,s,a,d) * x (1,s,e,f)) =
      if i = a ∧ d = e ∧ f = j then 1 else 0

private def relation {b r : ℕ} (i j a d e f : Fin b) : MvPolynomial (Coeff b r) ℚ :=
  (∑ s : Fin r, X (2,s,i,j) * X (0,s,a,d) * X (1,s,e,f)) -
    if i = a ∧ d = e ∧ f = j then 1 else 0

private theorem at_relation {F : Type*} [Field F] [CharZero F] {b r : ℕ}
    (x : Coeff b r → F) (i j a d e f : Fin b) :
    aeval x (relation i j a d e f) =
      (∑ s : Fin r, x (2,s,i,j) * x (0,s,a,d) * x (1,s,e,f)) -
      (if i = a ∧ d = e ∧ f = j then 1 else 0) := by
  by_cases h : i = a ∧ d = e ∧ f = j <;> simp [relation,h]

theorem bilinear_over_number_field {b r : ℕ} {x : Coeff b r → ℂ} (hx : Bilinear x) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
      ∃ y : Coeff b r → E, Bilinear y := by
  obtain ⟨E,hE,y,hy⟩ := finite_extension x
  refine ⟨E,hE,y,?_⟩
  intro i j a d e f
  apply sub_eq_zero.mp
  rw [← at_relation]
  apply hy
  rw [at_relation]
  exact sub_eq_zero.mpr (hx i j a d e f)

end
end VWZClique.Specialization
end

/- MMUniformBridge -/
section

open OAI.MatrixMultiplication.Arithmetic Filter
namespace VWZClique.BlockMM

/-- Any positive slack above the complex arithmetic exponent admits one fixed
positive-scale integer scheme, independent of the eventual matrix size. -/
theorem integer_uniform_at_omega (ε : ℝ) (hε : 0 < ε) :
    ∃ (B R : ℕ) (hB : 2 ≤ B) (S : Scheme B R), 0 < S.scale ∧
      (∀ n : ℕ, ∀ hn : 1 ≤ n, ∀ A B' : Square (Fin n), ∀ i j,
        scaled S hB hn A B' i j / S.scale^depth B n = (A*B') i j) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        (scalarBudget B R (depth B n) : ℝ) ≤ C*(n:ℝ)^(omega ℂ+ε) := by
  let σ := ε/3
  have hσ : 0 < σ := by dsimp [σ]; linarith
  obtain ⟨C,hC,alg⟩ := MM.omega_admissible ℂ σ hσ
  have lim := (tendsto_rpow_atTop hσ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ev : ∀ᶠ b : ℕ in atTop, 2*C < (b:ℝ)^σ := lim.eventually_gt_atTop (2*C)
  obtain ⟨b,hb,hbC⟩ := ((eventually_ge_atTop 2).and ev).exists
  obtain ⟨P,hP,hbound⟩ := alg b (by omega)
  obtain ⟨r,hr,x,hx⟩ := BilinearExtraction.square_tables P hP
  obtain ⟨E,hE,y,hy⟩ := Specialization.bilinear_over_number_field hx
  let _ := hE
  let T : Factors E (Fin b) (Fin r) :=
    ⟨fun s a d => y (0,s,a,d),fun s e f => y (1,s,e,f),fun i j s => y (2,s,i,j)⟩
  have hT : T.Valid := by
    intro i j a d e f
    have he := hy i j a d e f
    by_cases h : i=a ∧ d=e ∧ f=j <;> simpa [T,h] using he
  have hτ : 2 ≤ omega ℂ+σ+σ := by linarith [MM.omega_two_le ℂ]
  have hrate : (r:ℝ) ≤ (b:ℝ)^(omega ℂ+σ+σ) := by
    have hcast : (r:ℝ) ≤ 2*P.cost := by exact_mod_cast hr
    have hbpos : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    rw [Real.rpow_add hbpos]
    calc
      _ ≤ 2*(C*(b:ℝ)^(omega ℂ+σ)) := hcast.trans (mul_le_mul_of_nonneg_left hbound (by norm_num))
      _ = (b:ℝ)^(omega ℂ+σ)*(2*C) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbC.le (by positivity)
  have h := fixed_uniform T hT hb (omega ℂ+σ+σ) hτ hrate σ hσ
  rwa [show omega ℂ+σ+σ+σ = omega ℂ+ε by dsimp [σ]; ring] at h

end VWZClique.BlockMM
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

/-- One scheme, one explicit breadth-first array evaluator, a near-ω loop count and polynomial workspace. -/
theorem layout_at_omega (η : ℝ) (hη : 0<η) :
    ∃ (b r : ℕ) (S : Scheme b r) (C : ℝ), 2≤b ∧ 0<S.scale ∧ 0<C ∧
      ∀ (n : ℕ) (hn : 1≤n),
        (totalWork b r n : ℝ) ≤ C*(n:ℝ)^(omega ℂ+η) ∧
        (space b r (depth b n) 1 : ℝ) ≤ C*(n:ℝ)^4 ∧
        ∀ (base : ℕ) (m : Memory) (A B : Square (Fin n)) (i j : Fin n),
          execute S base m A B (base+(2*b^(depth b n)+i.val)*b^(depth b n)+j.val) =
            S.scale^(depth b n)*(A*B) i j := by
  let σ := min η 1
  have hσ : 0<σ := lt_min hη (by norm_num)
  obtain ⟨b,r,hb,S,hS,_,C,hC,budget⟩ := integer_uniform_at_omega σ hσ
  have hr := rank_pos S (by omega) hS
  refine ⟨b,r,S,13*C,hb,hS,by positivity,?_⟩
  intro n hn
  have hsum := size_and_work hb hr hn
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hsum' : (space b r (depth b n) 1 : ℝ) + totalWork b r n ≤ 13*(scalarBudget b r (depth b n):ℝ) :=
    by exact_mod_cast hsum
  have hh : (space b r (depth b n) 1 : ℝ)+totalWork b r n ≤ (13*C)*(n:ℝ)^(omega ℂ+σ) :=
    hsum'.trans ((mul_le_mul_of_nonneg_left (budget n hn) (by norm_num)).trans_eq (by ring))
  constructor
  · calc
      _ ≤ (space b r (depth b n) 1 : ℝ)+totalWork b r n := le_add_of_nonneg_left (Nat.cast_nonneg _)
      _ ≤ _ := hh
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn' (add_le_add_right (min_le_left η 1) _)) (by positivity)
  constructor
  · have hex : omega ℂ+σ ≤ (4:ℝ) := by linarith only [MM.omega_le_three ℂ,show σ≤1 from min_le_right _ _]
    have hp := Real.rpow_le_rpow_of_exponent_le hn' hex
    norm_num at hp
    calc
      _ ≤ (space b r (depth b n) 1 : ℝ)+totalWork b r n := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ ≤ _ := hh
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  · intro base m A B i j
    rw [← address_root_output hb hn]
    exact execute_exact S hb hn base m A B i j

end VWZClique.BlockMM.WordLayout
end

/- NativeSquareRate -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout OAI.MatrixMultiplication.Arithmetic

noncomputable def core {b r : ℕ} (S : Scheme b r) := Command.seq (assign rootReg side)
   (.seq (.repeatWhileNegative (downStep S) flag) (.seq leafLayer (.repeatWhileNegative (upStep S) flag)))

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

/-- Uniform positive-height matrix multiplication for every padded input side
chosen by the fixed scheme, with the exponent read from the canonical complex
matrix-multiplication definition. The output bank holds exact scaled integers;
the two input banks hold row-major zero-padded matrices. -/
theorem native_scaled_at_omega (η : ℝ) (hη : 0 < η) :
    ∃ (b r : ℕ) (hb : 2 ≤ b) (S : Scheme b r) (C : ℝ), 0<S.scale ∧ 0<C ∧
      ∀ (n : ℕ) (hn : 1 ≤ n) (W M baseVal : ℕ) (m : IntegerRAM.Memory) (A B : Square (Fin n)),
        let h := depth b n
        Room W M → baseVal+space b r h 1 ≤ M → lowOK baseVal 1 (b^h) m →
        WordLayout.get (heap m) baseVal b h 1 0 0 = padRadix A →
        WordLayout.get (heap m) baseVal b h 1 1 0 = padRadix B →
        ∃ t : ℕ, (t:ℝ) ≤ C*(n:ℝ)^(omega ℂ+η) ∧ ∃ out, Runs W (core S) m t out ∧
          (∀ i j, out ((baseVal+(2*b^h+(i:Fin n).val)*b^h+(j:Fin n).val:ℕ):ℤ) =
            S.scale^h * (A*B) i j) ∧
          (∀ a : ℕ, a<baseVal ∨ baseVal+space b r h 1 ≤ a → out a=m a) ∧ CallerFrame m out := by
  obtain ⟨b,r,hb,S,hs,_,K,hK,cost⟩ := integer_uniform_at_omega η hη
  have hr := rank_pos S (by omega) hs
  obtain ⟨P,hP⟩ := charge_bound S hb hr
  refine ⟨b,r,hb,S,(P:ℝ)*K+4,hs,by positivity,?_⟩
  intro n hn W M baseVal m A B h room spaceFit ready aa bb
  obtain ⟨t,ct,o,run,hheap,caller⟩ := core_runs S hb hr room (by dsimp [h,depth]; omega) (by decide : 0<1) spaceFit m ready
  refine ⟨t,?_,o,run,?_,?_,caller⟩
  · have b₁ := hP h 1 (by decide)
    have b₂ : t ≤ 4+P*scalarBudget b r h := by simpa using ct.trans (Nat.add_le_add_left b₁ 4)
    have b₃ : (t:ℝ) ≤ 4+(P:ℝ)*(scalarBudget b r h:ℝ) := by exact_mod_cast b₂
    have oneN := Real.one_le_rpow (by exact_mod_cast hn : (1:ℝ) ≤ n)
      (show 0 ≤ omega ℂ+η by linarith [MM.omega_two_le ℂ])
    have pc := mul_le_mul_of_nonneg_left (cost n hn) (Nat.cast_nonneg P)
    nlinarith only [b₃,pc,oneN]
  · intro i j
    rw [← address_root_output hb hn]
    change heap o _ = _
    rw [hheap]
    change WordLayout.get (BlockMM.WordLayout.run S h 1 baseVal (heap m)) baseVal b h 1 2 0 (includeIndex hb hn i) (includeIndex hb hn j) = _
    rw [run_result,aa,bb]
    exact (runRadix_eq S hb hn A B i j).trans (scaled_exact S hb hn A B i j)
  · intro a range
    exact (congrFun hheap a).trans (run_frame S h 1 baseVal (heap m) a range)

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareDepth -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM
def nReg : ℤ := -34
def scaleReg : ℤ := -15
def paddingTest : ℤ := -14
def scaleMultiply (c : ℤ) := Expr.mul (.reg scaleReg) (.int c)
def padComparison := Expr.sub side (.add (.reg nReg) .one)
def padIter (b : ℕ) (c : ℤ) := Command.seq (assign (-3) (times side (num b)))
  (.seq (assign scaleReg (scaleMultiply c)) (assign paddingTest padComparison))
def padCommand (b : ℕ) (c : ℤ) := Command.seq (.atom (.one (-3)))
  (.seq (.atom (.one scaleReg)) (.repeatWhileNegative (padIter b c) paddingTest))

def padSteps (b : ℕ) (c : ℤ) := ((times side (num b)).steps+2) +
  (((scaleMultiply c).steps+2)+((padComparison.steps+2)) )+1

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

abbrev srcPointer : ℤ := -17
abbrev srcStride : ℤ := -18
abbrev dstPointer : ℤ := -19
abbrev dstStride : ℤ := -20

def tileAddr (ptr stride : ℤ) := plus (.reg ptr) (plus (times (.reg stride) row) col)
def tileLoad (copy : Bool) : Expr := if copy then .read (tileAddr srcPointer srcStride) else .zero
def tileStore (copy : Bool) := write floor (tileAddr dstPointer dstStride) (tileLoad copy)
def tilePass (copy : Bool) := grid (tileStore copy)
def tileSteps (copy : Bool) := (tileAddr dstPointer dstStride).steps+((tileLoad copy).steps+1)

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

abbrev Setup := List (ℤ × Expr)
def setupCode : Setup → Command
  | [] => .skip
  | (i,e)::xs => .seq (assign i e) (setupCode xs)
def setupCost : Setup → ℕ
  | [] => 0
  | (_,e)::xs => (e.steps+2)+setupCost xs
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

abbrev rawSide : ℤ := -34
abbrev padSide : ℤ := -16
abbrev workPtr : ℤ := -21
abbrev lhsPtr : ℤ := -30
abbrev rhsPtr : ℤ := -31
abbrev resultPtr : ℤ := -32

structure Anchors where
  raw : ℕ
  pad : ℕ
  work : ℕ
  lhs : ℕ
  rhs : ℕ
  result : ℕ

inductive Width where | raw | padded
inductive Origin where | left | right | result | bank (k : ℕ)

def Width.expr : Width → Expr | .raw => .reg rawSide | .padded => .reg padSide
def Width.val (a : Anchors) : Width → ℕ | .raw => a.raw | .padded => a.pad

def Origin.expr : Origin → Expr
  | .left => .reg lhsPtr | .right => .reg rhsPtr | .result => .reg resultPtr
  | .bank k => plus (.reg workPtr) (times (num k) (times (.reg padSide) (.reg padSide)))

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

structure Job where
  copy : Bool
  dim : Width
  src : Origin
  srcStep : Width
  dst : Origin
  dstStep : Width

def Job.setup (q : Job) : Setup :=
  [(-2,.one),(-3,q.dim.expr),(srcPointer,q.src.expr),(srcStride,q.srcStep.expr),
    (dstPointer,q.dst.expr),(dstStride,q.dstStep.expr)]

def Job.cmd (q : Job) := Command.seq (setupCode q.setup) (tilePass q.copy)
def Job.cost (a : Anchors) (q : Job) := setupCost q.setup+gridCost 1 (q.dim.val a) (tileSteps q.copy)

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

/- NativeSquareCore -/
section

end

/- NativeSquareBoundary -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

def fillBank (k : ℕ) : Job := ⟨false,.padded,.left,.raw,.bank k,.padded⟩
def copyInto (src : Origin) (k : ℕ) : Job := ⟨true,.raw,src,.raw,.bank k,.padded⟩
def ingest (src : Origin) (k : ℕ) := Command.seq (fillBank k).cmd (copyInto src k).cmd

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

def chooseArea : Setup :=
  [(padSide,.reg (-3)),(workPtr,plus (.reg resultPtr) (times (.reg rawSide) (.reg rawSide)))]

def startSquare (b : ℕ) (c : ℤ) := Command.seq (padCommand b c) (setupCode chooseArea)

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

def pointCore : Setup := [(-1,.reg workPtr),(-2,.one),(-3,.reg padSide)]

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

def emitJob : Job := ⟨true,.raw,.bank 2,.padded,.result,.raw⟩
noncomputable def multiply {b r : ℕ} (S : Scheme b r) :=
  Command.seq (startSquare b S.scale) (.seq (ingest .left 0) (.seq (ingest .right 1)
    (.seq (setupCode pointCore) (.seq (core S) emitJob.cmd))))

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareMultiply -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

noncomputable def runtimeCost {b r : ℕ} (S : Scheme b r) (a : Anchors) :=
  (2+(depth b a.raw)*padSteps b S.scale + setupCost chooseArea) +
  ((fillBank 0).cost a+(copyInto .left 0).cost a + ((fillBank 1).cost a+(copyInto .right 1).cost a +
  (setupCost pointCore + (4+charge S (depth b a.raw) 1+emitJob.cost a))))

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

/- NativeSquareMultiplyRate -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout OAI.MatrixMultiplication.Arithmetic

def Job.factor (q : Job) := setupCost q.setup+(tileSteps q.copy+15)

theorem Job.cost_le (q : Job) (a : Anchors) (hn : 0<a.raw) (h : a.raw ≤ a.pad) :
    q.cost a ≤ q.factor*(a.pad*a.pad) := by
  have hd : 0 < q.dim.val a := by cases x : q.dim <;> simp [Width.val] <;> omega
  have bound : q.dim.val a ≤ a.pad := by cases x : q.dim <;> simp [Width.val] <;> omega
  have e := grid_cost_bound (N:=1) le_rfl hd (tileSteps q.copy)
  simp only [Nat.one_mul] at e
  have both := Nat.mul_le_mul bound bound
  have posSq : 1 ≤ a.pad*a.pad := Nat.mul_pos (by omega) (by omega)
  have fixed := Nat.mul_le_mul_left (setupCost q.setup) posSq
  simp only [Nat.mul_one] at fixed
  rw [Job.factor,Nat.add_mul]
  exact Nat.add_le_add fixed (e.trans (Nat.mul_le_mul_left _ both))

theorem runtime_le {b r : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hr : 0<r) :
    ∃ P Q : ℕ, ∀ a : Anchors, 1 ≤ a.raw → a.pad=b^(depth b a.raw) →
      runtimeCost S a ≤ P*scalarBudget b r (depth b a.raw) + Q*(a.raw*a.raw) := by
  obtain ⟨P,hP⟩ := charge_bound S hb hr
  let fixed := 2+setupCost chooseArea+setupCost pointCore+4
  let coeff := fixed+padSteps b S.scale+(fillBank 0).factor+(copyInto .left 0).factor+
    (fillBank 1).factor+(copyInto .right 1).factor+emitJob.factor
  refine ⟨P,coeff*(b*b),?_⟩
  intro a hn dim
  have rawPad : a.raw ≤ a.pad := dim ▸ (depth_bounds hb hn).1
  have padMax : a.pad ≤ b*a.raw := dim ▸ (depth_bounds hb hn).2
  have depthPow (j : ℕ) : j ≤ b^j := by
    induction j with
    | zero => simp
    | succ j ih =>
      have pos : 0 < b^j := Nat.pow_pos (by omega)
      rw [pow_succ]; nlinarith
  have depPad : depth b a.raw ≤ a.pad := dim ▸ depthPow _
  have posSq : 1 ≤ a.pad*a.pad := Nat.mul_pos (by omega) (by omega)
  have pp : a.pad ≤ a.pad*a.pad := by simpa using Nat.mul_le_mul_left a.pad (show 1 ≤ a.pad by omega)
  have d := Nat.mul_le_mul_right (padSteps b S.scale) (depPad.trans pp)
  have f := Nat.mul_le_mul_left fixed posSq
  simp only [Nat.mul_one] at f
  have l := (fillBank 0).cost_le a hn rawPad
  have l' := (copyInto .left 0).cost_le a hn rawPad
  have rhsFill := (fillBank 1).cost_le a hn rawPad
  have rhsCopy := (copyInto .right 1).cost_le a hn rawPad
  have u := emitJob.cost_le a hn rawPad
  have charge := hP (depth b a.raw) 1 (by decide)
  simp only [Nat.mul_one] at charge
  have padBound : coeff*(a.pad*a.pad) ≤ (coeff*(b*b))*(a.raw*a.raw) := by
    exact (Nat.mul_le_mul_left coeff (Nat.mul_le_mul padMax padMax)).trans_eq (by ring)
  apply (show runtimeCost S a ≤ P*scalarBudget b r (depth b a.raw) + coeff*(a.pad*a.pad) from ?_).trans
    (Nat.add_le_add_left padBound _)
  simp only [runtimeCost,coeff,Nat.add_mul]
  rw [Nat.mul_comm (depth b a.raw)] 
  rw [Nat.mul_comm (depth b a.raw)] at d
  rw [Nat.mul_comm (a.pad*a.pad) (padSteps b S.scale)] at d
  dsimp only [fixed] at f ⊢
  omega

/-- Near-omega runtime for one fixed native matrix subroutine operating on two
ordinary row-major arrays. The caller provides polynomial scratch capacity. -/
theorem row_major_at_omega (η : ℝ) (hη : 0<η) :
    ∃ (b r : ℕ) (hb : 2 ≤ b) (S : Scheme b r) (C : ℝ), 0<S.scale ∧ 0<C ∧
      ∀ (W M : ℕ) (a : Anchors) (_ : 1 ≤ a.raw), a.pad=b^(depth b a.raw) →
        a.work=a.result+a.raw*a.raw → a.lhs+a.raw*a.raw ≤ a.result → a.rhs+a.raw*a.raw ≤ a.result →
        Room W M → a.work+space b r (depth b a.raw) 1 ≤ M → ∀ (m : IntegerRAM.Memory),
        m rawSide=a.raw → m lhsPtr=a.lhs → m rhsPtr=a.rhs → m resultPtr=a.result →
        ∀ (A B : Square (Fin a.raw)), TileAt m a.lhs a.raw a.raw (lookup A) →
        TileAt m a.rhs a.raw a.raw (lookup B) →
        ∃ t : ℕ, (t:ℝ) ≤ C*(a.raw:ℝ)^(omega ℂ+η) ∧ ∃ o, Runs W (multiply S) m t o ∧
          (∀ i j : Fin a.raw, o (offset a.result a.raw i j)=S.scale^(depth b a.raw)*(A*B) i j) ∧
          (∀ z : ℕ, z<a.result → o z=m z) ∧ outerFrame m o ∧ o scaleReg=S.scale^(depth b a.raw) := by
  obtain ⟨b,r,hb,S,hs,_,K,hK,cost⟩ := integer_uniform_at_omega η hη
  have hr := rank_pos S (by omega) hs
  obtain ⟨P,Q,c⟩ := runtime_le S hb hr
  refine ⟨b,r,hb,S,(P:ℝ)*K+Q+1,hs,by positivity,?_⟩
  intro W M a hn dim area left right cap room m nr lr rr pr A B ha hB
  obtain ⟨t,ct,o,run,done'⟩ := multiply_run S hb hr cap a hn dim area left right room m nr lr rr pr A B ha hB
  refine ⟨t,?_,o,run,done'⟩
  have hbnd := ct.trans (c a hn dim)
  have cast : (t:ℝ) ≤ (P:ℝ)*(scalarBudget b r (depth b a.raw):ℝ)+(Q:ℝ)*((a.raw:ℝ)*a.raw) := by exact_mod_cast hbnd
  have k := mul_le_mul_of_nonneg_left (cost a.raw hn) (Nat.cast_nonneg P)
  have pw := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ)≤a.raw)
    (show (2:ℝ) ≤ omega ℂ+η by linarith [MM.omega_two_le ℂ])
  rw [Real.rpow_two] at pw
  have q := mul_le_mul_of_nonneg_left pw (Nat.cast_nonneg Q)
  have p0 : 0 ≤ (a.raw:ℝ)^(omega ℂ+η) := by positivity
  nlinarith only [cast,k,q,p0]

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareContiguous -/
section

end

/- NativeSquareProjectionCall -/
section

namespace VWZClique.IntegerRAM.Projected
open Structured BlockMM BlockMM.WordLayout
namespace SquareCaller
open SquareCode.Layout

noncomputable def duration {b r : ℕ} (S : Scheme b r) (s : ℕ) :=
  runtimeCost S ⟨s,b^(depth b s),0,0,0,0⟩

end SquareCaller
end VWZClique.IntegerRAM.Projected
end

/- NativeSquareWord -/
section

namespace VWZClique.IntegerRAM.Projected.SquareCaller
open Structured BlockMM BlockMM.WordLayout SquareCode.Layout TrulySubcubicAPSP

/-- The published bit-vector RAM executes the same fixed matrix subroutine.
Only values decoded as signed integers need to fit in a word. -/
theorem word_product {b r W M : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hr : 0<r) (hW : 0<W) (cap : Room W M)
    (a : Anchors) (hn : 1 ≤ a.raw) (dim : a.pad=b^(depth b a.raw)) (area : a.work=a.result+a.raw*a.raw)
    (leftBefore : a.lhs+a.raw*a.raw ≤ a.result) (rightBefore : a.rhs+a.raw*a.raw ≤ a.result)
    (spaceFit : a.work+space b r (depth b a.raw) 1 ≤ M) (m : IntegerRAM.Memory)
    (nreg : m rawSide=a.raw) (lhs : m lhsPtr=a.lhs) (rhs : m rhsPtr=a.rhs) (res : m resultPtr=a.result)
    (A B : Square (Fin a.raw)) (left : TileAt m a.lhs a.raw a.raw (lookup A))
    (right : TileAt m a.rhs a.raw a.raw (lookup B)) :
    ∃ t ≤ duration S a.raw+1, ∃ words : ℤ → BitVec W,
      exec (program (multiply S)) t 0 (encode W m)=some (true,words) ∧
      (∀ i j : Fin a.raw, words (offset a.result a.raw i j) =
        BitVec.ofInt W (S.scale^(depth b a.raw)*(A*B) i j)) ∧
      (∀ i j : Fin a.raw, Fits W (S.scale^(depth b a.raw)*(A*B) i j) →
        (words (offset a.result a.raw i j)).toInt=S.scale^(depth b a.raw)*(A*B) i j) ∧
      ∀ z : ℕ, z<a.result → words z=encode W m z := by
  obtain ⟨t,ct,o,run,values,frame,_,_⟩ := multiply_run S hb hr cap a hn dim area leftBefore rightBefore
    spaceFit m nreg lhs rhs res A B left right
  have cost : runtimeCost S a=duration S a.raw := by
    cases a; simp_all [runtimeCost,duration,Job.cost,fillBank,copyInto,emitJob,Width.val]
  refine ⟨t+1,Nat.add_le_add_right (ct.trans_eq cost) _,encode W o,word_program hW run,?_,?_,?_⟩
  · intro i j
    exact congrArg (BitVec.ofInt W) (values i j)
  · intro i j fit
    simpa only [encode,values] using decode_fits hW fit
  · exact fun z hz => congrArg (BitVec.ofInt W) (frame z hz)

end VWZClique.IntegerRAM.Projected.SquareCaller
end

/- NativeSquareSpace -/
section

namespace VWZClique.BlockMM.WordLayout

/-- The packed matrix calling convention has polynomial peak space for every
fixed scheme, without putting a restriction on its rank. -/
theorem polynomial_space {b r : ℕ} (hb : 2 ≤ b) :
    ∃ C d : ℕ, ∀ n : ℕ, 1 ≤ n → space b r (depth b n) 1 ≤ C*n^d := by
  let B := b*b+r+3
  have sq : b*b ≤ B := by dsimp [B]; omega
  have cap : 3+r ≤ B := by dsimp [B]; omega
  have batch (h N : ℕ) : space b r h N ≤ N*B^(h+1) := by
    induction h generalizing N with
    | zero =>
      simp only [space,size,plane,pow_zero,Nat.mul_one,Nat.zero_add,pow_one]
      exact (Nat.mul_comm 3 N).le.trans (Nat.mul_le_mul_left N (show 3 ≤ B by omega))
    | succ j ih =>
      have dd : b^(j+1)*b^(j+1) ≤ B^(j+1) := by
        rw [←mul_pow]; exact Nat.pow_le_pow_left sq _
      have parent := Nat.mul_le_mul_left (3*N) dd
      have child := ih (N*r)
      have larger := Nat.mul_le_mul_right (N*B^(j+1)) cap
      calc
        space b r (j+1) N = 3*N*(b^(j+1)*b^(j+1))+space b r j (N*r) := by
          rw [space,size,plane]; ring
        _ ≤ 3*N*B^(j+1)+(N*r)*B^(j+1) := Nat.add_le_add parent child
        _ = (3+r)*(N*B^(j+1)) := by ring
        _ ≤ B*(N*B^(j+1)) := larger
        _ = N*B^((j+1)+1) := by rw [pow_succ]; ring
  refine ⟨B*(b^B),B,?_⟩
  intro n hn
  have h := batch (depth b n) 1
  simp only [Nat.one_mul] at h
  calc
    _ ≤ B^(depth b n+1) := h
    _ = B*B^(depth b n) := by rw [pow_succ,Nat.mul_comm]
    _ ≤ B*((b*n)^B) := Nat.mul_le_mul_left B (depth_poly hb hn B)
    _ = (B*b^B)*n^B := by rw [mul_pow,Nat.mul_assoc]

end VWZClique.BlockMM.WordLayout
end

/- NativeSquareChoice -/
section

namespace VWZClique.IntegerRAM.Projected.SquareCaller
open SquareCode.Layout BlockMM BlockMM.WordLayout OAI.MatrixMultiplication.Arithmetic

/-- Choose the same native matrix scheme simultaneously for all projected
tiles, with numeric bounds for its call duration and its scratch address space. -/
theorem choose (η : ℝ) (hη : 0<η) :
    ∃ (b r : ℕ) (_ : 2 ≤ b) (S : Scheme b r) (C : ℝ) (U d : ℕ), 0<S.scale ∧ 0<r ∧ 0<C ∧
      ∀ n : ℕ, 1 ≤ n → ((duration S n:ℕ):ℝ) ≤ C*(n:ℝ)^(omega ℂ+η) ∧
        space b r (depth b n) 1 ≤ U*n^d := by
  obtain ⟨b,r,hb,S,hs,_,K,hK,cost⟩ := integer_uniform_at_omega η hη
  have hr := rank_pos S (by omega) hs
  obtain ⟨P,Q,rate⟩ := runtime_le S hb hr
  obtain ⟨U,d,spaceBound⟩ := polynomial_space (r:=r) hb
  refine ⟨b,r,hb,S,(P:ℝ)*K+Q+1,U,d,hs,hr,by positivity,?_⟩
  intro n hn
  refine ⟨?_,spaceBound n hn⟩
  have bound : duration S n ≤ P*scalarBudget b r (depth b n)+Q*(n*n) :=
    rate ⟨n,b^(depth b n),0,0,0,0⟩ hn rfl
  have cast : (duration S n:ℝ) ≤ (P:ℝ)*(scalarBudget b r (depth b n):ℝ)+(Q:ℝ)*((n:ℝ)*n) := by exact_mod_cast bound
  have mul := mul_le_mul_of_nonneg_left (cost n hn) (Nat.cast_nonneg P)
  have two := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ)≤n)
    (show (2:ℝ) ≤ omega ℂ+η by linarith [MM.omega_two_le ℂ])
  rw [Real.rpow_two] at two
  have q := mul_le_mul_of_nonneg_left two (Nat.cast_nonneg Q)
  have pos : 0 ≤ (n:ℝ)^(omega ℂ+η) := by positivity
  nlinarith only [cast,mul,q,pos]

end VWZClique.IntegerRAM.Projected.SquareCaller
end

/- NativeSquarePublic -/
section

open VWZClique VWZClique.BlockMM VWZClique.BlockMM.WordLayout VWZClique.IntegerRAM
open VWZClique.IntegerRAM.SquareCode.Layout VWZClique.IntegerRAM.Projected.SquareCaller

private theorem wordRoom {n k : ℕ} (hn : 1 ≤ n) : Room ((k+2)*(n.log2+1)) (n^k) := by
  let L := n.log2+1
  have hbase : n<2^L := (Nat.log2_lt (by omega : n≠0)).mp (by simp [L])
  have hlo : n^k≤2^(L*k) := by rw [pow_mul]; exact Nat.pow_le_pow_left hbase.le _
  have hw : L*k<(k+2)*L-1 := by
    have hL : 0<L := by dsimp [L]; omega
    have hm : (k+2)*L=L*k+L+L := by ring
    omega
  have hlt : (n:ℤ)^k<(2:ℤ)^((k+2)*(n.log2+1)-1) := by
    exact_mod_cast hlo.trans_lt (Nat.pow_lt_pow_right (by decide : 1<2) hw)
  intro x lo hi
  simp only [Nat.cast_pow] at lo hi
  exact ⟨(neg_le_neg hlt.le).trans lo,hi.trans_lt hlt⟩

private theorem productMagnitude {n d : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ)
    (ha : ∀ i j, |A i j|≤(n:ℤ)^d) (hb : ∀ i j, |B i j|≤(n:ℤ)^d) (i j : Fin n) :
    |(A*B) i j|≤(n:ℤ)^(1+d+d) := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k : Fin n, |A i k*B k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, (n:ℤ)^d*(n:ℤ)^d := by
      gcongr with k
      rw [abs_mul]
      exact mul_le_mul (ha i k) (hb k j) (abs_nonneg _) (by positivity)
    _ = _ := by simp [pow_add]; ring

theorem solution (η : ℝ) (hη : 0<η) (d : ℕ) :
    ∃ (b w : ℕ) (σ : ℤ) (P : List TrulySubcubicAPSP.Instr) (C : ℝ),
      2≤b ∧ 0<w ∧ 0<σ ∧ 0<C ∧
      ∀ (n : ℕ), 2≤n → ∀ (A B : Matrix (Fin n) (Fin n) ℤ) (m : ℤ → ℤ),
        (∀ i j, |A i j|≤(n:ℤ)^d) → (∀ i j, |B i j|≤(n:ℤ)^d) →
        m (-30)=0 → m (-31)=((n*n:ℕ):ℤ) → m (-32)=((2*(n*n):ℕ):ℤ) → m (-34)=(n:ℤ) →
        (∀ i j : Fin n, m ((n*i.val+j.val:ℕ):ℤ)=A i j) →
        (∀ i j : Fin n, m ((n*n+(n*i.val+j.val):ℕ):ℤ)=B i j) →
        ∃ t : ℕ, (t:ℝ)≤C*(n:ℝ)^(OAI.MatrixMultiplication.Arithmetic.omega ℂ+η) ∧
          ∃ out : ℤ → BitVec (w*(n.log2+1)),
            TrulySubcubicAPSP.exec P t 0 (fun z => BitVec.ofInt _ (m z))=some (true,out) ∧
            ∀ i j : Fin n, (out ((2*(n*n)+(n*i.val+j.val):ℕ):ℤ)).toInt=
              σ^(Nat.log b n+1)*(A*B) i j := by
  obtain ⟨b,r,hb,S,K,U,e,hs,hr,hK,rate⟩ := choose η hη
  let u := S.scale.natAbs
  let F := 3+U+b^u
  let D := 2+e+u+1+d+d
  let k := F+D
  refine ⟨b,k+2,S.scale,Structured.program (multiply S),K+1,hb,by omega,hs,by positivity,?_⟩
  intro n hn A B m hA hB lhs rhs result raw left right
  have hn' : 1≤n := by omega
  let a : Anchors := ⟨n,b^(depth b n),3*(n*n),0,n*n,2*(n*n)⟩
  have cap : F*n^D ≤ n^k := by
    have hF : F≤n^F := (show F<2^F from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hn F)
    simpa [k,pow_add] using Nat.mul_le_mul_right (n^D) hF
  have leD {v : ℕ} (h : v≤D) : n^v≤n^D := Nat.pow_le_pow_right (by omega) h
  have sq : n*n≤n^D := by simpa [pow_two] using leD (show 2≤D by dsimp [D]; omega)
  have lin : n^e≤n^D := leD (by dsimp [D]; omega)
  have workspace : 3*(n*n)+space b r (depth b n) 1 ≤ n^k := by
    apply le_trans _ cap
    calc
      _ ≤ 3*n^D+U*n^D := Nat.add_le_add (Nat.mul_le_mul_left _ sq)
        ((rate n hn').2.trans (Nat.mul_le_mul_left U lin))
      _ ≤ F*n^D := by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by dsimp [F]; omega)
  have li : TileAt m 0 n n (lookup A) := by
    intro i hi j hj
    simpa [lookup,offset,hi,hj] using left ⟨i,hi⟩ ⟨j,hj⟩
  have ri : TileAt m (n*n) n n (lookup B) := by
    intro i hi j hj
    simpa [lookup,offset,hi,hj] using right ⟨i,hi⟩ ⟨j,hj⟩
  have room := wordRoom (k:=k) hn'
  obtain ⟨t,ct,o,run,_,values,_⟩ := word_product S hb hr (by positivity) room a hn' rfl
    (by dsimp [a]; omega) (by dsimp [a]; omega) (by dsimp [a]; omega) workspace m raw lhs rhs result A B li ri
  refine ⟨t,?_,o,run,?_⟩
  · have dur := (rate n hn').1
    change t≤duration S n+1 at ct
    have ct' : (t:ℝ)≤(duration S n:ℝ)+1 := by exact_mod_cast ct
    have one := Real.one_le_rpow (by exact_mod_cast hn' : (1:ℝ)≤n)
      (show 0≤OAI.MatrixMultiplication.Arithmetic.omega ℂ+η by linarith [MM.omega_two_le ℂ])
    nlinarith only [ct',dur,one]
  · intro i j
    apply values i j
    have scale : (S.scale.natAbs^(depth b n):ℕ) * n^(1+d+d) ≤ n^k := by
      apply le_trans _ cap
      calc
        _ ≤ (b*n)^u*n^(1+d+d) := Nat.mul_le_mul_right _ (depth_poly hb hn' u)
        _ = b^u*n^(u+(1+d+d)) := by rw [mul_pow,pow_add n u (1+d+d), Nat.mul_assoc]
        _ ≤ F*n^D := Nat.mul_le_mul (by dsimp [F]; omega) (leD (by dsimp [D]; omega))
    have sc : (u:ℤ)=S.scale := by simp [u,abs_of_pos hs]
    have big : |S.scale^(depth b n)*(A*B) i j| ≤ (n:ℤ)^k := by
      have eq : (S.scale.natAbs:ℤ)^(depth b n)*(n:ℤ)^(1+d+d) ≤ (n:ℤ)^k := by exact_mod_cast scale
      rw [abs_mul,abs_pow,abs_of_pos hs]
      rw [← sc]
      exact (mul_le_mul_of_nonneg_left (productMagnitude A B hA hB i j) (by positivity)).trans eq
    have bi := abs_le.mp big
    apply room
    · exact_mod_cast bi.1
    · exact_mod_cast bi.2
end
