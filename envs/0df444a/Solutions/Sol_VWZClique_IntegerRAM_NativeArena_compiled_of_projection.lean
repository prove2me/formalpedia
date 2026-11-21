-- Prove2me | solution 1 for VWZClique.IntegerRAM.NativeArena.compiled_of_projection
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T14:07:45.437672+00:00
-- url     : https://prove2.me/submissions/57fcf173-e4a4-4c53-a232-0cff14d6645c

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

/- UniformFolds -/
section

open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds






theorem route_static {L : ℕ} (a b : Option (Mask L)) (h : Fin 3) (s : Slot) :
    (route a b h s).1 =
      (route (representative a.isSome) (representative b.isSome) h s).1 := by
  cases s <;> fin_cases h <;> cases a <;> cases b <;> rfl

theorem graph_static {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot) (d : Branch)
    (ha : a.isSome = first d) (hb : b.isSome = second d) :
    foldedGraph a b E = child E d := by
  unfold child
  rw [← ha,← hb]
  unfold foldedGraph
  apply congrArg SimpleGraph.fromEdgeSet
  apply congrArg (fun T : Finset (Sym2 V) => (T : Set (Sym2 V)))
  apply Finset.image_congr
  intro e _
  change s((route a b e.1 e.2.1).1,(route a b e.1 e.2.2).1) = _
  rw [route_static a b e.1 e.2.1,route_static a b e.1 e.2.2]
  rfl








noncomputable def height {H : SimpleGraph V} : Plan H → ℕ
  | .leaf _ _ => 0
  | .split _ _ _ kids => max (height (kids .left)) (max (height (kids .right)) (height (kids .both))) + 1

theorem height_bound {H : SimpleGraph V} (p : Plan H) : height p ≤ Nat.card H.edgeSet := by
  induction p with
  | leaf => exact Nat.zero_le _
  | split H π hp kids ih =>
    change max _ (max _ _) + 1 ≤ _
    apply Nat.succ_le_of_lt
    exact max_lt ((ih .left).trans_lt (branch_smaller H π hp _))
      (max_lt ((ih .right).trans_lt (branch_smaller H π hp _))
        ((ih .both).trans_lt (branch_smaller H π hp _)))

theorem fixed_depth (H : SimpleGraph V) : height (fixed H) ≤ 36 :=
  (height_bound (fixed H)).trans (edge_limit H)

end VWZClique.UniformFolds

end

/- WeightedPadding -/
section

open VWZClique OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.WeightedProof

variable {F I J : Type*} [Field F]


def translateGate {r : ℕ} (tag : J → I ⊕ F) : Gate F J (Fin r) → Gate F I (Fin r)
  | .input j => (tag j).elim Gate.input Gate.constant
  | .constant c => .constant c
  | .add x y => .add x y
  | .sub x y => .sub x y
  | .mul x y => .mul x y

def translate (tag : J → I ⊕ F) : {r : ℕ} → Program F J r → Program F I r
  | _,.nil => .nil
  | _,.step p gate => .step (translate tag p) (translateGate tag gate)


theorem translate_eval (tag : J → I ⊕ F) {r : ℕ} (p : Program F J r) (w : I → F) :
    (translate tag p).eval w = p.eval (fun j => literal w (tag j)) := by
  induction p with
  | nil => rfl
  | step p g ih =>
    simp only [translate,Program.eval,ih]
    cases g with
    | input j => cases ht : tag j <;> simp [translateGate,ht,Gate.eval,literal]
    | _ => rfl



theorem weights_padded {n N : ℕ} (hn : n ≤ N) (H : SimpleGraph V) (w : WeightKey n → F) :
    weightedSum H (fun k : WeightKey N => literal w (padTag k)) = weightedSum H w := by
  classical
  let up : (V → Fin n) → V → Fin N := fun a i => (a i).castLE hn
  have inj : Function.Injective up := by
    intro a b h
    funext i
    exact Fin.ext (congrArg (fun x : Fin N => x.val) (congrFun h i))
  symm
  unfold weightedSum
  apply Fintype.sum_of_injective up inj
  · intro a ha
    have hex : ∃ i, ¬ (a i).val < n := by
      by_contra! h
      exact ha ⟨fun i => ⟨a i,h i⟩,rfl⟩
    obtain ⟨i,hi⟩ := hex
    have hz : (∏ j, literal w (padTag (Sum.inl (j,a j)))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [padTag,hi,literal])
    simp [hz]
  · intro a
    simp [up,padTag,literal]



theorem exists_pow_sandwich {n : ℕ} (hn : 1 ≤ n) : ∃ L : ℕ, n ≤ 2^L ∧ 2^L ≤ 2*n := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt n (by decide : 1 < (2:ℕ))
  let L := Nat.find (⟨k,hk.le⟩ : ∃ k : ℕ, n ≤ 2^k)
  have hL : n ≤ 2^L := Nat.find_spec (⟨k,hk.le⟩ : ∃ k : ℕ, n ≤ 2^k)
  refine ⟨L,hL,?_⟩
  cases h : L with
  | zero => simp; omega
  | succ j =>
    have hj : ¬ n ≤ 2^j := Nat.find_min (⟨k,hk.le⟩ : ∃ k : ℕ, n ≤ 2^k) (by change j<L; omega)
    rw [pow_succ]
    omega

end VWZClique.WeightedProof

end

/- CliqueWord -/
section

/-! Word-level facts for the published RAM representation of clique counting. -/

namespace VWZClique.BlockReduction

open Classical
open TrulySubcubicAPSP

theorem count_le_pow {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : count G k ≤ n^k := by
  classical
  unfold count
  calc
    _ ≤ (Finset.univ.powersetCard k : Finset (Finset (Fin n))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = n.choose k := by simp
    _ ≤ _ := Nat.choose_le_pow _ _

/-- Signed words of the target's width represent every nonnegative value at most `n^k`. -/
theorem word_exact {n k a : ℕ} (hn : 1 ≤ n) (ha : a ≤ n^k) :
    (BitVec.ofInt ((k+2)*(n.log2+1)) (a:ℤ)).toInt = (a:ℤ) := by
  let L := n.log2 + 1
  have hbase : n < 2^L := (Nat.log2_lt (by omega : n ≠ 0)).mp (by simp [L])
  have hlo : n^k ≤ 2^(L*k) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hbase.le _
  have hw : L*k < (k+2)*L-1 := by
    have hL : 0 < L := Nat.succ_pos _
    have hm : (k+2)*L = L*k + L + L := by ring
    omega
  have hlt := ha.trans_lt (hlo.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) hw))
  apply BitVec.toInt_ofInt_eq_self (by positivity) (by exact le_trans (by norm_num : -(2:ℤ)^(_ : ℕ) ≤ 0) (by positivity))
  exact_mod_cast hlt

/-- In particular the specified signed output cell holds the exact unordered count. -/
theorem count_word_exact {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (hn : 1 ≤ n) :
    (BitVec.ofInt ((k+2)*(n.log2+1)) (count G k : ℤ)).toInt = (count G k : ℤ) :=
  word_exact hn (count_le_pow G k)

/-- The row-major representation is the ordinary length-`n²` listing. -/
theorem rowByRow_eq_ofFn {n : ℕ} (A : Fin n → Fin n → ℤ) :
    rowByRow A = List.ofFn (fun z : Fin (n*n) =>
      A (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) := by
  rw [List.ofFn_mul]
  unfold rowByRow
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have he (h : (i:ℕ)*n+j < n*n) : (⟨(i:ℕ)*n+j,h⟩ : Fin (n*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    change (i:ℕ)*n+j = (j:ℕ)+n*i
    ring
  simp only [he, Equiv.symm_apply_apply]

theorem graphInput_length {n : ℕ} (G : SimpleGraph (Fin n)) :
    (MonDepMW.graphInput G).length = 1+n*n := by
  classical
  simp [MonDepMW.graphInput, rowByRow_eq_ofFn, Nat.add_comm]

/-- Reading an input graph at a row-major index retrieves the adjacency bit. -/
theorem graphInput_getD {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    (MonDepMW.graphInput G).getD (1 + (i:ℕ)*n + j) 0 = if G.Adj i j then 1 else 0 := by
  classical
  have h : (i:ℕ)*n+j < n*n := by
    calc
      _ < (i:ℕ)*n+n := Nat.add_lt_add_left j.isLt _
      _ = ((i:ℕ)+1)*n := by ring
      _ ≤ n*n := Nat.mul_le_mul_right _ i.isLt
  have he : (⟨(i:ℕ)*n+j,h⟩ : Fin (n*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    change (i:ℕ)*n+j = (j:ℕ)+n*i
    ring
  rw [show 1+(i:ℕ)*n+j = ((i:ℕ)*n+j)+1 by omega]
  change (rowByRow _).getD ((i:ℕ)*n+j) 0 = _
  rw [rowByRow_eq_ofFn]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h)]
  simp only [List.getElem_ofFn, he, Equiv.symm_apply_apply]

end VWZClique.BlockReduction

end

/- WordGraph -/
section

/-! Native row-major graph reads and grouped input tests for the clique word RAM. -/

namespace VWZClique.IntegerRAM.Graph
open Structured BlockReduction Classical
open TrulySubcubicAPSP

/-- The two endpoints are ordinary vertex numbers. Cell zero holds the graph order. -/
def address {n : ℕ} (u v : Fin n) : ℤ := ((1+u.val*n+v.val : ℕ) : ℤ)

def GraphAt {n : ℕ} (G : SimpleGraph (Fin n)) (m : Memory) : Prop :=
  m 0 = (n:ℤ) ∧ ∀ u v, m (address u v) = if G.Adj u v then 1 else 0

theorem graphAt_input {n : ℕ} (G : SimpleGraph (Fin n)) :
    GraphAt G (input (MonDepMW.graphInput G)) := by
  classical
  refine ⟨?_,?_⟩
  · simp [input,MonDepMW.graphInput]
  · intro u v
    unfold input address
    rw [if_neg (Int.not_lt.mpr (Int.natCast_nonneg _)), Int.toNat_natCast]
    exact graphInput_getD G u v

/-- Within a test the scratch cells are -1 through -4. Every graph cell and every digit register
outside that interval survives a weight test. -/
def Protected (a : ℤ) : Prop := a ≤ -5 ∨ 0 ≤ a

def Frame (m out : Memory) : Prop := ∀ a, Protected a → out a = m a

theorem Frame.refl (m : Memory) : Frame m m := fun _ _ => rfl
theorem Frame.trans {a b c : Memory} (ab : Frame a b) (bc : Frame b c) : Frame a c :=
  fun i hi => (bc i hi).trans (ab i hi)

theorem Frame.write (m : Memory) {r : ℤ} (hr : -5 < r ∧ r < 0) (v : ℤ) :
    Frame m (update m r v) := by
  intro i hi
  have hd : i ≠ r := by rcases hi with h|h <;> omega
  simp [update,hd]

theorem GraphAt.frame {n : ℕ} {G : SimpleGraph (Fin n)} {m out : Memory}
    (h : GraphAt G m) (fr : Frame m out) : GraphAt G out := by
  refine ⟨(fr 0 (Or.inr le_rfl)).trans h.1,?_⟩
  intro u v
  exact (fr _ (Or.inr (Int.natCast_nonneg _))).trans (h.2 u v)

/-- Magnitude available to every indirect address and signed comparison
in these routines. Four times the binary input-order length suffices. -/
def Capacity (W n : ℕ) : Prop := (n:ℤ)^2 < (2:ℤ)^(W-1)

theorem graphCapacity {b n : ℕ} (hb : 4 ≤ b) (hn : 1 ≤ n) :
    Capacity (b*(n.log2+1)) n := by
  have h := BitVec.toInt_lt (x := BitVec.ofInt ((2+2)*(n.log2+1)) ((n^2 : ℕ) : ℤ))
  rw [word_exact (k:=2) hn le_rfl] at h
  apply lt_of_lt_of_le (by simpa using h : (n:ℤ)^2 < (2:ℤ)^((2+2)*(n.log2+1)-1))
  exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_right (Nat.mul_le_mul_right _ hb) 1)

private theorem fits_range {W n : ℕ} {z : ℤ} (capacity : Capacity W n)
    (lo : -((n:ℤ)^2) ≤ z) (hi : z ≤ (n:ℤ)^2) : Fits W z :=
  ⟨(neg_le_neg (le_of_lt capacity)).trans lo, hi.trans_lt capacity⟩

theorem fits_address {W n : ℕ} (cap : Capacity W n) (u v : Fin n) :
    Fits W (address u v) := by
  have hv := v.isLt
  have hh := Nat.mul_le_mul_right n u.isLt
  have hh' : 1+u.val*n+v.val ≤ n*n := by rw [Nat.succ_mul] at hh; omega
  apply fits_range cap
  · exact le_trans (neg_nonpos.mpr (sq_nonneg _)) (Int.natCast_nonneg _)
  · dsimp [address]
    rw [sq]
    exact_mod_cast hh'

theorem fits_difference {W n : ℕ} (cap : Capacity W n) (u v : Fin n) :
    Fits W ((u.val:ℤ)-v.val) := by
  have hu : (u.val:ℤ)<n := by exact_mod_cast u.isLt
  have hv : (v.val:ℤ)<n := by exact_mod_cast v.isLt
  have hsq : (n:ℤ) ≤ (n:ℤ)^2 := by nlinarith [Int.natCast_nonneg u.val]
  apply fits_range cap <;> omega

theorem fits_before_zero {W n : ℕ} (cap : Capacity W n) (u : Fin n) :
    Fits W ((u.val:ℤ)-1) := by
  have hu : (u.val:ℤ)<n := by exact_mod_cast u.isLt
  have hsq : (n:ℤ) ≤ (n:ℤ)^2 := by nlinarith [Int.natCast_nonneg u.val]
  apply fits_range cap <;> omega

namespace Reg
abbrev acc : ℤ := -1
abbrev test : ℤ := -2
abbrev ptr : ℤ := -3
abbrev value : ℤ := -4
abbrev one : ℤ := -5
end Reg

/-- Embedded row-major probe. The caller keeps the constant one in cell -5.
There is no accepting instruction between probes. -/
def probe (x y : ℤ) : Command :=
  .seq (.atom (.mul Reg.ptr 0 x))
  (.seq (.atom (.add Reg.ptr Reg.ptr y))
  (.seq (.atom (.add Reg.ptr Reg.ptr Reg.one))
        (.atom (.load Reg.value Reg.ptr))))

def probed (m : Memory) (a z : ℤ) := update (update m Reg.ptr a) Reg.value z

private theorem overwrite (m : Memory) (d x y : ℤ) :
    update (update m d x) d y = update m d y := by
  funext a
  by_cases e : a = d <;> simp [update,e]

theorem probe_runs {W n : ℕ} {G : SimpleGraph (Fin n)} {m : Memory} (u v : Fin n)
    {x y : ℤ} (_hx : x ≤ -6) (hy : y ≤ -6) (hu : m x = u.val) (hv : m y = v.val)
    (one : m Reg.one = 1) (gr : GraphAt G m) (cap : Capacity W n) :
    Runs W (probe x y) m 4 (probed m (address u v) (if G.Adj u v then 1 else 0)) := by
  let m₁ := update m Reg.ptr (m 0*m x)
  let m₂ := update m₁ Reg.ptr (m₁ Reg.ptr+m₁ y)
  let m₃ := update m₂ Reg.ptr (m₂ Reg.ptr+m₂ Reg.one)
  have hp : m₃ Reg.ptr = address u v := by
    have hy' : y ≠ Reg.ptr := by change y ≠ -3; omega
    simp [m₃,m₂,m₁,update,hy',Reg.ptr,Reg.one,hu,hv,gr.1,one,address] at *
    ring
  have hptr : m₃ = update m Reg.ptr (address u v) := by
    unfold m₃ m₂ m₁
    rw [overwrite,overwrite]
    exact congrArg _ hp
  have ha : address u v ≠ Reg.ptr := by
    have hh : 0 ≤ address u v := Int.natCast_nonneg _
    change address u v ≠ -3
    omega
  have hz : m₃ (m₃ Reg.ptr) = if G.Adj u v then 1 else 0 := by
    rw [hp,hptr]
    simpa [update,ha] using gr.2 u v
  have hf : Fits W (m₃ Reg.ptr) := hp.symm ▸ fits_address cap u v
  have run : Runs W (probe x y) m 4 (update m₃ Reg.value (m₃ (m₃ Reg.ptr))) :=
    Runs.seq (t:=3) (.atom (.mul _ _ _ _))
      (.seq (t:=2) (.atom (.add _ _ _ _))
        (.seq (.atom (.add _ _ _ _)) (.atom (.load _ _ _ hf))))
  rwa [hz,hptr] at run

theorem probe_frame (m : Memory) (a z : ℤ) : Frame m (probed m a z) :=
  (Frame.write _ (by decide : -5 < Reg.ptr ∧ Reg.ptr < 0) _).trans
    (Frame.write _ (by decide : -5 < Reg.value ∧ Reg.value < 0) _)

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


theorem room_pow {b n k : ℕ} (hn : 1 ≤ n) (hb : k+2 ≤ b) :
    Room (b*(n.log2+1)) (n^k) := by
  have h := BitVec.toInt_lt (x := BitVec.ofInt ((k+2)*(n.log2+1)) ((n^k:ℕ):ℤ))
  rw [word_exact (k:=k) hn le_rfl] at h
  exact h.trans_le (pow_le_pow_right₀ (by norm_num)
    (Nat.sub_le_sub_right (Nat.mul_le_mul_right _ hb) 1))


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

/- NativeFrame -/
section

namespace VWZClique.IntegerRAM.NativeFrame
open Structured






theorem different (d : ℕ) {a b : Field} (h : a ≠ b) : reg d a ≠ reg d b := by
  cases a <;> cases b <;> simp_all [reg,Field.offset] <;> omega


theorem reset_runs (W d : ℕ) (m : Memory) :
    ∃ o, Runs W (.atom (.sub (reg d .index) (reg d .index) (reg d .index))) m 1 o ∧
      o (reg d .index) = 0 ∧ ∀ a ≠ reg d .index, o a=m a := by
  refine ⟨_,.atom (.sub _ _ _ _),by simp [update],?_⟩
  intro a h; simp [update,h]

def reset (d : ℕ) : Command := .atom (.sub (reg d .index) (reg d .index) (reg d .index))

/-- The cursor's running sum is already in the return cell. -/
def finish : Command := .skip

def pop (d : ℕ) (lim : ℤ) : Command :=
  let flag := reg d .flag
  let acc := reg d .value
  let ix := reg d .index
  .seq (.atom (.mul flag (reg d .coefficient) (reg (d+1) .value)))
    (.seq (.atom (.add acc acc flag))
      (.seq (.atom (.one flag))
        (.seq (.atom (.add ix ix flag)) (.atom (.sub flag ix lim)))))

/-- The coefficient of this particular child was written by push, and stays
in the parent header over the recursive child call. -/
theorem pop_runs (W d : ℕ) (lim : Field) (hl : lim ≠ .flag) (ha : lim ≠ .value)
    (hi : lim ≠ .index) (m : Memory) :
    ∃ o, Runs W (pop d (reg d lim)) m 5 o ∧
      o (reg d .value) = m (reg d .value) + m (reg d .coefficient)*m (reg (d+1) .value) ∧
      o (reg d .index) = m (reg d .index)+1 ∧
      o (reg d .flag) = m (reg d .index)+1-m (reg d lim) ∧
      ∀ a, a≠reg d .value → a≠reg d .index → a≠reg d .flag → o a=m a := by
  let f := reg d .flag
  let z := reg d .value
  let ix := reg d .index
  let c := reg d .coefficient
  let v := reg (d+1) .value
  let l := reg d lim
  have zf : z ≠ f := different d (by decide)
  have iz : ix ≠ z := different d (by decide)
  have ifl : ix ≠ f := different d (by decide)
  have lf : l ≠ f := different d hl
  have lz : l ≠ z := different d ha
  have li : l ≠ ix := different d hi
  let m₁ := update m f (m c*m v)
  let m₂ := update m₁ z (m z+m c*m v)
  let m₃ := update m₂ f 1
  let m₄ := update m₃ ix (m ix+1)
  let o := update m₄ f (m ix+1-m l)
  have a : Runs W (.atom (.mul f c v)) m 1 m₁ := .atom (.mul _ _ _ _)
  have b : Runs W (.atom (.add z z f)) m₁ 1 m₂ := by
    simpa [m₁,m₂,update,zf] using Runs.atom (Step.add (W:=W) m₁ z z f)
  have e : Runs W (.atom (.one f)) m₂ 1 m₃ := .atom (.one _ _)
  have g : Runs W (.atom (.add ix ix f)) m₃ 1 m₄ := by
    simpa [m₄,m₃,m₂,m₁,update,ifl,iz] using Runs.atom (Step.add (W:=W) m₃ ix ix f)
  have t : Runs W (.atom (.sub f ix l)) m₄ 1 o := by
    simpa [o,m₄,m₃,m₂,m₁,update,lf,li,lz] using Runs.atom (Step.sub (W:=W) m₄ f ix l)
  refine ⟨o,a.seq (b.seq (e.seq (g.seq t))),?_,?_,?_,?_⟩
  · change o z=m z+m c*m v
    simp [o,m₄,m₃,m₂,update,zf,Ne.symm iz]
  · change o ix=m ix+1
    simp [o,m₄,update,ifl]
  · change o f=m ix+1-m l
    simp [o,update]
  · intro a az ai af
    change a≠z at az
    change a≠ix at ai
    change a≠f at af
    simp [o,m₄,m₃,m₂,m₁,update,af,az,ai]



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

/- NativeArena -/
section

namespace VWZClique.IntegerRAM.NativeArena
open Structured SquareCode NativeFrame


def pointer (j : ℕ) : ℤ := 400+(j:ℤ)

def pointerValue (base n j : ℕ) : ℕ :=
  if j<9 then base+j*n else
  if j<90 then base+9*n+(j-9)*(n*n) else maps base n+(j-90)*n

def sizeExp : Expr := .reg 0
def baseExp (d : ℕ) : Expr := .reg (reg d .weights)
def nsq : Expr := .mul sizeExp sizeExp
def cube : Expr := .mul nsq sizeExp
def mapExp (d : ℕ) : Expr :=
  .add (.add (.add (baseExp d) (.add (.mul (.num 9) sizeExp) (.mul (.num 81) nsq)))
    (.mul (.num 7) cube)) (.num 2)
def childExp (d : ℕ) : Expr := .add (.add (mapExp d) (.mul (.num 22) sizeExp)) (.mul (.num 4) sizeExp)

def ptrExp (d j : ℕ) : Expr :=
  if j<9 then .add (baseExp d) (.mul (.num j) sizeExp) else
  if j<90 then .add (.add (baseExp d) (.mul (.num 9) sizeExp)) (.mul (.num (j-9)) nsq) else
  .add (mapExp d) (.mul (.num (j-90)) sizeExp)

theorem ptrExp_value {m : Memory} {d base n : ℕ} (hn : m 0=n) (hb : m (reg d .weights)=base) (j : ℕ) :
    (ptrExp d j).val m=pointerValue base n j := by
  dsimp only [ptrExp,pointerValue]
  split <;> (try split) <;>
    simp [mapExp,metaBase,tableWords,maps,baseExp,sizeExp,nsq,cube,Expr.val,hn,hb,pow_succ] <;> ring

theorem childExp_value {m : Memory} {d base n : ℕ} (hn : m 0=n) (hb : m (reg d .weights)=base) :
    (childExp d).val m=child base n := by
  simp [childExp,child,rows,mapExp,metaBase,tableWords,maps,baseExp,sizeExp,nsq,cube,Expr.val,hn,hb,pow_succ]
  <;> ring

theorem ptrExp_safe {W : ℕ} (m : Memory) (d j : ℕ) : (ptrExp d j).safe SquareCode.Layout.floor W m := by
  have keep := reg_positive d .weights
  dsimp only [ptrExp]; split <;> (try split) <;>
    simp [mapExp,baseExp,sizeExp,nsq,cube,Expr.safe,SquareCode.Layout.floor] <;> omega

theorem childExp_safe {W : ℕ} (m : Memory) (d : ℕ) : (childExp d).safe SquareCode.Layout.floor W m := by
  have keep := reg_positive d .weights
  simp [childExp,mapExp,baseExp,sizeExp,nsq,cube,Expr.safe,SquareCode.Layout.floor] <;> omega

def setPointers (d : ℕ) : ℕ → Command
  | 0 => .skip
  | j+1 => .seq (setPointers d j) (SquareCode.Layout.assign (pointer j) (ptrExp d j))

def setupCost (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => setupCost d j+((ptrExp d j).steps+2)

theorem setup_runs {W d base n : ℕ} (hd : d≤36) (m : Memory) (hn : m 0=n)
    (hb : m (reg d .weights)=base) (J : ℕ) :
    ∃ out, Runs W (setPointers d J) m (setupCost d J) out ∧
      (∀ j<J, out (pointer j) = pointerValue base n j) ∧
      ∀ z, SquareCode.Layout.floor<z → (z<400 ∨ pointer J≤z) → out z=m z := by
  induction J with
  | zero => exact ⟨m,.skip _,by omega,fun _ _ _ => rfl⟩
  | succ j ih =>
    obtain ⟨u,old,ready,fr⟩ := ih
    have un : u 0=n := (fr 0 (by decide) (Or.inl (by decide))).trans hn
    have ub : u (reg d .weights)=base := (fr _ (by dsimp [SquareCode.Layout.floor]; have := reg_positive d .weights; omega)
      (Or.inl (by have := reg_below hd .weights; omega))).trans hb
    have above (i : ℕ) : SquareCode.Layout.floor < pointer i := by dsimp [pointer,SquareCode.Layout.floor]; omega
    obtain ⟨o,run,changeAt⟩ := SquareCode.Layout.assign_run (W:=W) u (reg:=pointer j) (above j)
      (ptrExp d j) (ptrExp_safe u d j)
    refine ⟨o,.seq old run,?_,?_⟩
    · intro i hi
      rw [changeAt _ (above i)]
      by_cases h : i=j
      · subst i
        simpa using ptrExp_value un ub j
      · rw [if_neg (by dsimp [pointer]; omega)]
        exact ready i (by omega)
    · intro z hz range
      have neq : z≠pointer j := by dsimp [pointer] at *; omega
      rw [changeAt z hz,if_neg neq]
      apply fr z hz
      dsimp [pointer] at *; omega

end VWZClique.IntegerRAM.NativeArena

end

/- NativeWidth -/
section

namespace VWZClique.IntegerRAM.NativeArena
open BlockReduction WeightedProof


theorem atDepth_formula (root n d : ℕ) :
    atDepth root n d = root+d*(tableWords n+7*n^3+2+26*n) := by
  induction d with
  | zero => simp [atDepth]
  | succ d ih => simp only [atDepth,child,rows,maps,metaBase,ih,Nat.succ_mul]; ring


/-- One logarithmic width works for every polynomially bounded arena address
and every polynomially bounded quantity tested by a branch. The width constant
depends only on the static scheme, k and the fixed polynomial. -/
theorem graph_room (k c p : ℕ) : ∃ b : ℕ, k+3 ≤ b ∧ ∀ n : ℕ, 2≤n →
    Graph.Division.Room (b*(n.log2+1)) (c*((2^graphLength n k)^p)) := by
  let t := (k+8)/9
  let B := c+p*(t+1)
  refine ⟨max (k+3) (B+2),le_max_left _ _,?_⟩
  intro n hn
  have Npos : 1≤n^t := Nat.one_le_pow _ _ (by omega)
  obtain ⟨u,lo,hi⟩ := exists_pow_sandwich Npos
  have upper : 2^graphLength n k≤2*n^t :=
    (Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow lo)).trans hi
  have lng : 2^graphLength n k≤n^(t+1) := upper.trans (by rw [pow_succ]; nlinarith)
  have cps : c ≤ n^c := (Nat.lt_two_pow_self (n:=c)).le.trans (Nat.pow_le_pow_left hn _)
  have bound := Nat.mul_le_mul cps (Nat.pow_le_pow_left lng p)
  have eqn : n^c * (n^(t+1))^p=n^B := by rw [←pow_mul,←pow_add]; dsimp [B]; ring_nf
  rw [eqn] at bound
  exact lt_of_le_of_lt (by exact_mod_cast bound) (Graph.Division.room_pow (by omega) (le_max_right _ _))

theorem child_polynomial {b n : ℕ} (hn : 1≤n) : child b n ≤ b+125*n^3 := by
  have lo : n≤n^3 := by simpa using (Nat.pow_le_pow_right hn (by decide : 1≤3))
  have sq : n*n≤n^3 := by simpa [pow_two] using (Nat.pow_le_pow_right hn (by decide : 2≤3))
  dsimp [child,rows,maps,metaBase,tableWords]
  omega

end VWZClique.IntegerRAM.NativeArena

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

/- WordGraphWeights -/
section

/-! Fixed native code for every blocked unary or edge weight. The two block
labels are supplied as vertex digits in read-only registers. -/

namespace VWZClique.IntegerRAM.Graph
open Structured BlockReduction Classical
open TrulySubcubicAPSP

private def foreach {ι : Type*} {t : ℕ} (f : Fin t → List ι) : List ι :=
  (List.finRange t).flatMap f

private theorem foreach_iff {ι : Type*} {t : ℕ} (f : Fin t → List ι) (P : ι → Prop) :
    (∀ c ∈ foreach f, P c) ↔ ∀ i, ∀ c ∈ f i, P c := by
  constructor
  · intro h i c hc
    exact h c (List.mem_flatMap.mpr ⟨i,by simp,hc⟩)
  · intro h c hc
    obtain ⟨i,_,hc⟩ := List.mem_flatMap.mp hc
    exact h i c hc

private theorem foreach_length {ι : Type*} {t B : ℕ} (f : Fin t → List ι)
    (h : ∀ i, (f i).length ≤ B) : (foreach f).length ≤ t*B := by
  have go (xs : List (Fin t)) : (xs.flatMap f).length ≤ xs.length * B := by
    induction xs with
    | nil => simp
    | cons i xs ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
      have hb := h i
      omega
  simpa [foreach] using go (List.finRange t)







abbrev Side (t : ℕ) := Fin t ⊕ Fin t




/-- One unary group or an ordered pair of groups. Its program is independent of n
and of the graph. -/
inductive Shape where
  | unary (i : V)
  | cross (i j : V)


def Shape.key {n t : ℕ} (x y : Fin (n^t)) : Shape → WeightKey (n^t)
  | .unary i => .inl (i,x)
  | .cross i j => .inr (i,j,x,y)

def digits {n t : ℕ} (x y : Fin (n^t)) : Side t → Fin n := Sum.elim (digit x) (digit y)



def digitRegister {t : ℕ} : Side t → ℤ
  | .inl p => -6 - 2*(p.val:ℤ)
  | .inr p => -7 - 2*(p.val:ℤ)

theorem digitRegister_le {t : ℕ} (i : Side t) : digitRegister i ≤ -6 := by
  cases i <;> simp only [digitRegister] <;> omega






end VWZClique.IntegerRAM.Graph

end

/- NativeMaskScanTable -/
section

namespace VWZClique.IntegerRAM.MaskScan
open Structured Graph Butterfly




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



theorem totalN_le (b h z j : ℕ) : totalN b h z j ≤ j := by
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih => simp only [totalN,localN]; split <;> omega



end VWZClique.IntegerRAM.MaskScan

end

/- MaskEnumeration -/
section

open VWZClique
namespace VWZClique.RankSwap.MaskEnumeration











theorem scan_range_bound (L : ℕ) : 5^L ≤ (2^L)^3 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (by decide) L

/-- Decode the signed pin directly from a base-five digit. -/
def integerMask {L : ℕ} (w : Digits L) : Mask L := fun i =>
  if w i=0 then none else some (unitBits ((w i).val-1))


theorem unpack_mask {L d : ℕ} (w : Digits L) (h : (support w).card ≤ d) :
    termMask (unpack w h) = integerMask w := by
  funext i
  by_cases hi : w i=0 <;> simp [unpack,termMask,integerMask,maskBit,active,support,hi]

theorem unpack_weight {L d : ℕ} (w : Digits L) (h : (support w).card ≤ d) (c : ℕ → ℤ) :
    termCoeff c (unpack w h) = integerWeight c w := by
  unfold termCoeff integerWeight
  apply congrArg (c (support w).card * ·)
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : w i=0
  · simp [unpack,active,signBit,support,hi]
  · have reg : (2 ≤ (w i).val-1) ↔ (3 ≤ (w i).val) := by omega
    simp [unpack,active,signBit,support,hi,reg]

/-- The sparse part of the actual decomposition can be summed by scanning
the range of integers, testing the number of nonzero digits and decoding each
survivor by explicit formulas. -/
theorem sparse_sum_as_range {L d : ℕ} (c : ℕ → ℤ) (x y : PairBits L) :
    (∑ t : Terms L d, (termCoeff c t : ℚ) * swapEntry (termMask t) x y) =
      ∑ z : Fin (5^L), if z ∈ allowed L d then
        let w : Digits L := finFunctionFinEquiv.symm z
        (integerWeight c w : ℚ) * swapEntry (integerMask w) x y else 0 := by
  classical
  let e := enumerate L d
  let f (z : Fin (5^L)) : ℚ :=
    (integerWeight c (finFunctionFinEquiv.symm z : Digits L) : ℚ) *
      swapEntry (integerMask (finFunctionFinEquiv.symm z)) x y
  calc
    _ = ∑ z : ↥(allowed L d), f z := by
      apply Fintype.sum_equiv e
      intro t
      let w : Digits L := finFunctionFinEquiv.symm (e t).val
      have hs : (support w).card ≤ d := (Finset.mem_filter.mp (e t).property).2
      have hb : unpack w hs = t := e.left_inv t
      have hm := unpack_mask w hs
      have hc := unpack_weight w hs c
      rw [hb] at hm hc
      change _ = (integerWeight c w : ℚ) * swapEntry (integerMask w) x y
      rw [hm,hc]
    _ = ∑ z ∈ allowed L d, f z := Finset.sum_coe_sort _ _
    _ = _ := by simp [f,Finset.sum_ite_mem]

/-- The low-rank diagonal can likewise be generated by scanning 4^L integers. -/
theorem diagonal_as_range (L a d : ℕ) (f : BasisLabel L → ℚ) :
    ∑ j ∈ outside L a d, f j =
      ∑ z : Fin (4^L), if (finFunctionFinEquiv.symm z : BasisLabel L) ∈ outside L a d
        then f (finFunctionFinEquiv.symm z) else 0 := by
  classical
  calc
    _ = ∑ j : BasisLabel L, if j ∈ outside L a d then f j else 0 := by simp
    _ = _ := Fintype.sum_equiv finFunctionFinEquiv _ _ (fun j => by simp)

/-- The entire finite-window identity has integer-indexed summation domains.
An implementation can compact the two filtered tables once per length. -/
theorem generated_identity (K L : ℕ) (x y : PairBits L) :
    let a := UniformFolds.lower K L
    let d := UniformFolds.width K L
    let c := UniformFolds.windowCoeff K L
    (if x=y then (1:ℚ) else 0) =
      (∑ z : Fin (4^L), let j : BasisLabel L := finFunctionFinEquiv.symm z
        if j ∈ outside L a d then UniformFolds.windowDiagonal K L j * basisEntry j x * basisEntry j y else 0) +
      ∑ z : Fin (5^L), let w : Digits L := finFunctionFinEquiv.symm z
        if z ∈ allowed L d then (integerWeight c w : ℚ)*swapEntry (integerMask w) x y else 0 := by
  let a := UniformFolds.lower K L
  let d := UniformFolds.width K L
  let c := UniformFolds.windowCoeff K L
  have h := (UniformFolds.windowExpansion K L).identity x y
  change _ = (∑ j ∈ outside L a d, UniformFolds.windowDiagonal K L j * basisEntry j x * basisEntry j y) +
    ∑ t : Terms L d, (termCoeff c t : ℚ)*swapEntry (termMask t) x y at h
  rw [diagonal_as_range,sparse_sum_as_range] at h
  exact h

end VWZClique.RankSwap.MaskEnumeration

end

/- EnumerationBudget -/
section

namespace VWZClique.RankSwap.MaskEnumeration

theorem digit_extraction {b L : ℕ} (x : Fin (b^L)) (p : Fin L) :
    ((finFunctionFinEquiv.symm x : Fin L → Fin b) p).val = x.val / b^p.val % b := rfl

private theorem length_sum (L : ℕ) : (L+1)*25^L ≤ 4*32^L := by
  induction L with
  | zero => decide
  | succ L ih =>
    have small : 25^L ≤ 32^L := Nat.pow_le_pow_left (by decide) L
    calc
      _ = 25*((L+1)*25^L) + 25*25^L := by rw [pow_succ]; ring
      _ ≤ 25*(4*32^L)+25*32^L :=
        Nat.add_le_add (Nat.mul_le_mul_left 25 ih) (Nat.mul_le_mul_left 25 small)
      _ ≤ _ := by rw [pow_succ]; omega


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




theorem maskKey_iff {L d : ℕ} (z : Fin (5^L)) : maskKey L d z.val = true ↔ z∈allowed L d := by
  have hn := totalN_le 5 1 z.val L
  simp only [maskKey,selected,decide_eq_true_eq,allowed,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [← mask_pop z]; omega


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


theorem slot_filled (key : ℕ → Bool) (N r : ℕ) (hr : r<rank key N) :
    ∃ j<N, key j=true ∧ rank key j=r := by
  induction N with
  | zero => simp [rank] at hr
  | succ N ih =>
    by_cases old : r<rank key N
    · obtain ⟨j,hj,h,e⟩ := ih old; exact ⟨j,by omega,h,e⟩
    · by_cases h : key N=true
      · simp only [rank,h,if_true] at hr; exact ⟨N,by omega,h,by omega⟩
      · simp [rank,h] at hr; omega

private theorem scale (L : ℕ) : (L+1)*25^L ≤ 4*32^L := by
  induction L with
  | zero => decide
  | succ L ih =>
    have u : 25^L ≤ 32^L := Nat.pow_le_pow_left (by decide) L
    calc
      _ = 25*((L+1)*25^L)+25*25^L := by rw [pow_succ]; ring
      _ ≤ 25*(4*32^L)+25*32^L := Nat.add_le_add (Nat.mul_le_mul_left _ ih) (Nat.mul_le_mul_left _ u)
      _ ≤ _ := by rw [pow_succ]; omega


end VWZClique.IntegerRAM.MaskScan

end

/- WordGraphPacked -/
section

/-! Fixed native computation of one grouped graph weight from two packed integer
labels and the original row-major adjacency array. -/

namespace VWZClique.IntegerRAM.Graph
open Structured BlockReduction
open TrulySubcubicAPSP

def leftCell (p : ℕ) : ℤ := -6-2*(p:ℤ)
def rightCell (p : ℕ) : ℤ := -7-2*(p:ℤ)
def leftArg (t : ℕ) : ℤ := -8-2*(t:ℤ)
def rightArg (t : ℕ) : ℤ := -9-2*(t:ℤ)

def Kept (t : ℕ) (z : ℤ) : Prop :=
  (z ≤ -6 ∨ 0 ≤ z) ∧ ∀ p<t, z ≠ leftCell p ∧ z ≠ rightCell p

theorem kept_nonneg {z : ℤ} (hz : 0 ≤ z) (t : ℕ) : Kept t z := by
  refine ⟨Or.inr hz,?_⟩
  intro p _
  simp only [leftCell,rightCell]
  omega

theorem kept_leftArg (t : ℕ) : Kept t (leftArg t) := by
  constructor
  · left; unfold leftArg; omega
  · intro p h; simp only [leftArg,leftCell,rightCell]; omega

theorem kept_rightArg (t : ℕ) : Kept t (rightArg t) := by
  constructor
  · left; unfold rightArg; omega
  · intro p h; simp only [rightArg,leftCell,rightCell]; omega

theorem leftCell_le (p : ℕ) : leftCell p ≤ -6 := by unfold leftCell; omega
theorem rightCell_le (p : ℕ) : rightCell p ≤ -6 := by unfold rightCell; omega
theorem leftCell_inj : Function.Injective leftCell := by intro i j h; unfold leftCell at h; omega
theorem rightCell_inj : Function.Injective rightCell := by intro i j h; unfold rightCell at h; omega
theorem cells_distinct (i j : ℕ) : leftCell i ≠ rightCell j := by unfold leftCell rightCell; omega

theorem digit_val {n t : ℕ} (x : Fin (n^t)) (p : Fin t) :
    (digit x p).val = x.val/n^p.val%n := rfl






end VWZClique.IntegerRAM.Graph

end

/- WordGraphCursor -/
section

namespace VWZClique.IntegerRAM.Graph.Table
open Structured BlockReduction

inductive Cell where
  | x | y | ptr | unit | cols | lim | index | flag
  deriving DecidableEq

def cell (t : ℕ) : Cell → ℤ
  | .x => leftArg t
  | .y => rightArg t
  | .ptr => -10-2*(t:ℤ)
  | .unit => -11-2*(t:ℤ)
  | .cols => -12-2*(t:ℤ)
  | .lim => -13-2*(t:ℤ)
  | .index => -14-2*(t:ℤ)
  | .flag => -15-2*(t:ℤ)

theorem cell_below (t : ℕ) (c : Cell) : cell t c≤ -8 := by
  cases c <;> simp only [cell,leftArg,rightArg] <;> omega

@[simp] theorem cell_eq {t : ℕ} {a b : Cell} : cell t a=cell t b ↔ a=b := by
  constructor
  · intro h
    cases a <;> cases b <;> simp_all [cell,leftArg,rightArg] <;> omega
  · exact congrArg _

@[simp] theorem nat_ne_cell (t k : ℕ) (c : Cell) : (k:ℤ) ≠ cell t c := by
  have := cell_below t c; omega

@[simp] theorem cell_ne_nat (t k : ℕ) (c : Cell) : cell t c ≠ (k:ℤ) := (nat_ne_cell t k c).symm

@[simp] theorem zero_ne_cell (t : ℕ) (c : Cell) : 0 ≠ cell t c := nat_ne_cell t 0 c

theorem cell_kept (t : ℕ) (c : Cell) : Kept t (cell t c) := by
  constructor
  · left; have := cell_below t c; omega
  · intro p h; cases c <;> simp only [cell,leftArg,rightArg,leftCell,rightCell] <;> omega

/-- Register contents between consecutive positions in the same shape's table. -/
structure Controls (t C N p x y q : ℕ) (m : Memory) : Prop where
  unit : m (cell t .unit)=1
  cols : m (cell t .cols)=C
  lim : m (cell t .lim)=N
  ptr : m (cell t .ptr)=p
  x : m (cell t .x)=x
  y : m (cell t .y)=y
  index : m (cell t .index)=q

theorem Controls.transfer {t C N p x y q : ℕ} {a b : Memory} (h : Controls t C N p x y q a)
    (eqs : ∀ c, b (cell t c)=a (cell t c)) : Controls t C N p x y q b :=
  ⟨(eqs _).trans h.unit,(eqs _).trans h.cols,(eqs _).trans h.lim,
   (eqs _).trans h.ptr,(eqs _).trans h.x,(eqs _).trans h.y,(eqs _).trans h.index⟩

def carry (t : ℕ) : Command :=
  .seq (.atom (.sub (cell t .y) (cell t .y) (cell t .y)))
    (.atom (.add (cell t .x) (cell t .x) (cell t .unit)))

def advance (t : ℕ) : Command :=
  .seq (.atom (.store (cell t .ptr) Reg.acc))
  (.seq (.atom (.add (cell t .ptr) (cell t .ptr) (cell t .unit)))
  (.seq (.atom (.add (cell t .y) (cell t .y) (cell t .unit)))
  (.seq (.atom (.sub (cell t .flag) (cell t .y) (cell t .cols)))
        (.whenNonnegative (cell t .flag) (carry t)))))

def xNext (C x y : ℕ) := if y+1<C then x else x+1
def yNext (C y : ℕ) := if y+1<C then y+1 else 0

theorem advance_runs {W M t C N p x y q : ℕ} {m : Memory}
    (r : Controls t C N p x y q m) (hy : y<C) (hp : p≤M) (hc : C≤M)
    (room : Division.Room W M) :
    ∃ out, Runs W (advance t) m (4+(if y+1<C then 1 else 3)) out ∧
      Controls t C N (p+1) (xNext C x y) (yNext C y) q out ∧
      ∀ z : ℕ, out (z:ℤ) = if z=p then m Reg.acc else m z := by
  let a := update m (p:ℤ) (m Reg.acc)
  let b := update a (cell t .ptr) ((p:ℤ)+1)
  let c := update b (cell t .y) ((y:ℤ)+1)
  let d := update c (cell t .flag) ((y:ℤ)+1-C)
  have pa : Fits W (m (cell t .ptr)) := by rw [r.ptr]; apply room.fits <;> omega
  have first : Runs W (.atom (.store (cell t .ptr) Reg.acc)) m 1 a := by
    simpa only [a,r.ptr] using Runs.atom (Step.store m (cell t .ptr) Reg.acc pa)
  have ra : Controls t C N p x y q a := r.transfer (fun i => by simp [a,update])
  have second : Runs W (.atom (.add (cell t .ptr) (cell t .ptr) (cell t .unit))) a 1 b := by
    simpa only [b,ra.ptr,ra.unit] using Runs.atom (Step.add (W:=W) a (cell t .ptr) (cell t .ptr) (cell t .unit))
  have third : Runs W (.atom (.add (cell t .y) (cell t .y) (cell t .unit))) b 1 c := by
    simpa [b,c,update,ra.y,ra.unit] using Runs.atom (Step.add (W:=W) b (cell t .y) (cell t .y) (cell t .unit))
  have fourth : Runs W (.atom (.sub (cell t .flag) (cell t .y) (cell t .cols))) c 1 d := by
    simpa [d,c,b,update,ra.cols] using Runs.atom (Step.sub (W:=W) c (cell t .flag) (cell t .y) (cell t .cols))
  have dt : d (cell t .flag) = (y:ℤ)+1-C := by simp [d,update]
  have hd : Fits W (d (cell t .flag)) := by rw [dt]; apply room.fits <;> omega
  have cin : Controls t C N (p+1) x (y+1) q d := by
    constructor <;> simp [d,c,b,update,ra.unit,ra.cols,ra.lim,ra.ptr,ra.x,ra.index]
  have data (z : ℕ) : d z = if z=p then m Reg.acc else m z := by
    simp [d,c,b,a,update]
  by_cases small : y+1<C
  · refine ⟨d,?_,by simpa [xNext,yNext,small] using cin,data⟩
    have branch := Runs.guard_skip (c:=carry t) hd (show d (cell t .flag)<0 by omega)
    simpa [advance,small] using Runs.seq first (.seq second (.seq third (.seq fourth branch)))
  · let e := update d (cell t .y) 0
    let f := update e (cell t .x) ((x:ℤ)+1)
    have c₁ : Runs W (.atom (.sub (cell t .y) (cell t .y) (cell t .y))) d 1 e := by
      simpa [e] using Runs.atom (Step.sub (W:=W) d (cell t .y) (cell t .y) (cell t .y))
    have c₂ : Runs W (.atom (.add (cell t .x) (cell t .x) (cell t .unit))) e 1 f := by
      simpa [e,f,update,cin.x,cin.unit] using Runs.atom (Step.add (W:=W) e (cell t .x) (cell t .x) (cell t .unit))
    have branch := Runs.guard_take (c:=carry t) hd (show ¬ d (cell t .flag)<0 by omega) (.seq c₁ c₂)
    refine ⟨f,?_,?_,?_⟩
    · simpa [advance,small] using Runs.seq first (.seq second (.seq third (.seq fourth branch)))
    · constructor <;> simp [xNext,yNext,small,e,f,update,cin.unit,cin.cols,cin.lim,cin.ptr,cin.index]
    · intro z
      simpa [f,e,update] using data z

theorem Controls.tick {t C N p x y q : ℕ} {m : Memory} (h : Controls t C N p x y q m) :
    Controls t C N p x y (q+1) (nextMemory m (cell t .index) (cell t .flag) q N) := by
  constructor <;> simp [nextMemory,update,h.unit,h.cols,h.lim,h.ptr,h.x,h.y]

theorem tick_data (t q N z : ℕ) (m : Memory) :
    nextMemory m (cell t .index) (cell t .flag) q N (z:ℤ)=m z := by simp [nextMemory,update]

end VWZClique.IntegerRAM.Graph.Table

end

/- WordGraphSetup -/
section

namespace VWZClique.IntegerRAM.Graph.Table
open Structured BlockReduction

def columns (s : Shape) (N : ℕ) : ℕ := match s with
  | .unary _ => 1
  | .cross _ _ => N

theorem cols_le (s : Shape) {N : ℕ} (h : 0<N) : columns s N ≤ N := by cases s <;> simp [columns] <;> omega
theorem cols_pos (s : Shape) {N : ℕ} (h : 0<N) : 0<columns s N := by cases s <;> simp [columns,h]

private theorem overwrite (m : Memory) (d u v : ℤ) : update (update m d u) d v=update m d v := by
  funext z; by_cases h:z=d <;> simp [update,h]

def power (t : ℕ) : ℕ → Command
  | 0 => .atom (.one (cell t .lim))
  | j+1 => .seq (power t j) (.atom (.mul (cell t .lim) (cell t .lim) 0))

theorem power_runs (W t j : ℕ) (m : Memory) :
    Runs W (power t j) m (j+1) (update m (cell t .lim) (m 0 ^ j)) := by
  induction j with
  | zero => simpa [power] using Runs.atom (Step.one (W:=W) m (cell t .lim))
  | succ j ih =>
    let z := update m (cell t .lim) (m 0^j)
    have act := Runs.atom (Step.mul (W:=W) z (cell t .lim) (cell t .lim) 0)
    have hl : z (cell t .lim)=m 0 ^ j := by simp [z,update]
    have hd : z 0=m 0 := by simp [z,update]
    rw [hl,hd,←pow_succ] at act
    simpa only [power,z,overwrite] using Runs.seq ih act

def colCode (t : ℕ) : Shape → Command
  | .unary _ => .atom (.one (cell t .cols))
  | .cross _ _ => .atom (.mul (cell t .cols) (cell t .lim) (cell t .unit))

theorem colCode_runs {W t N : ℕ} (s : Shape) {m : Memory}
    (hl : m (cell t .lim)=(N:ℤ)) (hu : m (cell t .unit)=1) :
    Runs W (colCode t s) m 1 (update m (cell t .cols) (columns s N)) := by
  cases s with
  | unary i => simpa [colCode,columns] using Runs.atom (Step.one (W:=W) m (cell t .cols))
  | cross i j =>
    simpa [colCode,columns,hl,hu] using Runs.atom (Step.mul (W:=W) m (cell t .cols) (cell t .lim) (cell t .unit))

def zeroCell (d : ℤ) : Command := .atom (.sub d d d)

theorem zeroCell_runs (W : ℕ) (m : Memory) (d : ℤ) :
    Runs W (zeroCell d) m 1 (update m d 0) := by simpa [zeroCell] using Runs.atom (Step.sub (W:=W) m d d d)

def setup (t : ℕ) (s : Shape) : Command :=
  .seq (.atom (.one (cell t .unit)))
  (.seq (power t t)
  (.seq (colCode t s)
  (.seq (.atom (.mul (cell t .lim) (cell t .lim) (cell t .cols)))
  (.seq (zeroCell (cell t .x)) (.seq (zeroCell (cell t .y)) (zeroCell (cell t .index)))))))

theorem setup_runs {W n t base : ℕ} (s : Shape) (m : Memory) (hd : m 0=n)
    (hp : m (cell t .ptr)=base) :
    ∃ out, Runs W (setup t s) m (t+7) out ∧
      Controls t (columns s (n^t)) ((n^t)*columns s (n^t)) base 0 0 0 out ∧
      ∀ z : ℕ, out z=m z := by
  let N := n^t
  let C := columns s N
  let u := update m (cell t .unit) 1
  let v := update u (cell t .lim) (N:ℤ)
  let w := update v (cell t .cols) (C:ℤ)
  let x := update w (cell t .lim) ((N*C:ℕ):ℤ)
  let y := update x (cell t .x) 0
  let z := update y (cell t .y) 0
  let f := update z (cell t .index) 0
  have op₁ : Runs W (.atom (.one (cell t .unit))) m 1 u := .atom (.one _ _)
  have op₂ : Runs W (power t t) u (t+1) v := by
    have h0 : u 0=n := by simpa [u,update] using hd
    simpa only [v,N,Nat.cast_pow,h0] using power_runs W t t u
  have op₃ : Runs W (colCode t s) v 1 w := by
    apply colCode_runs (N:=N) <;> simp [v,u,update]
  have op₄ : Runs W (.atom (.mul (cell t .lim) (cell t .lim) (cell t .cols))) w 1 x := by
    simpa [x,w,v,update] using Runs.atom (Step.mul (W:=W) w (cell t .lim) (cell t .lim) (cell t .cols))
  have run := Runs.seq op₁ (.seq op₂ (.seq op₃ (.seq op₄
    (.seq (zeroCell_runs W x (cell t .x)) (.seq (zeroCell_runs W y (cell t .y)) (zeroCell_runs W z (cell t .index)))))))
  refine ⟨f,?_,?_,?_⟩
  · simpa only [setup,show 1+((t+1)+(1+(1+(1+(1+1)))))=t+7 by omega] using run
  · constructor <;> simp [f,z,y,x,w,v,u,update,hp,N,C]
  · intro i; simp [f,z,y,x,w,v,u,update]

end VWZClique.IntegerRAM.Graph.Table

end

/- WordGraphSchedule -/
section

namespace VWZClique.IntegerRAM.Graph.Table
open Structured BlockReduction

def vertex (i : ℕ) : V := ⟨i%9,Nat.mod_lt _ (by decide)⟩

/-- The nine unary tables come first, followed by the 81 ordered edge tables. -/
def shapeAt (j : ℕ) : Shape :=
  if j<9 then .unary (vertex j) else .cross (vertex ((j-9)/9)) (vertex (j-9))

theorem unaryAt (i : V) : shapeAt i.val=.unary i := by
  simp only [shapeAt,if_pos i.isLt]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem crossAt (i j : V) : shapeAt (9+i.val*9+j.val)=.cross i j := by
  have h : 9+i.val*9+j.val-9=i.val*9+j.val := by omega
  have hdiv : (i.val*9+j.val)/9=i.val := by
    rw [Nat.mul_comm,Nat.mul_add_div (by decide : 0<9),Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have hmod : (i.val*9+j.val)%9=j.val := by
    rw [Nat.mul_comm,Nat.mul_add_mod,Nat.mod_eq_of_lt j.isLt]
  simp only [shapeAt,if_neg (by omega : ¬9+i.val*9+j.val<9), h,hdiv]
  congr 1
  · exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  · exact Fin.ext hmod

def offset (N j : ℕ) : ℕ := min j 9 * N + (j-9)*(N*N)

theorem offset_succ (N j : ℕ) :
    offset N (j+1) = offset N j + N*columns (shapeAt j) N := by
  by_cases h : j<9
  · simp only [offset,min_eq_left (by omega : j+1≤9),min_eq_left h.le,
      Nat.sub_eq_zero_of_le (by omega : j+1≤9),Nat.sub_eq_zero_of_le h.le,zero_mul,
      Nat.add_zero,shapeAt,if_pos h,columns,mul_one,add_mul,one_mul]
  · have d : j+1-9=(j-9)+1 := by omega
    simp only [offset,min_eq_right (by omega : 9≤j+1),min_eq_right (by omega : 9≤j),
      d,shapeAt,if_neg h,columns]
    ring

theorem offset_mono (N : ℕ) : Monotone (offset N) := by
  intro i j hij
  exact Nat.add_le_add (Nat.mul_le_mul_right N (min_le_min_right 9 hij))
    (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hij 9))


theorem index_lt (N C : ℕ) (x y : Fin N) (hy : y.val<C) : x.val*C+y.val<N*C := by
  have h := Nat.mul_le_mul_right C x.isLt
  rw [Nat.succ_mul] at h
  omega


def baseCommand (t : ℕ) : Command :=
  .seq (.atom (.one (cell t .unit)))
  (.seq (.atom (.mul (cell t .ptr) 0 0))
        (.atom (.add (cell t .ptr) (cell t .ptr) (cell t .unit))))

theorem base_runs {W n : ℕ} (t : ℕ) (m : Memory) (hn : m 0=n) :
    ∃ out, Runs W (baseCommand t) m 3 out ∧ out (cell t .ptr)=((1+n*n:ℕ):ℤ) ∧
      ∀ z : ℕ, out z=m z := by
  let x := update m (cell t .unit) 1
  let y := update x (cell t .ptr) ((n:ℤ)*n)
  let out := update y (cell t .ptr) (((n:ℤ)*n)+1)
  have h₁ : Runs W (.atom (.one (cell t .unit))) m 1 x := .atom (.one _ _)
  have h₂ : Runs W (.atom (.mul (cell t .ptr) 0 0)) x 1 y := by
    simpa [x,y,update,hn] using Runs.atom (Step.mul (W:=W) x (cell t .ptr) 0 0)
  have h₃ : Runs W (.atom (.add (cell t .ptr) (cell t .ptr) (cell t .unit))) y 1 out := by
    simpa [y,x,out,update] using Runs.atom (Step.add (W:=W) y (cell t .ptr) (cell t .ptr) (cell t .unit))
  refine ⟨out,.seq h₁ (.seq h₂ h₃),?_,?_⟩
  · simp [out,update,add_comm]
  · intro z; simp [out,y,x,update]

end VWZClique.IntegerRAM.Graph.Table

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

theorem capacity_stride {lay : StackLayout} {L start stride : ℕ}
    (layout : ∀ j, lay.base j=start+j*stride) (room : 9*(2^L)+81*(2^L*2^L) ≤ stride) :
    Capacity lay L := by
  intro d
  calc
    _ = start + d*stride + 9*(2^L) + 81*(2^L*2^L) := by rw [layout d]
    _ ≤ start + d*stride + stride := by omega
    _ = lay.base (d+1) := by rw [layout (d+1),Nat.add_mul]; omega

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

/-- Projection may freely write its own arena after the weight table. -/
theorem project_repr {L} (lay : StackLayout) (cap : Capacity lay L) {d H π w}
    (q : List (NativeTraversal.Slot L)) {m o : Memory} {z : ℤ}
    (src : Repr lay (.input d w::q) m) (globals : Globals L lay o)
    (older : ∀ a : ℕ, 512≤a → a<lay.base d → o a=m a)
    (hdr : ∀ j<d, ∀ f, o (reg j f)=m (reg j f))
    (wt : Weights lay d w o) (prep : lay.prepared d H o)
    (len : ∀ b, o (reg d (lengthField b))=visits (number L H) b)
    (ix : o (reg d .index)=0) (val : o (reg d .value)=z) :
    Repr lay (.cursor d H π .left w 0 z::q) o :=
  ⟨globals,⟨wt,prep,len,by simpa using ix,val⟩,saved_before lay cap d q older hdr src.2.2⟩

/-- During a push the route and pin scratch can be overwritten inside the
parent's arena. Only the parent's permanent weight and projection tables must
retain their mathematical contents. -/
theorem push_repr {L} (lay : StackLayout) (cap : Capacity lay L) {d H π b w}
    (i : Fin (visits (number L H) b)) (z : ℤ) (q : List (NativeTraversal.Slot L)) {m o : Memory}
    {cw : WeightKey (2^L) → ℚ} (src : Repr lay (.cursor d H π b w i.val z::q) m)
    (globals : Globals L lay o) (older : ∀ a : ℕ, 512≤a → a<lay.base d → o a=m a)
    (hdr : ∀ j<d, ∀ f, o (reg j f)=m (reg j f))
    (parent : ∀ f ≠ Field.coefficient, o (reg d f)=m (reg d f))
    (weights : ∀ a : WeightKey (2^L),
      o ((lay.base d+Graph.Table.wordIndex a:ℕ):ℤ)=m ((lay.base d+Graph.Table.wordIndex a:ℕ):ℤ))
    (prep : lay.prepared d H o) (wt : Weights lay (d+1) cw o)
    (coef : o (reg d .coefficient)=(numbered H b i).coeff) :
    Repr lay (.input (d+1) cw :: .cursor d H π b w i.val z :: q) o := by
  obtain ⟨_,⟨⟨ptr,was⟩,_,lengths,ix,val⟩,anc⟩ := src
  have table : Weights lay d w o :=
    ⟨(parent _ (by decide)).trans ptr,fun a => (congrArg (Int.cast : ℤ → ℚ) (weights a)).trans (was a)⟩
  have len (e : Branch) := (parent (lengthField e) (by cases e <;> decide)).trans (lengths e)
  refine ⟨globals,wt,Nat.lt_succ_self d,⟨table,prep,len,(parent _ (by decide)).trans ix,
    (parent _ (by decide)).trans val⟩,⟨i.isLt,coef⟩,saved_before lay cap d q older hdr anc⟩


theorem reset_transition {L W} (lay : StackLayout) (d : ℕ) (hd : d≤36) (H : SimpleGraph V)
    (π : Equiv.Perm V) (b e : Branch) (w : WeightKey (2^L) → ℚ) (i : ℕ) (z : ℤ) (q : List (NativeTraversal.Slot L)) :
    Transition W (Repr lay) (reset d) (.cursor d H π b w i z::q) (.cursor d H π e w 0 z::q) 1 := by
  intro m pre
  obtain ⟨global,⟨wt,prepared,len,_,val⟩,anc⟩ := pre
  obtain ⟨o,run,answer,fr⟩ := reset_runs W d m
  have plane (a : ℕ) (ha:297≤a) := fr (a:ℤ) (distinctData ha hd _)
  have parent (j) (hj:j<d) (k) := fr (reg j k) (ne_of_lt (separate hj _ _))
  have lengths (k : Branch) : o (reg d (lengthField k)) = m (reg d (lengthField k)) :=
    fr _ (different d (by cases k <;> decide))
  exact ⟨1,le_rfl,o,run,global.transfer (fr _ (ne_of_lt (reg_positive d _))) (plane 320 (by decide)) (plane 321 (by decide)),
    ⟨weights_transfer wt (fr _ (different d (by decide))) plane,lay.transferAll _ _ _ _ plane prepared,
    fun k => (lengths k).trans (len k),by simpa using answer,(fr _ (different d (by decide))).trans val⟩,
    saved_transfer lay d q plane parent anc⟩

theorem finish_transition {L W} (lay : StackLayout) (d : ℕ) (H : SimpleGraph V)
    (π : Equiv.Perm V) (b : Branch) (w : WeightKey (2^L) → ℚ) (i : ℕ) (z : ℤ) (q : List (NativeTraversal.Slot L)) :
    Transition W (Repr lay) finish (.cursor d H π b w i z::q) (.value d z::q) 0 := by
  intro m pre
  exact ⟨0,le_rfl,m,.skip _,pre.1,pre.2.1.2.2.2.2,pre.2.2⟩

theorem number_bound (L : ℕ) (H : SimpleGraph V) : number L H ≤ (2^L)^3 := by
  change Fintype.card (RankSwap.Terms L _) ≤ _
  have compact {d : ℕ} : Fintype.card (RankSwap.Terms L d) ≤ 5^L := by
    simpa [RankSwap.MaskEnumeration.Digits] using
      (Fintype.card_le_of_injective _ (RankSwap.MaskEnumeration.code_injective (L:=L) (d:=d)))
  exact compact.trans (RankSwap.MaskEnumeration.scan_range_bound L)

theorem visit_bound (L : ℕ) (H : SimpleGraph V) (b : Branch) : visits (number L H) b ≤ (2^L)^6 := by
  have h := number_bound L H
  have pos : 0<(2^L:ℕ) := by positivity
  have top : (2^L:ℕ)^3 ≤ (2^L)^6 := Nat.pow_le_pow_right pos (by decide)
  cases b with
  | left => exact h.trans top
  | right => exact h.trans top
  | both =>
    calc
      _ ≤ (2^L)^3*(2^L)^3 := Nat.mul_le_mul h h
      _ = _ := by ring

theorem visit_room {W L : ℕ} (H : SimpleGraph V) (b : Branch)
    (cap : Graph.Division.Room W ((2^L)^6)) : Graph.Division.Room W (visits (number L H) b) :=
  lt_of_le_of_lt (by exact_mod_cast visit_bound L H b) cap

theorem pop_transition {L W} (lay : StackLayout) (d : ℕ) (hd : d≤36) (H : SimpleGraph V)
    (π : Equiv.Perm V) (b : Branch) (w : WeightKey (2^L) → ℚ)
    (i : Fin (visits (number L H) b)) (z y : ℤ) (q : List (NativeTraversal.Slot L)) (m : Memory)
    (cap : Graph.Division.Room W (visits (number L H) b))
    (pre : Repr lay (.value (d+1) y :: .cursor d H π b w i.val z :: q) m) :
    ∃ f ≤ 5, ∃ o, Runs W (pop d (reg d (lengthField b))) m f o ∧
      Repr lay (.cursor d H π b w (i.val+1) (z+(numbered H b i).coeff*y)::q) o ∧
      Fits W (o (reg d .flag)) ∧ (o (reg d .flag)<0 ↔ i.val+1<visits (number L H) b) := by
  obtain ⟨global,child,_,⟨wt,prepared,len,ix,val⟩,⟨hi,coeff⟩,anc⟩ := pre
  obtain ⟨o,run,os,oi,flag,fr⟩ := pop_runs W d (lengthField b)
    (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide) m
  have plane (a : ℕ) (ha:297≤a) := fr (a:ℤ) (distinctData ha hd _) (distinctData ha hd _) (distinctData ha hd _)
  have parent (j) (hj:j<d) (k) := fr (reg j k) (ne_of_lt (separate hj _ _))
    (ne_of_lt (separate hj _ _)) (ne_of_lt (separate hj _ _))
  have lengths (k : Branch) : o (reg d (lengthField k)) = m (reg d (lengthField k)) :=
    fr _ (different d (by cases k <;> decide)) (different d (by cases k <;> decide))
        (different d (by cases k <;> decide))
  have zp : o 0=m 0 := fr _ (ne_of_lt (reg_positive ..)) (ne_of_lt (reg_positive ..)) (ne_of_lt (reg_positive ..))
  have ptr : o (reg d .weights)=m (reg d .weights) :=
    fr _ (different d (by decide)) (different d (by decide)) (different d (by decide))
  change m (reg (d+1) .value) = y at child
  change m (reg d .index) = (i.val:ℤ) at ix
  change m (reg d .value) = z at val
  change m (reg d .coefficient) = (numbered H b i).coeff at coeff
  rw [val,coeff,child] at os
  rw [ix] at oi
  rw [ix,len] at flag
  have ilt := i.isLt
  refine ⟨5,le_rfl,o,run,⟨global.transfer zp (plane 320 (by decide)) (plane 321 (by decide)),⟨weights_transfer wt ptr plane,lay.transferAll _ _ _ _ plane prepared,
    fun k => (lengths k).trans (len k),by exact_mod_cast oi,os⟩,saved_transfer lay d q plane parent anc⟩,?_,?_⟩
  · rw [flag]; apply cap.fits <;> omega
  · rw [flag]; omega

end VWZClique.IntegerRAM.NativeFrame

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

/- NativeGraphCapacity -/
section

namespace VWZClique.IntegerRAM.NativeArena
open NativeFrame NativeTraversal UniformFolds BlockReduction Graph

def allowance (c p D : ℕ) := (6000+c)*D^(max 9 p)

theorem flat_bound {D x : ℕ} (hd : 1≤D) (hx : x≤D) {j p : ℕ} (hj : j ≤ max 9 p) :
    x^j ≤ D^(max 9 p) := (Nat.pow_le_pow_left hx _).trans (Nat.pow_le_pow_right hd hj)

theorem graph_index {n k : ℕ} (hn : 32≤n) (hk : 32≤k) :
    let t := (k+8)/9
    let L := graphLength n k
    0<L ∧ n≤n^t ∧ n^t≤2^L := by
  let t := (k+8)/9
  have hkt : 1≤t := by dsimp [t]; omega
  have pow : n≤n^t := by simpa using (Nat.pow_le_pow_right (by omega : 0<n) hkt)
  have shape : n^t≤2^graphLength n k := Nat.le_pow_clog (by decide) _
  exact ⟨by by_contra! no; rw [Nat.eq_zero_of_le_zero no,pow_zero] at shape; omega,pow,shape⟩

theorem uniform_space {n k : ℕ} (hn : 32≤n) (hk : 32≤k) (c p d : ℕ) (hd : d≤36) :
    let L := graphLength n k
    let D := 2^L
    let base := (forGraph n k hn).base d
    let M := allowance c p D
    (base+c*D^p≤M) ∧
    (child base D+Table.offset D 90≤M) ∧
    (6*L+1≤M) ∧ (5*2^(3*L+1)≤M) ∧ (2^(6*L+1)*D^3≤M) ∧ (D^6≤M) := by
  let t := (k+8)/9
  let L := graphLength n k
  let D := 2^L
  let root := DyadicCell.target n (n^t)
  let base := atDepth root D d
  let Q := D^(max 9 p)
  let M := allowance c p D
  obtain ⟨_,small,shape⟩ := graph_index hn hk
  have dp : 1 ≤ D := Nat.one_le_pow _ _ (by decide)
  have lQ (j : ℕ) (h : j≤9) : D^j≤Q := Nat.pow_le_pow_right dp (h.trans (le_max_left _ _))
  have pQ : D^p≤Q := Nat.pow_le_pow_right dp (le_max_right _ _)
  have one : 1≤Q := Nat.one_le_pow _ _ dp
  have dq : D≤Q := by simpa using lQ 1 (by decide)
  have dsq : D*D≤Q := by simpa [pow_two] using lQ 2 (by decide)
  have cube := lQ 3 (by decide)
  have nD : n≤D := small.trans shape
  have tD : n^t≤D := shape
  have gSq : n*n≤Q := (Nat.mul_le_mul nD nD).trans dsq
  have qSq : n^t*n^t≤Q := (Nat.mul_le_mul tD tD).trans dsq
  have nQ : n^t≤Q := tD.trans dq
  have rootQ : root≤92*Q := by
    dsimp [root,DyadicCell.target,DyadicCell.origin,DyadicCell.space]
    nlinarith
  have stride : tableWords D+7*D^3+2+26*D≤125*Q := by
    dsimp [tableWords]; omega
  have baseQ : base≤4592*Q := by
    dsimp [base]; rw [atDepth_formula]
    have h := Nat.mul_le_mul hd stride
    omega
  have childQ : child base D≤4717*Q := (child_polynomial dp).trans (by omega)
  have regionQ : Table.offset D 90 ≤ 90*Q := by norm_num [Table.offset]; omega
  have top : 6000*Q+c*Q=M := by dsimp [M,allowance,Q]; ring
  have lin : L≤D := (Nat.lt_two_pow_self (n:=L)).le
  have two : 2^(3*L+1)=2*D^3 := by rw [pow_succ, Nat.mul_comm 3, pow_mul]; dsimp [D]; ring
  have six : 2^(6*L+1)*D^3=2*D^9 := by rw [pow_succ, Nat.mul_comm 6, pow_mul]; dsimp [D]; ring
  have scaled := Nat.mul_le_mul_left c pQ
  change base+c*D^p≤M ∧ child base D+Table.offset D 90≤M ∧ 6*L+1≤M ∧ 5*2^(3*L+1)≤M ∧
    2^(6*L+1)*D^3≤M ∧ D^6≤M
  rw [two,six]
  have d9 := lQ 9 (by decide)
  have d6 := lQ 6 (by decide)
  omega

theorem admissible_width (k c p : ℕ) : ∃ b : ℕ, k+3≤b ∧ 2*((k+8)/9)+11≤b ∧ ∀ n : ℕ, 32≤n →
    Division.Room (b*(n.log2+1)) (allowance c p (2^graphLength n k)) := by
  obtain ⟨v,hv,room⟩ := graph_room k (6000+c) (max 9 p)
  let b := max v (2*((k+8)/9)+11)
  refine ⟨b,hv.trans (le_max_left _ _),le_max_right _ _,?_⟩
  intro n hn
  have old := room n (by omega)
  exact old.trans_le (pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_right
    (Nat.mul_le_mul_right _ (le_max_left v _)) 1))

end VWZClique.IntegerRAM.NativeArena

end

/- NativeFoldWeight -/
section

namespace VWZClique.IntegerRAM.FoldWeight
open FoldProof UniformFolds WeightedProof SquareCode Structured

/-- Pointers to the parent tables, coordinate maps, and four pin filters.
All are ordinary words, so the same compiled expression applies at every size. -/
structure Layout where
  n : ℤ
  unary : V → ℤ
  edge : V → V → ℤ
  adjust : Fin 3 → Slot → ℤ
  pin : Fin 4 → ℤ
  x : ℤ
  y : ℤ

def raw {n : ℕ} (s : Kind) (x y : Fin n) : WeightKey n :=
  match s with
  | .inl i => .inl (i,x)
  | .inr (i,j) => .inr (i,j,x,y)

def coord (l : Layout) (s : Kind) (i : V) : Expr :=
  match s with
  | .inl _ => .reg l.x
  | .inr (j,_) => .reg (if i=j then l.x else l.y)

def read (p : ℤ) (x : Expr) : Expr := .read (.add (.reg p) x)
def pairRead (l : Layout) (i j : V) (x y : Expr) : Expr :=
  read (l.edge i j) (.add (.mul x (.reg l.n)) y)
def edgeRead (l : Layout) (i j : V) (x y : Expr) : Expr :=
  if i<j then pairRead l i j x y else pairRead l j i y x

def staticRoute (d : Branch) (h : Fin 3) (s : Slot) :=
  (route (representative (first d)) (representative (second d)) h s).1

def adjusted (l : Layout) (shape : Kind) (d : Branch) (h : Fin 3) (s : Slot) : Expr :=
  read (l.adjust h s) (coord l shape (staticRoute d h s))

def token {E : Finset EdgeSlot} (π : Equiv.Perm V) (l : Layout) (s : Kind) (d : Branch) :
    FoldToken E → Expr
  | .inl i => read (l.pin i) (coord l s (pinSite i))
  | .inr (.inl (h,.inl i)) => read (l.unary (π (site h i))) (adjusted l s d h (.inl i))
  | .inr (.inl (_,.inr _)) => .one
  | .inr (.inr e) => edgeRead l (π (endpoint e.val.1 e.val.2.1)) (π (endpoint e.val.1 e.val.2.2))
      (adjusted l s d e.val.1 e.val.2.1) (adjusted l s d e.val.1 e.val.2.2)

def staticEnds (E : Finset EdgeSlot) (d : Branch) :=
  FoldProof.ends (E:=E) (representative (first d)) (representative (second d))

noncomputable def factors (E : Finset EdgeSlot) (d : Branch) (s : Kind) :=
  (Finset.univ.filter (fun t : FoldToken E => kind (staticEnds E d t) = s)).toList

def product : List Expr → Expr
  | [] => .one
  | e :: es => .mul e (product es)

noncomputable def entry (H : SimpleGraph V) (π : Equiv.Perm V) (l : Layout) (s : Kind) (d : Branch) : Expr :=
  product ((factors (slots π H) d s).map (token π l s d))

structure Records {L : ℕ} (l : Layout) (m : Memory)
    (a b : Option (Mask L)) (w : WeightKey (2^L) → ℚ) : Prop where
  dim : m l.n=2^L
  unary : ∀ i (x : Fin (2^L)), (m (m (l.unary i)+x.val):ℚ)=w (.inl (i,x))
  edge : ∀ i j (x y : Fin (2^L)), (m (m (l.edge i j)+(x.val:ℤ)*2^L+y.val):ℚ)=w (.inr (i,j,x,y))
  adjust : ∀ h s (x : Fin (2^L)), m (m (l.adjust h s)+x.val)=
    ((wordIndex L ((route a b h s).2 ((wordIndex L).symm x))).val:ℤ)
  pin : ∀ i (x : Fin (2^L)), (m (m (l.pin i)+x.val):ℚ)=pinWeight a b i ((wordIndex L).symm x)

private theorem ends_eq {L : ℕ} {a b : Option (Mask L)} {d : Branch}
    (ha : a.isSome=first d) (hb : b.isSome=second d) (E : Finset EdgeSlot) (t : FoldToken E) :
    FoldProof.ends a b t=staticEnds E d t := by
  rcases t with i | ⟨h,s⟩ | ⟨⟨h,s,t⟩,he⟩
  · rfl
  · simp only [FoldProof.ends,staticEnds,route_static a b,ha,hb]
  · simp only [FoldProof.ends,staticEnds,route_static a b,ha,hb]

private theorem product_val (m : Memory) (es : List Expr) :
    (product es).val m = (es.map (Expr.val m)).prod := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [product,Expr.val,ih]

private theorem coord_val {n : ℕ} {l : Layout} {m : Memory} {x y : Fin n}
    (hx : m l.x=x.val) (hy : m l.y=y.val) (s : Kind) (i : V) :
    (coord l s i).val m = (addressValue (raw s x y) i).val := by
  cases s with
  | inl j => exact hx
  | inr p => rcases p with ⟨j,k⟩; by_cases e:i=j <;> simp [coord,raw,addressValue,Expr.val,e,hx,hy]

private theorem token_val {L : ℕ} {H : SimpleGraph V} {π : Equiv.Perm V} {l : Layout} {m : Memory}
    {a b : Option (Mask L)} {w : WeightKey (2^L) → ℚ} (rec : Records l m a b w)
    {d : Branch} (ha : a.isSome=first d) (hb : b.isSome=second d)
    (s : Kind) {x y : Fin (2^L)} (hx : m l.x=x.val) (hy : m l.y=y.val) (t : FoldToken (slots π H)) :
    ((token π l s d t).val m:ℚ) =
      weight a b t ((wordIndex L).symm (addressValue (raw s x y) (FoldProof.ends a b t).1))
        ((wordIndex L).symm (addressValue (raw s x y) (FoldProof.ends a b t).2)) ((Round.mk H π a b).inputs w) := by
  let k := raw s x y
  let adj (h : Fin 3) (u : Slot) := wordIndex L ((route a b h u).2
    ((wordIndex L).symm (addressValue k (route a b h u).1)))
  have hr (h : Fin 3) (u : Slot) : staticRoute d h u=(route a b h u).1 := by
    unfold staticRoute
    rw [←ha,←hb,←route_static a b]
  have ar (h : Fin 3) (u : Slot) : (adjusted l s d h u).val m=(adj h u).val := by
    simp only [adjusted,read,Expr.val,coord_val hx hy,hr]
    exact rec.adjust _ _ _
  have pair (i j : V) (p q : Expr) (u v : Fin (2^L)) (hu : p.val m=u.val) (hv : q.val m=v.val) :
      ((pairRead l i j p q).val m:ℚ)=w (.inr (i,j,u,v)) := by
    simpa [pairRead,read,Expr.val,hu,hv,rec.dim,add_assoc] using rec.edge i j u v
  rcases t with i | ⟨h,u|u⟩ | ⟨⟨h,u,v⟩,active⟩
  · simp only [token,read,Expr.val,coord_val hx hy,weight,FoldProof.ends]
    apply rec.pin
  · simp only [token,read,Expr.val,ar,weight,FoldProof.ends,Round.inputs,inputKey,literal,Sum.elim_inl]
    apply rec.unary
  · rfl
  · simp only [token,weight,FoldProof.ends,Round.inputs,inputKey,if_pos active,literal,Sum.elim_inl]
    unfold edgeRead edgeKey
    split <;> apply pair <;> apply ar

/-- Each folded weight is a single fixed expression in the parent table, the
four pin tables, and the eighteen routed coordinate maps. It is independent
of the word length and the choice of sparse mask. -/
theorem entry_val {L : ℕ} {H : SimpleGraph V} {π : Equiv.Perm V} {l : Layout} {m : Memory}
    {a b : Option (Mask L)} {w : WeightKey (2^L) → ℚ} (rec : Records l m a b w)
    {d : Branch} (ha : a.isSome=first d) (hb : b.isSome=second d) (s : Kind)
    {x y : Fin (2^L)} (hx : m l.x=x.val) (hy : m l.y=y.val) :
    ((entry H π l s d).val m:ℚ) = (Round.mk H π a b).apply w (raw s x y) := by
  classical
  have shape_eq : shape (raw s x y)=s := by cases s with
    | inl => rfl
    | inr p => rcases p with ⟨_,_⟩; rfl
  have eq (t : FoldToken (slots π H)) := token_val (H:=H) (π:=π) rec ha hb s hx hy t
  simp only [entry,product_val,List.map_map,Round.apply,updated,collect,shape_eq]
  rw [Int.cast_list_prod]
  unfold factors
  simp only [List.map_map,Function.comp_def,eq,ends_eq ha hb]
  rw [Finset.prod_map_toList]

end VWZClique.IntegerRAM.FoldWeight

namespace VWZClique.IntegerRAM.FoldWeight
open FoldProof UniformFolds WeightedProof SquareCode Structured

/-- Physical memory bounds for a single gather. Pointer registers and both index
registers must lie above the expression compiler's scratch area. -/
structure SafeTables {L : ℕ} (l : Layout) (m : Memory) (W : ℕ) (floor : ℤ) : Prop where
  scratch : floor<0
  size : floor<l.n
  xreg : floor<l.x
  yreg : floor<l.y
  unaryReg : ∀ i, floor<l.unary i
  edgeReg : ∀ i j, floor<l.edge i j
  adjustReg : ∀ h t, floor<l.adjust h t
  pinReg : ∀ i, floor<l.pin i
  unary : ∀ i (x : Fin (2^L)), (0:ℤ) ≤ m (l.unary i)+x.val ∧ Fits W (m (l.unary i)+x.val)
  edge : ∀ i j (x y : Fin (2^L)), (0:ℤ) ≤ m (l.edge i j)+(x.val:ℤ)*2^L+y.val ∧
    Fits W (m (l.edge i j)+(x.val:ℤ)*2^L+y.val)
  adjust : ∀ h t (x : Fin (2^L)), (0:ℤ) ≤ m (l.adjust h t)+x.val ∧ Fits W (m (l.adjust h t)+x.val)
  pin : ∀ i (x : Fin (2^L)), (0:ℤ) ≤ m (l.pin i)+x.val ∧ Fits W (m (l.pin i)+x.val)

private theorem read_safe {p floor : ℤ} {m : Memory} {W : ℕ} {x : Expr} (hr : floor<p) (hx : x.safe floor W m)
    (hf : floor<0) (h : (0:ℤ) ≤ m p+x.val m ∧ Fits W (m p+x.val m)) : (read p x).safe floor W m :=
  ⟨⟨hr,hx⟩,hf.trans_le h.1,h.2⟩

theorem entry_safe {L W : ℕ} {H : SimpleGraph V} {π : Equiv.Perm V} {l : Layout} {m : Memory}
    {a b : Option (Mask L)} {w : WeightKey (2^L) → ℚ} {floor : ℤ} (safe : SafeTables (L:=L) l m W floor)
    (rec : Records l m a b w) {d : Branch} (ha : a.isSome=first d) (hb : b.isSome=second d)
    (s : Kind) {x y : Fin (2^L)} (hx : m l.x=x.val) (hy : m l.y=y.val) : (entry H π l s d).safe floor W m := by
  let k := raw s x y
  have coords (i : V) : (coord l s i).safe floor W m := by
    cases s with
    | inl => exact safe.xreg
    | inr p => obtain ⟨j,_⟩ := p; by_cases h : i=j <;> simp [coord,h,Expr.safe,safe.xreg,safe.yreg]
  let idx (h : Fin 3) (t : Slot) := addressValue k (staticRoute d h t)
  let dest (h : Fin 3) (t : Slot) := wordIndex L ((route a b h t).2 ((wordIndex L).symm (idx h t)))
  have amap (h : Fin 3) (t : Slot) : (adjusted l s d h t).safe floor W m := by
    apply read_safe (safe.adjustReg _ _) (coords _) safe.scratch
    rw [coord_val hx hy]
    apply safe.adjust
  have ix (h : Fin 3) (t : Slot) : (adjusted l s d h t).val m=(dest h t).val := by
    simp only [adjusted,read,Expr.val,coord_val hx hy]
    apply rec.adjust
  have pr (i j : V) (h : Fin 3) (t u : Slot) : (pairRead l i j (adjusted l s d h t)
      (adjusted l s d h u)).safe floor W m := by
    let e := Expr.add (.mul (adjusted l s d h t) (.reg l.n)) (adjusted l s d h u)
    have es : e.safe floor W m := ⟨⟨amap h t,safe.size⟩,amap h u⟩
    apply @read_safe (l.edge i j) floor m W e (safe.edgeReg i j) es safe.scratch
    simpa only [e,Expr.val,ix,rec.dim,←add_assoc] using safe.edge i j (dest h t) (dest h u)
  have ts (t : FoldToken (slots π H)) : (token π l s d t).safe floor W m := by
    rcases t with i | ⟨h,u|u⟩ | ⟨⟨h,u,v⟩,active⟩
    · apply read_safe (safe.pinReg _) (coords _) safe.scratch
      rw [coord_val hx hy]; apply safe.pin
    · apply read_safe (safe.unaryReg _) (amap _ _) safe.scratch
      rw [ix]; apply safe.unary
    · trivial
    · simp only [token,edgeRead]
      split <;> apply pr
  unfold entry
  generalize factors (slots π H) d s = xs
  induction xs with
  | nil => trivial
  | cons t xs ih => exact ⟨ts t,ih⟩

/-- Execute a folded entry on the fixed-width target without specializing the
code to the assignment domain or to the mask's digits. -/
theorem entry_native {L W : ℕ} {H : SimpleGraph V} {π : Equiv.Perm V} {l : Layout} {m : Memory}
    {a b : Option (Mask L)} {w : WeightKey (2^L) → ℚ} {floor : ℤ} (safe : SafeTables (L:=L) l m W floor)
    (rec : Records l m a b w) {d : Branch} (ha : a.isSome=first d) (hb : b.isSome=second d)
    (s : Kind) {x y : Fin (2^L)} (hx : m l.x=x.val) (hy : m l.y=y.val) :
    let e := entry H π l s d
    ∃ out, Runs W (e.code floor) m e.steps out ∧
      (out floor:ℚ)=(Round.mk H π a b).apply w (raw s x y) ∧ ∀ i, floor < i → out i=m i := by
  obtain ⟨out,run,val,fr⟩ := (entry H π l s d).run m floor (entry_safe safe rec ha hb s hx hy)
  exact ⟨out,run,val ▸ entry_val rec ha hb s hx hy,fr⟩

end VWZClique.IntegerRAM.FoldWeight

end

/- NativeGather -/
section

namespace VWZClique.IntegerRAM.Graph.Table.Gather
open Structured BlockReduction

def block (t : ℕ) (s : Shape) (body : Command) : Command :=
  .seq (setup t s) (repeatN (.seq body (advance t))
    (cell t .index) (cell t .unit) (cell t .lim) (cell t .flag))

private theorem coords_unique {w a b c d : ℕ} (hw : 0<w) (hb : b<w) (hd : d<w)
    (h : a*w+b=c*w+d) : a=c ∧ b=d := by
  have div (u v : ℕ) (hv : v<w) : (u*w+v)/w=u := by
    rw [Nat.mul_comm,Nat.mul_add_div hw,Nat.div_eq_of_lt hv,Nat.add_zero]
  have modn (u v : ℕ) (hv : v<w) : (u*w+v)%w=v := by
    rw [Nat.mul_comm,Nat.mul_add_mod,Nat.mod_eq_of_lt hv]
  exact ⟨(div a b hb).symm.trans ((congrArg (·/w) h).trans (div c d hd)),
    (modn a b hb).symm.trans ((congrArg (·%w) h).trans (modn c d hd))⟩

/-- Materialize one arbitrary unary or pair table using a fixed cell command.
The kernel may read the positive-memory prefix and preserves every other positive cell. -/
theorem block_runs {W n t base M B : ℕ} (hn : 1≤n) (s : Shape) (m : Memory)
    (hd : m 0=n) (hp : m (cell t .ptr)=base)
    (room : Division.Room W M) (fits : base+n^t*columns s (n^t)≤M)
    (body : Command) (value : Fin (n^t) → Fin (n^t) → ℚ)
    (eval : ∀ a : Memory, (∀ u : ℕ, u<base → a u=m u) → ∀ x y : Fin (n^t),
      a (cell t .x)=x.val → a (cell t .y)=y.val →
      ∃ f ≤ B, ∃ o, Runs W body a f o ∧ (o Reg.acc:ℚ)=value x y ∧
        (∀ c, o (cell t c)=a (cell t c)) ∧ ∀ j : ℕ, o j=a j) :
    ∃ T, T≤(t+7)+(n^t*columns s (n^t))*(B+10) ∧ ∃ out,
      Runs W (block t s body) m T out ∧
      out (cell t .ptr)=((base+n^t*columns s (n^t):ℕ):ℤ) ∧
      (∀ x y : Fin (n^t), y.val<columns s (n^t) →
        (out ((base+x.val*columns s (n^t)+y.val:ℕ):ℤ) : ℚ)=value x y) ∧
      ∀ z : ℕ, z<base ∨ base+n^t*columns s (n^t)≤z → out z=m z := by
  let N := n^t
  let C := columns s N
  let D := N*C
  have hN : 0<N := Nat.pow_pos hn
  have hC : 0<C := cols_pos s hN
  have hCN : C≤N := cols_le s hN
  have hD : 0<D := Nat.mul_pos hN hC
  have hcap : base+D≤M := fits
  have hCM : C≤M := by
    have hh : C≤D := by simpa [D] using Nat.mul_le_mul_right C hN
    omega
  let inv := fun (j : ℕ) (a : Memory) => ∃ u v : ℕ,
    u*C+v=j ∧ v<C ∧ Controls t C D (base+j) u v j a ∧
    (∀ x y : Fin (n^t), y.val<C → x.val*C+y.val<j →
      (a ((base+x.val*C+y.val:ℕ):ℤ) : ℚ)=value x y) ∧
    ∀ z : ℕ, z<base ∨ base+j≤z → a z=m z
  obtain ⟨m₀,start,ctl₀,same₀⟩ := setup_runs (W:=W) s m hd hp
  have init : inv 0 m₀ := ⟨0,0,by simp,hC,by simpa using ctl₀,by omega,fun z _ => same₀ z⟩
  have fitGuard (q : ℕ) (hq : q≤D) : Fits W ((q:ℤ)-D) := by apply room.fits <;> omega
  have action (q : ℕ) (hq : q<D) (a : Memory) (hin : inv q a) :
      ∃ T : ℕ, T≤B+7 ∧ ∃ out : Memory,
        Runs W (.seq (body) (advance t)) a T out ∧
        out (cell t .index)=q ∧ out (cell t .unit)=1 ∧ out (cell t .lim)=D ∧
        inv (q+1) (nextMemory out (cell t .index) (cell t .flag) q D) := by
    obtain ⟨u,v,loc,vc,ctl,previous,same⟩ := hin
    have un : u<N := by
      by_contra! bad
      have := Nat.mul_le_mul_right C bad
      omega
    let x : Fin (n^t) := ⟨u,un⟩
    let y : Fin (n^t) := ⟨v,vc.trans_le hCN⟩
    obtain ⟨f,hf,v₀,weight,ans,csaved,saved⟩ := eval a (fun z hz => same z (Or.inl hz)) x y ctl.x ctl.y
    have ctl' := ctl.transfer csaved
    obtain ⟨a₁,act,nxt,write⟩ := advance_runs ctl' vc (by omega : base+q≤M) hCM room
    have stepB : f+(4+(if v+1<C then 1 else 3)) ≤ B+7 := by split <;> omega
    refine ⟨_,stepB,a₁,.seq weight act,nxt.index,nxt.unit,nxt.lim,?_⟩
    have nextloc : xNext C u v*C+yNext C v=q+1 := by
      by_cases h : v+1<C <;> simp [xNext,yNext,h,Nat.add_mul] <;> omega
    have nextlt : yNext C v<C := by by_cases h:v+1<C <;> simp [yNext,h,hC]
    let a₂ := nextMemory a₁ (cell t .index) (cell t .flag) q D
    have new (z : ℕ) : a₂ z = if z=base+q then v₀ Reg.acc else a z := by
      rw [show a₂ z=a₁ z from tick_data t q D z a₁,write]
      by_cases h : z=base+q <;> simp [h,saved z]
    change inv (q+1) a₂
    refine ⟨_,_,nextloc,nextlt,by simpa only [Nat.add_assoc] using nxt.tick,?_,?_⟩
    · intro i j hj hlt
      by_cases old : i.val*C+j.val<q
      · rw [new,if_neg (by omega)]
        exact previous i j hj old
      · obtain ⟨hi,hj'⟩ := coords_unique hC hj vc (show i.val*C+j.val=u*C+v by omega)
        have ei : i=x := Fin.ext hi
        have ej : j=y := Fin.ext hj'
        rw [new,if_pos (by omega),ei,ej]
        exact ans
    · intro z hz
      rw [new,if_neg (by omega)]
      exact same z (by omega)
  obtain ⟨fuel,time,out,run,done⟩ := repeatN_runs (W:=W) (B:=B+7) hD _
    (by simp : cell t .lim ≠ cell t .index) inv fitGuard action init
  obtain ⟨_,_,_,_,ctl,all,same⟩ := done
  refine ⟨(t+7)+fuel,?_,out,.seq start run,ctl.ptr,?_,same⟩
  · change (t+7)+fuel ≤ (t+7) + D*(B+10)
    exact Nat.add_le_add_left (by simpa only [Nat.add_assoc] using time) _
  · intro x y hy
    change y.val<C at hy
    apply all x y hy
    have hx : (x.val+1)*C≤N*C := Nat.mul_le_mul_right _ x.isLt
    rw [Nat.add_mul,one_mul] at hx
    change x.val*C+y.val < N*C
    omega

end VWZClique.IntegerRAM.Graph.Table.Gather

end

/- NativeFoldGather -/
section

namespace VWZClique.IntegerRAM.FoldWeight
open FoldProof UniformFolds WeightedProof SquareCode Structured Graph

def owned (base : ℕ) (i : ℤ) := 0 ≤ i ∧ i<(base:ℤ)

/-- All source pointers, coordinate lookup tables and source weights precede
the area being filled. Only the current row/column counters live in scratch. -/
structure Before {L : ℕ} (l : Layout) (m : Memory) (base : ℕ) : Prop where
  size : owned base l.n
  unaryReg : ∀ i, owned base (l.unary i)
  edgeReg : ∀ i j, owned base (l.edge i j)
  adjustReg : ∀ h t, owned base (l.adjust h t)
  pinReg : ∀ i, owned base (l.pin i)
  unary : ∀ i (x : Fin (2^L)), owned base (m (l.unary i)+x.val)
  edge : ∀ i j (x y : Fin (2^L)), owned base (m (l.edge i j)+(x.val:ℤ)*2^L+y.val)
  adjust : ∀ h t (x : Fin (2^L)), owned base (m (l.adjust h t)+x.val)
  pin : ∀ i (x : Fin (2^L)), owned base (m (l.pin i)+x.val)

private theorem same_int {base : ℕ} {m a : Memory} (hf : ∀ z : ℕ, z < base → a z=m z)
    {j : ℤ} (h : owned base j) : a j=m j := by
  obtain ⟨z,rfl⟩ := Int.eq_ofNat_of_zero_le h.1
  exact hf z (by exact_mod_cast h.2)

theorem Records.prefix {L : ℕ} {l : Layout} {m a : Memory} {base : ℕ} {ma mb : Option (Mask L)}
    {w : WeightKey (2^L) → ℚ} (rec : Records l m ma mb w) (pre : Before (L:=L) l m base)
    (hf : ∀ j : ℕ, j < base → a j=m j) : Records l a ma mb w := by
  constructor
  · exact (same_int hf pre.size).trans rec.dim
  · intro i x; rw [same_int hf (pre.unaryReg i),same_int hf (pre.unary i x),rec.unary]
  · intro i j x y; rw [same_int hf (pre.edgeReg i j),same_int hf (pre.edge i j x y),rec.edge]
  · intro h t x; rw [same_int hf (pre.adjustReg h t),same_int hf (pre.adjust h t x),rec.adjust]
  · intro i x; rw [same_int hf (pre.pinReg i),same_int hf (pre.pin i x),rec.pin]

theorem safe_prefix {L W base : ℕ} {l : Layout} {m a : Memory} {floor : ℤ}
    (pre : Before (L:=L) l m base) (cap : Division.Room W base) (hf : ∀ j : ℕ, j < base → a j=m j)
    (neg : floor<0) (sx : floor < l.x) (sy : floor < l.y) : SafeTables (L:=L) l a W floor := by
  have safe (j : ℤ) (hj : owned base j) : 0 ≤ j ∧ Fits W j := ⟨hj.1,cap.fits (by have := hj.1; omega) hj.2.le⟩
  refine ⟨neg,neg.trans_le pre.size.1,sx,sy,fun i => neg.trans_le (pre.unaryReg i).1,
    fun i j => neg.trans_le (pre.edgeReg i j).1,fun h t => neg.trans_le (pre.adjustReg h t).1,
    fun i => neg.trans_le (pre.pinReg i).1,?_,?_,?_,?_⟩
  · intro i x; rw [same_int hf (pre.unaryReg i)]; exact safe _ (pre.unary i x)
  · intro i j x y; rw [same_int hf (pre.edgeReg i j)]; exact safe _ (pre.edge i j x y)
  · intro h t x; rw [same_int hf (pre.adjustReg h t)]; exact safe _ (pre.adjust h t x)
  · intro i x; rw [same_int hf (pre.pinReg i)]; exact safe _ (pre.pin i x)

def shapeOf : Graph.Shape → Kind
  | .unary i => .inl i
  | .cross i j => .inr (i,j)

def cellCommand (e : Expr) (floor : ℤ) : Command :=
  .seq (e.code floor) (.seq (.atom (.sub Reg.acc Reg.acc Reg.acc)) (.atom (.add Reg.acc Reg.acc floor)))

noncomputable def gather (H : SimpleGraph V) (π : Equiv.Perm V) (l : Layout) (d : Branch)
    (s : Graph.Shape) (floor : ℤ) :=
  Table.Gather.block 1 s (cellCommand (entry H π l (shapeOf s) d) floor)

/-- One fixed native array-filling program for a whole unary or edge weight
table of a folded subproblem. Both the expression and its exact per-cell
instruction count are independent of L and of the input mask digits. -/
theorem gather_runs {L W base M : ℕ} {H : SimpleGraph V} {π : Equiv.Perm V} {l : Layout}
    {m : Memory} {a b : Option (Mask L)} {w : WeightKey (2^L) → ℚ}
    (rec : Records l m a b w) (pre : Before (L:=L) l m base)
    {d : Branch} (ha : a.isSome=first d) (hb : b.isSome=second d) (s : Graph.Shape)
    (dim : m 0=(2:ℤ)^L) (px : l.x=Table.cell 1 .x) (py : l.y=Table.cell 1 .y)
    (dst : m (Table.cell 1 .ptr)=base) (cap : Division.Room W M)
    (room : base+2^L*Table.columns s (2^L) ≤ M) {floor : ℤ}
    (bottom : ∀ j, floor < Table.cell 1 j) :
    let B := (entry H π l (shapeOf s) d).steps
    ∃ fuel ≤ 8+(2^L*Table.columns s (2^L))*(B+12), ∃ out,
      Runs W (gather H π l d s floor) m fuel out ∧
      out (Table.cell 1 .ptr)=((base+2^L*Table.columns s (2^L):ℕ):ℤ) ∧
      (∀ x y : Fin (2^L), y.val < Table.columns s (2^L) →
        (out ((base+x.val*Table.columns s (2^L)+y.val:ℕ):ℤ):ℚ)=
          (Round.mk H π a b).apply w (raw (shapeOf s) x y)) ∧
      ∀ j : ℕ, j < base ∨ base+2^L*Table.columns s (2^L) ≤ j → out j=m j := by
  let e := entry H π l (shapeOf s) d
  let f := fun x y => (Round.mk H π a b).apply w (raw (shapeOf s) x y)
  have capB : Division.Room W base := lt_of_le_of_lt (by exact_mod_cast (by omega : base ≤ M)) cap
  have neg : floor < Reg.acc := by have h := bottom .x; change floor < -10 at h; change floor < -1; omega
  have neg0 : floor<0 := neg.trans (by decide)
  have eval (xmem : Memory) (priorHeap : ∀ j : ℕ, j < base → xmem j=m j) (x y : Fin (2^L))
      (hx : xmem (Table.cell 1 .x)=x.val) (hy : xmem (Table.cell 1 .y)=y.val) :
      ∃ fuel ≤ e.steps+2, ∃ o, Runs W (cellCommand e floor) xmem fuel o ∧
        (o Reg.acc:ℚ)=f x y ∧ (∀ c, o (Table.cell 1 c)=xmem (Table.cell 1 c)) ∧ ∀ j : ℕ, o j=xmem j := by
    have safe := safe_prefix pre capB priorHeap neg0 (px ▸ bottom .x) (py ▸ bottom .y)
    obtain ⟨u,run,ans,frame⟩ := entry_native safe (rec.prefix pre priorHeap) ha hb (shapeOf s) (px ▸ hx) (py ▸ hy)
    let t := update u Reg.acc 0
    let o := update t Reg.acc (u floor)
    have r₁ : Runs W (.atom (.sub Reg.acc Reg.acc Reg.acc)) u 1 t := by
      simpa [t] using Runs.atom (Step.sub (W:=W) u Reg.acc Reg.acc Reg.acc)
    have r₂ : Runs W (.atom (.add Reg.acc Reg.acc floor)) t 1 o := by
      simpa [t,o,update,neg.ne] using Runs.atom (Step.add (W:=W) t Reg.acc Reg.acc floor)
    refine ⟨_,by dsimp [e]; omega,o,.seq run (.seq r₁ r₂),by simpa [o,update,f] using ans,?_,?_⟩
    · intro c
      have hh : Table.cell 1 c≠Reg.acc := by have := Table.cell_below 1 c; change Table.cell 1 c≠ -1; omega
      simpa [o,t,update,hh] using frame _ (bottom c)
    · intro j
      simpa [o,t,update,Reg.acc] using frame j (by omega)
  have lemma' := @Table.Gather.block_runs W (2^L) 1 base M (e.steps+2)
  rw [pow_one] at lemma'
  simpa only [Nat.reduceAdd,Nat.add_assoc,gather,e,f] using
    lemma' (Nat.one_le_pow _ _ (by decide)) s m (by exact_mod_cast dim) dst cap room (cellCommand e floor) f eval

end VWZClique.IntegerRAM.FoldWeight

end

/- NativeFoldTable -/
section

namespace VWZClique.IntegerRAM.FoldWeight
open FoldProof UniformFolds WeightedProof Structured Graph Graph.Table

private theorem before_mono {a b : ℕ} (h : a ≤ b) {i : ℤ} (hi : owned a i) : owned b i :=
  ⟨hi.1, hi.2.trans_le (by exact_mod_cast h)⟩

theorem Before.prefix {a b L : ℕ} {l : Layout} {m u : Memory} (h : a ≤ b)
    (pre : Before (L:=L) l m a) (keep : ∀ z : ℕ, z < a → u z=m z) :
    Before (L:=L) l u b := by
  have eqr {j : ℤ} (hj : owned a j) : u j=m j := by
    obtain ⟨t,rfl⟩ := Int.eq_ofNat_of_zero_le hj.1
    apply keep; exact_mod_cast hj.2
  refine ⟨before_mono h pre.size,fun i => before_mono h (pre.unaryReg i),
    fun i j => before_mono h (pre.edgeReg i j),fun i j => before_mono h (pre.adjustReg i j),
    fun i => before_mono h (pre.pinReg i),?_,?_,?_,?_⟩
  · intro i x; rw [eqr (pre.unaryReg i)]; exact before_mono h (pre.unary i x)
  · intro i j x y; rw [eqr (pre.edgeReg i j)]; exact before_mono h (pre.edge i j x y)
  · intro i s x; rw [eqr (pre.adjustReg i s)]; exact before_mono h (pre.adjust i s x)
  · intro i x; rw [eqr (pre.pinReg i)]; exact before_mono h (pre.pin i x)

noncomputable def tabulate (H : SimpleGraph V) (π : Equiv.Perm V) (l : Layout)
    (d : Branch) (floor : ℤ) : ℕ → Command
  | 0 => .skip
  | j+1 => .seq (tabulate H π l d floor j) (gather H π l d (shapeAt j) floor)

noncomputable def bound (H : SimpleGraph V) (π : Equiv.Perm V) (l : Layout) (d : Branch) : ℕ :=
  ∑ j : Fin 90, (entry H π l (shapeOf (shapeAt j.val)) d).steps

theorem tabulate_runs {L W M base : ℕ} {H : SimpleGraph V} {π : Equiv.Perm V} {l : Layout}
    {m : Memory} {a b : Option (Mask L)} {w : WeightKey (2^L) → ℚ}
    (rec : Records l m a b w) (pre : Before (L:=L) l m base)
    {d : Branch} (ha : a.isSome=first d) (hb : b.isSome=second d)
    (dim : m 0=(2:ℤ)^L) (pos : 0 < base) (px : l.x=cell 1 .x) (py : l.y=cell 1 .y)
    (ptr : m (cell 1 .ptr)=base) (cap : Division.Room W M) {floor : ℤ}
    (bottom : ∀ j, floor < cell 1 j) (J : ℕ) (hj : J≤90) (room : base+offset (2^L) J ≤ M) :
    let N := 2^L
    let B := 8+N*N*(bound H π l d +12)
    ∃ fuel ≤ J*B, ∃ out, Runs W (tabulate H π l d floor J) m fuel out ∧
      out (cell 1 .ptr)=((base+offset N J:ℕ):ℤ) ∧
      (∀ j < J, ∀ x y : Fin N, y.val < columns (shapeAt j) N →
        (out ((base+offset N j+x.val*columns (shapeAt j) N+y.val:ℕ):ℤ):ℚ)=
          (Round.mk H π a b).apply w (raw (shapeOf (shapeAt j)) x y)) ∧
      ∀ z : ℕ, z < base ∨ base+offset N J ≤ z → out z=m z := by
  let N := 2^L
  let B := 8+N*N*(bound H π l d+12)
  induction J with
  | zero => exact ⟨0,by simp,m,.skip _,by simpa [offset] using ptr,by omega,fun _ _ => rfl⟩
  | succ j ih =>
    have prev := Nat.add_le_add_left (offset_mono N (Nat.le_succ j)) base
    obtain ⟨t,ht,x,prior,dst,old,stable⟩ := ih (by omega) (prev.trans room)
    have keep (z : ℕ) (hz : z < base) := stable z (Or.inl hz)
    have read := rec.prefix pre keep
    have before := pre.prefix (b:=base+offset N j) (by omega) keep
    have xdim : x 0=(2:ℤ)^L := (keep 0 pos).trans dim
    have fits : base+offset N j+N*columns (shapeAt j) N ≤ M := by
      rw [Nat.add_assoc,←offset_succ]; exact room
    obtain ⟨u,hu,out,now,dst',done,next⟩ := gather_runs read before ha hb (shapeAt j)
      xdim px py dst cap fits bottom
    have leB : (entry H π l (shapeOf (shapeAt j)) d).steps ≤ bound H π l d :=
      Finset.single_le_sum (f:=fun q : Fin 90 => (entry H π l (shapeOf (shapeAt q.val)) d).steps)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨j,by omega⟩ : Fin 90))
    have hbnd : u ≤ B := hu.trans (Nat.add_le_add_left (Nat.mul_le_mul
      (Nat.mul_le_mul_left N (cols_le _ (Nat.pow_pos (by decide) : 0<N))) (Nat.add_le_add_right leB 12)) 8)
    refine ⟨t+u,by rw [Nat.succ_mul]; exact Nat.add_le_add ht hbnd,out,.seq prior now,?_,?_,?_⟩
    · simpa only [offset_succ,Nat.add_assoc] using dst'
    · intro i hi v u hcol
      by_cases last : i=j
      · subst i; exact done v u hcol
      · have he := offset_mono N (by omega : i+1 ≤ j)
        rw [offset_succ] at he
        have hbnd := index_lt N (columns (shapeAt i) N) v u hcol
        have addr : base+offset N i+v.val*columns (shapeAt i) N+u.val < base+offset N j := by omega
        rw [next _ (Or.inl addr)]; exact old i (by omega) v u hcol
    · intro z hz
      change z < base ∨ base+offset N (j+1)≤z at hz
      rw [offset_succ] at hz
      have outside : z < base+offset N j ∨ base+offset N j+N*columns (shapeAt j) N≤z := by omega
      have oldRange : z < base ∨ base+offset N j≤z := by omega
      exact (next z outside).trans (stable z oldRange)

theorem complete_table {L W M base : ℕ} {H : SimpleGraph V} {π : Equiv.Perm V} {l : Layout}
    {m : Memory} {a b : Option (Mask L)} {w : WeightKey (2^L) → ℚ}
    (rec : Records l m a b w) (pre : Before (L:=L) l m base)
    {d : Branch} (ha : a.isSome=first d) (hb : b.isSome=second d)
    (dim : m 0=(2:ℤ)^L) (pos : 0 < base) (px : l.x=cell 1 .x) (py : l.y=cell 1 .y)
    (ptr : m (cell 1 .ptr)=base) (cap : Division.Room W M) {floor : ℤ}
    (bottom : ∀ j, floor < cell 1 j) (room : base+offset (2^L) 90 ≤ M) :
    ∃ fuel ≤ 90*(8+2^L*2^L*(bound H π l d+12)), ∃ out,
      Runs W (tabulate H π l d floor 90) m fuel out ∧
      (∀ k, (out ((base+Table.wordIndex k:ℕ):ℤ):ℚ)=(Round.mk H π a b).apply w k) ∧
      ∀ z : ℕ, z < base ∨ base+offset (2^L) 90 ≤ z → out z=m z := by
  obtain ⟨t,ht,out,run,_,all,keep⟩ := tabulate_runs rec pre ha hb dim pos px py ptr cap bottom 90 le_rfl room
  refine ⟨t,ht,out,run,?_,keep⟩
  let N := 2^L
  rintro (⟨i,u⟩|⟨i,j,u,v⟩)
  · let z : Fin N := ⟨0,by dsimp [N]; positivity⟩
    have p := all i.val (by have := i.isLt; omega) u z
    rw [unaryAt i] at p
    have h := p (by decide : (0:ℕ)<1)
    have off : offset N i.val=i.val*N := by
      simp [offset,min_eq_left i.isLt.le,Nat.sub_eq_zero_of_le i.isLt.le]
    simpa only [N,off,Table.wordIndex,columns,Nat.mul_one,z,Nat.add_zero,Nat.add_assoc,shapeOf,raw] using h
  · let c := 9+i.val*9+j.val
    have hi := i.isLt
    have hj := j.isLt
    have p := all c (by dsimp [c]; omega) u v
    rw [show shapeAt c=.cross i j from crossAt i j] at p
    have h := p v.isLt
    have off : offset N c=9*N+(i.val*9+j.val)*(N*N) := by
      unfold offset
      rw [min_eq_right (by dsimp [c]; omega : 9 ≤ c),show c-9=i.val*9+j.val by dsimp [c]; omega]
    change (out ((base+offset N c+_+_:ℕ):ℤ):ℚ)=_ at h
    rw [off] at h
    simpa only [Table.wordIndex,columns,Nat.add_assoc,N,shapeOf,raw] using h

end VWZClique.IntegerRAM.FoldWeight

end

/- NativeArenaTables -/
section

namespace VWZClique.IntegerRAM.NativeArena
open Structured FoldWeight UniformFolds FoldProof Graph NativeFrame

def lane : VWZClique.Slot → ℕ
  | .inl i => i.val
  | .inr i => 3+i.val

def routeIndex (h : Fin 3) (s : VWZClique.Slot) := 6*h.val+lane s

theorem routeIndex_lt (h : Fin 3) (s : VWZClique.Slot) : routeIndex h s<18 := by
  have hh := h.isLt
  cases s with
  | inl j => have hj := j.isLt; simp only [routeIndex,lane]; omega
  | inr j => have hj := j.isLt; simp only [routeIndex,lane]; omega

def pointerLayout : FoldWeight.Layout where
  n := 0
  unary i := pointer i.val
  edge i j := pointer (9+i.val*9+j.val)
  adjust h s := pointer (90+routeIndex h s)
  pin i := pointer (108+i.val)
  x := Table.cell 1 .x
  y := Table.cell 1 .y

def routeBase (base N : ℕ) (h : Fin 3) (s : VWZClique.Slot) :=
  maps base N+routeIndex h s*N
def pinBase (base N : ℕ) (i : Fin 4) := maps base N+(18+i.val)*N

structure Sources {L : ℕ} (base : ℕ) (m : Memory) (a b : Option (Mask L)) (w : WeightKey (2^L)→ℚ) : Prop where
  weights : ∀ k, (m ((base+Table.wordIndex k:ℕ):ℤ):ℚ)=w k
  route : ∀ h s (x : Fin (2^L)), m ((routeBase base (2^L) h s+x.val:ℕ):ℤ)=
    ((UniformFolds.wordIndex L ((FoldProof.route a b h s).2 ((UniformFolds.wordIndex L).symm x))).val:ℤ)
  pin : ∀ i (x : Fin (2^L)), (m ((pinBase base (2^L) i+x.val:ℕ):ℤ):ℚ)=
    pinWeight a b i ((UniformFolds.wordIndex L).symm x)

private theorem unaryPtr (base N : ℕ) (i : V) : pointerValue base N i.val=base+i.val*N := by
  simp [pointerValue,i.isLt]

private theorem edgePtr (base N : ℕ) (i j : V) :
    pointerValue base N (9+i.val*9+j.val)=base+9*N+(i.val*9+j.val)*(N*N) := by
  have hi := i.isLt
  have hj := j.isLt
  simp [pointerValue,show ¬ 9+i.val*9+j.val<9 by omega,show 9+i.val*9+j.val<90 by omega,
    show 9+i.val*9+j.val-9=i.val*9+j.val by omega]

private theorem routePtr (base N : ℕ) (h : Fin 3) (s : VWZClique.Slot) :
    pointerValue base N (90+routeIndex h s)=routeBase base N h s := by
  simp [routeBase,pointerValue,show ¬90+routeIndex h s<9 by omega,show ¬90+routeIndex h s<90 by omega]

private theorem pinPtr (base N : ℕ) (i : Fin 4) :
    pointerValue base N (108+i.val)=pinBase base N i := by
  simp [pinBase,pointerValue,show ¬108+i.val<9 by omega,show ¬108+i.val<90 by omega,
    show 108+i.val-90=18+i.val by omega]

theorem records_of_setup {L W d base : ℕ} {m : Memory} {a b : Option (Mask L)} {w : WeightKey (2^L)→ℚ}
    (hd : d≤36) (start : 512 ≤ base) (Nval : m 0=(2^L:ℕ)) (baseval : m (reg d .weights)=base)
    (src : Sources base m a b w) :
    ∃ out, Runs W (setPointers d 112) m (setupCost d 112) out ∧ Records pointerLayout out a b w ∧
      Before (L:=L) pointerLayout out (child base (2^L)) ∧
      ∀ z, SquareCode.Layout.floor < z → (z<400 ∨ 512 ≤ z) → out z=m z := by
  let N := 2^L
  obtain ⟨o,run,ptr,keep⟩ := setup_runs (W:=W) hd m Nval baseval 112
  have fr (z : ℕ) (hz : 512 ≤ z) : o z=m z := keep z (by dsimp [SquareCode.Layout.floor]; omega)
    (Or.inr (by change (512:ℤ) ≤ z; exact_mod_cast hz))
  have pu (i : V) : o (pointerLayout.unary i)=(base+i.val*N:ℕ) :=
    (ptr _ (by have := i.isLt; omega)).trans (by rw [unaryPtr])
  have pe (i j : V) : o (pointerLayout.edge i j)=(base+9*N+(i.val*9+j.val)*(N*N):ℕ) :=
    (ptr _ (by have := i.isLt; have := j.isLt; omega)).trans (by rw [edgePtr])
  have pa (h : Fin 3) (s : VWZClique.Slot) : o (pointerLayout.adjust h s)=(routeBase base N h s:ℕ) :=
    (ptr _ (by have := routeIndex_lt h s; omega)).trans (by rw [routePtr])
  have pp (i : Fin 4) : o (pointerLayout.pin i)=(pinBase base N i:ℕ) :=
    (ptr _ (by have := i.isLt; omega)).trans (by rw [pinPtr])
  have ncast : (N:ℤ)=(2:ℤ)^L := by simp [N]
  have head : base ≤ maps base N := by dsimp [maps,metaBase]; omega
  have tail : base ≤ child base N := by dsimp [child,rows]; omega
  have hN : 0 < N := by dsimp [N]; positivity
  have hdr : o 0=(2:ℤ)^L := by
    rw [keep 0 (by decide) (Or.inl (by decide)),Nval]; norm_cast
  refine ⟨o,run,⟨hdr,?_,?_,?_,?_⟩,?_,keep⟩
  · intro i x
    rw [pu,←Nat.cast_add,fr _ (by omega)]
    simpa [Table.wordIndex,N,Nat.add_assoc] using src.weights (.inl (i,x))
  · intro i j x y
    rw [pe,←ncast,←Nat.cast_mul,←Nat.cast_add,←Nat.cast_add,fr _ (by omega)]
    simpa [Table.wordIndex,N,Nat.add_assoc] using src.weights (.inr (i,j,x,y))
  · intro h s x
    rw [pa,←Nat.cast_add,fr _ (by dsimp [routeBase]; omega)]
    exact src.route h s x
  · intro i x
    rw [pp,←Nat.cast_add,fr _ (by dsimp [pinBase]; omega)]
    exact src.pin i x
  · have small {j : ℕ} (hj : j<112) : owned (child base N) (pointer j) := by
      dsimp [owned,pointer]; constructor <;> omega
    have um (i : V) (x : Fin N) : base+i.val*N+x.val < metaBase base N := by
      have ix := x.isLt
      have lim := Nat.mul_le_mul_right N i.isLt
      rw [Nat.succ_mul] at lim
      dsimp [metaBase,tableWords]; omega
    have em (i j : V) (x y : Fin N) : base+9*N+(i.val*9+j.val)*(N*N)+x.val*N+y.val < metaBase base N := by
      have xx := Table.index_lt N N x y y.isLt
      have hi := i.isLt
      have hj := j.isLt
      have lim := Nat.mul_le_mul_right (N*N) (by omega : i.val*9+j.val+1≤81)
      rw [Nat.add_mul,one_mul] at lim
      dsimp [metaBase,tableWords]; omega
    have cm : metaBase base N ≤ child base N := by dsimp [child,rows,maps]; omega
    have rm (j : ℕ) (hj : j<22) (x : Fin N) : maps base N+j*N+x.val < child base N := by
      have ix := x.isLt
      have lim := Nat.mul_le_mul_right N hj
      rw [Nat.succ_mul] at lim
      dsimp [child,rows]; omega
    refine ⟨⟨by decide,by change (0:ℤ)<(child base N:ℤ); exact_mod_cast (show 0 < child base N from (by omega : 0 < base).trans_le tail)⟩,fun i => small (by have := i.isLt; omega),
      fun i j => small (by have := i.isLt; have := j.isLt; omega),
      fun h s => small (by have := routeIndex_lt h s; omega),fun i => small (by have := i.isLt; omega),?_,?_,?_,?_⟩
    · intro i x; rw [pu,←Nat.cast_add]
      exact ⟨by positivity,by exact_mod_cast (um i x).trans_le cm⟩
    · intro i j x y; rw [pe,←ncast,←Nat.cast_mul,←Nat.cast_add,←Nat.cast_add]
      exact ⟨by positivity,by exact_mod_cast (em i j x y).trans_le cm⟩
    · intro h s x; rw [pa,←Nat.cast_add]
      exact ⟨by positivity,by exact_mod_cast rm _ (by have := routeIndex_lt h s; omega) x⟩
    · intro i x; rw [pp,←Nat.cast_add]
      exact ⟨by positivity,by exact_mod_cast rm _ (by have := i.isLt; omega) x⟩

end VWZClique.IntegerRAM.NativeArena

end

/- NativeArenaMapKinds -/
section

namespace VWZClique.IntegerRAM.NativeArena.MapSchedule
open FoldProof UniformFolds RankSwap.MaskEnumeration NativeFrame

inductive Kind
  | route (h : Fin 3) (s : VWZClique.Slot)
  | pin (i : Fin 4)
  deriving DecidableEq

inductive Source | identity | left | right
  deriving DecidableEq

def effective {L} (a : Option (Mask L)) : Mask L := a.getD (fun _ => none)

def Source.meaning {L} (a b : Option (Mask L)) : Source → Mask L
  | .identity => fun _ => none
  | .left => effective a
  | .right => effective b

def Source.take {L} (a b : Fin (5^L)) : Source → Fin (5^L)
  | .identity => 0
  | .left => a
  | .right => b

def Source.code : Source → SquareCode.Expr
  | .identity => .zero
  | .left => .reg 322
  | .right => .reg 323

def Encodes {L} (c : Fin (5^L)) (a : Option (Mask L)) :=
  integerMask (finFunctionFinEquiv.symm c : Digits L) = effective a

theorem Source.resolve {L} {ca cb : Fin (5^L)} {a b : Option (Mask L)}
    (ha : Encodes ca a) (hb : Encodes cb b) (s : Source) :
    integerMask (finFunctionFinEquiv.symm (s.take ca cb) : Digits L) = s.meaning a b := by
  cases s with
  | left => exact ha
  | right => exact hb
  | identity =>
    funext i
    have zero : ((finFunctionFinEquiv.symm (0 : Fin (5^L)) : Digits L) i)=0 := by
      apply Fin.ext
      change 0/5^i.val%5=0
      simp
    simp [take,meaning,integerMask,zero]

structure Setting where
  source : Source
  valid : Bool
  read : Quad → Bool

def adjustSetting (s : Source) (i : Fin 3) : Setting :=
  if i=0 then ⟨s,false,fun q => q.2.2.1⟩ else
  if i=1 then ⟨s,false,fun q => q.2.2.2⟩ else ⟨.identity,false,Prod.fst⟩

def setting : Kind → Setting
  | .route h (.inl i) => if h=1 then adjustSetting .right i else ⟨.identity,false,Prod.fst⟩
  | .route h (.inr i) => if h=2 then adjustSetting .left i else ⟨.identity,false,Prod.fst⟩
  | .pin i => ⟨if i.val<2 then .left else .right,true,if i.val%2=0 then Prod.fst else fun q => q.2.1⟩

def ordinal : Kind → ℕ
  | .route h s => routeIndex h s
  | .pin i => 18+i.val

theorem ordinal_lt (k : Kind) : ordinal k<22 := by
  cases k with
  | route h s => exact (routeIndex_lt h s).trans (by decide)
  | pin i => have := i.isLt; dsimp [ordinal]; omega

private theorem lane_inj : Function.Injective lane := by
  rintro (a|a) (b|b) eq
  all_goals have ha := a.isLt; have hb := b.isLt; simp only [lane] at eq
  · exact congrArg Sum.inl (Fin.ext eq)
  · omega
  · omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem ordinal_inj : Function.Injective ordinal := by
  rintro (⟨h,s⟩|i) (⟨g,t⟩|j) eq
  · have bound (r : VWZClique.Slot) : lane r<6 := by cases r with
      | inl k => have := k.isLt; dsimp [lane]; omega
      | inr k => have := k.isLt; dsimp [lane]; omega
    have hs := bound s
    have ht := bound t
    change 6*h.val+lane s=6*g.val+lane t at eq
    obtain rfl : h=g := Fin.ext (by omega)
    obtain rfl : s=t := lane_inj (by omega)
    rfl
  · have := routeIndex_lt h s; dsimp [ordinal] at eq; omega
  · have := routeIndex_lt g t; dsimp [ordinal] at eq; omega
  · exact congrArg Kind.pin (Fin.ext (by dsimp [ordinal] at eq; omega))

def routes (h : Fin 3) : List Kind :=
  (List.finRange 3).map (fun i => .route h (.inl i)) ++
  (List.finRange 3).map (fun i => .route h (.inr i))

def all : List Kind := (List.finRange 3).flatMap routes ++ (List.finRange 4).map .pin

theorem mem_all (k : Kind) : k∈all := by
  cases k with
  | route h s =>
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨h,List.mem_finRange h,?_⟩
    cases s with
    | inl i => exact List.mem_append_left _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)
    | inr i => exact List.mem_append_right _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)
  | pin i => exact List.mem_append_right _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)

theorem length_all : all.length=22 := by decide

noncomputable def value {L : ℕ} (a b : Option (Mask L)) (k : Kind) (x : Fin (2^L)) : ℚ :=
  match k with
  | .route h s => ((wordIndex L ((FoldProof.route a b h s).2 ((wordIndex L).symm x))).val:ℚ)
  | .pin i => pinWeight a b i ((wordIndex L).symm x)

theorem route_meaning {L} (a b : Option (Mask L)) (h : Fin 3) (s : VWZClique.Slot) (x : Bits L) :
    restore ((setting (.route h s)).source.meaning a b) (setting (.route h s)).read x =
      (FoldProof.route a b h s).2 x := by
  cases s with
  | inl i => fin_cases h <;> fin_cases i <;> cases b <;> rfl
  | inr i => fin_cases h <;> fin_cases i <;> cases a <;> rfl

theorem pin_meaning {L} (a b : Option (Mask L)) (i : Fin 4) (x : Bits L) :
    (flag (some ((setting (.pin i)).source.meaning a b)) (setting (.pin i)).read x : ℚ) =
      pinWeight a b i x := by
  fin_cases i <;> cases a <;> cases b <;> simp [setting,Source.meaning,effective,pinWeight,flag,pin,Fin.isValue] <;> rfl

end VWZClique.IntegerRAM.NativeArena.MapSchedule

end

/- NativeFoldBits -/
section

namespace VWZClique.IntegerRAM.FoldBits
open Structured

/-- A row sends a raw bit to an output bit and records whether the pin is satisfied. -/
structure Row where
  output : Bool → Bool
  valid : Bool → Bool

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

def N : ℤ := -100
def u : ℤ := -101
def z : ℤ := -102
def ok : ℤ := -103
def ptr : ℤ := -104
def cnt : ℤ := -105
def one : ℤ := -106
def two : ℤ := -107
def four : ℤ := -108
def guard : ℤ := -109
def a : ℤ := -110
def v : ℤ := -111


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

def pre : List Atom := [.add u u u,.sub guard u N,.mul a ptr one]
def setHigh : List Atom := [.sub u u N,.add a a two]
def finishRow : List Atom := [.load v a,.add z z z,.add z z v,.add a a one,.load v a,
  .mul ok ok v,.add ptr ptr four,.add cnt cnt one]

def body : Command := .seq (code pre) (.seq (.whenNonnegative guard (code setHigh)) (code finishRow))
def loop : Command := .repeatWhileNegative body cnt

structure Regs (n x y sign p : ℕ) (c : ℤ) (m : Memory) : Prop where
  size : m N=n
  src : m u=x
  dst : m z=y
  good : m ok=sign
  ip : m ptr=p
  count : m cnt=c
  h1 : m one=1
  h2 : m two=2
  h4 : m four=4

def At (m : Memory) (p : ℕ) (r : Row) : Prop :=
  ∀ b, m ((p+2*bit b:ℕ):ℤ)=bit (r.output b) ∧
    m ((p+2*bit b+1:ℕ):ℤ)=bit (r.valid b)

def frame (m m' : Memory) := ∀ i : ℤ, i < v ∨ N < i → m' i=m i

set_option maxHeartbeats 1500000 in
theorem body_run {W n x y sign p : ℕ} {c : ℤ} {m : Memory} (r : Row)
    (h : Regs n x y sign p c m) (hr : At m p r) (hx : x<n)
    (cap : Capacity W (max n (p+3))) :
    let b := decide (n≤2*x)
    ∃ t ≤ 14, ∃ o, Runs W body m t o ∧
      Regs n (2*x-bit b*n) (2*y+bit (r.output b)) (sign*bit (r.valid b)) (p+4) (c+1) o ∧ frame m o := by
  dsimp only
  have ns : m (-100)=n := h.size
  have xs : m (-101)=x := h.src
  have ps : m (-104)=p := h.ip
  have os : m (-106)=1 := h.h1
  have ts : m (-107)=2 := h.h2
  let x₁ := pre.foldl write m
  have preRun : Runs W (code pre) m 3 x₁ := code_runs _ _ _ (by simp [pre,Safe,safe])
  have val : x₁ guard = 2*(x:ℤ)-n := by simp [x₁,pre,write,update,N,u,guard,a,ptr,one,xs,ns] <;> omega
  have hf : Fits W (x₁ guard) := by rw [val]; apply cap.fits <;> omega
  let b := decide (n≤2*x)
  let x₂ := if b then setHigh.foldl write x₁ else x₁
  have guardRun : Runs W (.whenNonnegative guard (code setHigh)) x₁ (if b then 3 else 1) x₂ := by
    by_cases e : n≤2*x
    · simp only [b,decide_eq_true e,if_true,x₂]
      exact .guard_take hf (by rw [val]; omega) (code_runs _ _ _ (by simp [setHigh,Safe,safe]))
    · simp only [b,decide_eq_false e,if_false,x₂]
      exact .guard_skip hf (by rw [val]; omega)
  have x₂a : x₂ a = ((p+2*bit b:ℕ):ℤ) := by
    cases e:b <;> simp [x₂,e,x₁,pre,setHigh,write,update,a,u,guard,N,two,ptr,one,bit,ps,os,ts]
  have x₂u : x₂ u = ((2*x-bit b*n:ℕ):ℤ) := by
    by_cases e : n≤2*x <;> simp [x₂,x₁,pre,setHigh,write,update,a,u,guard,N,b,e,bit,xs,ns] <;> omega
  have keep (i : ℤ) (h1 : i≠u) (h2 : i≠guard) (h3 : i≠a) : x₂ i=m i := by
    cases e:b <;> simp [x₂,e,x₁,pre,setHigh,write,update,h1,h2,h3]
  have one₂ : x₂ one=1 := (keep _ (by decide) (by decide) (by decide)).trans h.h1
  have data (i : ℕ) : x₂ i = m i := keep _ (by dsimp [u]; omega) (by dsimp [guard]; omega) (by dsimp [a]; omega)
  have f₁ : Fits W (x₂ a) := by rw [x₂a]; apply cap.fits <;> cases e:b <;> simp [bit] <;> omega
  have f₂ : Fits W (x₂ a + 1) := by rw [x₂a]; apply cap.fits <;> cases e:b <;> simp [bit] <;> omega
  change x₂ (-106)=1 at one₂
  let o := finishRow.foldl write x₂
  have run : Runs W (code finishRow) x₂ 8 o := by
    apply code_runs
    simpa [finishRow,Safe,safe,write,update,one,z,v,a,one₂] using And.intro f₁ f₂
  have val₁ : x₂ (x₂ a) = (bit (r.output b):ℤ) := by rw [x₂a,data]; exact (hr b).1
  have val₂ : x₂ (x₂ a+1) = (bit (r.valid b):ℤ) := by rw [x₂a,← Nat.cast_one (R:=ℤ),← Nat.cast_add,data]; exact (hr b).2
  have zz : x₂ z=y := (keep _ (by decide) (by decide) (by decide)).trans h.dst
  have ss : x₂ ok=sign := (keep _ (by decide) (by decide) (by decide)).trans h.good
  have pp : x₂ ptr=p := (keep _ (by decide) (by decide) (by decide)).trans h.ip
  have ff : x₂ four=4 := (keep _ (by decide) (by decide) (by decide)).trans h.h4
  have aa : 0≤x₂ a := by rw [x₂a]; positivity
  have diff (j : ℤ) (hj : j<0) : x₂ a + 1 ≠ j := by omega
  have n₂ : x₂ (-100)=n := (keep _ (by decide) (by decide) (by decide)).trans h.size
  have c₂ : x₂ (-105)=c := (keep _ (by decide) (by decide) (by decide)).trans h.count
  have t₂ : x₂ (-107)=2 := (keep _ (by decide) (by decide) (by decide)).trans h.h2
  dsimp only [a,z,ok,ptr,four,u] at val₁ val₂ zz ss pp ff x₂u diff
  change ∃ t ≤ 14, ∃ out, Runs W body m t out ∧ Regs n (2*x-bit b*n) (2*y+bit (r.output b))
    (sign*bit (r.valid b)) (p+4) (c+1) out ∧ frame m out
  refine ⟨_,?_,o,.seq preRun (.seq guardRun run),?_,?_⟩
  · cases b <;> decide
  · constructor <;> simp [o,finishRow,write,update,N,u,z,guard,ok,ptr,cnt,one,two,four,a,v,
      diff,one₂,val₁,val₂,zz,ss,pp,ff,x₂u,n₂,c₂,t₂] <;> omega
  · intro i hi
    have hh : i≠u ∧ i≠guard ∧ i≠a ∧ i≠v ∧ i≠z ∧ i≠ok ∧ i≠ptr ∧ i≠cnt := by
      dsimp [u,guard,a,v,N,z,ok,ptr,cnt] at *; omega
    simpa [o,finishRow,write,update,hh] using keep i hh.1 hh.2.1 hh.2.2.1

end VWZClique.IntegerRAM.FoldBits

end

/- NativeFoldWalk -/
section

namespace VWZClique.IntegerRAM.FoldBits
open Structured

abbrev Pairs := List (Row × Bool)
def inputBits (bs : Pairs) := bs.map Prod.snd
def outputBits (bs : Pairs) := bs.map fun t => t.1.output t.2
def allGood (bs : Pairs) : Bool := bs.all fun t => t.1.valid t.2

def Rows (m : Memory) (p : ℕ) : Pairs → Prop
  | [] => True
  | (r,_)::bs => At m p r ∧ Rows m (p+4) bs

private theorem rows_frame {m o : Memory} (hf : frame m o) (bs : Pairs) (p : ℕ) :
    Rows m p bs → Rows o p bs := by
  induction bs generalizing p with
  | nil => exact fun x => x
  | cons s bs ih =>
    rintro ⟨h,g⟩
    refine ⟨fun b => ?_,ih _ g⟩
    have same (i : ℕ) : o i = m i := hf _ (Or.inr (by dsimp [N]; omega))
    simpa only [same] using h b

def initGuard : List Atom := [.sub guard one one,.sub guard guard cnt,.sub guard guard one]
def command : Command := .seq (code initGuard) (.whenNonnegative guard loop)

private theorem advance (n x h pow : ℕ) (b : Bool) (bound : x<pow)
    (hn : n=2*pow*h) (hh : 0<h) :
    let raw := (bit b*pow+x)*h
    decide (n≤2*raw) = b ∧ 2*raw-bit b*n=x*(2*h) ∧ raw<n := by
  subst n
  have lt := Nat.mul_lt_mul_of_pos_right bound hh
  cases b with
  | false =>
    simp only [bit, Bool.false_eq_true, if_false, zero_mul, zero_add, Nat.sub_zero, decide_eq_false_iff_not]
    exact ⟨by nlinarith, by ring, by nlinarith⟩
  | true =>
    simp only [bit, if_true, one_mul, decide_eq_true_eq]
    refine ⟨by nlinarith, ?_, by nlinarith⟩
    rw [show 2*((pow+x)*h) = x*(2*h)+2*pow*h by ring, Nat.add_sub_cancel]

set_option maxHeartbeats 600000 in
private theorem nonempty_run (bs : Pairs) (pos p y s W : ℕ) (m : Memory) (hne : bs≠[])
    (regs : Regs (2^bs.length * 2^pos) ((encode (inputBits bs))*2^pos) y s p (-(bs.length:ℤ)) m)
    (table : Rows m p bs)
    (cap : Capacity W (max (2^bs.length*2^pos) (max (p+4*bs.length) bs.length))) :
    ∃ fuel ≤ 15*bs.length, ∃ out, Runs W loop m fuel out ∧
      Regs (2^bs.length*2^pos) 0
        (y*2^bs.length+encode (outputBits bs)) (s*bit (allGood bs)) (p+4*bs.length) 0 out ∧ frame m out := by
  induction bs generalizing m p pos y s with
  | nil => contradiction
  | cons head bs ih =>
    obtain ⟨r,b⟩ := head
    have plen : (inputBits bs).length=bs.length := by simp [inputBits]
    have olen : (outputBits bs).length=bs.length := by simp [outputBits]
    let D := 2^((r,b)::bs).length*2^pos
    let raw := (bit b*2^bs.length+encode (inputBits bs))*2^pos
    have splitb := advance D (encode (inputBits bs)) (2^pos) (2^bs.length) b
      (by simpa [plen] using encode_lt (inputBits bs)) (by dsimp [D]; rw [pow_succ]; ring) (by positivity)
    obtain ⟨digit,next,small⟩ := splitb
    change Regs D _ y s p _ m at regs
    have regs' : Regs D raw y s p (-(((r,b)::bs).length:ℤ)) m := by
      simpa only [inputBits,List.map_cons,encode,List.length_map,raw] using regs
    have cap' : Capacity W (max D (p+3)) :=
      lt_of_le_of_lt (by dsimp [D]; exact_mod_cast (by simp; omega : max (2^((r,b)::bs).length*2^pos) (p+3) ≤
        max (2^((r,b)::bs).length*2^pos) (max (p+4*((r,b)::bs).length) ((r,b)::bs).length))) cap
    obtain ⟨t,ht,o,run,post,keep⟩ := body_run r regs' table.1 small cap'
    change decide (D≤2*raw)=b at digit
    change 2*raw-bit b*D=_ at next
    rw [digit,next] at post
    have hc : o cnt = -(bs.length:ℤ) := by simpa using post.count
    have fit : Fits W (o cnt) := by rw [hc]; apply cap.fits <;> simp <;> omega
    have hp : D=2^bs.length*2^(pos+1) := by dsimp [D]; simp [pow_succ]; ring
    by_cases he : bs=[]
    · subst bs
      refine ⟨_,by simp; omega,o,.loop_done run fit (by simpa using hc.ge),?_,keep⟩
      simpa [inputBits,outputBits,allGood,bit,encode,D,Nat.mul_comm,Nat.mul_add,Nat.add_comm,
        Nat.add_mul,Nat.mul_assoc] using post
    · have regs₂ : Regs (2^bs.length*2^(pos+1)) (encode (inputBits bs)*2^(pos+1))
          (2*y+bit (r.output b)) (s*bit (r.valid b)) (p+4) (-(bs.length:ℤ)) o := by
        simpa only [hp,pow_succ' 2 pos,List.length_cons,Nat.cast_add,Nat.cast_one,neg_add_rev,
          show ∀ x : ℤ, -1 + -x + 1 = -x by intro x; ring] using post
      have cap₂ : Capacity W (max (2^bs.length*2^(pos+1)) (max (p+4+4*bs.length) bs.length)) :=
        lt_of_le_of_lt (by rw [← hp]; exact_mod_cast (by simp [D]; omega : max D (max (p+4+4*bs.length) bs.length) ≤
          max D (max (p+4*((r,b)::bs).length) ((r,b)::bs).length))) cap
      obtain ⟨tt,ht',o',res,final,fr⟩ := ih (pos+1) (p+4) _ _ o he regs₂ (rows_frame keep _ _ table.2) cap₂
      have neg : o cnt<0 := by rw [hc]; have := List.length_pos_iff.mpr he; omega
      refine ⟨_,by simp; omega,o',.loop_again run fit neg res,?_,fun j hj => (fr _ hj).trans (keep _ hj)⟩
      have prod : bit (r.valid b && allGood bs) = bit (r.valid b)*bit (allGood bs) := by
        cases r.valid b <;> cases allGood bs <;> decide
      change Regs D 0 (y*2^(bs.length+1)+
        (bit (r.output b)*2^(outputBits bs).length+encode (outputBits bs)))
        (s*bit (r.valid b && allGood bs)) (p+4*(bs.length+1)) 0 o'
      rw [hp,olen,prod]
      convert final using 1 <;> (try simp only [pow_succ]) <;> ring

end VWZClique.IntegerRAM.FoldBits

namespace VWZClique.IntegerRAM.FoldBits
open Structured

/-- The same instruction list handles every bit-length, including zero. -/
theorem command_runs (bs : Pairs) {W p : ℕ} {m : Memory}
    (regs : Regs (2^bs.length) (encode (inputBits bs)) 0 1 p (-(bs.length:ℤ)) m)
    (data : Rows m p bs)
    (cap : Capacity W (max (2^bs.length) (max (p+4*bs.length) (bs.length+1)))) :
    ∃ f ≤ 4+15*bs.length, ∃ out, Runs W command m f out ∧
      out z=↑(encode (outputBits bs)) ∧ out ok=↑(bit (allGood bs)) ∧ frame m out := by
  let u₀ := initGuard.foldl write m
  have run : Runs W (code initGuard) m 3 u₀ := code_runs _ _ _ (by simp [initGuard,Safe,safe])
  have reg : u₀ guard = (bs.length:ℤ)-1 := by
    have c₁ : m (-105) = -(bs.length:ℤ) := regs.count
    have h₁ : m (-106)=1 := regs.h1
    simp [u₀,initGuard,write,update,guard,cnt,one,c₁,h₁] <;> omega
  have same (i : ℤ) (hi : i≠guard) : u₀ i=m i := by simp [u₀,initGuard,write,update,hi]
  have frame₀ : frame m u₀ := by intro i hi; apply same; dsimp [v,N,guard] at *; omega
  have regs' : Regs (2^bs.length*2^0) (encode (inputBits bs)*2^0) 0 1 p (-(bs.length:ℤ)) u₀ := by
    simp only [pow_zero,mul_one]; rcases regs with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    constructor <;> rw [same _ (by decide)] <;> assumption
  have fit : Fits W (u₀ guard) := by rw [reg]; apply cap.fits <;> omega
  by_cases h : bs=[]
  · subst bs
    refine ⟨4,by simp,u₀,.seq run (.guard_skip fit (by rw [reg]; simp)),?_,?_,frame₀⟩
    · simpa [outputBits,encode] using regs'.dst
    · simpa [allGood,bit] using regs'.good
  · have cap' : Capacity W (max (2^bs.length * 2^0) (max (p+4*bs.length) bs.length)) :=
      lt_of_le_of_lt (by exact_mod_cast (by simp; omega : max (2^bs.length*2^0) (max (p+4*bs.length) bs.length) ≤
        max (2^bs.length) (max (p+4*bs.length) (bs.length+1)))) cap
    obtain ⟨t,ht,o,more,post,fr⟩ := nonempty_run bs 0 p 0 1 W u₀ h regs' (rows_frame frame₀ _ _ data) cap'
    have nonneg : ¬ u₀ guard<0 := by rw [reg]; have := List.length_pos_iff.mpr h; omega
    exact ⟨3+(1+t),by omega,o,.seq run (.guard_take fit nonneg more),by simpa using post.dst,by simpa using post.good,
      fun j hj => (fr _ hj).trans (frame₀ _ hj)⟩

end VWZClique.IntegerRAM.FoldBits

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

/- NativeRowRules -/
section

namespace VWZClique.IntegerRAM.RowRules
open Structured FoldBits

abbrev cmp : ℤ := -161
abbrev yes : ℤ := -162
abbrev c0 : ℤ := -163
abbrev c1 : ℤ := -164
abbrev c2 : ℤ := -165
abbrev c3 : ℤ := -166
abbrev pointer : ℤ := -167
abbrev qreg : ℤ := -168
abbrev index : ℤ := -169
abbrev bound : ℤ := -170
abbrev test : ℤ := -171

def bitSet (dest : ℤ) (v : Bool) : Atom := if v then .one dest else .sub dest dest dest

theorem bit_op (dest : ℤ) (v : Bool) (m : Memory) : write m (bitSet dest v)=update m dest (bit v) := by
  cases v <;> simp [write,bitSet,bit]

def paint (r : Row) : List Atom := [bitSet c0 (r.output false),bitSet c1 (r.valid false),
  bitSet c2 (r.output true),bitSet c3 (r.valid true)]

def holds (m : Memory) (r : Row) := m c0=bit (r.output false) ∧ m c1=bit (r.valid false) ∧
  m c2=bit (r.output true) ∧ m c3=bit (r.valid true)

theorem paint_run (W : ℕ) (m : Memory) (r : Row) :
    ∃ o, Runs W (code (paint r)) m 4 o ∧ holds o r ∧
      ∀ j : ℤ, j<c3 ∨ c0<j → o j=m j := by
  let o := (paint r).foldl write m
  have typ (d : ℤ) (b : Bool) (x : Memory) : safe W x (bitSet d b) := by cases b <;> trivial
  have run : Runs W (code (paint r)) m 4 o := code_runs _ _ _ (by simp [paint,Safe,typ])
  refine ⟨o,run,?_,?_⟩
  · simp [holds,o,paint,bit_op,update,c0,c1,c2,c3]
  · intro j hj
    dsimp [c0,c3] at hj
    simp [o,paint,bit_op,update,c0,c1,c2,c3] <;> split_ifs <;> omega

/-- The threshold scan picks one of five static local rules from the decoded digit.
Each enabled case overwrites the preceding case. -/
def select (f : ℕ→Row) : ℕ → Command
  | 0 => code (paint (f 0))
  | n+1 => .seq (select f n) (.seq (.atom (.sub cmp cmp yes)) (.whenNonnegative cmp (code (paint (f (n+1))))))

theorem select_run {W M k n : ℕ} (room : Graph.Division.Room W M) (hk : k≤M) (hn : n≤M)
    (f : ℕ→Row) (m : Memory) (val : m cmp=k) (one : m yes=1) :
    ∃ t o, t≤4+6*n ∧ Runs W (select f n) m t o ∧ holds o (f (min k n)) ∧
      o cmp=(k:ℤ)-n ∧ ∀ j : ℤ, (j<c3 ∨ c0<j) → j≠cmp → o j=m j := by
  induction n generalizing m with
  | zero =>
    obtain ⟨o,run,data,keep⟩ := paint_run W m (f 0)
    exact ⟨4,o,by omega,run,by simpa using data,by simpa using (keep _ (Or.inr (by decide))).trans val,fun j h _ => keep j h⟩
  | succ n ih =>
    obtain ⟨u,x,ub,prev,cells,ptr,frame⟩ := ih (by omega) m val one
    have yo := (frame yes (Or.inr (by decide)) (by decide)).trans one
    let y := update x cmp (x cmp-x yes)
    have sub : Runs W (.atom (.sub cmp cmp yes)) x 1 y := .atom (.sub ..)
    have cmpV : y cmp=(k:ℤ)-(n+1) := by simp [y,update,ptr,yo]; ring
    have fit : Fits W (y cmp) := by rw [cmpV]; apply room.fits <;> omega
    have kept (j : ℤ) (hj : j≠cmp) : y j=x j := by simp [y,update,hj]
    by_cases enough : n+1≤k
    · obtain ⟨o,run,set,fr⟩ := paint_run W y (f (n+1))
      refine ⟨_,o,by omega,.seq prev (.seq sub (.guard_take fit (by rw [cmpV]; omega) run)),by simpa [Nat.min_eq_right enough] using set,?_,?_⟩
      · simpa using (fr _ (Or.inr (by decide))).trans cmpV
      · intro j jj k; exact (fr _ jj).trans ((kept _ k).trans (frame _ jj k))
    · have keeps : holds y (f (min k (n+1))) := by
        have he : min k (n+1)=min k n := by omega
        rw [he]; simpa [holds,y,update,cmp,c0,c1,c2,c3] using cells
      refine ⟨_,y,by omega,.seq prev (.seq sub (.guard_skip fit (by rw [cmpV];omega))),keeps,by simpa using cmpV,?_⟩
      intro j jj h;exact (kept j h).trans (frame _ jj h)

def writeNext (r : ℤ) : Command := .seq (.atom (.store pointer r)) (.atom (.add pointer pointer yes))
def emit : Command := .seq (writeNext c0) (.seq (writeNext c1) (.seq (writeNext c2) (writeNext c3)))

theorem writeNext_run {W p M : ℕ} (room : Graph.Division.Room W M) (space : p≤M)
    (m : Memory) (r : ℤ) (ptr : m pointer=p) (unit : m yes=1) :
    ∃ o, Runs W (writeNext r) m 2 o ∧ o pointer=((p+1:ℕ):ℤ) ∧ o (p:ℤ)=m r ∧
      ∀ j : ℤ, j≠pointer → j≠(p:ℤ) → o j=m j := by
  let x := update m (m pointer) (m r)
  let o := update x pointer (x pointer+x yes)
  have run : Runs W (writeNext r) m 2 o := .seq (.atom (.store _ _ _ (ptr ▸ room.fits (by omega) (by omega)))) (.atom (.add ..))
  have pp : pointer ≠ (p:ℤ) := by dsimp [pointer];omega
  have yy : yes ≠ (p:ℤ) := by dsimp [yes];omega
  exact ⟨o,run,by simp [o,x,update,ptr,unit,pp,yy],by simp [o,x,update,ptr,Ne.symm pp],
    fun j h₁ h₂ => by simp [o,x,update,ptr,h₁,h₂]⟩

theorem emit_run {W p M : ℕ} (room : Graph.Division.Room W M) (space : p+3≤M)
    (m : Memory) (r : Row) (ptr : m pointer=p) (unit : m yes=1) (h : holds m r) :
    ∃ o, Runs W emit m 8 o ∧ At o p r ∧ o pointer=((p+4:ℕ):ℤ) ∧
      ∀ j : ℤ, j≠pointer → j<(p:ℤ) ∨ (p:ℤ)+3<j → o j=m j := by
  obtain ⟨v0,v1,v2,v3⟩ := h
  obtain ⟨a,ra,pa,d0,k0⟩ := writeNext_run room (by omega : p≤M) m c0 ptr unit
  have no (i : ℤ) (h : i<0) (k : ℕ) : i≠(k:ℤ) := by omega
  have dy (x : ℕ) : yes≠(x:ℤ) := no _ (by decide) _
  obtain ⟨b,rb,pb,d1,k1⟩ := writeNext_run room (by omega : p+1≤M) a c1 pa ((k0 _ (by decide) (dy _)).trans unit)
  obtain ⟨c,rc,pc,d2,k2⟩ := writeNext_run room (by omega : p+2≤M) b c2 pb
    ((k1 _ (by decide) (dy _)).trans ((k0 _ (by decide) (dy _)).trans unit))
  obtain ⟨o,ro,po,d3,k3⟩ := writeNext_run room space c c3 pc
    ((k2 _ (by decide) (dy _)).trans ((k1 _ (by decide) (dy _)).trans ((k0 _ (by decide) (dy _)).trans unit)))
  have notP (i : ℕ) : (i:ℤ)≠pointer := by dsimp [pointer];omega
  have m0 : o p=bit (r.output false) := by
    rw [k3 _ (notP _) (by omega),k2 _ (notP _) (by omega),k1 _ (notP _) (by omega),d0,v0]
  have m1 : o (p+1:ℕ)=bit (r.valid false) := by
    rw [k3 _ (notP _) (by omega),k2 _ (notP _) (by omega),d1,k0 _ (by decide) (no _ (by decide) _),v1]
  have m2 : o (p+2:ℕ)=bit (r.output true) := by
    rw [k3 _ (notP _) (by omega),d2,k1 _ (by decide) (no _ (by decide) _),k0 _ (by decide) (no _ (by decide) _),v2]
  have m3 : o (p+3:ℕ)=bit (r.valid true) := by
    rw [d3,k2 _ (by decide) (no _ (by decide) _),k1 _ (by decide) (no _ (by decide) _),k0 _ (by decide) (no _ (by decide) _),v3]
  refine ⟨o,.seq ra (.seq rb (.seq rc ro)),?_,po,?_⟩
  · intro b'; cases b' <;> simp only [bit,Bool.false_eq_true,if_false,if_true,mul_zero,mul_one,Nat.add_zero]
    · exact ⟨m0,m1⟩
    · exact ⟨m2,m3⟩
  · intro j hp h
    rw [k3 j hp (by omega),k2 j hp (by omega),k1 j hp (by omega),k0 j hp (by omega)]

end VWZClique.IntegerRAM.RowRules

end

/- NativeMaskRows -/
section

namespace VWZClique.IntegerRAM.RowRules
open Structured FoldBits
open SignedDivision

def setup : List Atom := [.mul SignedDivision.value SignedDivision.result yes,.mul cmp SignedDivision.remn yes]
def body (f : ℕ→Row) := Command.seq SignedDivision.divmod (.seq (code setup) (.seq (select f 4) emit))
def loop (f : ℕ→Row) := repeatN (body f) index yes bound test

def untouched (j : ℤ) := j ≠ SignedDivision.value ∧ (j < SignedDivision.signReg ∨ SignedDivision.result < j ∧ j ≠ SignedDivision.remn) ∧
  j≠cmp ∧ (j<c3 ∨ c0<j) ∧ j≠pointer

instance (j : ℤ) : Decidable (untouched j) := inferInstanceAs (Decidable (_ ∧ _))

theorem body_runs {W M h x p : ℕ} (hh : 0<h) (hM : h≤M) (room : Graph.Division.Room W M)
    (hc : (2:ℤ)^h*5≤M) (small : (x:ℤ)<(2:ℤ)^h*5) (space : p+3≤M) (m : Memory)
    (val : m SignedDivision.value=x) (div : m SignedDivision.divisor=5) (len : m SignedDivision.length=h)
    (one : m yes=1) (ptr : m pointer=p) (f : ℕ→Row) :
    ∃ t o, t≤13*h+51 ∧ Runs W (body f) m t o ∧ o SignedDivision.value=((x/5:ℕ):ℤ) ∧
      o pointer=((p+4:ℕ):ℤ) ∧ At o p (f (x%5)) ∧
      ∀ j : ℤ, untouched j → j<(p:ℤ) ∨ (p:ℤ)+3<j → o j=m j := by
  obtain ⟨s,a,hs,divrun,fr,vq,vr⟩ := SignedDivision.divmod_runs hh hM room (by decide : 0<5) small hc m val div len
  have ya : a yes=1 := (fr _ (by decide)).trans one
  let b := setup.foldl write a
  have prep : Runs W (code setup) a 2 b := code_runs _ _ _ (by simp [setup,Safe,safe])
  have yo : a (-162)=1 := ya
  have br : b cmp=((x%5:ℕ):ℤ) := by simpa [b,setup,write,update,cmp,SignedDivision.value,SignedDivision.remn,yes,yo] using vr
  have byes : b yes=1 := by simpa [b,setup,write,update,SignedDivision.value,cmp,yes] using ya
  have bval : b SignedDivision.value=((x/5:ℕ):ℤ) := by simpa [b,setup,write,update,SignedDivision.value,cmp,SignedDivision.result,yes,yo] using vq
  have rest (j : ℤ) (v : j≠SignedDivision.value) (c : j≠cmp) : b j=a j := by simp [b,setup,write,update,v,c]
  have pow : (1:ℤ)≤2^h := one_le_pow₀ (by decide) 
  have m5 : 5≤M := by exact_mod_cast (show (5:ℤ)≤M by linarith)
  obtain ⟨u,c,hu,act,data,_,keep⟩ := select_run room (by omega : x%5≤M) (by omega : 4≤M) f b br byes
  have cc : holds c (f (x%5)) := by simpa [Nat.min_eq_left (by omega : x%5≤4)] using data
  have cp := (keep pointer (by decide) (by decide)).trans ((rest _ (by decide) (by decide)).trans ((fr _ (by decide)).trans ptr))
  have cy := (keep yes (by decide) (by decide)).trans byes
  obtain ⟨o,wr,table,op,other⟩ := emit_run room space c _ cp cy cc
  refine ⟨_,o,by omega,.seq divrun (.seq prep (.seq act wr)),?_,op,table,?_⟩
  · have neg : SignedDivision.value < (p:ℤ) := by dsimp [SignedDivision.value];omega
    rw [other _ (by decide) (Or.inl neg),keep _ (by decide) (by decide),bval]
  · rintro j ⟨v,sg,cm,ce,pp⟩ rng
    exact (other j pp rng).trans ((keep _ ce cm).trans ((rest _ v cm).trans (fr _ sg)))

theorem at_copy {p : ℕ} {m a : Memory} {r : Row} (row : At m p r)
    (keep : ∀ k : ℕ, p≤k → k≤p+3 → a k=m k) : At a p r := by
  intro b
  have val : bit b≤1 := by cases b <;> decide
  rw [keep _ (by omega) (by omega),keep _ (by omega) (by omega)]
  exact row b

theorem loop_runs {W L M h z base : ℕ} (hL : 0<L) (hh : 0<h) (hM : h≤M)
    (room : Graph.Division.Room W M) (hc : (2:ℤ)^h*5≤M) (small : (z:ℤ)<(2:ℤ)^h*5)
    (space : base+4*L≤M) (f : ℕ→Row) (m : Memory)
    (val : m SignedDivision.value=z) (div : m SignedDivision.divisor=5) (len : m SignedDivision.length=h)
    (unit : m yes=1) (pt : m pointer=base) (ix : m index=0) (limit : m bound=L) :
    ∃ t o, t≤L*(13*h+54) ∧ Runs W (loop f) m t o ∧
      (∀ i<L, At o (base+4*i) (f (z/5^i%5))) ∧
      ∀ j : ℕ, j<base ∨ base+4*L≤j → o j=m j := by
  let I := fun (q : ℕ) (x : Memory) => x index=q ∧ x yes=1 ∧ x bound=L ∧
    x SignedDivision.divisor=5 ∧ x SignedDivision.length=h ∧ x SignedDivision.value=((z/5^q:ℕ):ℤ) ∧ x pointer=((base+4*q:ℕ):ℤ) ∧
    (∀ i<q, At x (base+4*i) (f (z/5^i%5))) ∧ ∀ j : ℕ, j<base ∨ base+4*q≤j → x j=m j
  have init : I 0 m := ⟨by simpa using ix,unit,limit,div,len,by simpa using val,by simpa using pt,by omega,fun _ _ => rfl⟩
  have iter (q : ℕ) (hq : q<L) (x : Memory) (init : I q x) :
      ∃ t≤13*h+51, ∃ y, Runs W (body f) x t y ∧ y index=q ∧ y yes=1 ∧ y bound=L ∧
        I (q+1) (nextMemory y index test q L) := by
    obtain ⟨xi,xu,xn,xd,xh,xv,xp,rows,keep⟩ := init
    have less : ((z/5^q:ℕ):ℤ)<(2:ℤ)^h*5 := (by exact_mod_cast Nat.div_le_self z (5^q) : ((z/5^q:ℕ):ℤ)≤z).trans_lt small
    obtain ⟨t,y,ht,run,ans,ptr,atq,fr⟩ := body_runs hh hM room hc less (by omega : base+4*q+3≤M) x xv xd xh xu xp f
    have fixed (j : ℤ) (neg : j<0) (ok : untouched j) : y j=x j := fr _ ok (Or.inl (by omega))
    have yi := (fixed index (by decide) (by decide)).trans xi
    have yu := (fixed yes (by decide) (by decide)).trans xu
    have yn := (fixed bound (by decide) (by decide)).trans xn
    have after (j : ℤ) (a : j≠index) (b : j≠test) : nextMemory y index test q L j=y j := by simp [nextMemory,update,a,b]
    have natkeep (j : ℕ) : nextMemory y index test q L j=y j := after _ (by dsimp [index];omega) (by dsimp [test];omega)
    have un (j : ℕ) : untouched (j:ℤ) := by
      dsimp [untouched,SignedDivision.value,SignedDivision.signReg,SignedDivision.result,SignedDivision.remn,cmp,c3,c0,pointer]; omega
    refine ⟨t,ht,y,run,yi,yu,yn,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp [nextMemory,update,index,test]
    · exact (after _ (by decide) (by decide)).trans yu
    · exact (after _ (by decide) (by decide)).trans yn
    · exact (after _ (by decide) (by decide)).trans ((fixed _ (by decide) (by decide)).trans xd)
    · exact (after _ (by decide) (by decide)).trans ((fixed _ (by decide) (by decide)).trans xh)
    · rw [after _ (by decide) (by decide),ans,Nat.div_div_eq_div_mul,pow_succ]
    · rw [after _ (by decide) (by decide),ptr];push_cast;ring
    · intro i hi
      by_cases eq : i=q
      · subst i; exact at_copy atq (fun j _ _ => natkeep j)
      · apply at_copy (rows i (by omega));intro j low high
        exact (natkeep j).trans (fr j (un j) (Or.inl (by omega)))
    · intro j hj;rw [natkeep,fr _ (un j) (by omega),keep _ (by omega)]
  obtain ⟨t,ht,o,run,finish⟩ := repeatN_runs (W:=W) (B:=13*h+51) hL _ (by decide : bound≠index)
    I (fun j hj => room.fits (by omega) (by omega)) iter init
  exact ⟨t,o,ht,run,finish.2.2.2.2.2.2.2.1,finish.2.2.2.2.2.2.2.2⟩

end VWZClique.IntegerRAM.RowRules

end

/- NativeRouteMaps -/
section

namespace VWZClique.IntegerRAM.RouteMaps
open Structured FoldBits

abbrev rowsPtr : ℤ := -180
abbrev dest : ℤ := -181
abbrev iter : ℤ := -182
abbrev unit : ℤ := -183
abbrev test : ℤ := -184
def setup : List Atom := [.mul N 0 unit,.mul u iter unit,.sub z unit unit,.one ok,
  .mul ptr rowsPtr unit,.sub cnt 320 320,.sub cnt cnt 320,.one one,.add two one one,.add four two two]
def collect (valid : Bool) := if valid then ok else z
def finish (valid : Bool) : List Atom := [.store dest (collect valid),.add dest dest unit]
def body (valid : Bool) : Command := .seq (code setup) (.seq command (code (finish valid)))
def init : List Atom := [.one unit,.sub iter unit unit]
def map (valid : Bool) := Command.seq (code init) (repeatN (body valid) iter unit 0 test)
def selected (valid : Bool) (bs : Pairs) := if valid then bit (allGood bs) else FoldBits.encode (outputBits bs)

theorem rows_copy {p : ℕ} {m a : Memory} (bs : Pairs) (data : Rows m p bs)
    (keep : ∀ j : ℕ, p≤j → j<p+4*bs.length → a j=m j) : Rows a p bs := by
  induction bs generalizing p with
  | nil => trivial
  | cons h tl ih =>
    obtain ⟨at0,rest⟩ := data
    exact ⟨RowRules.at_copy at0 (fun j hj hi => keep j hj (by simp; omega)),ih rest
      (fun j hj hi => keep j (by omega) (by simp;omega))⟩

theorem body_runs {W L M p dst j : ℕ} (room : Graph.Division.Room W M) (capacity : max (2^L) (max (p+4*L) (L+1))≤M)
    (space : dst≤M) (valid : Bool) (m : Memory) (bs : Pairs) (size : bs.length=L) (src : FoldBits.encode (inputBits bs)=j)
    (data : Rows m p bs) (nreg : m 0=((2^L:ℕ):ℤ)) (lreg : m 320=L) (oneR : m unit=1) (ip : m iter=j)
    (rp : m rowsPtr=p) (dp : m dest=dst) :
    ∃ t y, t≤16+15*L ∧ Runs W (body valid) m t y ∧ y dest=((dst+1:ℕ):ℤ) ∧
      y (dst:ℤ)=selected valid bs ∧
      ∀ k : ℤ, (k<v ∨ N<k) → k≠dest → k≠(dst:ℤ) → y k=m k := by
  let a := setup.foldl write m
  have prep : Runs W (code setup) m 10 a := code_runs _ _ _ (by simp [setup,Safe,safe])
  have reg : Regs (2^bs.length) (FoldBits.encode (inputBits bs)) 0 1 p (-(bs.length:ℤ)) a := by
    rw [size,src]
    constructor <;> dsimp [unit,iter,rowsPtr] at * <;>
      simp [a,setup,write,update,N,u,z,ok,ptr,cnt,one,two,four,unit,iter,rowsPtr,nreg,lreg,oneR,ip,rp]
  have fixed (k : ℤ) (h : k<v ∨ N<k) : a k=m k := by
    dsimp [v,N] at h
    simp [a,setup,write,update,N,u,z,ok,ptr,cnt,one,two,four] <;> split_ifs <;> omega
  have hData := rows_copy bs data (fun k _ _ => fixed k (Or.inr (by dsimp [N];omega)))
  obtain ⟨t,ht,x,run,ans,flag,fr⟩ := command_runs bs reg hData
    (by rw [size];exact lt_of_le_of_lt (by exact_mod_cast capacity) room)
  have keep (k : ℤ) (hk : k<v ∨ N<k) : x k=m k := (fr _ hk).trans (fixed _ hk)
  have xd := (keep dest (by decide)).trans dp
  have xu := (keep unit (by decide)).trans oneR
  have val : x (collect valid)=(selected valid bs:ℤ) := by cases valid <;> simpa [collect,selected] using (by first | exact ans | exact flag)
  have fit : Fits W (x dest) := xd ▸ room.fits (by omega) (by omega)
  let y := (finish valid).foldl write x
  have save : Runs W (code (finish valid)) x 2 y := code_runs _ _ _ (by simpa [finish,Safe,safe] using fit)
  have dneg : dest≠(dst:ℤ) := by dsimp [dest];omega
  have uneg : unit≠(dst:ℤ) := by dsimp [unit];omega
  refine ⟨_,y,by omega,.seq prep (.seq run save),?_,?_,?_⟩
  · simp [y,finish,write,update,xd,xu,dneg,uneg]
  · simp [y,finish,write,update,xd,val,Ne.symm dneg]
  · intro k hk h₁ h₂;simpa [y,finish,write,update,xd,h₁,h₂] using keep _ hk

theorem map_runs {W L M p dst : ℕ} (room : Graph.Division.Room W M)
    (capacity : max (2^L) (max (p+4*L) (L+1))≤M) (space : dst+2^L≤M)
    (before : 320<dst) (sep : dst+2^L≤p) (valid : Bool) (m : Memory)
    (spec : Fin (2^L)→Pairs) (len : ∀ x, (spec x).length=L) (src : ∀ x, FoldBits.encode (inputBits (spec x))=x.val)
    (data : ∀ x, Rows m p (spec x)) (nreg : m 0=((2^L:ℕ):ℤ)) (lreg : m 320=L)
    (rptr : m rowsPtr=p) (dptr : m dest=dst) :
    ∃ t y, t≤2+(2^L)*(19+15*L) ∧ Runs W (map valid) m t y ∧
      (∀ x : Fin (2^L), y ((dst+x.val:ℕ):ℤ)=selected valid (spec x)) ∧
      ∀ j : ℕ, j<dst ∨ dst+2^L≤j → y j=m j := by
  let n := 2^L
  let I := fun (q : ℕ) (x : Memory) => x iter=q ∧ x unit=1 ∧ x 0=(n:ℤ) ∧ x 320=L ∧ x rowsPtr=p ∧
    x dest=((dst+q:ℕ):ℤ) ∧ (∀ j : Fin n, j.val<q → x ((dst+j.val:ℕ):ℤ)=selected valid (spec j)) ∧
    ∀ j : ℕ, j<dst ∨ dst+q≤j → x j=m j
  let a := init.foldl write m
  have st : Runs W (code init) m 2 a := code_runs _ _ _ (by simp [init,Safe,safe])
  have start : I 0 a := by
    refine ⟨?_,?_,?_,?_,?_,?_,by omega,?_⟩
    all_goals try intro j hj
    all_goals dsimp [rowsPtr,dest] at *
    all_goals simp [a,init,write,update,iter,unit,dest,rowsPtr,n,nreg,lreg,rptr,dptr]
  have every (q : ℕ) (hq : q<n) (x : Memory) (h : I q x) :
    ∃ t≤16+15*L, ∃ y, Runs W (body valid) x t y ∧ y iter=q ∧ y unit=1 ∧ y 0=(n:ℤ) ∧
      I (q+1) (nextMemory y iter test q n) := by
    obtain ⟨ix,un,nr,lr,rp,dp,prior,frame⟩ := h
    let k : Fin n := ⟨q,hq⟩
    have rowData := rows_copy (spec k) (data k) (fun j hj _ => frame j (Or.inr (by omega)))
    obtain ⟨t,o,ht,run,ptr,answer,keep⟩ := body_runs room capacity (by omega : dst+q≤M) valid x (spec k)
      (len k) (src k) rowData nr lr un ix rp dp
    have control (j : ℤ) (neg : j<0) (bot : j<v) (d : j≠dest) : o j=x j := keep j (Or.inl bot) d (by omega)
    have other (j : ℕ) (ne : j≠dst+q) : o j=x j :=
      keep _ (Or.inr (by dsimp [N];omega)) (by dsimp [dest];omega) (by omega)
    have yi := (control iter (by decide) (by decide) (by decide)).trans ix
    have yu := (control unit (by decide) (by decide) (by decide)).trans un
    have yn : o 0=n := (other 0 (by omega)).trans nr
    have tick (j : ℤ) (i : j≠iter) (s : j≠test) : nextMemory o iter test q n j=o j := by simp [nextMemory,update,i,s]
    have natT (j : ℕ) : nextMemory o iter test q n j=o j := tick _ (by dsimp [iter];omega) (by dsimp [test];omega)
    refine ⟨t,ht,o,run,yi,yu,yn,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp [nextMemory,update,iter,test]
    · exact (tick _ (by decide) (by decide)).trans yu
    · exact (tick _ (by decide) (by decide)).trans yn
    · exact (tick _ (by decide) (by decide)).trans ((other 320 (by omega)).trans lr)
    · exact (tick _ (by decide) (by decide)).trans ((control _ (by decide) (by decide) (by decide)).trans rp)
    · rw [tick _ (by decide) (by decide),ptr];simp [Nat.add_assoc]
    · intro j hj;rw [natT]
      by_cases eq : j.val=q
      · obtain rfl : j=k := Fin.ext eq; exact answer
      · rw [other _ (by omega)];exact prior _ (by omega)
    · intro j hj;rw [natT,other _ (by omega),frame _ (by omega)]
  obtain ⟨t,ht,y,run,e⟩ := repeatN_runs (W:=W) (B:=16+15*L) (by dsimp [n];positivity : 0<n) _
    (by decide : (0:ℤ)≠iter) I (fun j hj => room.fits (by omega) (by omega)) every start
  refine ⟨_,y,by rw [show 19+15*L=16+15*L+3 by omega]; exact Nat.add_le_add_left ht 2,.seq st run,fun j => e.2.2.2.2.2.2.1 j j.isLt,e.2.2.2.2.2.2.2⟩

end VWZClique.IntegerRAM.RouteMaps

end

/- NativeRoutePreparation -/
section

namespace VWZClique.IntegerRAM.RouteMaps
open Structured FoldBits

def radixSetup : List Atom := [.one RowRules.yes,.mul SignedDivision.value 400 RowRules.yes,
  .add SignedDivision.divisor RowRules.yes RowRules.yes,.add SignedDivision.divisor SignedDivision.divisor SignedDivision.divisor,
  .add SignedDivision.divisor SignedDivision.divisor RowRules.yes,.add SignedDivision.length 320 320,
  .add SignedDivision.length SignedDivision.length 320,.add SignedDivision.length SignedDivision.length RowRules.yes,
  .mul RowRules.pointer 401 RowRules.yes,.mul RowRules.bound 320 RowRules.yes,.sub RowRules.index RowRules.yes RowRules.yes]
def mapSetup : List Atom := [.one unit,.mul rowsPtr 401 unit,.mul dest 402 unit]
def realize (valid : Bool) (f : ℕ→Row) : Command := .seq (code radixSetup) (.seq (RowRules.loop f) (.seq (code mapSetup) (map valid)))

theorem rows_for {L base : ℕ} {m : Memory} (f : Fin L→Row) (src : Fin L→Bool)
    (data : ∀ i : Fin L, At m (base+4*i.val) (f i)) :
    Rows m base (List.ofFn fun i => (f i,src i)) := by
  induction L generalizing base with
  | zero => simp [Rows]
  | succ L ih =>
    rw [List.ofFn_succ]
    refine ⟨by simpa using data 0,?_⟩
    apply ih (fun i => f i.succ) (fun i => src i.succ)
    intro i
    convert data i.succ using 1 <;> simp <;> omega

theorem realize_runs {W L M z p dst : ℕ} (hL : 0<L) (hz : z<5^L) (cap : Graph.Division.Room W M)
    (capacity : 5*2^(3*L+1)≤M) (before : 402<dst) (sep : dst+2^L≤p) (space : p+4*L≤M)
    (valid : Bool) (f : ℕ→Row) (m : Memory) (nreg : m 0=((2^L:ℕ):ℤ)) (lreg : m 320=L)
    (input : m 400=z) (rp : m 401=p) (dp : m 402=dst)
    (bits : Fin (2^L)→Fin L→Bool)
    (encoded : ∀ x : Fin (2^L), FoldBits.encode (List.ofFn (bits x))=x.val) :
    let spec := fun x : Fin (2^L) => List.ofFn fun i : Fin L => (f (z/5^i.val%5),bits x i)
    ∃ t y, t≤16+L*(13*(3*L+1)+54)+(2^L)*(19+15*L) ∧ Runs W (realize valid f) m t y ∧
      (∀ x : Fin (2^L), y ((dst+x.val:ℕ):ℤ)=selected valid (spec x)) ∧
      ∀ j : ℕ, (j<dst ∨ dst+2^L≤j) → (j<p ∨ p+4*L≤j) → y j=m j := by
  intro spec
  have smallReg : 402<p := before.trans_le ((Nat.le_add_right dst (2^L)).trans sep)
  have width : 2^L≤M := (Nat.le_add_left (2^L) dst).trans (sep.trans ((Nat.le_add_right p (4*L)).trans space))
  have maxCap : max (2^L) (max (p+4*L) (L+1))≤M := by omega
  have dstCap : dst+2^L≤M := sep.trans ((Nat.le_add_right p (4*L)).trans space)
  let a := radixSetup.foldl write m
  have init : Runs W (code radixSetup) m 11 a := code_runs _ _ _ (by simp [radixSetup,Safe,safe])
  have ar : a SignedDivision.value=z ∧ a SignedDivision.divisor=5 ∧ a SignedDivision.length=((3*L+1:ℕ):ℤ) ∧
      a RowRules.yes=1 ∧ a RowRules.pointer=p ∧ a RowRules.index=0 ∧ a RowRules.bound=L := by
    simp [a,radixSetup,write,update,SignedDivision.value,SignedDivision.divisor,SignedDivision.length,
      RowRules.yes,RowRules.pointer,RowRules.index,RowRules.bound,lreg,input,rp] <;> omega
  have aMem (j : ℕ) : a (j:ℤ)=m j := by
    simp [a,radixSetup,write,update,SignedDivision.value,SignedDivision.divisor,SignedDivision.length,
      RowRules.yes,RowRules.pointer,RowRules.index,RowRules.bound]
  have hcap : 2^(3*L+1)*5≤M := by simpa only [Nat.mul_comm (2^_) 5] using capacity
  have bitsize : 3*L+1≤M := (Nat.lt_two_pow_self (n:=3*L+1)).le.trans (by omega)
  have sz : 5^L≤2^(3*L+1) := by
    calc
      5^L ≤ 8^L := Nat.pow_le_pow_left (by decide) _
      _ = 2^(3*L) := by rw [pow_mul];rfl
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨v,u,hv,make,atRow,fr⟩ := RowRules.loop_runs hL (by omega : 0<3*L+1) bitsize cap
    (by exact_mod_cast hcap) (by exact_mod_cast (by omega : z<2^(3*L+1)*5)) space f a
    ar.1 ar.2.1 ar.2.2.1 ar.2.2.2.1 ar.2.2.2.2.1 ar.2.2.2.2.2.1 ar.2.2.2.2.2.2
  have orig (j : ℕ) (hj : j<p) : u (j:ℤ)=m j := (fr j (Or.inl hj)).trans (aMem _)
  let b := mapSetup.foldl write u
  have set : Runs W (code mapSetup) u 3 b := code_runs _ _ _ (by simp [mapSetup,Safe,safe])
  have low (j : ℕ) : b (j:ℤ)=u j := by simp [b,mapSetup,write,update,unit,rowsPtr,dest]
  have br : b rowsPtr=p := by
    simpa [b,mapSetup,write,update,unit,rowsPtr,dest] using (orig 401 (by omega)).trans rp
  have bd : b dest=dst := by
    simpa [b,mapSetup,write,update,unit,rowsPtr,dest] using (orig 402 (by omega)).trans dp
  have len (x) : (spec x).length=L := by simp [spec]
  have sr (x) : FoldBits.encode (inputBits (spec x))=x.val := by
    simpa [spec,inputBits,List.map_ofFn,Function.comp_def] using encoded x
  have data (x) : Rows b p (spec x) := by
    apply rows_for; intro i; exact RowRules.at_copy (atRow i.val i.isLt) (fun j _ _ => low j)
  obtain ⟨t,y,ht,rest,vals,other⟩ := map_runs cap maxCap dstCap (by omega) sep valid b spec len sr data
    ((low 0).trans ((orig _ (by omega)).trans nreg)) ((low 320).trans ((orig _ (by omega)).trans lreg)) br bd
  refine ⟨_,y,by omega,.seq init (.seq make (.seq set rest)),vals,?_⟩
  intro j h₁ h₂;rw [other _ h₁,low _,fr _ h₂,aMem]

end VWZClique.IntegerRAM.RouteMaps

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

def row (m : Option Quad) (r p : Quad → Bool) : Row :=
  { output := fun b => m.elim b r
    valid := fun b => m.elim true (fun d => decide (b = p d)) }



def inputRows {L : ℕ} (mask : Mask L) (src : Bits L) (r p : Quad → Bool) : Pairs :=
  List.ofFn fun i => (row (mask i) r p,src i)

theorem transfer {L : ℕ} (mask : Mask L) (src : Bits L) (r p : Quad → Bool) :
    let bs := inputRows mask src r p
    bs.length=L ∧ encode (inputBits bs)=(UniformFolds.wordIndex L src).val ∧
    encode (outputBits bs)=(UniformFolds.wordIndex L (restore mask r src)).val ∧
    (allGood bs=true ↔ pin (some mask) p src) := by
  dsimp only
  have iv : inputBits (inputRows mask src r p) = List.ofFn src := by simp [inputBits,inputRows,List.map_ofFn,Function.comp_def]
  have ov : outputBits (inputRows mask src r p) = List.ofFn (restore mask r src) := by
    simp [outputBits,inputRows,List.map_ofFn,Function.comp_def,row] <;> rfl
  refine ⟨by simp [inputRows],iv ▸ packed_eq src,ov ▸ packed_eq _,?_⟩
  simp only [allGood,List.all_eq_true,inputRows,List.mem_ofFn] 
  constructor
  · intro h i x hx
    have hh := h _ ⟨i,rfl⟩
    simpa [row,hx] using hh
  · rintro h _ ⟨i,rfl⟩
    cases hi : mask i with
    | none => simp [row,hi]
    | some v => simp [row,hi,h i v hi]

end VWZClique.IntegerRAM.FoldBits

end

/- NativeRouteMapBuild -/
section

namespace VWZClique.IntegerRAM.RouteMaps
open Structured FoldBits FoldProof UniformFolds RankSwap RankSwap.MaskEnumeration

def symbolRow (r p : Quad→Bool) (j : ℕ) : Row := row (if j=0 then none else some (unitBits (j-1))) r p

def build (valid : Bool) (r p : Quad→Bool) := realize valid (symbolRow r p)

noncomputable def mapValue {L : ℕ} (valid : Bool) (m : Mask L) (r p : Quad→Bool) (x : Fin (2^L)) : ℤ := by
  classical
  exact if valid then (if pin (some m) p ((wordIndex L).symm x) then 1 else 0)
    else ((wordIndex L (restore m r ((wordIndex L).symm x))).val:ℤ)

abbrev buildCost (L : ℕ) := 16+L*(13*(3*L+1)+54)+(2^L)*(19+15*L)

theorem buildCost_le (L : ℕ) : buildCost L ≤ 156*(2^L)^2 := by
  have h : L≤2^L := (Nat.lt_two_pow_self (n:=L)).le
  have pos : 1≤(2:ℕ)^L := Nat.one_le_pow _ _ (by decide)
  have sq : L*L≤(2^L)*(2^L) := Nat.mul_le_mul h h
  have one : 2^L≤(2^L)*(2^L) := Nat.le_mul_of_pos_right _ pos
  have cross : 2^L*L≤2^L*(2^L) := Nat.mul_le_mul_left _ h
  unfold buildCost
  nlinarith only [one,pos,h,sq,cross]

theorem radix_capacity (L : ℕ) : 5*2^(3*L+1)=10*(2^L)^3 := by
  rw [pow_succ,Nat.mul_comm 3 L,pow_mul]
  ring

theorem build_runs {W L M rowBase dst : ℕ} (hL : 0<L) (z : Fin (5^L)) (cap : Graph.Division.Room W M)
    (capacity : 5*2^(3*L+1)≤M) (before : 402<dst) (sep : dst+2^L≤rowBase) (space : rowBase+4*L≤M)
    (valid : Bool) (r p : Quad→Bool) (m : Memory) (nreg : m 0=((2^L:ℕ):ℤ)) (lreg : m 320=L)
    (input : m 400=z.val) (rp : m 401=rowBase) (dp : m 402=dst) :
    ∃ t y, t≤buildCost L ∧ Runs W (build valid r p) m t y ∧
      (∀ x : Fin (2^L), y ((dst+x.val:ℕ):ℤ)=mapValue valid (integerMask (finFunctionFinEquiv.symm z)) r p x) ∧
      ∀ j : ℕ, (j<dst ∨ dst+2^L≤j) → (j<rowBase ∨ rowBase+4*L≤j) → y j=m j := by
  classical
  let src := (wordIndex L).symm
  let mask := integerMask (finFunctionFinEquiv.symm z : Digits L)
  have enc (x : Fin (2^L)) : FoldBits.encode (List.ofFn (src x))=x.val := by
    simpa [src,packed] using packed_eq (src x)
  obtain ⟨t,y,ht,run,val,fr⟩ := realize_runs hL z.isLt cap capacity before sep space valid
    (symbolRow r p) m nreg lreg input rp dp src enc
  have rowEq (i : Fin L) : symbolRow r p (z.val/5^i.val%5) = row (mask i) r p := by
    rw [←digit_extraction z i]
    simp [symbolRow,mask,integerMask,Fin.ext_iff]
  refine ⟨t,y,ht,run,?_,fr⟩
  intro x
  have actual := val x
  simp only [rowEq] at actual
  change y ((dst+x.val:ℕ):ℤ)=selected valid (inputRows mask (src x) r p) at actual
  rw [actual]
  have tr := transfer mask (src x) r p
  cases valid with
  | false => simp [mapValue,selected,src,tr.2.2.1] <;> rfl
  | true =>
    by_cases e : pin (some mask) p (src x)
    · have good := tr.2.2.2.mpr e
      simp [mapValue,selected,bit,good,src] at e ⊢
      exact e
    · have bad : allGood (inputRows mask (src x) r p)=false :=
        Bool.eq_false_iff.mpr (fun h => e (tr.2.2.2.mp h))
      simp [mapValue,selected,bit,bad,src] at e ⊢
      exact e

end VWZClique.IntegerRAM.RouteMaps

end

/- NativeArenaMapSchedule -/
section

namespace VWZClique.IntegerRAM.NativeArena.MapSchedule
open Structured FoldProof UniformFolds NativeFrame SquareCode

def address (base n : ℕ) (k : Kind) := maps base n+ordinal k*n

def addrExpr (d j : ℕ) := ptrExp d (90+j)
def prep (d : ℕ) (k : Kind) : Command :=
  .seq (SquareCode.Layout.assign 400 (setting k).source.code)
    (.seq (SquareCode.Layout.assign 401 (addrExpr d 22))
      (SquareCode.Layout.assign 402 (addrExpr d (ordinal k))))

def prepCost (d : ℕ) (k : Kind) := ((setting k).source.code.steps+2)+
  (((addrExpr d 22).steps+2)+((addrExpr d (ordinal k)).steps+2))

structure Controls (d base L : ℕ) (ca cb : Fin (5^L)) (m : Memory) : Prop where
  N : m 0=((2^L:ℕ):ℤ)
  len : m 320=L
  left : m 322=ca.val
  right : m 323=cb.val
  weightPtr : m (reg d .weights)=base

theorem prep_runs {L W d base : ℕ} {ca cb : Fin (5^L)} (hd : d≤36) (m : Memory)
    (ctrl : Controls d base L ca cb m) (k : Kind) :
    ∃ o, Runs W (prep d k) m (prepCost d k) o ∧
      o 400=(((setting k).source.take ca cb).val:ℤ) ∧
      o 401=(rows base (2^L):ℕ) ∧ o 402=(address base (2^L) k:ℕ) ∧
      ∀ j : ℕ, j<400 ∨ 402<j → o j=m j := by
  let src := (setting k).source
  have safe : src.code.safe Layout.floor W m := by cases src <;> simp [Source.code,Expr.safe,Layout.floor]
  have got : src.code.val m=(src.take ca cb).val := by
    cases src with
    | identity => rfl
    | left => exact ctrl.left
    | right => exact ctrl.right
  obtain ⟨x,s₁,f₁⟩ := Layout.assign_run m (reg:=400) (by decide) src.code safe
  have keep₁ (z : ℤ) (low : Layout.floor<z) (ne : z≠400) : x z=m z := by rw [f₁ _ low,if_neg ne]
  have pos := reg_positive d .weights
  have small := reg_below hd .weights
  have neg : Layout.floor < reg d .weights := by dsimp [Layout.floor];omega
  have xn := (keep₁ 0 (by decide) (by decide)).trans ctrl.N
  have xb := (keep₁ _ neg (by omega)).trans ctrl.weightPtr
  obtain ⟨u,s₂,f₂⟩ := Layout.assign_run x (W:=W) (reg:=401) (by decide) (addrExpr d 22) (ptrExp_safe ..)
  have keep₂ (z : ℤ) (low : Layout.floor<z) (ne : z≠401) : u z=x z := by rw [f₂ _ low,if_neg ne]
  have un := (keep₂ 0 (by decide) (by decide)).trans xn
  have ub := (keep₂ _ neg (by omega)).trans xb
  obtain ⟨o,s₃,f₃⟩ := Layout.assign_run u (W:=W) (reg:=402) (by decide) (addrExpr d (ordinal k)) (ptrExp_safe ..)
  have keep₃ (z : ℤ) (low : Layout.floor<z) (ne : z≠402) : o z=u z := by rw [f₃ _ low,if_neg ne]
  have ptr {d n base j : ℕ} {m : Memory} (hn : m 0=n) (hb : m (reg d .weights)=base) :
      (addrExpr d j).val m = ((maps base n+j*n:ℕ):ℤ) := by
    rw [addrExpr,ptrExp_value hn hb]
    simp [pointerValue,show ¬90+j<9 by omega,show ¬90+j<90 by omega]
  refine ⟨o,.seq s₁ (.seq s₂ s₃),?_,?_,?_,?_⟩
  · rw [keep₃ _ (by decide) (by decide),keep₂ _ (by decide) (by decide),f₁ 400 (by decide),if_pos rfl]
    exact got
  · rw [keep₃ _ (by decide) (by decide),f₂ 401 (by decide),if_pos rfl,ptr xn xb]
    rfl
  · rw [f₃ 402 (by decide),if_pos rfl,ptr un ub]; rfl
  · intro j h
    have low : Layout.floor<(j:ℤ) := by dsimp [Layout.floor];omega
    rw [keep₃ _ low (by omega),keep₂ _ low (by omega),keep₁ _ low (by omega)]

def single (d : ℕ) (k : Kind) : Command :=
  .seq (prep d k) (RouteMaps.build (setting k).valid (setting k).read (setting k).read)

def emit (d : ℕ) : List Kind → Command
  | [] => .skip
  | k::ks => .seq (single d k) (emit d ks)

def outsideAll (base n j : ℕ) := (j<400 ∨ 402<j) ∧ (j< maps base n ∨ child base n≤j)

theorem controls_transfer {d base L : ℕ} {ca cb : Fin (5^L)} {m o : Memory}
    (hd : d≤36) (start : 512≤base) (c : Controls d base L ca cb m)
    (keep : ∀ j : ℕ, outsideAll base (2^L) j → o j=m j) : Controls d base L ca cb o := by
  have low : base≤ maps base (2^L) := by dsimp [maps,metaBase];omega
  have fr (j : ℕ) (p : j<400) : o j=m j := keep _ ⟨Or.inl p,Or.inl (by omega)⟩
  have rg := reg_positive d .weights
  have rb := reg_below hd .weights
  have hp : o (reg d .weights)=m (reg d .weights) := by
    simpa only [Int.toNat_of_nonneg rg.le] using fr (reg d .weights).toNat (by omega)
  exact ⟨(fr 0 (by decide)).trans c.N,(fr 320 (by decide)).trans c.len,
    (fr 322 (by decide)).trans c.left,(fr 323 (by decide)).trans c.right,hp.trans c.weightPtr⟩

theorem block_before {base n : ℕ} (k : Kind) : address base n k+n ≤ rows base n := by
  have top := Nat.mul_le_mul_right n (ordinal_lt k)
  rw [Nat.succ_mul] at top
  dsimp [address,rows];omega

theorem block_apart {base n : ℕ} {j k : Kind} (neq : j≠k) (x : Fin n) :
    address base n j+x.val<address base n k ∨ address base n k+n≤address base n j+x.val := by
  have different : ordinal j ≠ ordinal k := fun e => neq (ordinal_inj e)
  have hx := x.isLt
  rcases lt_or_gt_of_ne different with small|big
  · have h := Nat.mul_le_mul_right n small
    rw [Nat.succ_mul] at h
    dsimp [address];omega
  · have h := Nat.mul_le_mul_right n big
    rw [Nat.succ_mul] at h
    dsimp [address];omega


theorem map_value {L} (a b : Option (Mask L)) (k : Kind) (x : Fin (2^L)) :
    ((RouteMaps.mapValue (setting k).valid ((setting k).source.meaning a b) (setting k).read (setting k).read x):ℚ)=value a b k x := by
  classical
  cases k with
  | route h s =>
    have mode : (setting (.route h s)).valid=false := by
      cases s with
      | inl i => fin_cases h <;> fin_cases i <;> rfl
      | inr i => fin_cases h <;> fin_cases i <;> rfl
    simp only [RouteMaps.mapValue,mode,Bool.false_eq_true,if_false,route_meaning,value,Int.cast_natCast]
  | pin i =>
    change _=pinWeight a b i _
    rw [←pin_meaning]
    simp only [RouteMaps.mapValue,show (setting (.pin i)).valid=true by rfl,if_true,FoldProof.flag]
    split_ifs <;> norm_num

def fee (d L : ℕ) (k : Kind) := prepCost d k+RouteMaps.buildCost L

theorem single_runs {W L M d base : ℕ} {ca cb : Fin (5^L)} {a b : Option (Mask L)}
    (hd : d≤36) (hL : 0<L) (start : 512≤base) (cap : Graph.Division.Room W M)
    (capacity : 5*2^(3*L+1)≤M) (space : child base (2^L)≤M) (k : Kind)
    (ha : Encodes ca a) (hb : Encodes cb b) (m : Memory) (c : Controls d base L ca cb m) :
    ∃ t o, t≤fee d L k ∧ Runs W (single d k) m t o ∧
      (∀ x : Fin (2^L), (o ((address base (2^L) k+x.val:ℕ):ℤ):ℚ)=value a b k x) ∧
      ∀ j : ℕ, (j<400 ∨ 402<j) → (j<address base (2^L) k ∨ address base (2^L) k+2^L≤j) →
        (j<rows base (2^L) ∨ child base (2^L)≤j) → o j=m j := by
  obtain ⟨v,init,raw,rp,dp,fr⟩ := prep_runs hd m c k
  let cfg := setting k
  have lo : base≤address base (2^L) k := by dsimp [address,maps,metaBase];omega
  have hN : L≤2^L := (Nat.lt_two_pow_self (n:=L)).le
  have sc : rows base (2^L)+4*L≤child base (2^L) := by unfold child;omega
  obtain ⟨t,o,cost,step,answer,keep⟩ := RouteMaps.build_runs hL (cfg.source.take ca cb) cap capacity
    (by omega : 402<address base (2^L) k) (block_before k) (sc.trans space)
    cfg.valid cfg.read cfg.read v ((fr 0 (Or.inl (by decide))).trans c.N)
    ((fr 320 (Or.inl (by decide))).trans c.len) raw rp dp
  refine ⟨_,o,Nat.add_le_add_left cost _,.seq init step,?_,?_⟩
  · intro x
    rw [answer,cfg.source.resolve ha hb]
    exact map_value a b k x
  · intro j small block slot
    exact (keep j block (by omega)).trans (fr j small)

def cost (d L : ℕ) (ks : List Kind) := (ks.map (fee d L)).sum

theorem runs {W L M d base : ℕ} {ca cb : Fin (5^L)} {a b : Option (Mask L)}
    (hd : d≤36) (hL : 0<L) (start : 512≤base) (cap : Graph.Division.Room W M)
    (capacity : 5*2^(3*L+1)≤M) (space : child base (2^L)≤M) (ha : Encodes ca a) (hb : Encodes cb b)
    (ks : List Kind) (m : Memory) (c : Controls d base L ca cb m) :
    ∃ t o, t≤cost d L ks ∧ Runs W (emit d ks) m t o ∧
      (∀ k ∈ ks, ∀ x : Fin (2^L), (o ((address base (2^L) k+x.val:ℕ):ℤ):ℚ)=value a b k x) ∧
      ∀ j : ℕ, (j<400 ∨ 402<j) → (j<rows base (2^L) ∨ child base (2^L)≤j) →
        (∀ k ∈ ks, j<address base (2^L) k ∨ address base (2^L) k+2^L≤j) → o j=m j := by
  induction ks generalizing m with
  | nil => exact ⟨0,m,le_rfl,.skip _,by simp,fun _ _ _ _ => rfl⟩
  | cons k ks ih =>
    obtain ⟨s,u,sc,first,data,fr⟩ := single_runs hd hL start cap capacity space k ha hb m c
    have low : maps base (2^L)≤address base (2^L) k := Nat.le_add_right _ _
    have next : address base (2^L) k+(2^L)≤rows base (2^L) := block_before k
    have mrow : maps base (2^L)≤rows base (2^L) := Nat.le_add_right _ _
    have tail : rows base (2^L)≤child base (2^L) := Nat.le_add_right _ _
    have uc := controls_transfer hd start c (fun j (pre : outsideAll base (2^L) j) =>
      fr j pre.1 (by obtain h|h := pre.2 <;> omega) (by obtain h|h := pre.2 <;> omega))
    obtain ⟨t,o,tc,late,entries,keep⟩ := ih u uc
    refine ⟨_,o,Nat.add_le_add sc tc,.seq first late,?_,?_⟩
    · intro j hj x
      by_cases belongs : j∈ks
      · exact entries j belongs x
      · obtain rfl : j=k := (List.mem_cons.mp hj).resolve_right belongs
        have hx := x.isLt
        have big : base≤ maps base (2^L) := by dsimp [maps,metaBase];omega
        have fixed := keep (address base (2^L) j+x.val) (Or.inr (by omega)) (Or.inl (by omega))
          (fun y hy => block_apart (by rintro rfl;exact belongs hy) x)
        rw [fixed]; exact data x
    · intro j reg row prec
      rw [keep j reg row (fun y hy => prec y (List.mem_cons_of_mem _ hy)),fr j reg (prec _ List.mem_cons_self) row]

/-- All 18 routed coordinate maps and all four pin-filter maps are initialized
in the addresses consumed by the child table evaluator. -/
theorem sources {W L M d base : ℕ} {ca cb : Fin (5^L)} {a b : Option (Mask L)}
    (hd : d≤36) (hL : 0<L) (start : 512≤base) (cap : Graph.Division.Room W M)
    (capacity : 5*2^(3*L+1)≤M) (space : child base (2^L)≤M) (ha : Encodes ca a) (hb : Encodes cb b)
    (w : WeightKey (2^L)→ℚ) (m : Memory) (c : Controls d base L ca cb m)
    (wt : ∀ k, (m ((base+Graph.Table.wordIndex k:ℕ):ℤ):ℚ)=w k) :
    ∃ t o, t≤cost d L all ∧ Runs W (emit d all) m t o ∧ Sources base o a b w ∧
      ∀ j : ℕ, outsideAll base (2^L) j → o j=m j := by
  obtain ⟨t,o,time,run,data,fr⟩ := runs hd hL start cap capacity space ha hb all m c
  have ms : maps base (2^L)≤rows base (2^L) := Nat.le_add_right _ _
  have rc : rows base (2^L)≤child base (2^L) := Nat.le_add_right _ _
  have keep (j : ℕ) (pre : outsideAll base (2^L) j) : o j=m j := by
    obtain ⟨reg,earlier|later⟩ := pre
    · apply fr j reg (Or.inl (by omega))
      intro k _
      exact Or.inl (earlier.trans_le (Nat.le_add_right _ _))
    · apply fr j reg (Or.inr later)
      intro k _
      exact Or.inr ((block_before k).trans (rc.trans later))
  refine ⟨t,o,time,run,⟨?_,?_,?_⟩,keep⟩
  · intro k
    have hk := NativeLeaf.index_lt k
    rw [keep (base+Graph.Table.wordIndex k) ⟨Or.inr (by omega),Or.inl (by dsimp [maps,metaBase,tableWords];omega)⟩]
    exact wt k
  · intro h s x
    have v := data (.route h s) (mem_all _) x
    change (o ((routeBase base (2^L) h s+x.val:ℕ):ℤ):ℚ) = (((wordIndex L ((FoldProof.route a b h s).2 ((wordIndex L).symm x))).val:ℕ):ℚ) at v
    exact_mod_cast v
  · intro i x
    exact data (.pin i) (mem_all _) x

/-- One fixed quadratic overhead pays for the 22 maps at every possible
recursion depth of a nine-vertex pattern. -/
def overhead := ((List.range 37).map fun d => (all.map (prepCost d)).sum).sum + 22*156

theorem cost_le {d : ℕ} (hd : d≤36) (L : ℕ) : cost d L all ≤ overhead*(2^L)^2 := by
  have split (ks : List Kind) : cost d L ks=(ks.map (prepCost d)).sum + ks.length*RouteMaps.buildCost L := by
    induction ks with
    | nil => simp [cost]
    | cons k ks ih =>
      change fee d L k+cost d L ks=_
      rw [ih]
      simp [fee,Nat.add_mul]
      omega
  rw [split,length_all]
  let fixed := ((List.range 37).map fun d => (all.map (prepCost d)).sum).sum
  have h : (all.map (prepCost d)).sum≤fixed := List.le_sum_of_mem (List.mem_map.mpr ⟨d,List.mem_range.mpr (by omega),rfl⟩)
  have cost := Nat.mul_le_mul_left 22 (RouteMaps.buildCost_le L)
  have one : 0<(2^L:ℕ)^2 := by positivity
  have fixedCost := h.trans (Nat.le_mul_of_pos_right fixed one)
  dsimp [overhead,fixed] at *
  rw [Nat.add_mul]
  rw [←Nat.mul_assoc] at cost
  exact Nat.add_le_add fixedCost cost

end VWZClique.IntegerRAM.NativeArena.MapSchedule

end

/- NativeArenaChild -/
section

namespace VWZClique.IntegerRAM.NativeArena
open Structured UniformFolds FoldProof NativeFrame Graph FoldWeight

noncomputable def childTable (d : ℕ) (H : SimpleGraph V) (π : Equiv.Perm V) (br : Branch) : Command :=
  .seq (setPointers d 112) <| .seq (SquareCode.Layout.assign (Table.cell 1 .ptr) (childExp d)) <|
    .seq (tabulate H π pointerLayout br SquareCode.Layout.floor 90)
      (SquareCode.Layout.assign (reg (d+1) .weights) (childExp d))

noncomputable def tableCost (d : ℕ) (H : SimpleGraph V) (π : Equiv.Perm V) (br : Branch) (n : ℕ) :=
  setupCost d 112 + ((childExp d).steps+2 +
    (90*(8+n*n*(bound H π pointerLayout br+12))+((childExp d).steps+2)))

/-- Materialize the child's complete row-major weight table and install its
physical frame pointer. Only the pointer bank and new table are modified, apart
from the new frame's pointer and negative scratch. -/
theorem child_table_runs {W M L d base : ℕ} {m : Memory} {a b : Option (Mask L)} {w : WeightKey (2^L)→ℚ}
    (H : SimpleGraph V) (π : Equiv.Perm V) (br : Branch)
    (ha : a.isSome=first br) (hb : b.isSome=second br)
    (hd : d<36) (start : 512 ≤ base) (Nval : m 0=(2^L:ℕ)) (baseval : m (reg d .weights)=base)
    (src : Sources base m a b w) (room : Division.Room W M)
    (enough : child base (2^L)+Table.offset (2^L) 90 ≤ M) :
    let N := 2^L
    let dst := child base N
    ∃ fuel ≤ tableCost d H π br N, ∃ out, Runs W (childTable d H π br) m fuel out ∧
      out (reg (d+1) .weights)=dst ∧
      (∀ k, (out ((dst+Table.wordIndex k:ℕ):ℤ):ℚ)=(Round.mk H π a b).apply w k) ∧
      ∀ z : ℕ, (z:ℤ)≠reg (d+1) .weights → (z<400 ∨ 512 ≤ z) →
        (z < dst ∨ dst+Table.offset N 90 ≤ z) → out z=m z := by
  let N := 2^L
  let dst := child base N
  have dst₀ : base ≤ dst := by dsimp [dst,child,rows,maps,metaBase]; omega
  have small : reg d .weights<297 := reg_below (by omega) _
  have large := reg_positive d .weights
  obtain ⟨u,first,ready,before,frame₁⟩ := records_of_setup (W:=W) hd.le start Nval baseval src
  have unf : u 0=(N:ℕ) := (frame₁ 0 (by decide) (Or.inl (by decide))).trans Nval
  have ub : u (reg d .weights)=base :=
    (frame₁ _ (by dsimp [SquareCode.Layout.floor]; omega) (Or.inl (by omega))).trans baseval
  have flc (j : Table.Cell) : SquareCode.Layout.floor < Table.cell 1 j := by cases j <;> decide
  obtain ⟨v,init,frame₂⟩ := SquareCode.Layout.assign_run (W:=W) u (flc .ptr) (childExp d) (childExp_safe ..)
  have same (z : ℕ) : v z=u z := by
    rw [frame₂ _ (by dsimp [SquareCode.Layout.floor]; omega),if_neg (Table.nat_ne_cell 1 z .ptr)]
  have vm : v 0=(2:ℤ)^L := (same 0).trans (unf.trans (by simp [N]))
  have dest : v (Table.cell 1 .ptr)=(dst:ℕ) := by
    rw [frame₂ _ (flc .ptr),if_pos rfl]; exact childExp_value unf ub
  obtain ⟨f,hf,q,scan,table,frame₃⟩ := complete_table (H:=H) (π:=π) (ready.prefix before (fun z _ => same z))
    (before.prefix le_rfl (fun z _ => same z)) ha hb vm (by omega : 0 < dst) rfl rfl dest room flc enough
  have qn : q 0=(N:ℕ) := (frame₃ 0 (Or.inl (show 0 < dst from (by omega : 0 < base).trans_le dst₀))).trans ((same 0).trans unf)
  have qbase : q (reg d .weights)=base := by
    obtain ⟨r,hr⟩ := Int.eq_ofNat_of_zero_le large.le
    have rs : r < dst := by omega
    rw [hr,frame₃ r (Or.inl rs),same,←hr,ub]
  have hi := reg_positive (d+1) .weights
  obtain ⟨o,last,frame₄⟩ := SquareCode.Layout.assign_run (W:=W) q (reg:=reg (d+1) .weights)
    (by dsimp [SquareCode.Layout.floor]; omega) (childExp d) (childExp_safe ..)
  refine ⟨_,Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_right hf _) _) _,o,
    .seq first (.seq init (.seq scan last)),?_,?_,?_⟩
  · rw [frame₄ _ (by dsimp [SquareCode.Layout.floor]; omega),if_pos rfl]
    exact childExp_value qn qbase
  · intro k
    have hi' := reg_below (show d+1≤36 by omega) .weights
    have high : 512 ≤ dst+Table.wordIndex k := start.trans (dst₀.trans (Nat.le_add_right ..))
    have ne : ((dst+Table.wordIndex k:ℕ):ℤ)≠reg (d+1) .weights := by omega
    rw [frame₄ _ (by dsimp [SquareCode.Layout.floor]; omega),if_neg ne]
    exact table k
  · intro z ne region outside
    rw [frame₄ _ (by dsimp [SquareCode.Layout.floor]; omega),if_neg ne,frame₃ z outside,same]
    exact frame₁ z (by dsimp [SquareCode.Layout.floor]; omega) (by exact_mod_cast region)

end VWZClique.IntegerRAM.NativeArena

end

/- NativeArenaPush -/
section

namespace VWZClique.IntegerRAM.NativeArena
open Structured UniformFolds FoldProof NativeFrame NativeTraversal

noncomputable def materialize (d : ℕ) (H : SimpleGraph V) (π : Equiv.Perm V) (br : Branch) :=
  Command.seq (MapSchedule.emit d MapSchedule.all) (childTable d H π br)

noncomputable def pushMaterialCost (L d : ℕ) (H : SimpleGraph V) (π : Equiv.Perm V) (br : Branch) :=
  MapSchedule.cost d L MapSchedule.all + tableCost d H π br (2^L)

/-- From the selected mask codes in words 322 and 323, compute all routed indices and
pins, read the parent's binary values, and write the complete child weight table. -/
theorem materialize_runs {W L M d base : ℕ} {H : SimpleGraph V} (π : Equiv.Perm V) (br : Branch)
    {a b : Option (Mask L)} {ca cb : Fin (5^L)} (hd : d<36) (hL : 0 < L) (start : 512 ≤ base)
    (cap : Graph.Division.Room W M) (capacity : 5*2^(3*L+1) ≤ M)
    (space : child base (2^L)+Graph.Table.offset (2^L) 90 ≤ M)
    (caOK : MapSchedule.Encodes ca a) (cbOK : MapSchedule.Encodes cb b)
    (left : a.isSome=first br) (right : b.isSome=second br)
    (w : WeightKey (2^L)→ℚ) (m : Memory) (ctrl : MapSchedule.Controls d base L ca cb m)
    (source : ∀ k, (m ((base+Graph.Table.wordIndex k:ℕ):ℤ):ℚ)=w k) :
    let N := 2^L
    let dst := child base N
    ∃ f ≤ pushMaterialCost L d H π br, ∃ o, Runs W (materialize d H π br) m f o ∧
      o (reg (d+1) .weights)=dst ∧
      (∀ k, (o ((dst+Graph.Table.wordIndex k:ℕ):ℤ):ℚ)=(Round.mk H π a b).apply w k) ∧
      ∀ z : ℕ, (z:ℤ)≠reg (d+1) .weights → (z<400 ∨ 512 ≤ z) →
        (z < maps base N ∨ dst+Graph.Table.offset N 90 ≤ z) → o z=m z := by
  let N := 2^L
  let dst := child base N
  have mz : base ≤ maps base N := by dsimp [maps,metaBase]; omega
  have zd : maps base N ≤ dst := by dsimp [dst,child,rows]; omega
  obtain ⟨f,u,hf,build,tables,keep⟩ := MapSchedule.sources hd.le hL start cap capacity (by omega) caOK cbOK w m ctrl source
  have saved (j : ℕ) (regLow : j<400 ∨ 512 ≤ j) (outside : j < maps base N ∨ dst ≤ j) : u j=m j :=
    keep j ⟨by omega,outside⟩
  have un : u 0=(2^L:ℕ) := (saved 0 (Or.inl (by decide)) (Or.inl (by omega))).trans ctrl.N
  have regLo := reg_positive d .weights
  have regHi := reg_below hd.le .weights
  obtain ⟨v,hv⟩ := Int.eq_ofNat_of_zero_le regLo.le
  have ub : u (reg d .weights)=base := by
    rw [hv,saved v (Or.inl (by omega)) (Or.inl (by omega)),←hv,ctrl.weightPtr]
  obtain ⟨g,hg,o,sub,pointer,data,fr⟩ := child_table_runs H π br left right hd start un ub tables cap space
  refine ⟨f+g,Nat.add_le_add hf hg,o,.seq build sub,pointer,data,?_⟩
  intro z ne reg side
  change z < maps base N ∨ dst+Graph.Table.offset N 90 ≤ z at side
  rcases side with lo | hi
  · exact (fr z ne reg (Or.inl (lo.trans_le zd))).trans (saved z reg (Or.inl lo))
  · exact (fr z ne reg (Or.inr hi)).trans (saved z reg (Or.inr ((Nat.le_add_right ..).trans hi)))

end VWZClique.IntegerRAM.NativeArena

end

/- NativeArenaChoiceRead -/
section

namespace VWZClique.IntegerRAM.NativeArena.Choice
open NativeFrame Structured SquareCode Butterfly

/-- Raw base-five codes for the two children of a signed inclusion-exclusion call. -/
abbrev firstCode : ℤ := 322
abbrev secondCode : ℤ := 323

def lookup (d k : ℕ) (idx : ℤ) : Expr := .read (.add
  (.add (.add (baseExp d) (.add (.mul (.num 9) sizeExp) (.mul (.num 81) nsq)))
    (.mul (.num k) cube)) (.reg idx))

def slot (base n k i : ℕ) := metaBase base n+k*n^3+i

theorem lookup_spec {W d k n base i : ℕ} {idx : ℤ} (m : Memory)
    (hn : m 0=n) (hb : m (reg d .weights)=base) (hi : m idx=i) (above : -128 < idx)
    (addr : Fits W (slot base n k i:ℤ)) :
    (lookup d k idx).safe (-128) W m ∧ (lookup d k idx).val m=m (slot base n k i:ℕ) := by
  have hp := reg_positive d .weights
  have val : (baseExp d).val m+(((9:ℕ):ℤ)*(sizeExp.val m)+((81:ℕ):ℤ)*(nsq.val m))+
      (k:ℤ)*(cube.val m) + m idx = (slot base n k i:ℤ) := by
    simp [baseExp,sizeExp,nsq,cube,Expr.val,slot,metaBase,tableWords,hi,hn,hb,pow_succ]
  have safe : (baseExp d).safe (-128) W m := by simp [baseExp,Expr.safe]; omega
  simp only [lookup,Expr.safe,Expr.val,Expr.num_val]
  change (_ ∧ _ ∧ _) ∧ _
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · simp [Expr.safe,baseExp,sizeExp,nsq,cube,Expr.num_safe,above]; omega
  · rw [val]; have := Int.natCast_nonneg (slot base n k i); omega
  · rwa [val]
  · rw [val]

def writeResults (d : ℕ) : List Atom :=
  [.sub (-16) (-16) (-16), .add firstCode (-16) (-128), .add secondCode (-16) (-129),
    .add (reg d .coefficient) (-16) (-130)]

def triple (d : ℕ) (a b c : Expr) := Command.seq (a.code (-128))
  (.seq (b.code (-129)) (.seq (c.code (-130)) (line (writeResults d))))

def tripleCost (a b c : Expr) := a.steps+(b.steps+(c.steps+4))

theorem triple_run {W d : ℕ} (hd : d≤36) (m : Memory) (a b c : Expr)
    (sa : a.safe (-128) W m) (sb : b.safe (-128) W m) (sc : c.safe (-128) W m) :
    ∃ out, Runs W (triple d a b c) m (tripleCost a b c) out ∧
      out firstCode=a.val m ∧ out secondCode=b.val m ∧ out (reg d .coefficient)=c.val m ∧
      ∀ z : ℤ, 0 ≤ z → z≠firstCode → z≠secondCode → z≠reg d .coefficient → out z=m z := by
  have pos := reg_positive d .coefficient
  have low := reg_below hd .coefficient
  obtain ⟨x,ra,xa,fx⟩ := a.run m _ sa
  obtain ⟨bv,bs⟩ := carry (show (-129:ℤ)≤ -128 by decide) fx b sb
  obtain ⟨y,rb,yb,fy⟩ := b.run x _ bs
  have gy (z : ℤ) (hz : -128 < z) := (fy z (by omega)).trans (fx z hz)
  obtain ⟨cv,cs⟩ := carry (show (-130:ℤ)≤ -128 by decide) gy c sc
  obtain ⟨p,rc,pc,fp⟩ := c.run y _ cs
  let out := (writeResults d).foldl effect p
  have fin : Runs W (line (writeResults d)) p 4 out := line_runs _ _ (by simp [writeResults,safeLine,safe])
  have va := (fp _ (by decide : (-130:ℤ)< -128)).trans ((fy _ (by decide)).trans xa)
  have vb := (fp _ (by decide : (-130:ℤ)< -129)).trans (yb.trans bv)
  have vc := pc.trans cv
  have far₁ : firstCode≠reg d .coefficient := by unfold firstCode; omega
  have far₂ : secondCode≠reg d .coefficient := by unfold secondCode; omega
  have rz : (-16:ℤ)≠reg d .coefficient := by omega
  refine ⟨out,ra.seq (rb.seq (rc.seq fin)),?_,?_,?_,?_⟩
  · simp [out,writeResults,effect,update,far₁,firstCode,secondCode,va]
  · simp [out,writeResults,effect,update,far₂,firstCode,secondCode,vb]
  · simp [out,writeResults,effect,update,Ne.symm rz,vc]
  · intro z hz h₁ h₂ h₃
    have z0 : z≠ -16 := by omega
    simp [out,writeResults,effect,update,h₁,h₂,h₃,z0,fp z (by omega),gy z (by omega)]

end VWZClique.IntegerRAM.NativeArena.Choice

end

/- NativeArenaChoiceDivide -/
section

namespace VWZClique.IntegerRAM.NativeArena.Choice
open NativeFrame Structured SquareCode Butterfly SignedDivision

def divSetup (d : ℕ) : List Atom :=
  [.sub (-96) (-96) (-96),.add value (-96) (reg d .index),.add divisor (-96) (reg d .leftLength),
   .add length 320 320,.add (-97) length length,.add length (-97) length,
   .one (-96),.add length length (-96)]

def splitCursor (d : ℕ) := Command.seq (line (divSetup d)) divmod

theorem split_runs {W d L i mLen M : ℕ} (mem : Memory) (ii : mem (reg d .index)=i)
    (ln : mem (reg d .leftLength)=mLen) (depth : mem 320=L) (positive : 0 < mLen)
    (bound : (i:ℤ)<(2:ℤ)^(6*L+1)*mLen)
    (hlen : 6*L+1 ≤ M) (room : Graph.Division.Room W M) (cap : (2:ℤ)^(6*L+1)*mLen≤(M:ℤ)) :
    ∃ t≤13*(6*L+1)+21, ∃ out, Runs W (splitCursor d) mem t out ∧
      out result=((i/mLen:ℕ):ℤ) ∧ out remn=((i%mLen:ℕ):ℤ) ∧ ∀ z : ℤ, 0 ≤ z → out z=mem z := by
  let a := (divSetup d).foldl effect mem
  have d₁ := reg_positive d .index
  have d₂ := reg_positive d .leftLength
  have ni (f : Field) (z : ℤ) (nz : z≤0) : reg d f≠z := by have := reg_positive d f; omega
  have run : Runs W (line (divSetup d)) mem 8 a := line_runs _ _ (by simp [divSetup,safeLine,safe])
  have aI : a value=i := by simp [a,divSetup,effect,update,value,divisor,length,ni,ii]
  have aM : a divisor=mLen := by simp [a,divSetup,effect,update,value,divisor,length,ni,ln]
  have aL : a length=((6*L+1:ℕ):ℤ) := by simp [a,divSetup,effect,update,value,divisor,length,depth]; ring
  obtain ⟨v,out,ht,step,fr,q,r⟩ := divmod_runs (by omega) hlen room positive bound cap a aI aM aL
  refine ⟨_,by omega,out,run.seq step,q,r,?_⟩
  intro z hz
  rw [fr z (Or.inr (by dsimp [result,remn]; omega))]
  simp only [a,divSetup,List.foldl_cons,List.foldl_nil,effect,update]
  dsimp only [value,divisor,length]
  repeat' rw [if_neg (by omega)]

end VWZClique.IntegerRAM.NativeArena.Choice

end

/- NativeArenaChoice -/
section

namespace VWZClique.IntegerRAM.NativeArena.Choice
open NativeFrame Structured SquareCode UniformFolds NativeTraversal

def left (d : ℕ) := triple d (lookup d 3 (reg d .index)) .zero (lookup d 4 (reg d .index))
def right (d : ℕ) := triple d .zero (lookup d 3 (reg d .index)) (lookup d 4 (reg d .index))

def bothExpr (d : ℕ) := Expr.sub .zero (.mul
    (lookup d 4 SignedDivision.result) (lookup d 4 SignedDivision.remn))

def bothRead (d : ℕ) := triple d (lookup d 3 SignedDivision.result) (lookup d 3 SignedDivision.remn) (bothExpr d)

def choose (d : ℕ) : Branch → Command
  | .left => left d
  | .right => right d
  | .both => .seq (splitCursor d) (bothRead d)

def straightCost (d : ℕ) : Branch → ℕ
  | .left => tripleCost (lookup d 3 (reg d .index)) .zero (lookup d 4 (reg d .index))
  | .right => tripleCost .zero (lookup d 3 (reg d .index)) (lookup d 4 (reg d .index))
  | .both => tripleCost (lookup d 3 SignedDivision.result) (lookup d 3 SignedDivision.remn) (bothExpr d)

def selected (code coeff : ℕ→ℤ) (m i : ℕ) : Branch → ℤ × ℤ × ℤ
  | .left => (code i, 0,coeff i)
  | .right => (0,code i,coeff i)
  | .both => (code (i/m),code (i%m),-(coeff (i/m)*coeff (i%m)))

/-- The count and cursor are read from parent-frame registers. All arrays are
    addressed using the runtime dimension and the parent-frame weights pointer. -/
theorem choose_runs {d W L base n mLen i M : ℕ} (b : Branch) (hd : d≤36)
    (m : Memory) (hN : m 0=n) (hb : m (reg d .weights)=base) (hi : m (reg d .index)=i)
    (len : m (reg d .leftLength)=mLen) (depth : m 320=L)
    (code coeff : ℕ→ℤ) (table : ∀ j < mLen, m (slot base n 3 j:ℕ)=code j ∧ m (slot base n 4 j:ℕ)=coeff j)
    (fit : ∀ j < mLen, Fits W (slot base n 3 j:ℤ) ∧ Fits W (slot base n 4 j:ℤ))
    (valid : i < visits mLen b) (lengthFits : 6*L+1 ≤ M) (room : Graph.Division.Room W M)
    (many : (mLen:ℤ)≤(2:ℤ)^(6*L+1)) (cap : (2:ℤ)^(6*L+1)*mLen≤(M:ℤ)) :
    ∃ t ≤ straightCost d b+(13*(6*L+1)+21), ∃ out, Runs W (choose d b) m t out ∧
      out firstCode=(selected code coeff mLen i b).1 ∧
      out secondCode=(selected code coeff mLen i b).2.1 ∧
      out (reg d .coefficient)=(selected code coeff mLen i b).2.2 ∧
      ∀ z : ℤ, 0 ≤ z → z≠firstCode → z≠secondCode → z≠reg d .coefficient → out z=m z := by
  have hix : (-128:ℤ) < reg d .index := by have := reg_positive d .index; omega
  cases b with
  | left =>
    obtain ⟨sa,va⟩ := lookup_spec m hN hb hi hix (fit i valid).1
    obtain ⟨sc,vc⟩ := lookup_spec m hN hb hi hix (fit i valid).2
    obtain ⟨o,run,a,b,c,fr⟩ := triple_run hd m _ .zero _ sa True.intro sc
    exact ⟨_,Nat.le_add_right _ _,o,run,a.trans (va.trans (table i valid).1),b,c.trans (vc.trans (table i valid).2),fr⟩
  | right =>
    obtain ⟨sb,vb⟩ := lookup_spec m hN hb hi hix (fit i valid).1
    obtain ⟨sc,vc⟩ := lookup_spec m hN hb hi hix (fit i valid).2
    obtain ⟨o,run,a,b,c,fr⟩ := triple_run hd m .zero _ _ True.intro sb sc
    exact ⟨_,Nat.le_add_right _ _,o,run,a,b.trans (vb.trans (table i valid).1),c.trans (vc.trans (table i valid).2),fr⟩
  | both =>
    change i < mLen*mLen at valid
    have pos : 0 < mLen := by by_contra! fail; simp [Nat.eq_zero_of_le_zero fail] at valid
    have iBound : (i:ℤ)<(2:ℤ)^(6*L+1)*mLen := by
      exact (show (i:ℤ)<(mLen:ℤ)*mLen by exact_mod_cast valid).trans_le
        (mul_le_mul_of_nonneg_right many (Nat.cast_nonneg _))
    obtain ⟨t,ht,x,dv,q,r,fr⟩ := split_runs m hi len depth pos iBound lengthFits room cap
    have xN := (fr 0 (by decide)).trans hN
    have xb := (fr _ (reg_positive d .weights).le).trans hb
    have qok : i/mLen < mLen := (Nat.div_lt_iff_lt_mul pos).mpr valid
    have rok := Nat.mod_lt i pos
    have input (k j : ℕ) : x (slot base n k j:ℕ)=m (slot base n k j:ℕ) := fr _ (Int.natCast_nonneg _)
    obtain ⟨sa,va⟩ := lookup_spec x xN xb q (by decide) (fit _ qok).1
    obtain ⟨sb,vb⟩ := lookup_spec x xN xb r (by decide) (fit _ rok).1
    obtain ⟨sx,vx⟩ := lookup_spec x xN xb q (by decide) (fit _ qok).2
    obtain ⟨sy,vy⟩ := lookup_spec x xN xb r (by decide) (fit _ rok).2
    have sc : (bothExpr d).safe (-128) W x := ⟨True.intro,sx,sy⟩
    have prod : (bothExpr d).val x= -(coeff (i/mLen)*coeff (i%mLen)) := by
      change 0-_ * _ = _; rw [vx,vy,input,input,(table _ qok).2,(table _ rok).2,zero_sub]
    obtain ⟨o,run,a,b,c,keep⟩ := triple_run hd x _ _ _ sa sb sc
    refine ⟨_,?_,o,dv.seq run,a.trans (va.trans ((input ..).trans (table _ qok).1)),
      b.trans (vb.trans ((input ..).trans (table _ rok).1)),c.trans prod,?_⟩
    · change t+straightCost d .both ≤ straightCost d .both+(13*(6*L+1)+21); omega
    · intro z hz h₁ h₂ h₃; exact (keep z hz h₁ h₂ h₃).trans (fr z hz)

end VWZClique.IntegerRAM.NativeArena.Choice

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

noncomputable def codeAt (K L : ℕ) (i : Fin (Fintype.card (windowExpansion K L).Index)) :
    Fin (5^L) := ((enumerate L (width K L)) (indexOrder K L i)).val

theorem rank_codeAt (K L : ℕ) (i : Fin (Fintype.card (windowExpansion K L).Index)) :
    rank (maskKey L (width K L)) (codeAt K L i).val=i.val := by
  let s := allowed L (width K L)
  let e : (windowExpansion K L).Index ≃ ↥s := enumerate L (width K L)
  have card : Fintype.card (windowExpansion K L).Index=s.card := by simpa only [Fintype.card_coe] using Fintype.card_congr e
  have rankN := (mask_count L (width K L)).trans (show Fintype.card (Terms L (width K L))=s.card by
    simpa only [Fintype.card_coe] using Fintype.card_congr (enumerate L (width K L)))
  have r := ranked_order (maskKey L (width K L)) s (fun z h => (maskKey_iff z).mpr h) rankN ((finCongr card) i)
  change rank (maskKey L (width K L)) (e (e.symm (s.orderIsoOfFin rfl ((finCongr card) i)))).val.val=i.val
  rw [e.apply_symm_apply]
  exact r

theorem codeAt_spec (K L : ℕ) (i : Fin (Fintype.card (windowExpansion K L).Index)) :
    let z := codeAt K L i
    z∈allowed L (width K L) ∧
      integerMask (finFunctionFinEquiv.symm z)=(windowExpansion K L).masks (indexOrder K L i) ∧
      integerWeight (windowCoeff K L) (finFunctionFinEquiv.symm z)=(windowExpansion K L).coefficients (indexOrder K L i) := by
  let e := enumerate L (width K L)
  let a := e (indexOrder K L i)
  have ha := a.property
  have small := (Finset.mem_filter.mp ha).2
  have eq : e.symm a=indexOrder K L i := e.symm_apply_apply _
  refine ⟨ha,?_,?_⟩
  · exact ((unpack_mask (finFunctionFinEquiv.symm a.val) small).symm).trans (congrArg termMask eq)
  · exact ((unpack_weight (finFunctionFinEquiv.symm a.val) small (windowCoeff K L)).symm).trans
      (congrArg (termCoeff (windowCoeff K L)) eq)

end VWZClique.IntegerRAM.NativeArena.Choice

end

/- NativeArenaChoiceGraph -/
section

namespace VWZClique.IntegerRAM.NativeArena.Choice
open RankSwap RankSwap.MaskEnumeration UniformFolds NativeTraversal NativeFrame MaskScan Structured

private def extend {n : ℕ} (f : Fin n→ℤ) (i : ℕ) := if h : i < n then f ⟨i,h⟩ else 0

/-- A missing mask has the zero word, which unpacks to the all-free mask. -/
theorem zeroMask (L : ℕ) : integerMask (finFunctionFinEquiv.symm (0 : Fin (5^L)) : Digits L)=(fun _ => none) := by
  funext i
  have hz : ((finFunctionFinEquiv.symm (0 : Fin (5^L)) : Digits L) i)=0 := by
    apply Fin.ext; change 0/5^i.val%5=0; simp
  simp [integerMask,hz]

theorem count_le (K L : ℕ) : Fintype.card (windowExpansion K L).Index≤5^L :=
  calc
    _ = Fintype.card (Terms L (width K L)) := Fintype.card_congr (Equiv.refl _ :
      (windowExpansion K L).Index ≃ Terms L (width K L))
    _ = _ := (mask_count L (width K L)).symm
    _ ≤ _ := rank_le (maskKey L (width K L)) (5^L)

theorem cursor_bits (K L : ℕ) :
    (Fintype.card (windowExpansion K L).Index:ℤ)≤(2:ℤ)^(6*L+1) := by
  have a := (count_le K L).trans (scan_range_bound L)
  have b : (2^L)^3≤2^(6*L+1) := by rw [←pow_mul]; apply Nat.pow_le_pow_right (by decide); omega
  exact_mod_cast a.trans b


theorem bitLength_le (L : ℕ) : 6*L+1≤7*(2^L)^9 := by
  have h := L.lt_two_pow_self
  have q : 1≤2^L := Nat.one_le_pow _ _ (by decide)
  have z : 2^L≤(2^L)^9 := by simpa only [pow_one] using Nat.pow_le_pow_right q (by decide : 1≤9)
  omega

theorem numbered_runs {d W L base M : ℕ} (H : SimpleGraph V) (b : Branch) (hd : d≤36)
    (mem : Memory) (hN : mem 0=(2^L:ℕ)) (hb : mem (reg d .weights)=base)
    (i : Fin (visits (Fintype.card (qOf H L).Index) b)) (hi : mem (reg d .index)=i.val)
    (len : mem (reg d .leftLength)=Fintype.card (qOf H L).Index) (depth : mem 320=L)
    (data : ∀ z : Fin (5^L), z∈allowed L (width (windowAt (Nat.card H.edgeSet)) L) →
      let K := windowAt (Nat.card H.edgeSet)
      let j := rank (maskKey L (width K L)) z.val
      mem (slot base (2^L) 3 j:ℕ)=z.val ∧
      mem (slot base (2^L) 4 j:ℕ)=integerWeight (windowCoeff K L) (finFunctionFinEquiv.symm z))
    (fit : ∀ j < Fintype.card (qOf H L).Index, Fits W (slot base (2^L) 3 j:ℤ) ∧ Fits W (slot base (2^L) 4 j:ℤ))
    (lengthFits : 6*L+1 ≤ M) (room : Graph.Division.Room W M)
    (cap : (2:ℤ)^(6*L+1)*Fintype.card (qOf H L).Index≤(M:ℤ)) :
    ∃ t ≤ straightCost d b+(13*(6*L+1)+21), ∃ out, Runs W (choose d b) mem t out ∧
      (∃ ca cb : Fin (5^L), out firstCode=ca.val ∧ out secondCode=cb.val ∧
        integerMask (finFunctionFinEquiv.symm ca)=(numbered H b i).a.getD (fun _ => none) ∧
        integerMask (finFunctionFinEquiv.symm cb)=(numbered H b i).b.getD (fun _ => none)) ∧
      out (reg d .coefficient)=(numbered H b i).coeff ∧
      ∀ z : ℤ, 0 ≤ z → z≠firstCode → z≠secondCode → z≠reg d .coefficient → out z=mem z := by
  let K := windowAt (Nat.card H.edgeSet)
  let cnt := Fintype.card (windowExpansion K L).Index
  let codes (p : Fin cnt) : ℤ := (codeAt K L p).val
  let coefs (p : Fin cnt) := (windowExpansion K L).coefficients (indexOrder K L p)
  have eval (f : Fin cnt → ℤ) (v : Fin cnt) : extend f v.val=f v := by simp only [extend,dif_pos v.isLt]
  have rows (p : ℕ) (hp : p < cnt) :
      mem (slot base (2^L) 3 p:ℕ)=extend codes p ∧ mem (slot base (2^L) 4 p:ℕ)=extend coefs p := by
    let v : Fin cnt := ⟨p,hp⟩
    obtain ⟨allowed',_,weight⟩ := codeAt_spec K L v
    obtain ⟨cc,vv⟩ := data (codeAt K L v) allowed'
    change mem (slot base (2^L) 3 (rank (maskKey L (width K L)) (codeAt K L v).val):ℕ)=_ at cc
    change mem (slot base (2^L) 4 (rank (maskKey L (width K L)) (codeAt K L v).val):ℕ)=_ at vv
    rw [rank_codeAt] at cc vv
    simp only [extend,dif_pos hp]
    exact ⟨cc,vv.trans weight⟩
  obtain ⟨t,ht,out,run,left',right',coef,fr⟩ := choose_runs b hd mem hN hb hi len depth
    (extend codes) (extend coefs) rows fit i.isLt lengthFits room (cursor_bits K L) cap
  refine ⟨t,ht,out,run,?_,?_,fr⟩
  · cases b with
    | left =>
      exact ⟨codeAt K L i,0,left'.trans (eval codes i),right',
        (codeAt_spec K L i).2.1,zeroMask L⟩
    | right =>
      exact ⟨0,codeAt K L i,left',right'.trans (eval codes i),
        zeroMask L,(codeAt_spec K L i).2.1⟩
    | both =>
      let p : Fin cnt × Fin cnt := finProdFinEquiv.symm i
      exact ⟨codeAt K L p.1,codeAt K L p.2,left'.trans (eval codes p.1),right'.trans (eval codes p.2),
        (codeAt_spec K L p.1).2.1,(codeAt_spec K L p.2).2.1⟩
  · cases b with
    | left | right => exact coef.trans (eval coefs i)
    | both =>
      let p : Fin cnt × Fin cnt := finProdFinEquiv.symm i
      change out (reg d .coefficient)= -(extend coefs p.1.val*extend coefs p.2.val) at coef
      change out (reg d .coefficient)= -(coefs p.1*coefs p.2)
      exact coef.trans (by rw [eval,eval])

end VWZClique.IntegerRAM.NativeArena.Choice

end

/- NativeArenaDispatch -/
section

namespace VWZClique.IntegerRAM.NativeArena
open Structured UniformFolds NativeTraversal NativeFrame FoldProof

noncomputable def pushProgram (d : ℕ) (H : SimpleGraph V) (π : Equiv.Perm V) (br : Branch) :=
  Command.seq (Choice.choose d br) (materialize d H π br)

noncomputable def pushTicks (L d : ℕ) (H : SimpleGraph V) (π : Equiv.Perm V) (br : Branch) :=
  Choice.straightCost d br + (13*(6*L+1)+21) + pushMaterialCost L d H π br

private theorem isSelected {L : ℕ} (H : SimpleGraph V) (br : Branch) (i : Fin (visits (number L H) br)) :
    (numbered H br i).a.isSome=first br ∧ (numbered H br i).b.isSome=second br := by cases br <;> exact ⟨rfl,rfl⟩

private theorem same_slot (base N j i : ℕ) : Choice.slot base N j i = MaskScan.Arena.slot base N j+i := by
  dsimp [Choice.slot,metaBase,tableWords,MaskScan.Arena.slot,MaskScan.Arena.origin,MaskScan.Arena.span]
  ring

/-- The complete physical push kernel, including rank selection, signed coefficient, all map
construction, and installing a full new frame for the recursive call. -/
theorem push_transition {L W M d base₀ output : ℕ} (hbase : 512 ≤ base₀) (hd : d<36) (hL : 0 < L)
    (H : SimpleGraph V) (π : Equiv.Perm V) (br : Branch) (i : Fin (visits (number L H) br))
    (w : WeightKey (2^L)→ℚ) (z : ℤ) (q : List (NativeTraversal.Slot L))
    (room : Graph.Division.Room W M) (lenFits : 6*L+1 ≤ M) (cap : (2:ℤ)^(6*L+1)*number L H≤(M:ℤ))
    (rowCap : 5*2^(3*L+1) ≤ M)
    (space : child (atDepth base₀ (2^L) d) (2^L)+Graph.Table.offset (2^L) 90 ≤ M) :
    let lay := layout L base₀ output hbase
    Transition W (Repr lay) (pushProgram d H π br) (.cursor d H π br w i.val z::q)
      (.input (d+1) (childWeights H π (numbered H br i) w):: .cursor d H π br w i.val z::q)
      (pushTicks L d H π br) := by
  let N := 2^L
  let lay := layout L base₀ output hbase
  let base := atDepth base₀ N d
  let dest := child base N
  have start : 512 ≤ base := lay.large d
  have atMap : base ≤ maps base N := by dsimp [maps,metaBase]; omega
  have mEnd : maps base N ≤ dest := by dsimp [dest,child,rows]; omega
  have numBound := number_bound L H
  have pp := reg_positive d .coefficient
  have cp := reg_below hd.le .coefficient
  have addCost := reg_below (by omega : d+1≤36) .weights
  have fits (j : ℕ) (hj : j < number L H) :
      Fits W (Choice.slot base N 3 j:ℤ) ∧ Fits W (Choice.slot base N 4 j:ℤ) := by
    have hm : j < N^3 := hj.trans_le numBound
    change child base N+Graph.Table.offset N 90 ≤ M at space
    dsimp [Choice.slot]
    constructor <;> apply room.fits <;> try exact (neg_nonpos.mpr (by positivity)).trans (by positivity)
    all_goals exact_mod_cast (by dsimp [dest,child,rows,maps] at space; omega)
  change Transition W (Repr lay) _ _ _ _
  intro m pre
  obtain ⟨glob,⟨old,prep,lens,index,val⟩,rest⟩ := pre
  have prepared : MaskScan.Arena.Prepared L (windowAt (Nat.card H.edgeSet)) base m := prep
  obtain ⟨s,hs,u,select,⟨ca,cb,ra,rb,ha,hb⟩,cf,selFrame⟩ :=
    Choice.numbered_runs (base:=base) H br hd.le m glob.dim old.1 i index (lens .left) glob.length
      (fun zz hz => by simpa only [same_slot] using prepared.mask zz hz) fits lenFits room cap
  have uSame (j : ℕ) (a : j≠322) (b : j≠323) (c : (j:ℤ)≠reg d .coefficient) : u j=m j :=
    selFrame _ (by positivity) (by change (j:ℤ)≠322; exact_mod_cast a) (by change (j:ℤ)≠323; exact_mod_cast b) c
  have wp : u (reg d .weights)=m (reg d .weights) :=
    selFrame _ (reg_positive ..).le (by have := reg_below hd.le .weights; change _ ≠ 322; omega)
      (by have := reg_below hd.le .weights; change _ ≠ 323; omega) (different d (by decide))
  have ctrl : MapSchedule.Controls d base L ca cb u :=
    ⟨(uSame 0 (by decide) (by decide) (ne_of_lt pp)).trans glob.dim,
      (uSame 320 (by decide) (by decide) (by omega)).trans glob.length,ra,rb,wp.trans old.1⟩
  have src (k : WeightKey N) : (u ((base+Graph.Table.wordIndex k:ℕ):ℤ):ℚ)=w k := by
    rw [uSame _ (by omega) (by omega) (by omega)]
    exact old.2 k
  have ab := isSelected H br i
  obtain ⟨t,ht,o,build,ptr,data,unchanged⟩ := materialize_runs π br hd hL start room rowCap space ha hb ab.1 ab.2 w u ctrl src
  have upper (j : ℕ) (bounds : j<400 ∨ 512 ≤ j) (lo : j < maps base N)
      (ne : (j:ℤ)≠reg (d+1) .weights) : o j=u j := unchanged _ ne bounds (Or.inl lo)
  have loSame (v : ℤ) (h₀ : 0 ≤ v) (lt : v<400) (ne₁ : v≠322) (ne₂ : v≠323)
      (ne₃ : v≠reg d .coefficient) (ne₄ : v≠reg (d+1) .weights) : o v=m v := by
    obtain ⟨j,rfl⟩ := Int.eq_ofNat_of_zero_le h₀
    exact (upper _ (Or.inl (by omega)) (by omega) ne₄).trans (uSame _ (by omega) (by omega) ne₃)
  have dataSame (j : ℕ) (lo : 512 ≤ j) (hi : j < maps base N) : o j=m j :=
    (upper _ (Or.inr lo) hi (by omega)).trans (uSame _ (by omega) (by omega) (by omega))
  refine ⟨s+t,Nat.add_le_add hs ht,o,.seq select build,?_⟩
  apply push_repr lay (layoutCapacity L base₀ output hbase) i z q (m:=m) (o:=o) ⟨glob,⟨old,prep,lens,index,val⟩,rest⟩
  · apply glob.transfer
    · exact loSame 0 (by decide) (by decide) (by decide) (by decide) (ne_of_lt pp) (ne_of_lt (reg_positive ..))
    · exact loSame 320 (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
    · exact loSame 321 (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  · intro j lo hi; exact dataSame j lo (hi.trans_le atMap)
  · intro j hj f
    have bounded := reg_below (show j≤36 by omega) f
    have h1 := separate hj f .coefficient
    have h2 := separate (show j < d+1 by omega) f .weights
    exact loSame _ (reg_positive ..).le (by omega) (by omega) (by omega) h1.ne h2.ne
  · intro f ne
    have h1 := reg_below hd.le f
    exact loSame _ (reg_positive ..).le (by omega) (by omega) (by omega) (different _ ne)
      (separate (Nat.lt_succ_self _) _ _).ne
  · intro k
    have hi : Graph.Table.wordIndex k < tableWords N := NativeLeaf.index_lt k
    change o ((base+Graph.Table.wordIndex k:ℕ):ℤ)=m _
    exact dataSame _ (start.trans (Nat.le_add_right ..)) (by dsimp [maps,metaBase]; omega)
  · apply prepared.congr
    intro j lo hi
    rw [←maps_eq] at hi; exact dataSame j (start.trans lo) hi
  · exact ⟨ptr,data⟩
  · obtain ⟨j,hj⟩ := Int.eq_ofNat_of_zero_le pp.le
    rw [hj,upper j (Or.inl (by omega)) (by omega) (by rw [←hj]; exact (separate (Nat.lt_succ_self _) _ _).ne),←hj,cf]

end VWZClique.IntegerRAM.NativeArena

end

/- NativePushRate -/
section

namespace VWZClique.IntegerRAM.NativeArena
open NativeFrame FoldWeight UniformFolds

theorem table_cost_quadratic (d : ℕ) (H : SimpleGraph V) (π : Equiv.Perm V) (br : Branch) {N : ℕ} (hn : 0<N) :
    tableCost d H π br N ≤ tableCost d H π br 1 * N^2 := by
  let A := setupCost d 112 + 2*((childExp d).steps+2)+90*8
  let B := 90*(bound H π pointerLayout br+12)
  have form (n : ℕ) : tableCost d H π br n=A+B*n^2 := by dsimp [tableCost,A,B]; ring
  rw [form,form,one_pow,Nat.mul_one,Nat.add_mul]
  exact Nat.add_le_add_right (Nat.le_mul_of_pos_right A (by positivity)) _

private def selectConst (d : ℕ) (b : Branch) := Choice.straightCost d b + 112

private noncomputable def localCoefficient (d : ℕ) (H : SimpleGraph V) (π : Equiv.Perm V) (b : Branch) :=
  selectConst d b+MapSchedule.overhead+tableCost d H π b 1

theorem push_ticks_quadratic (L d : ℕ) (hd : d≤36) (H : SimpleGraph V) (π : Equiv.Perm V) (b : Branch) :
    pushTicks L d H π b≤localCoefficient d H π b*(2^L)^2 := by
  let Q := (2^L)^2
  have q0 : 1≤Q := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by decide))
  have ll : L≤Q := (Nat.lt_two_pow_self (n:=L)).le.trans (by simpa only [pow_one] using Nat.pow_le_pow_right (Nat.pow_pos (by decide : 0 < 2) (n:=L)) (by decide : 1 ≤ 2))
  have base : Choice.straightCost d b ≤ Choice.straightCost d b*Q := Nat.le_mul_of_pos_right _ q0
  have fixed : Choice.straightCost d b+(13*(6*L+1)+21) ≤ selectConst d b*Q := by
    rw [selectConst,Nat.add_mul]; omega
  have dyn := Nat.add_le_add (MapSchedule.cost_le hd L) (table_cost_quadratic d H π b (N:=2^L) (by positivity))
  have combined := Nat.add_le_add fixed dyn
  dsimp only [pushTicks,pushMaterialCost,localCoefficient]
  rw [Nat.add_mul,Nat.add_mul]
  exact combined.trans_eq (by dsimp [Q]; omega)

theorem uniform_push_rate : ∃ B : ℕ, ∀ L d : ℕ, d≤36 → ∀ (H : SimpleGraph V) (π : Equiv.Perm V) (b : Branch),
    pushTicks L d H π b+6 ≤ B*(2^L)^2 := by
  let f (x : Fin 37 × SimpleGraph V × Equiv.Perm V) :=
    localCoefficient x.1 x.2.1 x.2.2 .left+localCoefficient x.1 x.2.1 x.2.2 .right+
      localCoefficient x.1 x.2.1 x.2.2 .both
  obtain ⟨C,lim⟩ := Finite.exists_le f
  refine ⟨C+6,?_⟩
  intro L d hd H π b
  have all := lim (⟨d,by omega⟩,H,π)
  have hb : localCoefficient d H π b≤C := by dsimp [f] at all; cases b <;> omega
  have h := (push_ticks_quadratic L d hd H π b).trans (Nat.mul_le_mul_right _ hb)
  rw [Nat.add_mul]
  exact Nat.add_le_add h (Nat.le_mul_of_pos_right _ (by positivity))

end VWZClique.IntegerRAM.NativeArena

end

/- NativeEndgame -/
section

namespace VWZClique.IntegerRAM.NativeArena
open Structured UniformFolds NativeTraversal NativeFrame BlockReduction
open OAI.MatrixMultiplication.Arithmetic




end VWZClique.IntegerRAM.NativeArena

end

open VWZClique VWZClique.UniformFolds VWZClique.NativeTraversal VWZClique.IntegerRAM VWZClique.IntegerRAM.NativeFrame VWZClique.IntegerRAM.NativeArena VWZClique.IntegerRAM.Structured VWZClique.BlockReduction

theorem solution
    {mm : ℕ → ℕ} {T : ℕ} (pk : VWZClique.IntegerRAM.NativeArena.ProjectionKernel mm T) :
    Nonempty (VWZClique.IntegerRAM.NativeFrame.Implemented mm T 1 1) := by
  obtain ⟨bnd,costs⟩ := uniform_push_rate
  let S := leafCoefficient+bnd+pk.timeCoefficient+2
  let P (L : ℕ) (H : SimpleGraph V) :=
    pk.timeCoefficient*(L+1)^pk.logPower*(NativeTraversal.projected mm T 1 L H+1)
  let pushTime (L : ℕ) (_ : SimpleGraph V) := bnd*(2^L)^2
  refine ⟨{
    projection := pk.command
    push := pushProgram
    projectTime := P
    pushTime := pushTime
    factor := S+6
    logPower := pk.logPower
    positive := by decide
    sparseTime := ?_
    projectedTime := ?_
    pushBound := ?_
    kernels := ?_ }⟩
  · intro L H
    simp only [fees,Nat.one_mul]
    apply Nat.mul_le_mul_right
    have logs : 0<(L+1)^pk.logPower := by positivity
    exact (by dsimp [S]; omega : leafCoefficient≤S+6).trans (Nat.le_mul_of_pos_right _ logs)
  · intro L H
    let v := (L+1)^pk.logPower
    let a := NativeTraversal.projected mm T 1 L H
    have pos : 1 ≤ v := Nat.one_le_pow _ _ (by omega)
    have sc : pk.timeCoefficient ≤ S+6 := by dsimp [S]; omega
    have h := Nat.mul_le_mul_right (a+1) (Nat.mul_le_mul_right v sc)
    have one : 1≤(S+6)*v := Nat.one_le_of_lt (Nat.mul_pos (by omega) pos)
    change pk.timeCoefficient*v*(a+1)+2≤(S+6)*v*(a+3)
    rw [show a+3=a+1+2 by omega,Nat.mul_add ((S+6)*v) (a+1) 2]
    omega
  · intro L H
    let N := 2^L
    have n : 1 ≤ N := Nat.one_le_pow _ _ (by decide)
    have a : N^2≤N^5 := Nat.pow_le_pow_right n (by decide)
    have one : 1≤N^5 := Nat.one_le_pow _ _ n
    have logs : 1 ≤ (L+1)^pk.logPower := Nat.one_le_pow _ _ (by omega)
    have lim : bnd+6≤(S+6)*(L+1)^pk.logPower :=
      (by dsimp [S]; omega : bnd+6≤S+6).trans (Nat.le_mul_of_pos_right _ logs)
    simp only [pushTime,Nat.one_mul]
    calc
      bnd*N^2+6 ≤ (bnd+6)*N^5 := by
        rw [Nat.add_mul]
        exact Nat.add_le_add (Nat.mul_le_mul_left _ a) (Nat.le_mul_of_pos_right _ one)
      _ ≤ _ := Nat.mul_le_mul_right _ lim
  · intro k hk
    let c := pk.workspaceCoefficient
    let p := pk.workspacePower
    obtain ⟨b,hb,wide,forAll⟩ := admissible_width k c p
    refine ⟨b,hb,wide,?_⟩
    intro n hn
    let L := graphLength n k
    let N := 2^L
    let M := allowance c p N
    let W := b*(n.log2+1)
    let root := DyadicCell.target n (n^((k+8)/9))
    let layout := forGraph n k hn
    have r : Graph.Division.Room W M := forAll n hn
    have room {a : ℕ} (h : a≤M) : Graph.Division.Room W a := lt_of_le_of_lt (by exact_mod_cast h) r
    have bound (d : ℕ) (hd : d≤36) := uniform_space hn hk c p d hd
    have hL : 0<L := (graph_index hn hk).1
    have start : 512≤root := DyadicCell.header_floor hn _
    refine ⟨⟨?_,?_⟩,?_,room (bound 0 (by decide)).2.2.2.2.2⟩
    · intro d H π w stack deep bin
      exact pk.run start hL H π w stack deep bin (room (bound d (by omega)).1)
    · intro d H π br i w z stack deep bin
      have vals := bound d deep.le
      have step := push_transition (W:=W) (output:=layout.outputAddress) start deep hL H π br i w z stack r vals.2.2.1
        (by have hi := vals.2.2.2.2.1
            have card := number_bound L H
            exact_mod_cast (Nat.mul_le_mul_left (2^(6*L+1)) card).trans hi)
        vals.2.2.2.1 vals.2.1
      intro input hs
      obtain ⟨f,hf,out,run,done⟩ := step input hs
      refine ⟨f,?_,out,run,done⟩
      have extra := costs L d deep.le H π br
      change f ≤ bnd*(2^L)^2; exact hf.trans ((Nat.le_add_right _ 6).trans extra)
    · intro d hd
      have bnd := (bound d hd).2.1
      apply room
      have le : layout.base d+9*N+81*(N*N)≤child (layout.base d) N := by
        apply layoutCapacity
      exact le.trans ((Nat.le_add_right _ _).trans bnd)

