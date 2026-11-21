-- Prove2me | solution 1 for VWZClique.NativeTraversal.wordRam_of_realizes
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T14:08:20.252119+00:00
-- url     : https://prove2.me/submissions/0cff449b-cd2d-4160-a14c-c7f488f92b87

import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_VWZClique_Contraction
import Definitions.Def_VWZClique_Count
import Definitions.Def_VWZClique_FoldedSum
import Definitions.Def_VWZClique_NativeCliqueCompiler
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

/- NativePolylog -/
section
namespace VWZClique.NativeTraversal
open Filter Asymptotics

/-- Any fixed power of the word length fits into any positive fraction of
the exponent saving, uniformly for every dyadic dimension, including L=0. -/
theorem absorb_word_length (p : ℕ) (s : ℝ) (hs : 0<s) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, ((L+1:ℕ):ℝ)^p ≤ C*((2:ℝ)^L)^s := by
  let r : ℝ := 2^s
  have hr : 1<r := Real.one_lt_rpow (by norm_num) hs
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp
    ((isLittleO_pow_const_const_pow_of_one_lt (R:=ℝ) p hr).bound (by norm_num : (0:ℝ)<1))
  let C := ((N+1:ℕ):ℝ)^p+r
  have hr' : 0<r := by linarith
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro L
  have eqr : ((2:ℝ)^L)^s = r^L := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul (by norm_num),Real.rpow_natCast]
  rw [eqr]
  by_cases hl : N ≤ L+1
  · have atL := hN (L+1) hl
    change ‖((L+1:ℕ):ℝ)^p‖ ≤ 1*‖r^(L+1)‖ at atL
    rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity),one_mul,pow_succ,mul_comm] at atL
    exact atL.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [show 0 ≤ ((N+1:ℕ):ℝ)^p by positivity]) (by positivity))
  · have hb : ((L+1:ℕ):ℝ)^p ≤ ((N+1:ℕ):ℝ)^p := by
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast (by omega : L+1≤N+1)
    exact (hb.trans (by dsimp [C]; linarith)).trans (le_mul_of_one_le_right hC.le (one_le_pow₀ hr.le))

end VWZClique.NativeTraversal
end

/- CliqueVM -/
section
/-! Simulation of bounded integer arithmetic, indirect addressing and branches on
    the fixed-width instruction interpreter used for clique counting. -/

namespace VWZClique.IntegerRAM
open TrulySubcubicAPSP

instance (W : ℕ) (x : ℤ) : Decidable (Fits W x) := inferInstanceAs (Decidable (_ ∧ _))

def encode (W : ℕ) (m : Memory) : ℤ → BitVec W := fun a => BitVec.ofInt W (m a)

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

/-- Convert an exact checked run writing one integer after its input into the
    mission's word-RAM predicate. -/
theorem runsWithin {P : List Instr} {W t : ℕ} (hW : 0 < W) {ws : List ℤ} {m : Memory} {z : ℤ}
    (h : checked P W t 0 (input ws) = some (true,m))
    (hout : m (ws.length : ℤ) = z) (hfit : Fits W z) :
    MonDepMW.RunsWithin P W t ws (fun out => out 0 = z) := by
  refine ⟨encode W m, ?_, ?_⟩
  · rw [← encode_input]
    exact simulate hW h
  · simp only [Nat.add_zero, encode, hout]
    exact decode_fits hW hfit

end VWZClique.IntegerRAM
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

/- CliqueReduction -/
section
/-! Exact reduction from unordered cliques to a single weighted nine-vertex instance.
    A fixed vertex fills unused slots, and order constraints choose one increasing
    enumeration of each clique. The extra slots allow all clique sizes. -/

namespace VWZClique
namespace BlockReduction

open Finset
open scoped BigOperators
noncomputable section
open Classical

/-- An increasing enumeration of a clique. -/
def Ordered {n k : ℕ} (G : SimpleGraph (Fin n)) (f : Fin k → Fin n) : Prop :=
  ∀ i j, i < j → f i < f j ∧ G.Adj (f i) (f j)

/-- A clique has exactly one increasing enumeration. -/
theorem card_ordered {n k : ℕ} (G : SimpleGraph (Fin n)) :
    (univ.filter fun f : Fin k → Fin n => Ordered G f).card = count G k := by
  classical
  unfold count
  apply Finset.card_bij (fun f _ => univ.image f)
  · intro f hf
    have hg : Ordered G f := (mem_filter.mp hf).2
    have hmono : StrictMono f := fun i j h => (hg i j h).1
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, ?_⟩, ?_⟩
    · simpa using card_image_of_injective univ hmono.injective
    · intro u hu v hv huv
      obtain ⟨i, _, rfl⟩ := mem_image.mp hu
      obtain ⟨j, _, rfl⟩ := mem_image.mp hv
      rcases lt_trichotomy i j with hij | hij | hij
      · exact (hg i j hij).2
      · exact (huv (congrArg f hij)).elim
      · exact (hg j i hij).2.symm
  · intro f hf g hg hfg
    have hm : StrictMono f := fun i j h => ((mem_filter.mp hf).2 i j h).1
    have hn : StrictMono g := fun i j h => ((mem_filter.mp hg).2 i j h).1
    have hcard : (univ.image f).card = k := by
      simpa using card_image_of_injective univ hm.injective
    apply (orderEmbOfFin_unique hcard (fun x => mem_image.mpr ⟨x, mem_univ _, rfl⟩) hm).trans
    symm
    apply orderEmbOfFin_unique hcard _ hn
    intro x
    rw [hfg]
    exact mem_image.mpr ⟨x, mem_univ _, rfl⟩
  · intro s hs
    obtain ⟨hsize, hclique⟩ := mem_filter.mp hs
    have hcard := (mem_powersetCard.mp hsize).2
    let f := s.orderEmbOfFin hcard
    refine ⟨f, mem_filter.mpr ⟨mem_univ _, ?_⟩, s.image_orderEmbOfFin_univ hcard⟩
    intro i j hij
    have hlt := f.strictMono hij
    exact ⟨hlt, hclique _ (s.orderEmbOfFin_mem hcard _) _ (s.orderEmbOfFin_mem hcard _) hlt.ne⟩

/-- Read the assignment at a padded slot. -/
def readSlot {n t : ℕ} (a : V → Fin (n^t)) (z : Fin (9*t)) : Fin n :=
  let ij := finProdFinEquiv.symm z
  digit (a ij.1) ij.2

@[simp]
theorem readSlot_slot {n t : ℕ} (a : V → Fin (n^t)) (i : V) (p : Fin t) :
    readSlot a (slot i p) = digit (a i) p := by simp [readSlot, slot]

/-- Assemble the nine block labels from a tuple, filling inactive slots by `pad`. -/
def pack {n k t : ℕ} (pad : Fin n) (f : Fin k → Fin n) : V → Fin (n^t) :=
  fun i => finFunctionFinEquiv fun p =>
    if h : (slot i p).val < k then f ⟨(slot i p).val, h⟩ else pad

@[simp]
theorem readSlot_pack {n k t : ℕ} (pad : Fin n) (f : Fin k → Fin n) (z : Fin (9*t)) :
    readSlot (pack (t := t) pad f) z = if h : z.val < k then f ⟨z.val, h⟩ else pad := by
  obtain ⟨⟨i,p⟩, rfl⟩ := finProdFinEquiv.surjective z
  change readSlot _ (slot i p) = _
  rw [readSlot_slot]
  simp [digit, pack, slot]

/-- Read the first `k` slots, discarding padding. -/
def unpack {n k t : ℕ} (h : k ≤ 9*t) (a : V → Fin (n^t)) : Fin k → Fin n :=
  fun z => readSlot a (Fin.castLE h z)

@[simp]
theorem unpack_pack {n k t : ℕ} (h : k ≤ 9*t) (pad : Fin n) (f : Fin k → Fin n) :
    unpack h (pack pad f) = f := by
  funext z
  simp [unpack, z.isLt]

theorem compatible_comm {n t k : ℕ} {G : SimpleGraph (Fin n)}
    {r s : Fin (9*t)} {u v : Fin n} :
    compatible G k r s u v ↔ compatible G k s r v u := by
  unfold compatible
  constructor <;> intro h h₁ h₂ <;> exact (h h₂ h₁).symm

def valid {n t : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (pad : Fin n)
    (a : V → Fin (n^t)) : Prop :=
  (∀ i, unaryOK G k pad i (a i)) ∧
  ∀ i j, i < j → edgeOK G k i j (a i) (a j)

private theorem valid_iff_slots {n k t : ℕ} {G : SimpleGraph (Fin n)} {pad : Fin n}
    {a : V → Fin (n^t)} :
    valid G k pad a ↔
      (∀ r, k ≤ r.val → readSlot a r = pad) ∧
      ∀ r s, compatible G k r s (readSlot a r) (readSlot a s) := by
  constructor
  · rintro ⟨hu, he⟩
    constructor
    · intro r
      obtain ⟨⟨i,p⟩, rfl⟩ := finProdFinEquiv.surjective r
      change k ≤ (slot i p).val → readSlot a (slot i p) = pad
      simpa only [readSlot_slot] using (hu i).1 p
    · intro r s
      obtain ⟨⟨i,p⟩, rfl⟩ := finProdFinEquiv.surjective r
      obtain ⟨⟨j,q⟩, rfl⟩ := finProdFinEquiv.surjective s
      change compatible _ _ (slot i p) (slot j q) (readSlot a (slot i p)) (readSlot a (slot j q))
      rw [readSlot_slot, readSlot_slot]
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact he i j hij p q
      · exact (hu i).2 p q
      · exact compatible_comm.mpr (he j i hji q p)
  · rintro ⟨hp, hc⟩
    constructor
    · intro i
      constructor
      · intro p
        simpa only [readSlot_slot] using hp (slot i p)
      · intro p q
        simpa only [readSlot_slot] using hc (slot i p) (slot i q)
    · intro i j _ p q
      simpa only [readSlot_slot] using hc (slot i p) (slot j q)

theorem pack_valid {n k t : ℕ} {G : SimpleGraph (Fin n)} {pad : Fin n}
    {f : Fin k → Fin n} (hf : Ordered G f) : valid (t := t) G k pad (pack pad f) := by
  apply valid_iff_slots.mpr
  constructor
  · intro r hr
    simp [readSlot_pack, Nat.not_lt.mpr hr]
  · intro r s hr hs
    rw [readSlot_pack, readSlot_pack, dif_pos hr, dif_pos hs]
    exact ⟨fun hij => hf _ _ hij, fun hji => hf _ _ hji⟩

theorem ordered_unpack {n k t : ℕ} {G : SimpleGraph (Fin n)} {pad : Fin n}
    {a : V → Fin (n^t)} (h : k ≤ 9*t) (ha : valid G k pad a) : Ordered G (unpack h a) := by
  intro i j hij
  exact (((valid_iff_slots.mp ha).2 (Fin.castLE h i) (Fin.castLE h j)) i.isLt j.isLt).1 hij

theorem pack_unpack {n k t : ℕ} {G : SimpleGraph (Fin n)} {pad : Fin n}
    {a : V → Fin (n^t)} (h : k ≤ 9*t) (ha : valid G k pad a) :
    pack pad (unpack h a) = a := by
  funext i
  apply finFunctionFinEquiv.symm.injective
  funext p
  change digit (pack pad (unpack h a) i) p = digit (a i) p
  rw [← readSlot_slot, ← readSlot_slot, readSlot_pack]
  split_ifs with hp
  · rfl
  · exact ((valid_iff_slots.mp ha).1 _ (Nat.le_of_not_gt hp)).symm

theorem weights_binary {F : Type*} [Field F] {n t : ℕ} (G : SimpleGraph (Fin n))
    (k : ℕ) (pad : Fin n) (key : WeightKey (n^t)) :
    weights (F := F) G k pad key = 0 ∨ weights (F := F) G k pad key = 1 := by
  rcases key with ⟨i,a⟩ | ⟨i,j,a,b⟩ <;> simp [weights] <;> exact Classical.em _ |>.symm

/-- The weighted sum on nine vertices is the number of unordered `k`-cliques.
    Any block width with at least `k` slots works. -/
theorem weighted_eq_count {F : Type*} [Field F] {n k t : ℕ} (G : SimpleGraph (Fin n))
    (pad : Fin n) (h : k ≤ 9*t) :
    weightedSum (⊤ : SimpleGraph V) (weights (F := F) (t := t) G k pad) =
    (count G k : F) := by
  classical
  have hn : (univ.filter fun f : Fin k → Fin n => Ordered G f).card =
      (univ.filter fun a : V → Fin (n^t) => valid G k pad a).card := by
    apply Finset.card_bij (fun f _ => pack pad f)
    · intro f hf
      exact mem_filter.mpr ⟨mem_univ _, pack_valid (mem_filter.mp hf).2⟩
    · intro f _ g _ hfg
      simpa using congrArg (unpack h) hfg
    · intro a ha
      obtain hv := (mem_filter.mp ha).2
      exact ⟨unpack h a, mem_filter.mpr ⟨mem_univ _, ordered_unpack h hv⟩, pack_unpack h hv⟩
  rw [← card_ordered G, hn]
  unfold weightedSum
  calc
    _ = ∑ a : V → Fin (n^t), (if valid G k pad a then (1:F) else 0) := by
      apply sum_congr rfl
      intro a _
      by_cases hu : ∀ i, unaryOK G k pad i (a i)
      · have hones : (∏ i : V, weights (F := F) G k pad (.inl (i,a i))) = 1 :=
          prod_eq_one fun i _ => by simp [weights, hu i]
        rw [hones, one_mul]
        by_cases he : ∀ i j, i < j → edgeOK G k i j (a i) (a j)
        · rw [if_pos (show valid G k pad a from ⟨hu,he⟩)]
          apply prod_eq_one
          intro i _
          apply prod_eq_one
          intro j _
          by_cases hij : i < j
          · simp [hij, SimpleGraph.top_adj, hij.ne, weights, he i j hij]
          · simp [hij]
        · rw [if_neg (show ¬ valid G k pad a from fun hh => he hh.2)]
          obtain ⟨i,hi⟩ := not_forall.mp he
          obtain ⟨j,hj⟩ := not_forall.mp hi
          have hij : i < j := by by_contra h'; exact hj (fun h => (h' h).elim)
          have hbad : ¬ edgeOK G k i j (a i) (a j) := fun h => hj (fun _ => h)
          apply prod_eq_zero (mem_univ i)
          apply prod_eq_zero (mem_univ j)
          simp [hij, SimpleGraph.top_adj, hij.ne, weights, hbad]
      · rw [if_neg (show ¬ valid G k pad a from fun hh => hu hh.1)]
        obtain ⟨i,hi⟩ := not_forall.mp hu
        apply mul_eq_zero_of_left
        apply prod_eq_zero (mem_univ i)
        simp [weights, hi]
    _ = _ := Finset.sum_boole _ _

/-- The minimum common width accommodates every clique size. -/
theorem weighted_eq_count_ceil {F : Type*} [Field F] {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (k : ℕ) :
    weightedSum (⊤ : SimpleGraph V)
      (weights (F := F) (t := (k+8)/9) G k ⟨0,hn⟩) = (count G k : F) :=
  weighted_eq_count G _ (by omega)

end
end BlockReduction
end VWZClique
end

/- CliqueExponent -/
section
/-! The exponent loss from filling the nine equal-width blocks is bounded
    uniformly in the matrix multiplication exponent for `ω ≤ 3`. -/

namespace VWZClique.BlockReduction
open Classical

/-- With a nine-vertex saving `α`, the rounding from `k/9` to its ceiling
    costs at most a constant in the exponent. The threshold depends only on `α`. -/
theorem grouped_exponent {α ω : ℝ} (hα : 0 < α) (hω : ω ≤ 3) (hscale : 0 ≤ 3*ω-α)
    {k : ℕ} (hk : ⌈144 / α⌉₊ ≤ k) :
    (((k+8)/9 : ℕ) : ℝ) * (3*ω-α) ≤ (ω-α/6)*(k:ℝ)/3 := by
  have hsize : 9 * ((k+8)/9) ≤ k+8 := Nat.mul_div_le _ _
  have hsize' : 9 * (((k+8)/9 : ℕ) : ℝ) ≤ (k:ℝ)+8 := by exact_mod_cast hsize
  have ht : 144 / α ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hcap := (div_le_iff₀ hα).mp ht
  have hround := mul_le_mul_of_nonneg_right hsize' hscale
  nlinarith

/-- Rescaling the domain `N = n^ceil(k/9)` respects the target final time bound. -/
theorem grouped_rpow {α ω : ℝ} (hα : 0 < α) (hω : ω ≤ 3) (hscale : 0 ≤ 3*ω-α)
    {k n : ℕ} (hk : ⌈144 / α⌉₊ ≤ k) (hn : 1 ≤ n) :
    ((n^((k+8)/9) : ℕ) : ℝ)^(3*ω-α) ≤ (n:ℝ)^((ω-α/6)*(k:ℝ)/3) := by
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (grouped_exponent hα hω hscale hk)

/-- Time bounds for the fixed RAM program are closed upwards in their exponent. -/
theorem countsWithin_mono {k : ℕ} {e f : ℝ} (hef : e ≤ f) (h : countsWithin k e) :
    countsWithin k f := by
  obtain ⟨p,b,C,hb,hC,hp⟩ := h
  refine ⟨p,b,C,hb,hC,?_⟩
  intro n G hn
  obtain ⟨t,ht,hrun⟩ := hp n G hn
  refine ⟨t,ht.trans (mul_le_mul_of_nonneg_left ?_ hC.le),hrun⟩
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) hef

end VWZClique.BlockReduction
end

/- LoopCompiler -/
section
open TrulySubcubicAPSP
namespace VWZClique.IntegerRAM.Structured

def Atom.instruction : Atom → Instr
  | .one d => .one d
  | .add d a b => .add d a b
  | .sub d a b => .sub d a b
  | .mul d a b => .mul d a b
  | .load d p => .load d p
  | .store p s => .store p s

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

/- NativeCutoff -/
section
namespace VWZClique.IntegerRAM.Cutoff
open Structured BlockReduction

theorem count_zero {n k : ℕ} (G : SimpleGraph (Fin n)) (small : n < k) : count G k = 0 := by
  classical
  have h : (Finset.univ.powersetCard k : Finset (Finset (Fin n))) = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by simpa)
  simp [count,h]

def inc : ℕ → Command
  | 0 => .skip
  | h+1 => .seq (inc h) (.atom (.add (-2) (-2) (-1)))

def built (m : Memory) (h : ℕ) : Memory := update (update m (-1) 1) (-2) h

theorem inc_runs (m : Memory) (W h : ℕ) :
    Runs W (inc h) (built m 0) h (built m h) := by
  induction h with
  | zero => exact .skip _
  | succ h ih =>
    have run := Runs.seq ih (Runs.atom (Step.add (W:=W) (built m h) (-2) (-2) (-1)))
    simp only [inc]
    convert run using 1
    funext i
    by_cases hi : i=(-2) <;> simp [built,update,hi,eq_comm] at *

def pre (h : ℕ) : Command :=
  .seq (.atom (.one (-1))) (.seq (.atom (.sub (-2) (-2) (-2)))
    (.seq (inc h) (.atom (.sub (-2) 0 (-2)))))

def tested (m : Memory) (h : ℕ) : Memory := update (built m h) (-2) (m 0-h)

theorem pre_runs (W h : ℕ) (m : Memory) : Runs W (pre h) m (1+(1+(h+1))) (tested m h) := by
  let m₁ := update m (-1) 1
  have b : Runs W (.atom (.sub (-2) (-2) (-2))) m₁ 1 (built m 0) := by
    simpa [built,m₁] using (Runs.atom (Step.sub (W:=W) m₁ (-2) (-2) (-2)))
  have c : Runs W (.atom (.sub (-2) 0 (-2))) (built m h) 1 (tested m h) := by
    simpa [built,tested,update] using (Runs.atom (Step.sub (W:=W) (built m h) (-2) 0 (-2)))
  exact .seq (.atom (.one ..)) (.seq b (.seq (inc_runs m W h) c))

def clear : Command := .seq (.atom (.sub (-1) (-1) (-1))) (.atom (.sub (-2) (-2) (-2)))

theorem clear_runs {m : Memory} (W h : ℕ) (h₁ : m (-1)=0) (h₂ : m (-2)=0) :
    Runs W clear (tested m h) 2 m := by
  let x := tested m h
  let y := update x (-1) (x (-1)-x (-1))
  have run : Runs W clear x 2 (update y (-2) (y (-2)-y (-2))) :=
    .seq (.atom (.sub ..)) (.atom (.sub ..))
  convert run using 1
  funext i
  by_cases hi : i=(-1)
  · subst i; simp [y,update,h₁]
  by_cases hj : i=(-2)
  · subst i; simp [update,h₂]
  simp [y,x,tested,built,update,hi,hj]

def command (h : ℕ) (large : Command) : Command :=
  .seq (pre h) (.whenNonnegative (-2) (.seq clear large))

/-- A fixed cutoff reserves the first words of a sufficiently large graph's adjacency matrix
after preprocessing. Smaller hosts have zero k-cliques and initially have zero in the output cell. -/
theorem countsWithin_of_large {k h b : ℕ} {e C : ℝ} (hk : h ≤ k) (he : 0≤e)
    (hb : k+3 ≤ b) (hC : 0<C) (large : Command)
    (alg : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 2≤n → h≤n →
      ∃ (T : ℕ) (out : Memory), (T:ℝ) ≤ C*(n:ℝ)^e ∧
        Runs (b*(n.log2+1)) large (input (MonDepMW.graphInput G)) T out ∧
        out ((MonDepMW.graphInput G).length:ℤ) = (count G k:ℤ)) :
    countsWithin k e := by
  refine ⟨program (command h large), b, C+(h+8), by omega, by positivity, ?_⟩
  intro n G hn
  let m := input (MonDepMW.graphInput G)
  let W := b*(n.log2+1)
  have hm : m 0=n := (Graph.graphAt_input G).1
  have hp : (1:ℝ)≤(n:ℝ)^e := Real.one_le_rpow (by exact_mod_cast (by omega : 1≤n)) he
  have room : Graph.Division.Room W (n^(k+1)) :=
    Graph.Division.room_pow (by omega) (by omega)
  have hn' : n ≤ n^(k+1) := by simpa using (Nat.pow_le_pow_right (by omega : 0<n) (by omega : 1≤k+1))
  have hh' : h ≤ n^(k+1) := by
    have l := Nat.lt_two_pow_self (n:=k+1)
    exact (by omega : h≤2^(k+1)).trans (Nat.pow_le_pow_left hn _)
  have htest : tested m h (-2) = (n:ℤ)-h := by simp [tested,update,hm]
  have fit : Fits W (tested m h (-2)) := by
    rw [htest]; apply room.fits <;> omega
  have preRun := pre_runs W h m
  have outFit : Fits W (count G k : ℤ) := by
    apply (Graph.Division.room_pow (n:=n) (k:=k) (b:=b) (by omega) (by omega)).fits
    · exact (neg_nonpos.mpr (by positivity)).trans (by positivity)
    · exact_mod_cast count_le_pow G k
  by_cases hl : h≤n
  · obtain ⟨T,out,ht,hr,hv⟩ := alg n G hn hl
    have clr := clear_runs (m:=m) W h (by simp [m,input]) (by simp [m,input])
    have run : Runs W (command h large) m ((1+(1+(h+1)))+(1+(2+T))) out :=
      .seq preRun (.guard_take fit (by rw [htest]; omega) (.seq clr hr))
    refine ⟨_,?_,IntegerRAM.runsWithin (Nat.mul_pos (by omega) (by omega)) (completes run) hv outFit⟩
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ (h:ℝ)+8 by positivity)]
  · have run : Runs W (command h large) m ((1+(1+(h+1)))+1) (tested m h) :=
      .seq preRun (.guard_skip fit (by rw [htest]; omega))
    have hv : tested m h ((MonDepMW.graphInput G).length:ℤ) = (count G k:ℤ) := by
      rw [count_zero G (by omega)]
      simp [tested,built,update,m,input,List.getD_eq_default]
    refine ⟨_,?_,IntegerRAM.runsWithin (Nat.mul_pos (by omega) (by omega)) (completes run) hv outFit⟩
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ C+(h+8) by positivity)]

end VWZClique.IntegerRAM.Cutoff
end

/- FoldKernel -/
section
open VWZClique
namespace VWZClique.FoldProof

def post {L : ℕ} (m : Option (Mask L)) (x : PairBits L) : PairBits L :=
  match m with
  | none => x
  | some mask => (restore mask (fun r => r.2.2.1) x.2, restore mask (fun r => r.2.2.2) x.1)

theorem support {L : ℕ} (m : Mask L) (x y : PairBits L) :
    swapOK m x y ↔ pin (some m) Prod.fst x.1 ∧ pin (some m) (fun r => r.2.1) x.2 ∧
      y = post (some m) x := by
  constructor
  · intro h
    have fixed (i : Fin L) (r : Quad) (hi : m i = some r) := h i
    refine ⟨?_,?_,?_⟩
    · intro i r hr
      have hh := h i
      rcases r with ⟨s,u,v,t⟩
      simpa [hr] using congrArg Prod.fst (show (x.1 i,x.2 i,y.1 i,y.2 i) = (s,u,v,t) by simpa [hr] using hh)
    · intro i r hr
      rcases r with ⟨s,u,v,t⟩
      have hh := h i
      simp [hr] at hh
      exact hh.2.1
    · apply Prod.ext <;> funext i <;> have hh := h i <;>
        cases hm : m i with
        | none => simp [hm] at hh; simp [post,restore,hm]; grind
        | some r => rcases r with ⟨s,u,v,t⟩; simp [hm] at hh; simp [post,restore,hm]; grind
  · rintro ⟨h₁,h₂,rfl⟩ i
    cases h : m i with
    | none => simp [post,restore,h]
    | some r =>
      obtain ⟨s,u,v,t⟩ := r
      simp [post,restore,h,h₁ i _ h,h₂ i _ h]

theorem kernel_eq {F : Type*} [Field F] {L : ℕ} (m : Option (Mask L)) (x y : PairBits L) :
    maskKernel (F := F) m x y = if y = post m x then
      flag m Prod.fst x.1 * flag m (fun r => r.2.1) x.2 else 0 := by
  classical
  cases m with
  | none => simp [post,maskKernel,flag,pin,eq_comm]
  | some m =>
    simp only [maskKernel,support,flag]
    split_ifs <;> simp_all

theorem sum_kernels {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L))
    (f : PairBits L → PairBits L → PairBits L → PairBits L → F) :
    (∑ x, ∑ x', ∑ y, ∑ y', maskKernel a x x' * maskKernel b y y' * f x x' y y') =
    ∑ x, ∑ y, ((flag a Prod.fst x.1 * flag a (fun r => r.2.1) x.2) *
      (flag b Prod.fst y.1 * flag b (fun r => r.2.1) y.2)) * f x (post a x) y (post b y) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp [kernel_eq, mul_ite, ite_mul]

end VWZClique.FoldProof
end

/- FoldRouting -/
section
open VWZClique
namespace VWZClique.FoldProof

def slotWord {L : ℕ} (a b : Option (Mask L)) (X : V → Bits L) (h : Fin 3) (i : Slot) : Bits L :=
  (route a b h i).2 (X (route a b h i).1)

abbrev Packed (L : ℕ) := Bits L × Bits L × Block L × PairBits L × PairBits L

def unpack {L : ℕ} (z : Packed L) : V → Bits L := fun v =>
  let p := (finProdFinEquiv (m := 3) (n := 3)).symm v
  (![block z.2.2.2.1 z.1, block z.2.2.2.2 z.2.1, z.2.2.1] p.1) p.2

@[simp] theorem unpack_site {L : ℕ} (z : Packed L) (g i : Fin 3) :
    unpack z (site g i) = (![block z.2.2.2.1 z.1,block z.2.2.2.2 z.2.1,z.2.2.1] g) i := by
  simp only [unpack,site,Equiv.symm_apply_apply]

def packEquiv (L : ℕ) : (V → Bits L) ≃ Packed L where
  toFun X := (X (site 0 2),X (site 1 2),fun i => X (site 2 i),
    (X (site 0 0),X (site 0 1)),(X (site 1 0),X (site 1 1)))
  invFun := unpack
  left_inv := by
    intro X
    funext v
    obtain ⟨⟨g,i⟩,rfl⟩ := (finProdFinEquiv (m := 3) (n := 3)).surjective v
    fin_cases g <;> fin_cases i <;> rfl
  right_inv := by
    rintro ⟨z₁,z₂,c,x,y⟩
    simp [block, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

theorem routed_slots {L : ℕ} (a b : Option (Mask L)) (z₁ z₂ : Bits L) (c : Block L)
    (x y : PairBits L) (h : Fin 3) (s : Slot) :
    slotWord a b (unpack (z₁,z₂,c,x,y)) h s =
    Sum.elim (![block x z₁,block (post b y) z₂,c] h)
      (![block y z₂,c,block (post a x) z₁] h) s := by
  cases s with
  | inl i => fin_cases h <;> fin_cases i <;> cases b <;> simp [slotWord,route,adjust,perm,next,post,block,Fin.isValue]
  | inr i => fin_cases h <;> fin_cases i <;> cases a <;> simp [slotWord,route,adjust,perm,next,post,block,Fin.isValue]

noncomputable def unary {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (X : V → Bits L)
    (w : ChannelKey L → F) (v : Fin 3 × Slot) : F :=
  w (v.1,.inl (v.2,slotWord a b X v.1 v.2))

noncomputable def binary {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (X : V → Bits L)
    (w : ChannelKey L → F) (e : EdgeSlot) : F :=
  w (e.1,.inr (e.2.1,e.2.2,slotWord a b X e.1 e.2.1,slotWord a b X e.1 e.2.2))

theorem channels_product {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (z₁ z₂ : Bits L) (c : Block L) (x y : PairBits L) (w : ChannelKey L → F) :
    let X := unpack (z₁,z₂,c,x,y)
    placedChannel E w 0 (block x z₁) (block y z₂) *
    placedChannel E w 1 (block (post b y) z₂) c *
    placedChannel E w 2 c (block (post a x) z₁) =
    (∏ v, unary a b X w v) * ∏ e ∈ E, binary a b X w e := by
  classical
  let X := unpack (z₁,z₂,c,x,y)
  let row := ![block x z₁,block (post b y) z₂,c]
  let col := ![block y z₂,c,block (post a x) z₁]
  have chan (h : Fin 3) : placedChannel E w h (row h) (col h) =
      (∏ s : Slot, unary a b X w (h,s)) * ∏ e ∈ E, if e.1=h then binary a b X w e else 1 := by
    unfold placedChannel unary binary
    dsimp only
    apply congrArg₂ (·*·)
    · simp only [X,row,col,routed_slots]
    · apply Finset.prod_congr rfl
      intro e he
      by_cases hh : e.1=h
      · subst h
        simp [X,row,col,routed_slots]
      · simp [hh]
  have allRows := Finset.prod_congr (s₁ := Finset.univ) rfl (fun h _ => chan h)
  rw [Finset.prod_mul_distrib] at allRows
  rw [Finset.prod_comm (f := fun h e => if e.1=h then binary a b X w e else 1)] at allRows
  simp only [Finset.prod_ite_eq,Finset.mem_univ,if_true] at allRows
  dsimp only
  rw [Fintype.prod_prod_type]
  convert! allRows using 1
  rw [Fin.prod_univ_three]
  rfl

noncomputable def checks {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (X : V → Bits L) : F :=
  (flag a Prod.fst (X (site 0 0)) * flag a (fun r => r.2.1) (X (site 0 1))) *
  (flag b Prod.fst (X (site 1 0)) * flag b (fun r => r.2.1) (X (site 1 1)))

private theorem five_sums {A B C D E F : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
    [AddCommMonoid F] (f : A × B × C × D × E → F) :
    ∑ z, f z = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f (a,b,c,d,e) := by simp only [Fintype.sum_prod_type]

theorem reindexed {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (w : ChannelKey L → F) :
    placedFold E a b w = ∑ X : V → Bits L, checks a b X *
      ((∏ v, unary a b X w v) * ∏ e ∈ E, binary a b X w e) := by
  classical
  let expr := fun X : V → Bits L => checks a b X * ((∏ v, unary a b X w v) * ∏ e ∈ E, binary a b X w e)
  rw [← (packEquiv L).symm.sum_comp expr]
  rw [five_sums (D := PairBits L) (E := PairBits L)]
  unfold placedFold
  apply Finset.sum_congr rfl
  intro z₁ _
  apply Finset.sum_congr rfl
  intro z₂ _
  apply Finset.sum_congr rfl
  intro c _
  let f := fun x x' y y' => placedChannel E w 0 (block x z₁) (block y z₂) *
    placedChannel E w 1 (block y' z₂) c * placedChannel E w 2 c (block x' z₁)
  have h := sum_kernels a b f
  dsimp only [f] at h
  simp only [mul_assoc] at h ⊢
  rw [h]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hc := channels_product a b E z₁ z₂ c x y w
  dsimp only at hc
  change _ = expr (unpack (z₁,z₂,c,x,y))
  unfold expr
  rw [← hc]
  simp [checks,block,mul_assoc,Fin.isValue]

end VWZClique.FoldProof
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

theorem computes {f : (I → F) → F} {b : ℕ} (hf : Build f b) :
    computesWithin f b := by
  obtain ⟨r,p,out,_,hc,he,_⟩ := hf 0 .nil
  exact ⟨r,p,out,by exact_mod_cast (by simpa [Program.cost] using hc : p.cost ≤ b),he⟩

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

def weightAt {n : ℕ} (x : V → Fin n) : Kind → WeightKey n
  | .inl i => .inl (i,x i)
  | .inr (i,j) => .inr (i,j,x i,x j)

theorem value_at_ends {n : ℕ} (x : V → Fin n) (p : V × V) :
    addressValue (weightAt x (kind p)) p.1 = x p.1 ∧
    addressValue (weightAt x (kind p)) p.2 = x p.2 := by
  obtain ⟨i,j⟩ := p
  by_cases h : i=j
  · subst j; simp [kind,weightAt,addressValue]
  · by_cases h' : i < j <;> simp [kind,weightAt,addressValue,h,h',Ne.symm h]

theorem oriented (p : V × V) (i j : V) (h : kind p = .inr (i,j)) :
    i < j ∧ (p = (i,j) ∨ p = (j,i)) := by
  obtain ⟨u,v⟩ := p
  by_cases huv : u=v
  · simp [kind,huv] at h
  · by_cases hlt : u<v
    · simp [kind,huv,hlt] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨hlt,Or.inl rfl⟩
    · simp [kind,huv,hlt] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm huv),Or.inr rfl⟩

/-- Combine all input factors assigned to the same unary or unordered edge
weight. The upper triangular ordering is the one used by weightedSum. -/
theorem compile_weights {F I T : Type*} [Field F] [Fintype T] {n : ℕ}
    (H : SimpleGraph V) (ep : T → V × V)
    (edge : ∀ t, (ep t).1 ≠ (ep t).2 → H.Adj (ep t).1 (ep t).2)
    (f : T → Fin n → Fin n → (I → F) → F) (hf : ∀ t x y, Circuit.Build (f t x y) 0) :
    ∃ (r : ℕ) (p : Program F I r) (out : WeightKey n → Fin r),
      p.cost ≤ Fintype.card (WeightKey n) * Fintype.card T ∧ ∀ w,
      weightedSum H (fun k => p.eval w (out k)) =
        ∑ x : V → Fin n, ∏ t : T, f t (x (ep t).1) (x (ep t).2) w := by
  classical
  have build (k : WeightKey n) : Circuit.Build (collect ep f k) (Fintype.card T) := by
    let s := Finset.univ.filter (fun t => kind (ep t) = shape k)
    exact Circuit.cost_mono (Circuit.prod s _ 0 (fun t _ => hf t _ _)) (by simpa using Finset.card_le_univ s)
  obtain ⟨r,p,out,hc,he⟩ := tabulate _ _ build
  refine ⟨r,p,out,hc,?_⟩
  intro w
  have take (x : V → Fin n) (b : Kind) : collect ep f (weightAt x b) w =
      ∏ t ∈ Finset.univ.filter (fun t => kind (ep t) = b), f t (x (ep t).1) (x (ep t).2) w := by
    have hs : shape (weightAt x b) = b := by cases b with | inl _ => rfl | inr v => rcases v with ⟨_,_⟩; rfl
    unfold collect
    rw [hs]
    refine Finset.prod_congr rfl ?_
    intro t ht
    have h := (Finset.mem_filter.mp ht).2
    subst b
    rw [(value_at_ends x (ep t)).1,(value_at_ends x (ep t)).2]
  have inactive (x : V → Fin n) (i j : V) (h : ¬ (i < j ∧ H.Adj i j)) :
      collect ep f (weightAt x (.inr (i,j))) w = 1 := by
    rw [take]
    apply Finset.prod_eq_one
    intro t ht
    obtain ⟨hlt,hp|hp⟩ := oriented _ _ _ (Finset.mem_filter.mp ht).2
    · have hadj := edge t (by simpa [hp] using hlt.ne)
      exact (h ⟨hlt, by simpa [hp] using hadj⟩).elim
    · have hadj := edge t (by simpa [hp] using hlt.ne')
      exact (h ⟨hlt, by simpa [hp] using hadj.symm⟩).elim
  unfold weightedSum
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [he]
  have allKeys : (∏ b : Kind, collect ep f (weightAt x b) w) =
      ∏ t : T, f t (x (ep t).1) (x (ep t).2) w := by
    simp_rw [take]
    exact Finset.prod_fiberwise _ _ _
  rw [← allKeys,Fintype.prod_sum_type,Fintype.prod_prod_type]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : i < j ∧ H.Adj i j
  · simp [h,weightAt]
  · simpa only [if_neg h] using (inactive x i j h).symm

end VWZClique.FoldProof
end

/- WeightedPlacement -/
section
open VWZClique VWZClique.FoldProof OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.WeightedProof

def ends (e : EdgeSlot) : V × V := (endpoint e.1 e.2.1, endpoint e.1 e.2.2)

theorem locate_ends : ∀ u v : V, ends (locate u v) = (u,v) := by decide

theorem chosen_ends (π : Equiv.Perm V) (p : V × V) :
    ends (chosen π p) = (π.symm p.1,π.symm p.2) ∨
      ends (chosen π p) = (π.symm p.2,π.symm p.1) := by
  by_cases h : π.symm p.1 ≤ π.symm p.2
  · simp [chosen,locate_ends,min_eq_left h,max_eq_right h]
  · simp [chosen,locate_ends,min_eq_right (le_of_not_ge h),max_eq_left (le_of_not_ge h)]

theorem chosen_inj (π : Equiv.Perm V) (H : SimpleGraph V) : Set.InjOn (chosen π) (↑(pairs H)) := by
  classical
  intro p hp q hq he
  have hp' := (Finset.mem_filter.mp hp).2.1
  have hq' := (Finset.mem_filter.mp hq).2.1
  have hinv (a b : V) : π.symm a = π.symm b ↔ a=b := π.symm.injective.eq_iff
  have h := congrArg ends he
  rcases chosen_ends π p with p1|p2 <;> rcases chosen_ends π q with q1|q2 <;>
    simp_all [Prod.ext_iff] <;> exact (lt_asymm hq' hp').elim

end VWZClique.WeightedProof
end

/- FoldEdges -/
section
open VWZClique
namespace VWZClique.FoldProof

theorem folded_adj {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (e : EdgeSlot) (he : e ∈ E) (hne : (epPair a b e).1 ≠ (epPair a b e).2) :
    (foldedGraph a b E).Adj (epPair a b e).1 (epPair a b e).2 :=
  ⟨Finset.mem_image_of_mem (edgeImage a b) he, hne⟩

end VWZClique.FoldProof
end

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

/- FoldFactors -/
section
open VWZClique
namespace VWZClique.FoldProof

theorem weight_cost {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) {E : Finset EdgeSlot}
    (t : FoldToken E) (s u : Bits L) : Circuit.Build (weight (F := F) a b t s u) 0 := by
  rcases t with i | ⟨h,i⟩ | e
  · exact Circuit.const _
  · exact Circuit.read _
  · exact Circuit.read _

theorem token_product {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (X : V → Bits L) (w : ChannelKey L → F) :
    (∏ v : FoldToken E, weight a b v (X (ends a b v).1) (X (ends a b v).2) w) =
    checks a b X * ((∏ v, unary a b X w v) * ∏ e ∈ E, binary a b X w e) := by
  rw [Fintype.prod_sum_type,Fintype.prod_sum_type]
  congr 1
  · rw [Fin.prod_univ_four]
    change ((flag a _ _ * flag a _ _) * flag b _ _) * flag b _ _ = _
    simp only [checks,mul_assoc]
    rfl
  · congr 1
    change (∏ e : ↥E, binary a b X w e.val) = _
    exact Finset.prod_attach E (binary a b X w)

noncomputable def wordEquiv (L : ℕ) : Fin (2^L) ≃ Bits L :=
  Fintype.equivOfCardEq (by simp [Bits])

theorem weighted_encoding {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (w : ChannelKey L → F) :
    (∑ x : V → Fin (2^L), ∏ t : FoldToken E,
      weight a b t (wordEquiv L (x (ends a b t).1)) (wordEquiv L (x (ends a b t).2)) w)
    = placedFold E a b w := by
  rw [reindexed]
  let e := Equiv.piCongrRight (fun _ : V => wordEquiv L)
  let raw := fun X : V → Bits L => ∏ t : FoldToken E, weight a b t (X (ends a b t).1) (X (ends a b t).2) w
  change (∑ x, raw (e x)) = _
  rw [e.sum_comp raw]
  exact Finset.sum_congr rfl fun X _ => token_product a b E X w

theorem factor_table_cost (L : ℕ) (E : Finset EdgeSlot) :
    Fintype.card (WeightKey (2^L)) * Fintype.card (FoldToken E) ≤ 11700*(2^L)^2 := by
  let n := 2^L
  have hn : 1 ≤ n := Nat.one_le_pow _ _ (by decide)
  have hn' : n ≤ n^2 := by simpa only [pow_two, mul_one] using Nat.mul_le_mul_left n hn
  have base : E.card ≤ 108 := by
    have h := Finset.card_le_univ E
    simpa [EdgeSlot,Slot,Fintype.card_prod,Fintype.card_sum] using h
  have tok : Fintype.card (FoldToken E) ≤ 130 := by
    simp [FoldToken, Slot, Fintype.card_prod, Fintype.card_sum]
    omega
  have keys : Fintype.card (WeightKey n) ≤ 90*n^2 := by
    simp [WeightKey,V,Fintype.card_prod,Fintype.card_sum,pow_two] at *
    nlinarith only [hn']
  calc
    _ ≤ (90*n^2)*130 := Nat.mul_le_mul keys tok
    _ = _ := by dsimp [n]; ring

end VWZClique.FoldProof
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

omit [Field F] in
theorem translate_cost (tag : J → I ⊕ F) {r : ℕ} (p : Program F J r) :
    (translate tag p).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih =>
    simp only [translate,Program.cost,ih]
    congr 1
    cases g with
    | input j => cases ht : tag j <;> simp [translateGate,ht,Gate.cost]
    | _ => rfl

theorem translate_eval (tag : J → I ⊕ F) {r : ℕ} (p : Program F J r) (w : I → F) :
    (translate tag p).eval w = p.eval (fun j => literal w (tag j)) := by
  induction p with
  | nil => rfl
  | step p g ih =>
    simp only [translate,Program.eval,ih]
    cases g with
    | input j => cases ht : tag j <;> simp [translateGate,ht,Gate.eval,literal]
    | _ => rfl

theorem translated {f : (J → F) → F} {B : ℝ} (h : computesWithin f B) (tag : J → I ⊕ F) :
    computesWithin (fun w => f (fun j => literal w (tag j))) B := by
  obtain ⟨r,p,o,hc,he⟩ := h
  exact ⟨r,translate tag p,o,by rwa [translate_cost],fun w => by rw [translate_eval,he]⟩

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

theorem padding {n N : ℕ} (hn : n ≤ N) (H : SimpleGraph V) {B : ℝ}
    (h : computesWithin (weightedSum (F := F) (n := N) H) B) :
    computesWithin (weightedSum (F := F) (n := n) H) B := by
  simpa only [weights_padded hn H] using (translated h (padTag (n := n)))

theorem brute {n : ℕ} (H : SimpleGraph V) :
    Circuit.Build (weightedSum (F := F) (n := n) H) ((n^9)*101) := by
  classical
  let un := fun (a : V → Fin n) (i : V) (w : WeightKey n → F) => w (.inl (i,a i))
  let ed := fun (a : V → Fin n) (i j : V) (w : WeightKey n → F) =>
    if i<j ∧ H.Adj i j then w (.inr (i,j,a i,a j)) else 1
  have bu (a : V → Fin n) : Circuit.Build (fun w => ∏ i, un a i w) 9 :=
    Circuit.prod Finset.univ _ 0 (fun _ _ => Circuit.read _)
  have be (a : V → Fin n) (i j : V) : Circuit.Build (ed a i j) 0 := by
    by_cases h : i<j ∧ H.Adj i j
    · simpa [ed,h] using (Circuit.read (F := F) (Sum.inr (i,j,a i,a j) : WeightKey n))
    · simpa [ed,h] using (Circuit.const (I := WeightKey n) (1:F))
  have bi (a : V → Fin n) (i : V) : Circuit.Build (fun w => ∏ j, ed a i j w) 9 :=
    Circuit.prod Finset.univ _ 0 (fun j _ => be a i j)
  have bp (a : V → Fin n) : Circuit.Build (fun w => ∏ i, ∏ j, ed a i j w) 90 :=
    Circuit.prod Finset.univ _ 9 (fun i _ => bi a i)
  have total := Circuit.sum Finset.univ _ _ (fun a _ => Circuit.mul (bu a) (bp a))
  exact Circuit.cost_mono total (by simp [V])

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

/- WeightedChannels -/
section
open VWZClique VWZClique.FoldProof
namespace VWZClique.WeightedProof

noncomputable def indexWord (L : ℕ) : Bits L ≃ Fin (2^L) :=
  Fintype.equivOfCardEq (by simp [Bits])

noncomputable def channelTag {F : Type*} [Field F] {L : ℕ}
    (π : Equiv.Perm V) (E : Finset EdgeSlot) : ChannelKey L → WeightKey (2^L) ⊕ F
  | (h,.inl (.inl i,x)) => .inl (.inl (π (site h i), indexWord L x))
  | (_,.inl (.inr _,_)) => .inr 1
  | (h,.inr (s,t,x,y)) => if (h,s,t) ∈ E then
      .inl (edgeKey (π (endpoint h s)) (π (endpoint h t)) (indexWord L x) (indexWord L y))
    else .inr 1

theorem supported {F : Type*} [Field F] {L : ℕ} (π : Equiv.Perm V) (E : Finset EdgeSlot)
    (w : WeightKey (2^L) → F) (h : Fin 3) (a b : Block L) :
    let inputs := fun k : ChannelKey L => literal w (channelTag π E k)
    channel inputs h a b = placedChannel E inputs h a b := by
  classical
  dsimp only
  unfold channel placedChannel
  dsimp only
  apply congrArg (fun y : F => _ * y)
  let x := Sum.elim a b
  let v := fun e : EdgeSlot => if e.1=h then literal w
    (channelTag π E (h,.inr (e.2.1,e.2.2,x e.2.1,x e.2.2))) else 1
  have addBack : (∏ e ∈ E, v e) = ∏ e : EdgeSlot, v e := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro e _ he
    by_cases h' : e.1=h
    · obtain ⟨k,s,t⟩ := e
      dsimp only at h'
      subst k
      simp [v,channelTag,he,literal]
    · simp [v,h']
  change _ = ∏ e ∈ E, v e
  rw [addBack,Fintype.prod_prod_type,Finset.prod_comm (f := fun k st => v (k,st))]
  simp only [v,Finset.prod_ite_eq',Finset.mem_univ,if_true]
  rw [Fintype.prod_prod_type]

theorem no_swap_word {L : ℕ} (X : V → Bits L) (h : Fin 3) (s : Slot) :
    slotWord none none X h s = X (endpoint h s) := by
  cases s with
  | inl i => fin_cases h <;> rfl
  | inr i => fin_cases h <;> rfl

theorem encode_graph {F : Type*} [Field F] {L : ℕ} (π : Equiv.Perm V) (H : SimpleGraph V)
    (w : WeightKey (2^L) → F) :
    placedFold (slots π H) none none (fun j : ChannelKey L => literal w (channelTag π (slots π H) j)) =
      weightedSum H w := by
  classical
  let E := slots π H
  let inputs := fun k : ChannelKey L => literal w (channelTag π E k)
  let perm := π.arrowCongr (indexWord L)
  rw [reindexed,weightedSum,← perm.sum_comp]
  apply Finset.sum_congr rfl
  intro X _
  let X' := perm X
  have mapped (v : V) : X' (π v) = indexWord L (X v) := by simp [X',perm,Equiv.arrowCongr_apply]
  have mapped' (v : V) : indexWord L (X (π.symm v)) = X' v := rfl
  have uv : (∏ v : Fin 3 × Slot, unary none none X inputs v) =
      ∏ i : V, w (.inl (i,X' i)) := by
    let u := fun i : V => w (Sum.inl (i,X' i))
    rw [← Equiv.prod_comp π u, ← (finProdFinEquiv (m:=3) (n:=3)).prod_comp (fun i => u (π i))]
    rw [Fintype.prod_prod_type,Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro h _
    rw [Fintype.prod_sum_type]
    simp only [unary,inputs,channelTag,literal,Sum.elim_inl,Sum.elim_inr,id_eq,
      Finset.prod_const_one,mul_one,no_swap_word,endpoint,u,mapped,site]
  have ev : (∏ e ∈ E, binary none none X inputs e) =
      ∏ i : V, ∏ j : V, if i < j ∧ H.Adj i j then w (.inr (i,j,X' i,X' j)) else 1 := by
    rw [← Fintype.prod_prod_type (fun p : V × V => if p.1<p.2 ∧ H.Adj p.1 p.2 then
      w (.inr (p.1,p.2,X' p.1,X' p.2)) else 1)]
    rw [← Finset.prod_filter]
    change (∏ e ∈ (pairs H).image (chosen π), binary none none X inputs e) =
      ∏ p ∈ pairs H, w (.inr (p.1,p.2,X' p.1,X' p.2))
    rw [Finset.prod_image (chosen_inj π H)]
    apply Finset.prod_congr rfl
    intro p hp
    let e := chosen π p
    have he : e ∈ E := Finset.mem_image_of_mem _ hp
    have hlt := (Finset.mem_filter.mp hp).2.1
    change literal w (channelTag π E (e.1,.inr (e.2.1,e.2.2,_,_))) = _
    simp only [channelTag,if_pos he,literal,Sum.elim_inl,no_swap_word]
    change w (edgeKey (π (ends e).1) (π (ends e).2) (indexWord L (X (ends e).1)) (indexWord L (X (ends e).2))) = _
    rcases chosen_ends π p with he|he
    · dsimp only [e]
      simp only [he,Equiv.apply_symm_apply,edgeKey,hlt,if_true,mapped']
    · dsimp only [e]
      simp only [he,Equiv.apply_symm_apply,edgeKey,not_lt_of_gt hlt,if_false,mapped']
  have checksOne : checks (F:=F) none none X = 1 := by simp [checks,flag,pin]
  change checks (F:=F) none none X * ((∏ v, unary none none X inputs v) *
      ∏ e ∈ E, binary none none X inputs e) = _
  rw [checksOne,one_mul,uv,ev]

end VWZClique.WeightedProof
end

/- CliqueDyadic -/
section
/-! Exact clearing of power-of-two denominators in integer matrix products. -/

namespace VWZClique.Dyadic
open scoped BigOperators

def value (q : ℕ) (z : ℤ) : ℚ := (z:ℚ)/(2:ℚ)^q

/-- Raising all entries to a common denominator preserves the exact rational. -/
theorem widen {q Q : ℕ} (h : q ≤ Q) (z : ℤ) :
    value Q (z * (2:ℤ)^(Q-q)) = value q z := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  simp [value, pow_add]
  field_simp

theorem value_mul (q r : ℕ) (a b : ℤ) :
    value (q+r) (a*b) = value q a * value r b := by
  simp [value, pow_add, mul_div_mul_comm]

theorem value_sum {I : Type*} [Fintype I] (q : ℕ) (a : I → ℤ) :
    value q (∑ i, a i) = ∑ i, value q (a i) := by simp [value, Finset.sum_div]

def decode {I J : Type*} (q : ℕ) (A : Matrix I J ℤ) : Matrix I J ℚ :=
  fun i j => value q (A i j)

/-- One ordinary integer product followed by one rescaling is the original rational product. -/
theorem decode_mul {I J K : Type*} [Fintype J] (q r : ℕ)
    (A : Matrix I J ℤ) (B : Matrix J K ℤ) :
    decode (q+r) (A*B) = decode q A * decode r B := by
  ext i k
  simp only [decode, Matrix.mul_apply, value_sum, value_mul]

/-- A matrix product has a polynomial bound on the signed integers to be represented. -/
theorem product_bound {I J K : Type*} [Fintype J]
    (A : Matrix I J ℤ) (B : Matrix J K ℤ) (U V : ℕ)
    (hA : ∀ i j, |A i j| ≤ (U:ℤ)) (hB : ∀ j k, |B j k| ≤ (V:ℤ)) (i : I) (k : K) :
    |(A*B) i k| ≤ (Fintype.card J : ℤ)*U*V := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ j, |A i j * B j k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : J, (U:ℤ)*V := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hA i j) (hB j k) (abs_nonneg _) (by positivity)
    _ = _ := by simp [mul_assoc]

/-- Independent denominator exponents may be cleared before the product. The
    new integers have magnitude at most `U * 2^Q`. -/
theorem clear_matrix {I J : Type*} (X : Matrix I J ℚ) (Q U : ℕ)
    (hX : ∀ i j, ∃ q : ℕ, q ≤ Q ∧ ∃ z : ℤ, |z| ≤ (U:ℤ) ∧ X i j = value q z) :
    ∃ A : Matrix I J ℤ, decode Q A = X ∧ ∀ i j, |A i j| ≤ (U:ℤ)*2^Q := by
  classical
  choose q hq z hz he using hX
  let A : Matrix I J ℤ := fun i j => z i j * 2^(Q-q i j)
  refine ⟨A, ?_, ?_⟩
  · ext i j
    exact (widen (hq i j) (z i j)).trans (he i j).symm
  · intro i j
    change |z i j * (2:ℤ)^(Q-q i j)| ≤ _
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ 2^(Q-q i j))]
    exact mul_le_mul (hz i j)
      (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)) (by positivity) (by positivity)

end VWZClique.Dyadic
end

/- UniformFoldWeights -/
section
open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds

/-- Reindexing every value table by the same domain permutation leaves the pattern sum unchanged. -/
def permuteKey {n : ℕ} (e : Equiv.Perm (Fin n)) : WeightKey n → WeightKey n
  | .inl (i,x) => .inl (i,e x)
  | .inr (i,j,x,y) => .inr (i,j,e x,e y)

theorem permute_domain {F : Type*} [Field F] {n : ℕ} (H : SimpleGraph V)
    (w : WeightKey n → F) (e : Equiv.Perm (Fin n)) :
    weightedSum H (fun k => w (permuteKey e k)) = weightedSum H w := by
  classical
  unfold weightedSum
  let p := (Equiv.refl V).arrowCongr e
  let f := fun a : V → Fin n => (∏ i, w (.inl (i,a i))) *
    ∏ i, ∏ j, if i<j ∧ H.Adj i j then w (.inr (i,j,a i,a j)) else 1
  change (∑ a, f (p a)) = ∑ a, f a
  exact p.sum_comp f

theorem inputKey_eq {F : Type*} [Field F] {L : ℕ} (π : Equiv.Perm V) (E : Finset EdgeSlot)
    (w : WeightKey (2^L) → F) (k : ChannelKey L) :
    literal w (inputKey π E k) =
      literal (fun j => w (permuteKey ((indexWord L).symm.trans (wordIndex L)) j)) (channelTag π E k) := by
  rcases k with ⟨h,⟨s,x⟩|⟨s,t,x,y⟩⟩
  · cases s <;> simp [inputKey,channelTag,literal,permuteKey]
  · by_cases hs : (h,s,t) ∈ E
    · simp only [inputKey,channelTag,if_pos hs,literal,Sum.elim_inl]
      unfold edgeKey
      split <;> simp [permuteKey]
    · simp [inputKey,channelTag,literal,hs]

theorem input_exact {F : Type*} [Field F] {L : ℕ} (π : Equiv.Perm V) (H : SimpleGraph V)
    (w : WeightKey (2^L) → F) :
    placedFold (slots π H) none none (fun j : ChannelKey L => literal w (inputKey π (slots π H) j)) =
      weightedSum H w := by
  simp_rw [inputKey_eq]
  rw [encode_graph,permute_domain]

private theorem collect_identity {F I T : Type*} [Field F] [Fintype T] {n : ℕ}
    (H : SimpleGraph V) (ep : T → V × V)
    (edge : ∀ t, (ep t).1 ≠ (ep t).2 → H.Adj (ep t).1 (ep t).2)
    (f : T → Fin n → Fin n → (I → F) → F) (w : I → F) :
    weightedSum H (fun k => collect ep f k w) =
      ∑ x : V → Fin n, ∏ t : T, f t (x (ep t).1) (x (ep t).2) w := by
  classical
  have take (x : V → Fin n) (b : Kind) : collect ep f (weightAt x b) w =
      ∏ t ∈ Finset.univ.filter (fun t => kind (ep t) = b), f t (x (ep t).1) (x (ep t).2) w := by
    have hs : shape (weightAt x b) = b := by cases b with | inl _ => rfl | inr v => rcases v with ⟨_,_⟩; rfl
    unfold collect
    rw [hs]
    refine Finset.prod_congr rfl ?_
    intro t ht
    have h := (Finset.mem_filter.mp ht).2
    subst b
    rw [(value_at_ends x (ep t)).1,(value_at_ends x (ep t)).2]
  have inactive (x : V → Fin n) (i j : V) (h : ¬ (i < j ∧ H.Adj i j)) :
      collect ep f (weightAt x (.inr (i,j))) w = 1 := by
    rw [take]
    apply Finset.prod_eq_one
    intro t ht
    obtain ⟨hlt,hp|hp⟩ := oriented _ _ _ (Finset.mem_filter.mp ht).2
    · have hadj := edge t (by simpa [hp] using hlt.ne)
      exact (h ⟨hlt, by simpa [hp] using hadj⟩).elim
    · have hadj := edge t (by simpa [hp] using hlt.ne')
      exact (h ⟨hlt, by simpa [hp] using hadj.symm⟩).elim
  unfold weightedSum
  apply Finset.sum_congr rfl
  intro x _
  have allKeys : (∏ b : Kind, collect ep f (weightAt x b) w) =
      ∏ t : T, f t (x (ep t).1) (x (ep t).2) w := by
    simp_rw [take]
    exact Finset.prod_fiberwise _ _ _
  rw [← allKeys,Fintype.prod_sum_type,Fintype.prod_prod_type]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : i < j ∧ H.Adj i j
  · simp [h,weightAt]
  · simpa only [if_neg h] using (inactive x i j h).symm

theorem updated_exact {F : Type*} [Field F] {L : ℕ} (E : Finset EdgeSlot)
    (a b : Option (Mask L)) (w : ChannelKey L → F) :
    weightedSum (foldedGraph a b E) (updated E a b w) = placedFold E a b w := by
  let ep := ends (E:=E) a b
  have he (t : FoldToken E) (hn : (ep t).1 ≠ (ep t).2) :
      (foldedGraph a b E).Adj (ep t).1 (ep t).2 := by
    rcases t with i|⟨h,i⟩|e
    · exact (hn rfl).elim
    · exact (hn rfl).elim
    · exact folded_adj a b E e.val e.property hn
  unfold updated
  rw [collect_identity (foldedGraph a b E) ep he,reindexed]
  let g := Equiv.piCongrRight (fun _ : V => (wordIndex L).symm)
  let f := fun X : V → Bits L => ∏ t : FoldToken E, weight a b t (X (ep t).1) (X (ep t).2) w
  change (∑ x, f (g x)) = _
  rw [g.sum_comp f]
  exact Finset.sum_congr rfl fun X _ => token_product a b E X w

theorem token_limit (E : Finset EdgeSlot) : Fintype.card (FoldToken E) ≤ 130 := by
  have h : E.card ≤ 108 := by
    simpa [EdgeSlot,Slot,Fintype.card_prod,Fintype.card_sum] using Finset.card_le_univ E
  simp [FoldToken,Slot,Fintype.card_prod,Fintype.card_sum]
  omega

theorem token_property {F : Type*} [Field F] {L : ℕ} (P : F → Prop)
    (pz : P 0) (po : P 1) (E : Finset EdgeSlot) (a b : Option (Mask L))
    (w : ChannelKey L → F) (pw : ∀ k, P (w k))
    (t : FoldToken E) (s u : Bits L) : P (weight a b t s u w) := by
  rcases t with i|⟨h,i⟩|e
  · have hh (m : Option (Mask L)) (rd : Quad → Bool) : P (flag m rd s) := by
      unfold flag
      split <;> assumption
    fin_cases i <;> exact hh _ _
  · exact pw _
  · exact pw _

theorem binary_prod {T : Type*} (s : Finset T) (f : T → ℚ)
    (h : ∀ t ∈ s, Binary (f t)) : Binary (∏ t ∈ s,f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Binary]
  | @insert i s hi ih =>
    have h₁ := h i (Finset.mem_insert_self _ _)
    have h₂ := ih (fun t ht => h t (Finset.mem_insert_of_mem ht))
    rcases h₁ with h₁|h₁ <;> rcases h₂ with h₂|h₂ <;> simp [Binary,hi,h₁,h₂]

theorem updated_binary {L : ℕ} (E : Finset EdgeSlot) (a b : Option (Mask L))
    (w : ChannelKey L → ℚ) (h : ∀ k, Binary (w k)) (k : WeightKey (2^L)) :
    Binary (updated E a b w k) := by
  apply binary_prod
  intro t _
  exact token_property Binary (Or.inl rfl) (Or.inr rfl) E a b w h t _ _

/-- Number of bits above the unit needed for a dyadic numerator and its binary denominator. -/
def Bounded (N : ℕ) (x : ℚ) : Prop :=
  ∃ q : ℕ, q ≤ N ∧ ∃ z : ℤ, |z| ≤ (2:ℤ)^N ∧ x = Dyadic.value q z

theorem bounded_binary (N : ℕ) {x : ℚ} (h : Binary x) : Bounded N x := by
  rcases h with rfl|rfl
  · exact ⟨0,Nat.zero_le _,0,by simp,by simp [Dyadic.value]⟩
  · exact ⟨0,Nat.zero_le _,1,by simpa using one_le_pow₀ (n:=N) (by norm_num : (1:ℤ) ≤ 2),
      by simp [Dyadic.value]⟩

theorem bounded_mono {m n : ℕ} (hm : m ≤ n) {x : ℚ} (hx : Bounded m x) : Bounded n x := by
  obtain ⟨q,hq,z,hz,he⟩ := hx
  exact ⟨q,hq.trans hm,z,hz.trans (pow_le_pow_right₀ (by norm_num) hm),he⟩

theorem bounded_mul {m n : ℕ} {x y : ℚ} (hx : Bounded m x) (hy : Bounded n y) :
    Bounded (m+n) (x*y) := by
  obtain ⟨p,hp,a,ha,rfl⟩ := hx
  obtain ⟨q,hq,b,hb,rfl⟩ := hy
  refine ⟨p+q,Nat.add_le_add hp hq,a*b,?_,(Dyadic.value_mul p q a b).symm⟩
  rw [abs_mul,pow_add]
  exact mul_le_mul ha hb (abs_nonneg _) (by positivity)

theorem bounded_prod {T : Type*} (s : Finset T) (f : T → ℚ) (B : ℕ)
    (h : ∀ t ∈ s, Bounded B (f t)) : Bounded (s.card*B) (∏ t ∈ s, f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bounded_binary 0 (Or.inr rfl : Binary 1)
  | @insert i s hi ih =>
    have h₁ := h i (Finset.mem_insert_self _ _)
    have h₂ := ih (fun t ht => h t (Finset.mem_insert_of_mem ht))
    simpa [hi,Nat.succ_mul,Nat.add_comm] using bounded_mul h₁ h₂

theorem updated_bounded {L : ℕ} (E : Finset EdgeSlot) (a b : Option (Mask L))
    (w : ChannelKey L → ℚ) (B : ℕ) (h : ∀ k, Bounded B (w k)) (k : WeightKey (2^L)) :
    Bounded (130*B) (updated E a b w k) := by
  unfold updated collect
  apply bounded_mono _ (bounded_prod _ _ B (fun t _ =>
    token_property (Bounded B) (bounded_binary B (Or.inl rfl)) (bounded_binary B (Or.inr rfl)) E a b w h t _ _))
  exact Nat.mul_le_mul_right _ ((Finset.card_le_univ _).trans (token_limit E))

end VWZClique.UniformFolds
end

/- UniformFoldPaths -/
section
open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds

theorem Round.exact_value {L : ℕ} (r : Round L) (w : WeightKey (2^L) → ℚ) (d : Branch)
    (ha : r.a.isSome = first d) (hb : r.b.isSome = second d) :
    weightedSum (child (slots r.π r.H) d) (r.apply w) = placedFold (slots r.π r.H) r.a r.b (r.inputs w) := by
  rw [← graph_static r.a r.b _ d ha hb]
  exact updated_exact _ _ _ _

theorem Round.inputs_property {L : ℕ} (r : Round L) (w : WeightKey (2^L) → ℚ)
    (P : ℚ → Prop) (po : P 1) (hw : ∀ k, P (w k)) (j : ChannelKey L) : P (r.inputs w j) := by
  rcases j with ⟨h,⟨i,x⟩|⟨s,t,x,y⟩⟩
  · cases i
    · exact hw _
    · exact po
  · by_cases he : (h,s,t) ∈ slots r.π r.H
    · simpa only [Round.inputs,inputKey,if_pos he,literal,Sum.elim_inl] using hw
        (edgeKey (r.π (endpoint h s)) (r.π (endpoint h t)) (wordIndex L x) (wordIndex L y))
    · simpa only [Round.inputs,inputKey,if_neg he,literal,Sum.elim_inr,id_eq] using po

noncomputable def follow {L : ℕ} : List (Round L) → (WeightKey (2^L) → ℚ) → WeightKey (2^L) → ℚ
  | [], w => w
  | r::rs, w => follow rs (r.apply w)

theorem follow_binary {L : ℕ} (rs : List (Round L)) (w : WeightKey (2^L) → ℚ)
    (hw : ∀ k, Binary (w k)) : ∀ k, Binary (follow rs w k) := by
  induction rs generalizing w with
  | nil => exact hw
  | cons r rs ih =>
    exact ih (r.apply w) (updated_binary _ _ _ _ (r.inputs_property w Binary (Or.inr rfl) hw))

theorem follow_bounded {L : ℕ} (rs : List (Round L)) (w : WeightKey (2^L) → ℚ)
    (B : ℕ) (hw : ∀ k, Bounded B (w k)) (k : WeightKey (2^L)) :
    Bounded (130^rs.length*B) (follow rs w k) := by
  induction rs generalizing w B with
  | nil => simpa [follow] using hw k
  | cons r rs ih =>
    have h := ih (r.apply w) (130*B) (updated_bounded _ _ _ _ B
      (r.inputs_property w (Bounded B) (bounded_binary B (Or.inr rfl)) hw))
    simpa only [List.length_cons,pow_succ,Nat.mul_assoc,follow] using h

/-- An actual call path in a fixed ternary plan. Multiple masks may choose the same child. -/
inductive Trace (L : ℕ) : {H : SimpleGraph V} → Plan H → SimpleGraph V → List (Round L) → Prop where
  | stop {H} (p : Plan H) : Trace L p H []
  | take {H H' : SimpleGraph V} {π : Equiv.Perm V}
      {hp : wedgePlaced (slots π H) 0 2 ∧ wedgePlaced (slots π H) 1 0}
      {kids : (d : Branch) → Plan (child (slots π H) d)} {rs : List (Round L)}
      (d : Branch) (a b : Option (Mask L)) (ha : a.isSome = first d) (hb : b.isSome = second d)
      (tail : Trace L (kids d) H' rs) :
      Trace L (.split H π hp kids) H' (⟨H,π,a,b⟩ :: rs)

theorem Trace.length_bound {L : ℕ} {H H' : SimpleGraph V} {p : Plan H} {rs : List (Round L)}
    (tr : Trace L p H' rs) : rs.length + Nat.card H'.edgeSet ≤ Nat.card H.edgeSet := by
  induction tr with
  | stop => simp
  | @take H H' π hp kids rs d a b ha hb tail ih =>
    have h := branch_smaller H π hp d
    simp only [List.length_cons]
    omega

theorem Trace.polynomial_values {L : ℕ} {H H' : SimpleGraph V} {p : Plan H} {rs : List (Round L)}
    (tr : Trace L p H' rs) (w : WeightKey (2^L) → ℚ) (C : ℕ)
    (hw : ∀ k, Bounded (C*L) (w k)) (k : WeightKey (2^L)) :
    Bounded ((130^36*C)*L) (follow rs w k) := by
  have h₁ := tr.length_bound
  have h₂ := edge_limit H
  have hlen : rs.length ≤ 36 := by omega
  apply bounded_mono _ (follow_bounded rs w (C*L) hw k)
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hlen)

/-- For Boolean tables, the weighted sum counts a subset of the assignments. -/
theorem binary_sum {n : ℕ} (H : SimpleGraph V) (w : WeightKey n → ℚ)
    (hw : ∀ k, Binary (w k)) :
    ∃ z : ℕ, z ≤ n^9 ∧ weightedSum H w = (z:ℚ) := by
  classical
  let f := fun a : V → Fin n => (∏ i, w (.inl (i,a i))) *
    ∏ i, ∏ j, if i<j ∧ H.Adj i j then w (.inr (i,j,a i,a j)) else 1
  have hf (a : V → Fin n) : Binary (f a) := by
    have h₁ := binary_prod Finset.univ (fun i => w (.inl (i,a i))) (fun i _ => hw _)
    have h₂ : Binary (∏ i, ∏ j, if i<j ∧ H.Adj i j then w (.inr (i,j,a i,a j)) else 1) := by
      apply binary_prod
      intro i _
      apply binary_prod
      intro j _
      split
      · exact hw _
      · exact Or.inr rfl
    rcases h₁ with h₁|h₁ <;> rcases h₂ with h₂|h₂ <;> simp only [f,h₁,h₂,zero_mul,one_mul,Binary] <;> simp
  let s := Finset.univ.filter (fun a => f a=1)
  refine ⟨s.card,?_,?_⟩
  · simpa [V] using Finset.card_le_univ s
  · change (∑ a, f a) = (s.card:ℚ)
    calc
      _ = ∑ a, if f a=1 then (1:ℚ) else 0 := Finset.sum_congr rfl (fun a _ => by rcases hf a with h|h <;> simp [h])
      _ = _ := by rw [← Finset.sum_filter]; simp [s]

theorem Trace.integer_output {L : ℕ} {H H' : SimpleGraph V} {p : Plan H} {rs : List (Round L)}
    (_ : Trace L p H' rs) (w : WeightKey (2^L) → ℚ) (hw : ∀ k, Binary (w k)) :
    ∃ z : ℕ, z ≤ (2^L)^9 ∧ weightedSum H' (follow rs w) = (z:ℚ) :=
  binary_sum H' _ (follow_binary rs w hw)

end VWZClique.UniformFolds
end

/- DyadicBounds -/
section
open VWZClique
namespace VWZClique.RankSwap

theorem denominator_bits {L : ℕ} (j : BasisLabel L) : denominatorExponent j ≤ L := by
  simpa [denominatorExponent] using Finset.card_le_univ (Finset.univ.filter (fun i => ¬j i < 2))

end VWZClique.RankSwap
end

/- WeightedAlgebra -/
section
open VWZClique
namespace VWZClique.WeightedProof

abbrev KernelArgs (L : ℕ) := PairBits L × PairBits L × PairBits L × PairBits L

noncomputable def evaluate {F : Type*} [Field F] {L : ℕ} (E : Finset EdgeSlot)
    (w : ChannelKey L → F) : (KernelArgs L → F) →ₗ[F] F where
  toFun k :=
    ∑ z₁ : Bits L, ∑ z₂ : Bits L, ∑ c : Block L,
      ∑ x : PairBits L, ∑ x' : PairBits L, ∑ y : PairBits L, ∑ y' : PairBits L,
        k (x,x',y,y') * placedChannel E w 0 (block x z₁) (block y z₂) *
          placedChannel E w 1 (block y' z₂) c * placedChannel E w 2 c (block x' z₁)
  map_add' f g := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' a f := by simp [Finset.mul_sum,mul_assoc]

def pairKernel {F : Type*} [Field F] {L : ℕ} (p q : PairBits L → PairBits L → F) :
    KernelArgs L → F := fun z => p z.1 z.2.1 * q z.2.2.1 z.2.2.2

private theorem evalMask {F : Type*} [Field F] {L : ℕ} (E : Finset EdgeSlot)
    (a b : Option (Mask L)) (w : ChannelKey L → F) :
    evaluate E w (pairKernel (maskKernel a) (maskKernel b)) = placedFold E a b w := by
  rfl

private theorem evalProjection {F : Type*} [Field F] [CharZero F] {L : ℕ} (E : Finset EdgeSlot)
    (Λ : Finset (BasisLabel L)) (d : BasisLabel L → F) (w : ChannelKey L → F)
    (hc : ∀ h a b, channel w h a b = placedChannel E w h a b) :
    evaluate E w (pairKernel (projected Λ d) (projected Λ d)) = doubleProjection Λ Λ d d w := by
  unfold doubleProjection
  simp_rw [hc]
  rfl

theorem decomposition {F : Type*} [Field F] [CharZero F] {L M : ℕ}
    (Λ : Finset (BasisLabel L)) (d : BasisLabel L → ℚ)
    (m : Fin M → Mask L) (c : Fin M → ℤ)
    (hdecomp : ∀ x y : PairBits L,
      (if x = y then (1 : ℚ) else 0) =
        (∑ j ∈ Λ, d j * basisEntry j x * basisEntry j y) +
        ∑ i, (c i : ℚ) * swapEntry (m i) x y)
    (E : Finset EdgeSlot) (w : ChannelKey L → F)
    (hc : ∀ h a b, channel w h a b = placedChannel E w h a b) :
    placedFold E none none w =
      doubleProjection Λ Λ (fun j => (d j : F)) (fun j => (d j : F)) w +
      (∑ i, (c i : F) * placedFold E (some (m i)) none w) +
      (∑ j, (c j : F) * placedFold E none (some (m j)) w) -
      ∑ i, ∑ j, ((c i : F) * (c j : F)) * placedFold E (some (m i)) (some (m j)) w := by
  classical
  let I := maskKernel (F := F) (L := L) none
  let R := projected Λ (fun j => (d j : F))
  let S := fun i => maskKernel (F := F) (some (m i))
  have hkernel (x y : PairBits L) : I x y = R x y + ∑ i, (c i : F) * S i x y := by
    have eqn := congrArg (fun q : ℚ => (q : F)) (hdecomp x y)
    simpa [I,R,S,maskKernel,projected,swapEntry,apply_ite] using eqn
  have hp : pairKernel I I = pairKernel R R +
      (∑ i, (c i : F) • pairKernel (S i) I) +
      (∑ j, (c j : F) • pairKernel I (S j)) -
      ∑ i, ∑ j, ((c i : F) * (c j : F)) • pairKernel (S i) (S j) := by
    funext z
    rcases z with ⟨x,x',y,y'⟩
    simp only [Pi.add_apply,Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,pairKernel]
    simp only [← mul_assoc, ← Finset.sum_mul]
    have swap (j : Fin M) : (c j : F) * I x x' * S j y y' = I x x' * ((c j : F) * S j y y') := by ring
    have both (i j : Fin M) : (c i : F) * (c j : F) * S i x x' * S j y y' =
        ((c i : F) * S i x x') * ((c j : F) * S j y y') := by ring
    simp_rw [swap,both,← Finset.mul_sum,← Finset.sum_mul]
    rw [hkernel x x',hkernel y y']
    ring
  have he := congrArg (evaluate E w) hp
  simpa [I,R,S,map_sum,evalMask,evalProjection E Λ _ w hc] using he

end VWZClique.WeightedProof
end

/- UniformExpansion -/
section
open VWZClique VWZClique.RankSwap VWZClique.WeightedProof
namespace VWZClique.UniformFolds

attribute [instance] Expansion.finite

theorem windowExpansion_coefficients (K L : ℕ) :
    (∀ i : (windowExpansion K L).Index, |(((windowExpansion K L).coefficients i : ℤ) : ℝ)| ≤
      2^(lower K L)*4^(width K L)) ∧
    ∀ j : BasisLabel L, ∃ q : ℕ, q≤L ∧ ∃ z : ℤ,
      |(z:ℝ)| ≤ 1 + 3^L * (2^(lower K L)*4^(width K L)) ∧
      (windowExpansion K L).diagonal j = (z:ℚ)/2^q := by
  have hh := (Window.correct (lower K L) (width K L)).2.1
  exact ⟨fun i => term_bound hh i,fun j => ⟨denominatorExponent j,denominator_bits j,_,
    residual_bound (by positivity) hh j,rfl⟩⟩

theorem Expansion.decompose {L : ℕ} (q : Expansion L) (E : Finset EdgeSlot) (w : ChannelKey L → ℚ)
    (hc : ∀ h a b, channel w h a b = placedChannel E w h a b) :
    placedFold E none none w = doubleProjection q.labels q.labels q.diagonal q.diagonal w +
      (∑ i, (q.coefficients i : ℚ)*placedFold E (some (q.masks i)) none w) +
      (∑ j, (q.coefficients j : ℚ)*placedFold E none (some (q.masks j)) w) -
      ∑ i, ∑ j, ((q.coefficients i : ℚ)*(q.coefficients j : ℚ))*
        placedFold E (some (q.masks i)) (some (q.masks j)) w := by
  classical
  let e := (Fintype.equivFin q.Index).symm
  have hdecomp (x y : PairBits L) := q.identity x y
  have hx (x y : PairBits L) :
      (if x=y then (1:ℚ) else 0) =
        (∑ j ∈ q.labels, q.diagonal j * basisEntry j x * basisEntry j y) +
        ∑ i, (q.coefficients (e i) : ℚ)*swapEntry (q.masks (e i)) x y := by
    rw [e.sum_comp (fun i => (q.coefficients i : ℚ)*swapEntry (q.masks i) x y)]
    exact hdecomp x y
  have h := decomposition q.labels q.diagonal (fun i => q.masks (e i)) (fun i => q.coefficients (e i)) hx E w hc
  rw [e.sum_comp (fun i => (q.coefficients i : ℚ) * placedFold E (some (q.masks i)) none w),
    e.sum_comp (fun j => (q.coefficients j : ℚ) * placedFold E none (some (q.masks j)) w)] at h
  let f := fun i j => ((q.coefficients i : ℚ)*(q.coefficients j : ℚ))*placedFold E (some (q.masks i)) (some (q.masks j)) w
  have h₂ : (∑ i, ∑ j, f (e i) (e j)) = ∑ i, ∑ j, f i j := by
    simp_rw [fun i => e.sum_comp (f (e i))]
    exact e.sum_comp (fun i => ∑ j,f i j)
  rw [h₂] at h
  simpa only [f,Rat.cast_id] using h

end VWZClique.UniformFolds
end

/- DoubleIdentity -/
section
open VWZClique

namespace VWZClique.Double

variable {F : Type*} [Field F] [CharZero F] {L : ℕ}

noncomputable def leftEntry (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F)
    (w : ChannelKey L → F) (u : Node Λ) (v : Node Γ) : F :=
  (d u.1 * e v.1) * ∑ y : PairBits L, (basisEntry v.1 y : F) *
    ∑ x : PairBits L, (basisEntry u.1 x : F) * channel w 0 (block x u.2) (block y v.2)

noncomputable def midEntry (Γ : Finset (BasisLabel L)) (w : ChannelKey L → F)
    (v : Node Γ) (c : Block L) : F :=
  ∑ y' : PairBits L, (basisEntry v.1 y' : F) * channel w 1 (block y' v.2) c

noncomputable def rightEntry (Λ : Finset (BasisLabel L)) (w : ChannelKey L → F)
    (c : Block L) (u : Node Λ) : F :=
  ∑ x' : PairBits L, (basisEntry u.1 x' : F) * channel w 2 c (block x' u.2)

private theorem projection_subtype (S : Finset (BasisLabel L)) (d : BasisLabel L → F)
    (x x' : PairBits L) :
    projected S d x x' = ∑ j : S, d j * (basisEntry j x : F) * (basisEntry j x' : F) := by
  exact (Finset.sum_attach S (fun j => d j * (basisEntry j x : F) * (basisEntry j x' : F))).symm

private theorem distribute (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F)
    (x x' y y' : PairBits L) (a b c : F) :
    projected Λ d x x' * projected Γ e y y' * a * b * c =
    ∑ j : Λ, ∑ k : Γ, ((d j * e k) * ((basisEntry k y : F) * ((basisEntry j x : F) * a))) *
      (((basisEntry k y' : F) * b) * ((basisEntry j x' : F) * c)) := by
  simp only [projection_subtype, Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem reorder {Z C X J K R : Type*} [Fintype Z] [Fintype C] [Fintype X]
    [Fintype J] [Fintype K] [AddCommMonoid R]
    (f : Z → Z → C → X → X → X → X → J → K → R) :
    (∑ z, ∑ a, ∑ c, ∑ x, ∑ x', ∑ y, ∑ y', ∑ j, ∑ k, f z a c x x' y y' j k) =
    ∑ j, ∑ z, ∑ k, ∑ a, ∑ c, ∑ y, ∑ x, ∑ y', ∑ x', f z a c x x' y y' j k := by
  let E : (J × Z × K × Z × C × X × X × X × X) ≃
      (Z × Z × C × X × X × X × X × J × K) :=
    { toFun := fun ⟨j,z,k,a,c,y,x,y',x'⟩ => (z,a,c,x,x',y,y',j,k)
      invFun := fun ⟨z,a,c,x,x',y,y',j,k⟩ => (j,z,k,a,c,y,x,y',x')
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let g : Z × Z × C × X × X × X × X × J × K → R :=
    fun ⟨z,a,c,x,x',y,y',j,k⟩ => f z a c x x' y y' j k
  simpa only [Fintype.sum_prod_type, E, Equiv.coe_fn_mk, g] using (E.sum_comp g).symm

omit [CharZero F] in
private theorem contract_sums {C X : Type*} [Fintype C] [Fintype X]
    (q : F) (s : X → F) (a : X → X → F) (b : C → X → F) (h : C → X → F) :
    q * (∑ y, s y * ∑ x, a y x) * (∑ c, (∑ y', b c y') * ∑ x', h c x') =
    ∑ c, ∑ y, ∑ x, ∑ y', ∑ x', (q * (s y * a y x)) * (b c y' * h c x') := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum _ _ q, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum _ _ (s y), Finset.mul_sum _ _ q, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [← mul_assoc, Finset.mul_sum _ (b c), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y' _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x' _
  ring

/-- Expanding both projection kernels gives a three-matrix trace. -/
theorem trace_identity (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F) (w : ChannelKey L → F) :
    doubleProjection Λ Γ d e w =
      ∑ u : Node Λ, ∑ v : Node Γ,
        leftEntry Λ Γ d e w u v * ∑ c : Block L, midEntry Γ w v c * rightEntry Λ w c u := by
  classical
  unfold doubleProjection
  simp_rw [distribute]
  rw [reorder]
  let f := fun (u : Node Λ) (v : Node Γ) =>
    leftEntry Λ Γ d e w u v * ∑ c : Block L, midEntry Γ w v c * rightEntry Λ w c u
  change _ = ∑ u : Node Λ, ∑ v : Node Γ, f u v
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro z _
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  exact (contract_sums (d j * e k) (fun y => (basisEntry k y : F))
    (fun y x => (basisEntry j x : F) * channel w 0 (block x z) (block y a))
    (fun c y' => (basisEntry k y' : F) * channel w 1 (block y' a) c)
    (fun c x' => (basisEntry j x' : F) * channel w 2 c (block x' z))).symm

theorem matrix_trace_identity (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F)
    (w : ChannelKey L → F) :
    doubleProjection Λ Γ d e w = Matrix.trace
      (Matrix.of (leftEntry Λ Γ d e w) *
        (Matrix.of (midEntry Γ w) * Matrix.of (rightEntry Λ w))) := by
  exact trace_identity Λ Γ d e w

end VWZClique.Double
end

/- UniformFoldEvaluator -/
section
open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds

abbrev ProjectionEval (L : ℕ) := Expansion L → (ChannelKey L → ℚ) → ℚ

/-- Execute the same graph plan for every assignment-domain size.
    The two supplied subroutines evaluate sparse leaves and the pure projected term. -/
noncomputable def evaluatePlan {L : ℕ} (data : SimpleGraph V → Expansion L)
    (leaf : LeafEval L) (projection : ProjectionEval L) :
    {H : SimpleGraph V} → Plan H → (WeightKey (2^L) → ℚ) → ℚ
  | _,.leaf H hh,w => leaf H hh w
  | _,.split H π _ kids,w =>
    let q := data H
    let r := fun (a b : Option (Mask L)) => Round.mk H π a b
    let v := projection q ((r none none).inputs w)
    v + (∑ i, (q.coefficients i : ℚ) * evaluatePlan data leaf projection (kids .left)
          ((r (some (q.masks i)) none).apply w)) +
        (∑ j, (q.coefficients j : ℚ) * evaluatePlan data leaf projection (kids .right)
          ((r none (some (q.masks j))).apply w)) -
        ∑ i, ∑ j, ((q.coefficients i : ℚ) * (q.coefficients j : ℚ)) *
          evaluatePlan data leaf projection (kids .both)
            ((r (some (q.masks i)) (some (q.masks j))).apply w)

theorem input_supported {L : ℕ} (r : Round L) (w : WeightKey (2^L) → ℚ) (h : Fin 3) (a b : Block L) :
    channel (r.inputs w) h a b = placedChannel (slots r.π r.H) (r.inputs w) h a b := by
  unfold Round.inputs
  simp_rw [inputKey_eq]
  exact supported _ _ _ _ _ _

theorem evaluatePlan_correct {L : ℕ} (data : SimpleGraph V → Expansion L)
    (leaf : LeafEval L) (projection : ProjectionEval L)
    (hl : ∀ H h w, leaf H h w = weightedSum H w)
    (hp : ∀ (q : Expansion L) w, projection q w = doubleProjection q.labels q.labels q.diagonal q.diagonal w)
    {H : SimpleGraph V} (p : Plan H) (w : WeightKey (2^L) → ℚ) :
    evaluatePlan data leaf projection p w = weightedSum H w := by
  induction p generalizing w with
  | leaf H hh => exact hl H hh w
  | split H π hw kids ih =>
    let q := data H
    let E := slots π H
    let r (a b : Option (Mask L)) : Round L := ⟨H,π,a,b⟩
    let u := (r none none).inputs w
    have term (d : Branch) (a b : Option (Mask L)) (ha : a.isSome = first d) (hb : b.isSome = second d) :
        evaluatePlan data leaf projection (kids d) ((r a b).apply w) = placedFold E a b u :=
      (ih d ((r a b).apply w)).trans ((r a b).exact_value w d ha hb)
    have he := q.decompose E u (input_supported (r none none) w)
    change projection q u +
        (∑ i, (q.coefficients i : ℚ) * evaluatePlan data leaf projection (kids .left)
          ((r (some (q.masks i)) none).apply w)) +
        (∑ j, (q.coefficients j : ℚ) * evaluatePlan data leaf projection (kids .right)
          ((r none (some (q.masks j))).apply w)) -
        (∑ i, ∑ j, ((q.coefficients i : ℚ) * (q.coefficients j : ℚ)) *
          evaluatePlan data leaf projection (kids .both)
            ((r (some (q.masks i)) (some (q.masks j))).apply w)) = _
    simp_rw [fun i => term .left (some (q.masks i)) none rfl rfl,
      fun j => term .right none (some (q.masks j)) rfl rfl,
      fun i j => term .both (some (q.masks i)) (some (q.masks j)) rfl rfl,hp]
    calc
      _ = placedFold E none none u := by simpa only [Rat.cast_id] using he.symm
      _ = _ := input_exact π H w

open SparseProof in
theorem sparseLeaf_iterations (H : SimpleGraph V) (hw : ¬ HasWedges H) (n : ℕ) (hn : 1 ≤ n) :
    let key := leafKey H hw
    Fintype.card (Assignment key n none) * (∑ b : Bag, Fintype.card (Assignment key n (some b))) ≤
      Fintype.card Bag * n^5 := by
  let key := leafKey H hw
  have hh := Classical.choose_spec (matching_partition H hw)
  have root : Fintype.card (Assignment key n none) ≤ n^3 := by
    simpa [Assignment,key,leafKey] using Nat.pow_le_pow_right hn hh.1
  have bag (b : Bag) : Fintype.card (Assignment key n (some b)) ≤ n^2 := by
    simpa [Assignment,key,leafKey] using Nat.pow_le_pow_right hn (hh.2.1 b)
  have whole : (∑ b : Bag, Fintype.card (Assignment key n (some b))) ≤ Fintype.card Bag*n^2 := by
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun b _ => bag b)
  exact (Nat.mul_le_mul root whole).trans_eq (by ring)

theorem evaluateWithSparse_correct {L : ℕ} (data : SimpleGraph V → Expansion L)
    (projection : ProjectionEval L)
    (hp : ∀ (q : Expansion L) w, projection q w = doubleProjection q.labels q.labels q.diagonal q.diagonal w)
    (H : SimpleGraph V) (w : WeightKey (2^L) → ℚ) :
    evaluatePlan data (sparseLeaf L) projection (fixed H) w = weightedSum H w :=
  evaluatePlan_correct data _ projection (sparseLeaf_correct L) hp _ _

/-- Each projected contribution is the trace of the three explicit channel matrices. -/
noncomputable def traceProjection (L : ℕ) : ProjectionEval L := fun q w =>
  Matrix.trace (Matrix.of (Double.leftEntry q.labels q.labels q.diagonal q.diagonal w) *
    (Matrix.of (Double.midEntry q.labels w) * Matrix.of (Double.rightEntry q.labels w)))

theorem traceProjection_correct {L : ℕ} (q : Expansion L) (w : ChannelKey L → ℚ) :
    traceProjection L q w = doubleProjection q.labels q.labels q.diagonal q.diagonal w :=
  (Double.matrix_trace_identity _ _ _ _ _).symm

/-- The table of integer cutoffs is indexed by the number of edges of the current
pattern. The same cutoffs and the same finite branching plan apply at every length. -/
noncomputable def evaluateWindow (K : ℕ → ℕ) (L : ℕ) (H : SimpleGraph V)
    (w : WeightKey (2^L) → ℚ) : ℚ :=
  evaluatePlan (fun G => windowExpansion (K (Nat.card G.edgeSet)) L)
    (sparseLeaf L) (traceProjection L) (fixed H) w

theorem evaluateWindow_correct (K : ℕ → ℕ) (L : ℕ) (H : SimpleGraph V)
    (w : WeightKey (2^L) → ℚ) : evaluateWindow K L H w = weightedSum H w :=
  evaluateWithSparse_correct _ _ traceProjection_correct _ _

/-- On a Boolean source table every subproblem reached by the recursion returns
an integer between zero and the number of assignments on the nine vertices. -/
theorem evaluateWindow_on_trace (K : ℕ → ℕ) {L : ℕ} {H H' : SimpleGraph V}
    {p : Plan H} {rs : List (Round L)} (tr : Trace L p H' rs)
    (w : WeightKey (2^L) → ℚ) (hw : ∀ k, Binary (w k)) :
    ∃ z : ℕ, z ≤ (2^L)^9 ∧ evaluateWindow K L H' (follow rs w) = (z:ℚ) := by
  rw [evaluateWindow_correct]
  exact tr.integer_output w hw

end VWZClique.UniformFolds
end

/- DoubleEstimates -/
section
open VWZClique Real

namespace VWZClique.Double

noncomputable def side (n : ℕ) (δ : ℝ) : ℕ := ⌈(n : ℝ) ^ (3-δ)⌉₊
noncomputable def packets (n : ℕ) (δ : ℝ) : ℕ := ⌈(n : ℝ) ^ δ⌉₊

theorem side_pos {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) : 1 ≤ side n δ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hn' _)

theorem node_fits {n a : ℕ} (hn : 1 ≤ n) (δ : ℝ)
    (ha : (a : ℝ) ≤ (n : ℝ)^(2-δ)) : a*n ≤ side n δ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := mul_le_mul_of_nonneg_right ha hn'.le
  have hh : (n : ℝ)^(2-δ) * n = (n : ℝ)^(3-δ) := by
    rw [show (3:ℝ)-δ = (2-δ)+1 by ring, Real.rpow_add_one hn'.ne']
  have hh' := h.trans (hh.le.trans (Nat.le_ceil _))
  exact_mod_cast hh'

theorem block_fits {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) : n^3 ≤ packets n δ * side n δ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := mul_le_mul (Nat.le_ceil ((n : ℝ)^δ)) (Nat.le_ceil ((n : ℝ)^(3-δ)))
    (Real.rpow_nonneg hn'.le _) (by positivity)
  rw [← Real.rpow_add hn',show δ+(3-δ) = (3:ℝ) by ring] at h
  norm_num at h
  exact_mod_cast h

theorem ceil_bound {x : ℝ} (hx : 1 ≤ x) : (⌈x⌉₊ : ℝ) ≤ 2*x := by
  have h := Nat.ceil_lt_add_one (by linarith : 0 ≤ x)
  linarith

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

/- DoubleCost -/
section
open Real

namespace VWZClique.Double

private theorem exponent_product (x : ℝ) (hx : 1 ≤ x) {p q b : ℝ} (hab : p+q ≤ b) :
    x^p * x^q ≤ x^b := by
  rw [← Real.rpow_add (by linarith : 0 < x)]
  exact Real.rpow_le_rpow_of_exponent_le hx hab

noncomputable def rate (ω δ σ : ℝ) : ℝ := 3*ω-(ω-1)*δ+4*σ
noncomputable def coefficient (ω σ M H K : ℝ) : ℝ :=
  3*(M+129) + K*H + 5 + 2*(M*2^(ω+σ))

theorem coefficient_pos {ω σ M H K : ℝ} (hM : 0 < M) (hH : 0 < H) (hK : 0 ≤ K) :
    0 < coefficient ω σ M H K := by unfold coefficient; positivity

theorem budget_estimate {ω δ σ M H K : ℝ} (hω : 2 ≤ ω) (hδ : 0 ≤ δ)
    (hδ' : δ ≤ 1) (hσ : 0 ≤ σ) (hM : 0 ≤ M) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (a g n p T q : ℕ) (hn : 1 ≤ n)
    (ha : (a : ℝ) ≤ (n : ℝ)^(2-δ)) (hg : (g : ℝ) ≤ (n : ℝ)^(2-δ))
    (hp : (p : ℝ) ≤ M*(n : ℝ)^(ω+σ))
    (hT : (T : ℝ) ≤ K*H*((n : ℝ)^(2+σ)))
    (hq : (q : ℝ) ≤ M*(side n δ : ℝ)^(ω+σ)) :
    (budget a g n p T q (packets n δ) : ℝ) ≤
      coefficient ω σ M H K * (n : ℝ)^(rate ω δ σ) := by
  let x : ℝ := n
  let W := x^(rate ω δ σ)
  have hx : 1 ≤ x := by change (1:ℝ) ≤ (n:ℝ); exact_mod_cast hn
  have hx' : 0 < x := by linarith
  have hωσ : 0 ≤ ω+σ := by linarith
  have hs : (side n δ : ℝ) ≤ 2*x^(3-δ) :=
    ceil_bound (Real.one_le_rpow hx (by linarith))
  have ht : (packets n δ : ℝ) ≤ 2*x^δ := ceil_bound (Real.one_le_rpow hx hδ)
  have e₁ : (4-δ)+(ω+σ) ≤ rate ω δ σ := by
    unfold rate
    nlinarith [mul_nonneg (by linarith : 0 ≤ ω-2) (by linarith : 0 ≤ 2-δ)]
  have e₂ : (4-δ)+(2+σ) ≤ rate ω δ σ := by linarith
  have e₃ : δ+(6-2*δ) ≤ rate ω δ σ := by linarith
  have e₄ : 6-2*δ ≤ rate ω δ σ := by linarith
  have e₅ : δ+(3-δ)*(ω+σ) ≤ rate ω δ σ := by
    unfold rate; nlinarith [mul_nonneg hδ hσ]
  have a2 (v : ℕ) (hv : (v : ℝ) ≤ x^(2-δ)) : (v : ℝ)*x^2 ≤ x^(4-δ) := by
    calc
      _ ≤ x^(2-δ)*x^(2:ℝ) := by simpa using mul_le_mul_of_nonneg_right hv (sq_nonneg x)
      _ ≤ _ := exponent_product x hx (by linarith)
  have a1 (v : ℕ) (hv : (v : ℝ) ≤ x^(2-δ)) : (v : ℝ)*x ≤ x^(3-δ) := by
    calc
      _ ≤ x^(2-δ)*x^(1:ℝ) := by simpa using mul_le_mul_of_nonneg_right hv hx'.le
      _ ≤ _ := exponent_product x hx (by linarith)
  have h2 : x^2 ≤ x^(ω+σ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (show (2:ℝ) ≤ ω+σ by linarith)
  have hp' : (p : ℝ) + 129*x^2 ≤ (M+129)*x^(ω+σ) := by
    change (p : ℝ) ≤ M*x^(ω+σ) at hp
    linarith
  have prep (v : ℕ) (hv : (v : ℝ) ≤ x^(2-δ)) :
      (v : ℝ)*x^2*((p : ℝ)+129*x^2) ≤ (M+129)*W := by
    calc
      _ ≤ x^(4-δ)*((M+129)*x^(ω+σ)) := mul_le_mul (a2 _ hv) hp' (by positivity) (by positivity)
      _ = (M+129)*(x^(4-δ)*x^(ω+σ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (exponent_product x hx e₁) (by positivity)
  have trans : (a : ℝ)*x^2*(T : ℝ) ≤ (K*H)*W := by
    calc
      _ ≤ x^(4-δ)*(K*H*x^(2+σ)) := mul_le_mul (a2 _ ha) hT (by positivity) (by positivity)
      _ = (K*H)*(x^(4-δ)*x^(2+σ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (exponent_product x hx e₂) (by positivity)
  let N : ℝ := (a : ℝ)*x*((g : ℝ)*x)
  have pairs : N ≤ x^(6-2*δ) := by
    calc
      _ ≤ x^(3-δ)*x^(3-δ) := mul_le_mul (a1 _ ha) (a1 _ hg) (by positivity) (by positivity)
      _ ≤ _ := exponent_product x hx (by linarith)
  have pairs' : N ≤ W := pairs.trans (Real.rpow_le_rpow_of_exponent_le hx e₄)
  have tpair : (packets n δ : ℝ)*N ≤ 2*W := by
    calc
      _ ≤ (2*x^δ)*x^(6-2*δ) := mul_le_mul ht pairs (by dsimp [N]; positivity) (by positivity)
      _ = 2*(x^δ*x^(6-2*δ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (exponent_product x hx e₃) (by norm_num)
  have q' : (q : ℝ) ≤ (M*2^(ω+σ))*x^((3-δ)*(ω+σ)) := by
    calc
      _ ≤ M*(side n δ : ℝ)^(ω+σ) := hq
      _ ≤ M*(2*x^(3-δ))^(ω+σ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hs hωσ) hM
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),
        ← Real.rpow_mul hx'.le]; ring
  have tq : (packets n δ : ℝ)*(q : ℝ) ≤ (2*(M*2^(ω+σ)))*W := by
    calc
      _ ≤ (2*x^δ)*((M*2^(ω+σ))*x^((3-δ)*(ω+σ))) := mul_le_mul ht q' (by positivity) (by positivity)
      _ = (2*(M*2^(ω+σ)))*(x^δ*x^((3-δ)*(ω+σ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (exponent_product x hx e₅) (by positivity)
  unfold budget
  push_cast
  change ((a : ℝ)*x^2*((p : ℝ)+129*x^2)+(a:ℝ)*x^2*(T:ℝ)+N) +
    ((g:ℝ)*x^2*((p:ℝ)+129*x^2)+(a:ℝ)*x^2*((p:ℝ)+129*x^2)) +
    ((packets n δ:ℝ)*((q:ℝ)+N)+2*N) ≤ coefficient ω σ M H K*W
  unfold coefficient
  linarith only [prep a ha, prep g hg, trans, pairs', tpair, tq]

end VWZClique.Double
end

/- IntegerTiling -/
section
namespace VWZClique.Double.IntegerTiling

theorem cut_window (L q : ℕ) (hq : 0<q) :
    ((L/q:ℕ):ℝ) ≤ (L:ℝ)/(q:ℝ) ∧ (L:ℝ)/(q:ℝ) < ((L/q:ℕ):ℝ)+1 := by
  have hr : (0:ℝ) < q := by exact_mod_cast hq
  constructor
  · apply (le_div_iff₀ hr).2
    exact_mod_cast Nat.div_mul_le_self L q
  · apply (div_lt_iff₀ hr).2
    exact_mod_cast (show L < (L/q+1)*q by simpa [Nat.mul_comm] using Nat.lt_mul_div_succ L hq)

/-- The fixed integer schedule realizes power-of-two tiles within a factor
of two of the desired real size. No real powers occur in the schedule. -/
theorem shape_bound (L q : ℕ) (hq : 0<q) :
    ((2:ℝ)^L)^(3-(1:ℝ)/q) ≤ (side L q : ℝ) ∧
    (side L q : ℝ) ≤ 2*((2:ℝ)^L)^(3-(1:ℝ)/q) ∧
    (blocks L q : ℝ) ≤ ((2:ℝ)^L)^((1:ℝ)/q) := by
  obtain ⟨hl,hu⟩ := cut_window L q hq
  have hcut : L/q ≤ 3*L := (Nat.div_le_self L q).trans (by omega)
  have hleft : (L:ℝ)*(3-(1:ℝ)/q) ≤ ((3*L-L/q:ℕ):ℝ) := by
    rw [Nat.cast_sub hcut]
    push_cast
    linarith [show (L:ℝ) * (1/q) = (L:ℝ)/q by ring]
  have hright : ((3*L-L/q:ℕ):ℝ) ≤ 1+(L:ℝ)*(3-(1:ℝ)/q) := by
    rw [Nat.cast_sub hcut]
    push_cast
    linarith [show (L:ℝ) * (1/q) = (L:ℝ)/q by ring]
  have hb : ((L/q:ℕ):ℝ) ≤ (L:ℝ)*((1:ℝ)/q) := by simpa [div_eq_mul_inv] using hl
  have hw : (1:ℝ) ≤ 2 := by norm_num
  have to_power (t : ℝ) : ((2:ℝ)^L)^t = (2:ℝ)^((L:ℝ)*t) := by
    rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
  rw [to_power, to_power]
  simp only [side,blocks,Nat.cast_pow,Nat.cast_ofNat,← Real.rpow_natCast]
  refine ⟨Real.rpow_le_rpow_of_exponent_le hw hleft,?_,Real.rpow_le_rpow_of_exponent_le hw hb⟩
  convert Real.rpow_le_rpow_of_exponent_le hw hright using 1
  rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]

end VWZClique.Double.IntegerTiling
end

/- UniformProjectionBudget -/
section
namespace VWZClique.UniformFolds

/-- Both projected matrix dimensions fit a square tile. The third dimension
is exactly partitioned by the integer block schedule. -/
theorem projectionShape {q : ℕ} (hq : 0 < q) (L a : ℕ)
    (ha : (a:ℝ) ≤ ((2:ℝ)^L)^(2-(1:ℝ)/q)) :
    a * 2^L ≤ Double.IntegerTiling.side L q ∧
    Double.IntegerTiling.blocks L q * Double.IntegerTiling.side L q = (2^L)^3 := by
  refine ⟨?_,Double.IntegerTiling.exact_shape L q⟩
  have hn : 0 < (2:ℝ)^L := by positivity
  have h : (a:ℝ)*(2:ℝ)^L ≤ (((2:ℝ)^L)^(2-(1:ℝ)/q))*(2:ℝ)^L :=
    mul_le_mul_of_nonneg_right ha hn.le
  rw [← Real.rpow_add_one hn.ne',show (2:ℝ)-1/q+1 = 3-1/q by ring] at h
  exact_mod_cast h.trans (Double.IntegerTiling.shape_bound L q hq).1

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

/-- A fixed square multiplication procedure gives one uniform bound for all
positive integer tile parameters, including the ones chosen for different fold levels. -/
theorem projectionWork_rate (ω σ : ℝ) (hω : 2 ≤ ω) (hσ : 0 < σ)
    (mm : ℕ → ℕ) (M : ℝ) (hM : 0 < M)
    (hmm : ∀ n : ℕ, 1 ≤ n → (mm n : ℝ) ≤ M*(n:ℝ)^(ω+σ)) (T : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, 0<q → ∀ L a : ℕ,
      (a:ℝ) ≤ ((2:ℝ)^L)^(2-(1:ℝ)/q) →
      (projectionWork mm T q L a : ℝ) ≤ C*((2:ℝ)^L)^(3*ω-(ω-1)*((1:ℝ)/q)+4*σ) := by
  obtain ⟨H,hH,hL⟩ := Double.length_bound σ hσ
  let M' := M * (2:ℝ)^(ω+σ)
  have hM' : 0 < M' := by dsimp [M']; positivity
  have hωσ : 0 ≤ ω+σ := by linarith
  have hm' : M ≤ M' := le_mul_of_one_le_right hM.le (Real.one_le_rpow (by norm_num) hωσ)
  refine ⟨Double.coefficient ω σ M' H T,Double.coefficient_pos hM' hH (Nat.cast_nonneg _),?_⟩
  intro q hq L a ha
  have active : effectiveTile q L a = q := if_pos (projectionShape hq L a ha).1
  let n : ℕ := 2^L
  let s := Double.IntegerTiling.side L q
  let δ : ℝ := 1/q
  have hqr : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd' : δ ≤ 1 := (div_le_one₀ (by linarith : (0:ℝ)<q)).2 hqr
  have hn : 1 ≤ n := Nat.one_le_pow _ _ (by decide)
  have hx : (n:ℝ) = (2:ℝ)^L := by simp [n]
  have hx' : 0 < (n:ℝ) := by exact_mod_cast hn
  obtain ⟨_,hs,hb⟩ := Double.IntegerTiling.shape_bound L q hq
  change (s:ℝ) ≤ 2*((2:ℝ)^L)^(3-δ) at hs
  change (Double.IntegerTiling.blocks L q:ℝ) ≤ ((2:ℝ)^L)^δ at hb
  rw [← hx] at hs hb ha
  have hs' : (s:ℝ) ≤ 2*(Double.side n δ:ℝ) :=
    hs.trans (mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by norm_num))
  have ht : Double.IntegerTiling.blocks L q ≤ Double.packets n δ := by
    exact_mod_cast hb.trans (Nat.le_ceil _)
  have hw : 1 ≤ s := Nat.one_le_pow _ _ (by decide)
  have hpc : (mm n:ℝ) ≤ M'*(n:ℝ)^(ω+σ) :=
    (hmm n hn).trans (mul_le_mul_of_nonneg_right hm' (by positivity))
  have hsc : (mm s:ℝ) ≤ M'*(Double.side n δ:ℝ)^(ω+σ) := by
    calc
      _ ≤ M*(s:ℝ)^(ω+σ) := hmm s hw
      _ ≤ M*(2*(Double.side n δ:ℝ))^(ω+σ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hs' hωσ) hM.le
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity)]; dsimp [M']; ring
  have h4 : (4:ℝ)^L = (n:ℝ)^2 := by rw [hx,←pow_mul,Nat.mul_comm,pow_mul]; norm_num
  have htrans : ((T*(L+1)*4^L : ℕ):ℝ) ≤ (T:ℝ)*H*(n:ℝ)^(2+σ) := by
    have hh := hL L
    rw [← hx] at hh
    push_cast
    rw [h4, Real.rpow_add hx', Real.rpow_two]
    calc
      _ ≤ (T:ℝ)*(H*(n:ℝ)^σ)*(n:ℝ)^2 := by gcongr
      _ = _ := by ring
  have bud := Double.budget_estimate hω hd.le hd' hσ.le hM'.le hH.le (Nat.cast_nonneg T)
    a a n (mm n) (T*(L+1)*4^L) (mm s) hn ha ha hpc htrans hsc
  have hmono : projectionWork mm T q L a ≤
      Double.budget a a n (mm n) (T*(L+1)*4^L) (mm s) (Double.packets n δ) := by
    simp only [projectionWork,active,Double.budget]
    dsimp only [n,s] at *
    gcongr
  exact (Nat.cast_le.mpr hmono).trans (by simpa only [hx,Double.rate,δ] using bud)

end VWZClique.UniformFolds
end

/- WeightedEstimates -/
section
namespace VWZClique.WeightedProof

theorem recurrence_bound {n ω α β δ η C D M : ℝ} (hn : 1 ≤ n) (hω : 2 ≤ ω)
    (hα : 0 < α) (hα' : α ≤ 1) (hβa : β ≤ α/2) (hβd : β ≤ δ)
    (hδ : 0 < δ) (hη : 0 < η) (hc : 0 ≤ C) (hd : 0 ≤ D)
    (hm : 0 ≤ M) (hm' : M ≤ n^(α/8)) :
    C*n^(3*ω-(ω-1)*δ+η) +
        (2*M+M^2)*(D*n^(3*ω-α+η)+2)+3 ≤
      (C+3*(D+2)+3)*n^(3*ω-β+η) := by
  have hn0 : 0 ≤ n := by linarith
  let x := n^(α/8)
  let y := n^(3*ω-α+η)
  let z := n^(3*ω-β+η)
  have hx : 1 ≤ x := Real.one_le_rpow hn (by positivity)
  have hy : 1 ≤ y := Real.one_le_rpow hn (by linarith)
  have hz : 1 ≤ z := Real.one_le_rpow hn (by linarith)
  have hxy : x^2*y ≤ z := by
    calc
      x^2*y = n^((α/8+α/8)+(3*ω-α+η)) := by
        simp only [Real.rpow_add (by linarith : 0<n),pow_two,x,y,mul_assoc]
      _ ≤ z := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have hp : C*n^(3*ω-(ω-1)*δ+η) ≤ C*z := by
    apply mul_le_mul_of_nonneg_left _ hc
    apply Real.rpow_le_rpow_of_exponent_le hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hω) hδ.le]
  have hm2 : 2*M+M^2 ≤ 3*x^2 := by
    have hsq : M^2 ≤ x^2 := by gcongr
    have hx' : x ≤ x^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by linarith : 0 ≤ x)]
    change M ≤ x at hm'
    linarith
  have hDy : D*y+2 ≤ (D+2)*y := by nlinarith
  have hprod : (2*M+M^2)*(D*y+2) ≤ (3*x^2)*((D+2)*y) :=
    mul_le_mul hm2 hDy (by nlinarith [mul_nonneg hd (by linarith : 0 ≤ y)]) (by positivity)
  calc
    _ ≤ C*z+(3*x^2)*((D+2)*y)+3 := by linarith
    _ = C*z+3*(D+2)*(x^2*y)+3 := by ring
    _ ≤ C*z+3*(D+2)*z+3*z := by
      gcongr
      linarith
    _ = _ := by ring

end VWZClique.WeightedProof
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

/-- Sum the work over the individual masks actually passed to the recursive
calls, including the folded weight table of each distinct child invocation. -/
noncomputable def traversedWork (mm : ℕ → ℕ) (T U G L : ℕ) :
    {H : SimpleGraph V} → Plan H → (WeightKey (2^L) → ℚ) → ℕ
  | _,.leaf _ _,_ => U*(2^L)^5
  | _,.split H π _ kids,w =>
    let e := Nat.card H.edgeSet
    let q := windowExpansion (windowAt e) L
    let charged (d : Branch) (a b : Option (Mask L)) :=
      G*(2^L)^2 + traversedWork mm T U G L (kids d) ((Round.mk H π a b).apply w) + 3
    projectionWork mm T (tileAt e) L q.labels.card + U*(2^L)^5 +
      (∑ i, charged .left (some (q.masks i)) none) +
      (∑ j, charged .right none (some (q.masks j))) +
      (∑ i, ∑ j, charged .both (some (q.masks i)) (some (q.masks j))) + 3

theorem traversedWork_eq (mm : ℕ → ℕ) (T U G L : ℕ) {H : SimpleGraph V}
    (p : Plan H) (w : WeightKey (2^L) → ℚ) :
    traversedWork mm T U G L p w = planWork mm T U G L p := by
  induction p generalizing w with
  | leaf => rfl
  | split H π hw kids ih =>
    simp only [traversedWork,planWork,splitWork]
    simp_rw [ih]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,pow_two,Nat.mul_assoc]

private theorem local_le {n ω β η : ℝ} (hn : 1 ≤ n) (hω : 2 ≤ ω) (hβ : β ≤ 1)
    (hη : 0 ≤ η) (U : ℕ) :
    (U:ℝ)*n^5 ≤ (U:ℝ)*n^(3*ω-β+η) := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num; linarith)

private theorem splitWork_le (m p u a b c : ℕ) {P B : ℝ}
    (hp : (p:ℝ) ≤ P) (ha : (u:ℝ)+(a:ℝ)+3 ≤ B) (hb : (u:ℝ)+(b:ℝ)+3 ≤ B)
    (hc : (u:ℝ)+(c:ℝ)+3 ≤ B) :
    (splitWork m p u a b c : ℝ) ≤ P+(2*(m:ℝ)+(m:ℝ)^2)*B+3 := by
  unfold splitWork
  push_cast
  calc
    _ ≤ P+(m:ℝ)*B+(m:ℝ)*B+(m:ℝ)^2*B+3 := by gcongr
    _ = _ := by ring

/-- A uniform saving for all nine-vertex plans follows by applying this bound at k = 36. All three recursive multiplicities are charged at every split. -/
theorem planWork_rate (ω σ : ℝ) (hω : 2 ≤ ω) (hσ : 0 < σ)
    (mm : ℕ → ℕ) (M : ℝ) (hM : 0 < M)
    (hmm : ∀ n : ℕ, 1 ≤ n → (mm n : ℝ) ≤ M*(n:ℝ)^(ω+σ))
    (T U G k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ L ≥ N, ∀ H : SimpleGraph V, ∀ p : Plan H,
      Nat.card H.edgeSet ≤ k →
      (planWork mm T U G L p : ℝ) ≤ C*((2:ℝ)^L)^(3*ω-(levelSaving k).val+4*σ) := by
  obtain ⟨Q,hQ,project⟩ := projectionWork_rate ω σ hω hσ mm M hM hmm T
  induction k with
  | zero =>
    refine ⟨(U:ℝ)+1,by positivity,0,?_⟩
    intro L _ H p he
    cases p with
    | leaf H hh =>
      let n := (2:ℝ)^L
      have hn : 1 ≤ n := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
      have h := local_le hn hω (levelSaving 0).le_one (by positivity : 0 ≤ 4*σ) U
      apply le_trans (by simpa only [planWork,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using h)
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _)
    | split H π hw kids =>
      have dec := branch_smaller H π hw .left
      omega
  | succ k old =>
    obtain ⟨D,hD,N,old⟩ := old
    let a := levelSaving k
    let cut := selectCut a
    let b := levelSaving (k+1)
    let δ : ℝ := 1/cut.tile
    have htile : 0 < cut.tile := cut.tile_pos
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδ' : δ ≤ 1 := (div_le_one₀ (by exact_mod_cast htile)).2 (by exact_mod_cast htile)
    have hba : b.val ≤ a.val/2 := min_le_left _ _
    have hbd : b.val ≤ δ := min_le_right _ _
    let D' := (G:ℝ)+D+1
    let C := max D (max (U:ℝ) ((Q+U)+3*(D'+2)+3))
    have hD' : 0 ≤ D' := by dsimp [D']; positivity
    have hC : 0 < C := hD.trans_le (le_max_left _ _)
    refine ⟨C,hC,max N cut.threshold,?_⟩
    intro L hL H p hcount
    let n := (2:ℝ)^L
    have hn : 1 ≤ n := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
    have hn' : 0 < n := by linarith
    have hN : N ≤ L := (le_max_left _ _).trans hL
    have hsmall : 0 ≤ n^(3*ω-b.val+4*σ) := Real.rpow_nonneg hn'.le _
    by_cases prev : Nat.card H.edgeSet ≤ k
    · have h := old L hN H p prev
      calc
        _ ≤ D*n^(3*ω-a.val+4*σ) := h
        _ ≤ C*n^(3*ω-b.val+4*σ) := mul_le_mul (le_max_left _ _)
          (Real.rpow_le_rpow_of_exponent_le hn (by linarith [a.pos])) (by positivity) hC.le
    have he : Nat.card H.edgeSet = k+1 := by omega
    cases p with
    | leaf H hw =>
      have h := local_le hn hω b.le_one (by positivity : 0 ≤ 4*σ) U
      apply le_trans (by simpa only [planWork,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using h)
      exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hsmall
    | split H π hw kids =>
      let q := windowExpansion cut.window L
      let m := Fintype.card q.Index
      have hwin : windowAt (Nat.card H.edgeSet) = cut.window := by rw [he]; rfl
      have htil : tileAt (Nat.card H.edgeSet) = cut.tile := by rw [he]; rfl
      obtain ⟨hm,hr⟩ := cut.rates L ((le_max_right _ _).trans hL)
      have hproj := project cut.tile cut.tile_pos L q.labels.card hr
      let Y := n^(3*ω-a.val+4*σ)
      have h2 : n^2 ≤ Y := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num; linarith [a.le_one])
      have h1 : 1 ≤ Y := Real.one_le_rpow hn (by linarith [a.le_one])
      have branch (d : Branch) :
          ((G*(2^L)^2:ℕ):ℝ)+(planWork mm T U G L (kids d):ℝ)+3 ≤ D'*Y+2 := by
        have less := branch_smaller H π hw d
        have childBound := old L hN _ (kids d) (by omega)
        change (planWork mm T U G L (kids d):ℝ) ≤ D*Y at childBound
        push_cast
        change (G:ℝ)*n^2 + _ + 3 ≤ _
        calc
          _ ≤ (G:ℝ)*Y + D*Y + (Y+2) := by gcongr; linarith
          _ = _ := by dsimp [D']; ring
      let X := n^(3*ω-(ω-1)*δ+4*σ)
      have h5 : n^5 ≤ X := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le hn
        norm_num
        nlinarith [mul_nonneg (by linarith : 0 ≤ ω-1) (sub_nonneg.mpr hδ')]
      have hp : ((projectionWork mm T cut.tile L q.labels.card + U*(2^L)^5 : ℕ):ℝ) ≤ (Q+U)*X := by
        push_cast
        rw [add_mul]
        exact add_le_add hproj (mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg _))
      have hs := splitWork_le m _ _ _ _ _ hp (branch .left) (branch .right) (branch .both)
      have ht := WeightedProof.recurrence_bound hn hω a.pos a.le_one hba hbd hδ
        (by positivity : 0 < 4*σ) (show 0 ≤ Q+(U:ℝ) by positivity) hD'
        (Nat.cast_nonneg m) hm
      simp only [planWork,hwin,htil]
      exact (hs.trans ht).trans (mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_max_right _ _)) hsmall)

private theorem box_bound {I : Type*} [Fintype I] (f : ℕ → I → ℕ) {N L : ℕ}
    (hl : L < N) (i : I) : f L i ≤ ∑ l ∈ Finset.range N, ∑ j : I, f l j := by
  have h₁ : f L i ≤ ∑ j : I, f L j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (f L j)) (Finset.mem_univ i)
  exact h₁.trans <| Finset.single_le_sum (fun l _ => Nat.zero_le (∑ j : I, f l j))
    (Finset.mem_range.mpr hl)

/-- Fixed nine-vertex plans and the finitely many lengths below the window
threshold can all be covered by one scalar-work constant. -/
theorem planWork_allLengths (ω σ : ℝ) (hω : 2 ≤ ω) (hσ : 0 < σ)
    (mm : ℕ → ℕ) (M : ℝ) (hM : 0 < M)
    (hmm : ∀ n : ℕ, 1 ≤ n → (mm n : ℝ) ≤ M*(n:ℝ)^(ω+σ)) (T U G : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ L : ℕ, ∀ H : SimpleGraph V, ∀ w : WeightKey (2^L) → ℚ,
      (traversedWork mm T U G L (fixed H) w : ℝ) ≤
        C*((2:ℝ)^L)^(3*ω-(levelSaving 36).val+4*σ) := by
  classical
  obtain ⟨C,hC,N,hL⟩ := planWork_rate ω σ hω hσ mm M hM hmm T U G 36
  let _ : Fintype (SimpleGraph V) := Fintype.ofFinite _
  let f (l : ℕ) (g : SimpleGraph V) := planWork mm T U G l (fixed g)
  let B : ℕ := ∑ l ∈ Finset.range N, ∑ g : SimpleGraph V, f l g
  let D := max C (B:ℝ)
  have hD : 0 < D := hC.trans_le (le_max_left _ _)
  refine ⟨D,hD,?_⟩
  intro L H w
  rw [traversedWork_eq]
  by_cases hl : N ≤ L
  · exact (hL L hl H (fixed H) (edge_limit H)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have h : f L H ≤ B := box_bound f (by omega : L < N) H
    have h₃ : (f L H:ℝ) ≤ (B:ℝ) := Nat.cast_le.mpr h
    refine (h₃.trans (le_max_right _ _)).trans (le_mul_of_one_le_right hD.le ?_)
    apply Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
    linarith [(levelSaving 36).le_one]

end VWZClique.UniformFolds
end

/- TraceDyadicData -/
section
namespace VWZClique.TraceDyadic
open RankSwap UniformFolds Double

/-- The assignment side and common denominator of each diagonal residual. -/
def D (L : ℕ) : ℤ := 2^L

theorem D_pos (L : ℕ) : 0 < D L := by unfold D; positivity
theorem D_one (L : ℕ) : 1 ≤ D L := D_pos L

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

private theorem bit_cast {x : ℚ} (hx : Binary x) : (bitInt x : ℚ) = x := by
  rcases hx with rfl | rfl <;> norm_num [bitInt]

private theorem bit_bound (x : ℚ) : |bitInt x| ≤ 1 := by unfold bitInt; split <;> norm_num

theorem channel_cast {L : ℕ} (w : ChannelKey L → ℚ) (hw : ∀ k, Binary (w k))
    (h : Fin 3) (a b : Block L) : (channelInt w h a b : ℚ) = channel w h a b := by
  simp only [channelInt,channel,Int.cast_mul,Int.cast_prod,fun k => bit_cast (hw k)]

theorem mul_bound {a b A B : ℤ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a*b| ≤ A*B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

theorem channel_bound {L : ℕ} (w : ChannelKey L → ℚ) (h : Fin 3) (a b : Block L) :
    |channelInt w h a b| ≤ 1 := by
  unfold channelInt
  dsimp only
  exact (mul_bound (prod_unit _ (fun _ => bit_bound _))
    (prod_unit _ (fun _ => prod_unit _ (fun _ => bit_bound _)))).trans_eq (by norm_num)

theorem sum_bound {I : Type*} [Fintype I] (f : I → ℤ) (U : ℤ) (h : ∀ i, |f i| ≤ U) :
    |∑ i, f i| ≤ (Fintype.card I : ℤ)*U := by
  calc
    _ ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : I, U := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

theorem card_pair (L : ℕ) : (Fintype.card (PairBits L) : ℤ) = (D L)^2 := by
  simp [PairBits,Bits,D,pow_two]

theorem residual_cast (K L : ℕ) (j : BasisLabel L) :
    (residualInt K L j : ℚ) = (D L : ℚ) * (windowExpansion K L).diagonal j := by
  have h := Dyadic.widen (denominator_bits j) (residualNum (windowCoeff K L) (antisymmetric j).card)
  change (residualInt K L j : ℚ) / (2:ℚ)^L = (windowExpansion K L).diagonal j at h
  simpa [D,mul_comm] using (div_eq_iff (by positivity : (2:ℚ)^L ≠ 0)).mp h

private theorem window_extent {K : ℕ} (hK : 4<K) (L : ℕ) : lower K L + width K L ≤ L := by
  have ha : lower K L ≤ L := Nat.div_le_of_le_mul (Nat.mul_le_mul_right L (show K-4 ≤ 4*K by omega))
  have hb : upper K L ≤ L := Nat.div_le_of_le_mul (Nat.mul_le_mul_right L (show K+4 ≤ 4*K by omega))
  unfold width
  omega

theorem residual_bound {K : ℕ} (hK : 4<K) (L : ℕ) (j : BasisLabel L) :
    |residualInt K L j| ≤ 2*(D L)^5 := by
  let a := lower K L
  let d := width K L
  have hld : a+d ≤ L := window_extent hK L
  have hb := RankSwap.residual_bound (by positivity) (Window.correct a d).2.1 j
  have hz : |residualNum (windowCoeff K L) (antisymmetric j).card| ≤
      1 + (3:ℤ)^L * (2^a * 4^d) := by exact_mod_cast hb
  have hsq : (4:ℤ)^L = (D L)^2 := by rw [D,← pow_mul,Nat.mul_comm, pow_mul]; norm_num
  have hwin : (2:ℤ)^a * 4^d ≤ (D L)^2 := by
    calc
      _ ≤ (4:ℤ)^a * 4^d := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) _) (by positivity)
      _ = 4^(a+d) := (pow_add _ _ _).symm
      _ ≤ 4^L := pow_le_pow_right₀ (by norm_num) hld
      _ = _ := hsq
  have hthree : (3:ℤ)^L ≤ (D L)^2 := (pow_le_pow_left₀ (by norm_num) (by norm_num : (3:ℤ)≤4) L).trans_eq hsq
  have hone : (1:ℤ) ≤ (D L)^4 := one_le_pow₀ (D_one L)
  have hraw : |residualNum (windowCoeff K L) (antisymmetric j).card| ≤ 2*(D L)^4 := by
    apply hz.trans
    calc
      _ ≤ (D L)^4 + (D L)^2 * (D L)^2 := add_le_add hone (mul_le_mul hthree hwin (by positivity) (by positivity))
      _ = _ := by ring
  have hshift : |(2:ℤ)^(L - denominatorExponent j)| ≤ D L := by
    rw [abs_of_nonneg (by positivity : (0:ℤ) ≤ 2^(L-denominatorExponent j))]
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  exact (mul_bound hraw hshift).trans_eq (by ring)

end VWZClique.TraceDyadic
end

/- TraceDyadic -/
section
namespace VWZClique.TraceDyadic
open UniformFolds Double

variable {L : ℕ}

theorem transform_bound (j : BasisLabel L) (f : PairBits L → ℤ) (U : ℤ) (hf : ∀ x, |f x| ≤ U) :
    |transform j f| ≤ (D L)^2 * U :=
  (sum_bound _ _ (fun x => (mul_bound (basis_bound j x) (hf x)).trans_eq (one_mul _))).trans_eq
    (by rw [card_pair])

theorem left_cast (S T : Finset (BasisLabel L)) (K J : ℕ) (w : ChannelKey L → ℚ)
    (hw : ∀ k, Binary (w k)) (u : Node S) (v : Node T) :
    (leftTable S T K J w u v : ℚ) = (D L : ℚ)^2 *
      leftEntry S T (windowExpansion K L).diagonal (windowExpansion J L).diagonal w u v := by
  simp only [leftTable,rawLeft,transform,Int.cast_mul,Int.cast_sum,residual_cast,basis_cast,
    channel_cast w hw,leftEntry,Rat.cast_id]
  ring

theorem mid_cast (T : Finset (BasisLabel L)) (w : ChannelKey L → ℚ) (hw : ∀ k, Binary (w k))
    (v : Node T) (c : Block L) : (midTable T w v c : ℚ) = midEntry T w v c := by
  simp only [midTable,transform,Int.cast_sum,Int.cast_mul,basis_cast,channel_cast w hw,midEntry,Rat.cast_id]

theorem right_cast (S : Finset (BasisLabel L)) (w : ChannelKey L → ℚ) (hw : ∀ k, Binary (w k))
    (c : Block L) (u : Node S) : (rightTable S w c u : ℚ) = rightEntry S w c u := by
  simp only [rightTable,transform,Int.cast_sum,Int.cast_mul,basis_cast,channel_cast w hw,rightEntry,Rat.cast_id]

theorem rawLeft_bound (S T : Finset (BasisLabel L)) (w : ChannelKey L → ℚ) (u : Node S) (v : Node T) :
    |rawLeft S T w u v| ≤ (D L)^4 := by
  let f (y x : PairBits L) := channelInt w 0 (block x u.2) (block y v.2)
  have inner (y : PairBits L) := transform_bound u.1 (f y) 1 (fun x => channel_bound w 0 (block x u.2) (block y v.2))
  have outer := transform_bound v.1 (fun y => transform u.1 (f y)) ((D L)^2*1) inner
  exact outer.trans_eq (by ring)

theorem left_bound (S T : Finset (BasisLabel L)) {K J : ℕ} (hK : 4<K) (hJ : 4<J)
    (w : ChannelKey L → ℚ) (u : Node S) (v : Node T) :
    |leftTable S T K J w u v| ≤ 4*(D L)^14 :=
  (mul_bound (mul_bound (residual_bound hK L u.1) (residual_bound hJ L v.1))
    (rawLeft_bound S T w u v)).trans_eq (by ring)

theorem mid_bound (T : Finset (BasisLabel L)) (w : ChannelKey L → ℚ) (v : Node T) (c : Block L) :
    |midTable T w v c| ≤ (D L)^2 := by
  unfold midTable
  simpa only [mul_one] using transform_bound v.1 (fun y => channelInt w 1 (block y v.2) c) 1
    (fun y => channel_bound w 1 (block y v.2) c)

theorem right_bound (S : Finset (BasisLabel L)) (w : ChannelKey L → ℚ) (c : Block L) (u : Node S) :
    |rightTable S w c u| ≤ (D L)^2 := by
  unfold rightTable
  simpa only [mul_one] using transform_bound u.1 (fun x => channelInt w 2 c (block x u.2)) 1
    (fun x => channel_bound w 2 c (block x u.2))

private theorem product_bound {I J C : Type*} [Fintype J] (A : Matrix I J ℤ) (B : Matrix J C ℤ)
    (U V : ℤ) (hA : ∀ i j, |A i j| ≤ U) (hB : ∀ j k, |B j k| ≤ V) (i : I) (k : C) :
    |(A*B) i k| ≤ (Fintype.card J : ℤ)*(U*V) :=
  sum_bound _ _ (fun j => mul_bound (hA i j) (hB j k))

theorem numerator_exact (S T : Finset (BasisLabel L)) (K J : ℕ)
    (w : ChannelKey L → ℚ) (hw : ∀ k, Binary (w k)) :
    (numerator S T K J w : ℚ) = (D L : ℚ)^2 *
      doubleProjection S T (windowExpansion K L).diagonal (windowExpansion J L).diagonal w := by
  rw [Double.trace_identity]
  change ((∑ u : Node S, ∑ v : Node T, leftTable S T K J w u v *
    (∑ c : Block L, midTable T w v c * rightTable S w c u) : ℤ) : ℚ) = _
  simp only [Int.cast_sum,Int.cast_mul,left_cast S T K J w hw,mid_cast T w hw,right_cast S w hw]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact mul_assoc _ _ _

end VWZClique.TraceDyadic
end

/- CliqueQuotient -/
section
/-! Exact integer division by repeated addition, comparison and subtraction, for
    recovering scaled matrix-product entries on a RAM without a divide instruction.
    This is the arithmetic schedule; the cost below counts its scalar iterations. -/

namespace VWZClique.Quotient

@[simp] theorem twice_eq (j x : ℕ) : twice j x = 2^j*x := by
  induction j generalizing x with
  | zero => simp [twice]
  | succ j ih => rw [twice,ih,pow_succ]; ring

theorem scan_correct (h a d : ℕ) (_hd : 0 < d) (ha : a < 2^h*d) :
    a = (scan h a d).1*d + (scan h a d).2 ∧ (scan h a d).2 < d := by
  induction h generalizing a with
  | zero => simpa [scan] using ha
  | succ h ih =>
    rw [pow_succ] at ha
    have htop : 2^h*2*d = 2^h*d + 2^h*d := by ring
    rw [htop] at ha
    by_cases hy : 2^h*d ≤ a
    · have hsmall : a-2^h*d < 2^h*d := by omega
      obtain ⟨he,hr⟩ := ih (a-2^h*d) hsmall
      simp only [scan,twice_eq,if_pos hy,mul_one,add_mul]
      exact ⟨by omega,hr⟩
    · simpa only [scan,twice_eq,if_neg hy] using ih a (Nat.lt_of_not_ge hy)

theorem scan_quotient (h a d : ℕ) (hd : 0 < d) (ha : a < 2^h*d) :
    (scan h a d).1 = a/d ∧ (scan h a d).2 = a%d := by
  obtain ⟨he,hr⟩ := scan_correct h a d hd ha
  constructor
  · conv_rhs => rw [he, Nat.mul_comm (scan h a d).1 d, Nat.mul_add_div hd, Nat.div_eq_of_lt hr, Nat.add_zero]
  · conv_rhs => rw [he, Nat.mul_comm (scan h a d).1 d, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

theorem height_cover (a p : ℕ) : a < 2^(height a p)*(p+1) := by
  induction p using height.induct a with
  | case1 p hp ih =>
    rw [height,if_pos hp,pow_add]
    norm_num
    calc
      _ < 2^height a (p+p+1)*(p+p+1+1) := ih
      _ = _ := by ring
  | case2 p hp => rw [height,if_neg hp]; simpa using Nat.lt_of_not_ge hp

theorem height_minimal (a p : ℕ) (h : 0 < height a p) :
    2^(height a p-1)*(p+1) ≤ a := by
  induction p using height.induct a with
  | case1 p hp ih =>
    rw [height,if_pos hp,Nat.add_sub_cancel_left]
    by_cases hq : height a (p+p+1) = 0
    · simpa [hq] using hp
    · have hh := ih (Nat.zero_lt_of_ne_zero hq)
      obtain ⟨q,he⟩ := Nat.exists_eq_succ_of_ne_zero hq
      rw [he,Nat.succ_sub_one] at hh
      rw [he,pow_succ]
      calc
        _ = 2^q*(p+p+1+1) := by ring
        _ ≤ _ := hh
  | case2 p hp =>
    rw [height,if_neg hp] at h
    omega

theorem height_bound (a : ℕ) : height a 0 ≤ a.log2+1 := by
  by_cases ha : a = 0
  · subst a
    rw [height,if_neg (by decide : ¬ 0+1 ≤ 0)]
    omega
  by_cases hh : height a 0 = 0
  · simp [hh]
  have hb := height_minimal a 0 (Nat.zero_lt_of_ne_zero hh)
  simp only [zero_add,mul_one] at hb
  have hlog := (Nat.le_log2 ha).mpr hb
  omega

theorem quotient_correct (a d : ℕ) (hd : 0 < d) :
    (quotient a d).1 = a/d ∧ (quotient a d).2 = a%d := by
  apply scan_quotient _ _ _ hd
  have h := height_cover a 0
  simp only [zero_add,mul_one] at h
  exact h.trans_le (Nat.le_mul_of_pos_right _ hd)

theorem signed_exact (z : ℤ) (d : ℕ) (hd : 0 < d) : signed (z*d) d = z := by
  unfold signed
  rw [(quotient_correct _ _ hd).1, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_div_cancel _ hd]
  have hs : (d:ℤ).sign = 1 := Int.sign_eq_one_of_pos (by exact_mod_cast hd)
  rw [Int.sign_mul, hs, mul_one, Int.sign_mul_natAbs]

/-- Worst-case scalar iterations of the two doubling loops, comparison,
    subtraction and accumulation in the scan. -/
def scanBudget : ℕ → ℕ
  | 0 => 1
  | j+1 => scanBudget j + 2*j+4

theorem scanBudget_le (h : ℕ) : scanBudget h ≤ (h+1)*(h+4) := by
  induction h with
  | zero => simp [scanBudget]
  | succ h ih =>
    change scanBudget h + 2*h+4 ≤ _
    nlinarith

theorem totalBudget_le (a : ℕ) :
    (height a 0+1) + scanBudget (height a 0) ≤ (a.log2+2)*(a.log2+6) := by
  have h := height_bound a
  have hs := scanBudget_le (height a 0)
  calc
    _ ≤ (height a 0+1)*(height a 0+5) := by nlinarith
    _ ≤ _ := Nat.mul_le_mul (by omega) (by omega)

end VWZClique.Quotient
end

/- UniformFoldIntegers -/
section
open VWZClique VWZClique.RankSwap VWZClique.WeightedProof
namespace VWZClique.UniformFolds

private theorem cutoff_le {K : ℕ} (hK : 4<K) (L : ℕ) :
    lower K L ≤ L ∧ width K L ≤ L := by
  have cut (j : ℕ) (hj : j ≤ 4*K) : j*L/(4*K) ≤ L :=
    Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right L hj)
  exact ⟨cut _ (by omega),(Nat.sub_le _ _).trans (cut _ (by omega))⟩

/-- The same coefficients used by the evaluator have O(L)-bit signed numerators
and a binary denominator exponent at most L. -/
theorem windowWordBounds {K : ℕ} (hK : 4<K) (L : ℕ) :
    (∀ i : (windowExpansion K L).Index, |(windowExpansion K L).coefficients i| ≤ (2:ℤ)^(3*L)) ∧
    ∀ j : BasisLabel L, ∃ e : ℕ, e ≤ L ∧ ∃ z : ℤ, |z| ≤ (2:ℤ)^(5*L+1) ∧
      (windowExpansion K L).diagonal j = Dyadic.value e z := by
  obtain ⟨hl,hw⟩ := cutoff_le hK L
  obtain ⟨coeff,diag⟩ := windowExpansion_coefficients K L
  have hs : (2:ℝ)^(lower K L)*4^(width K L) ≤ 2^(3*L) := by
    rw [show (4:ℝ) = 2^2 by norm_num,←pow_mul,←pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have ht : (3:ℝ)^L ≤ 2^(2*L) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have htotal : 1+(3:ℝ)^L*(2^(lower K L)*4^(width K L)) ≤ 2^(5*L+1) := by
    calc
      _ ≤ 1+(2:ℝ)^(2*L)*2^(3*L) := by gcongr
      _ = 1+2^(5*L) := by rw [←pow_add,show 2*L+3*L=5*L by omega]
      _ ≤ (2:ℝ)^(5*L+1) := by rw [pow_succ]; linarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=5*L)]
  refine ⟨fun i => ?_,fun j => ?_⟩
  · exact_mod_cast (coeff i).trans hs
  · obtain ⟨e,he,z,hz,v⟩ := diag j
    exact ⟨e,he,z,by exact_mod_cast hz.trans htotal,v⟩

/-- This coarse bound holds even at lengths below the asymptotic rank cutoff. -/
theorem windowTerms_le (K L : ℕ) : Fintype.card (windowExpansion K L).Index ≤ 2^(3*L) := by
  change Fintype.card (Terms L (width K L)) ≤ _
  rw [terms_card]
  calc
    _ ≤ ∑ S : Finset (Fin L), 4^S.card := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 5^L := by
      simpa only [one_pow,mul_one,Fintype.card_fin] using
        (Fintype.sum_pow_mul_eq_add_pow (Fin L) (4:ℕ) 1)
    _ ≤ _ := by rw [pow_mul]; exact Nat.pow_le_pow_left (by decide) L

private theorem subtotal {I : Type*} [Fintype I] (s : Finset I) (f : I → ℤ)
    (m v : ℕ) (hm : Fintype.card I ≤ 2^m) (hv : ∀ i, |f i| ≤ (2:ℤ)^v) :
    |∑ i ∈ s, f i| ≤ (2:ℤ)^(m+v) := by
  calc
    _ ≤ ∑ i ∈ s, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ s, (2:ℤ)^v := Finset.sum_le_sum fun i _ => hv i
    _ = (s.card:ℤ)*(2:ℤ)^v := by simp
    _ ≤ (2:ℤ)^m * 2^v := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Finset.card_le_univ s).trans hm) (by positivity)
    _ = _ := (pow_add _ _ _).symm

/-- Every partial one-mask sum in an evaluation on binary inputs has at most
15L bits above the unit, independently of the enumeration order. -/
theorem singleSubtotal {K : ℕ} (hK : 4<K) (L : ℕ)
    (s : Finset (windowExpansion K L).Index) (v : (windowExpansion K L).Index → ℤ)
    (hv : ∀ i, |v i| ≤ (2:ℤ)^(9*L)) :
    |∑ i ∈ s, (windowExpansion K L).coefficients i * v i| ≤ (2:ℤ)^(15*L) := by
  have hh := (windowWordBounds hK L).1
  rw [show 15*L = 3*L+(3*L+9*L) by omega]
  apply subtotal _ _ _ _ (windowTerms_le K L)
  intro i
  rw [abs_mul,pow_add]
  exact mul_le_mul (hh i) (hv i) (abs_nonneg _) (by positivity)

/-- Arbitrary partial sums of the two-mask branch fit a signed integer
with 21L bits above the unit. -/
theorem doubleSubtotal {K : ℕ} (hK : 4<K) (L : ℕ)
    (s : Finset ((windowExpansion K L).Index × (windowExpansion K L).Index))
    (v : (windowExpansion K L).Index × (windowExpansion K L).Index → ℤ)
    (hv : ∀ i, |v i| ≤ (2:ℤ)^(9*L)) :
    |∑ i ∈ s, (windowExpansion K L).coefficients i.1 *
      (windowExpansion K L).coefficients i.2 * v i| ≤ (2:ℤ)^(21*L) := by
  have hh := (windowWordBounds hK L).1
  have hm := windowTerms_le K L
  rw [show 21*L = (3*L+3*L) + ((3*L+3*L)+9*L) by omega]
  apply subtotal
  · rw [Fintype.card_prod,pow_add]
    exact Nat.mul_le_mul hm hm
  · intro i
    rw [abs_mul,abs_mul,pow_add,pow_add]
    exact mul_le_mul (mul_le_mul (hh i.1) (hh i.2) (abs_nonneg _) (by positivity))
      (hv i) (abs_nonneg _) (by positivity)

private theorem folded_integer {L : ℕ} (H : SimpleGraph V) (π : Equiv.Perm V)
    (w : WeightKey (2^L) → ℚ) (hw : ∀ k, Binary (w k)) (d : Branch)
    (a b : Option (Mask L)) (ha : a.isSome = first d) (hb : b.isSome = second d) :
    ∃ z : ℤ, |z| ≤ (2:ℤ)^(9*L) ∧
      placedFold (slots π H) a b ((Round.mk H π none none).inputs w) = (z:ℚ) := by
  let r : Round L := ⟨H,π,a,b⟩
  have binary (i) : Binary (r.apply w i) := updated_binary _ _ _ _
    (r.inputs_property w Binary (Or.inr rfl) hw) i
  obtain ⟨z,hz,hv⟩ := binary_sum (child (slots π H) d) _ binary
  refine ⟨z,?_,?_⟩
  · rw [abs_of_nonneg (Nat.cast_nonneg _)]
    rw [←pow_mul,Nat.mul_comm L 9] at hz
    exact_mod_cast hz
  · exact (r.exact_value w d ha hb).symm.trans (by simpa only [Int.cast_natCast] using hv)

/-- The complete projected contribution is integral on every Boolean fold input,
even though its three channel matrices contain rational diagonal coefficients. -/
theorem traceProjection_integer {K : ℕ} (hK : 4<K) (L : ℕ)
    (H : SimpleGraph V) (π : Equiv.Perm V) (w : WeightKey (2^L) → ℚ)
    (hw : ∀ k, Binary (w k)) :
    ∃ z : ℤ, |z| ≤ (2:ℤ)^(21*L+2) ∧
      traceProjection L (windowExpansion K L) ((Round.mk H π none none).inputs w) = (z:ℚ) := by
  classical
  let q := windowExpansion K L
  let E := slots π H
  let u := (Round.mk H π (none : Option (Mask L)) none).inputs w
  choose left leftBound leftVal using
    fun i : q.Index => folded_integer H π w hw .left (some (q.masks i)) none rfl rfl
  choose right rightBound rightVal using
    fun j : q.Index => folded_integer H π w hw .right none (some (q.masks j)) rfl rfl
  choose both bothBound bothVal using fun ij : q.Index × q.Index =>
    folded_integer H π w hw .both (some (q.masks ij.1)) (some (q.masks ij.2)) rfl rfl
  let A : ℤ := ∑ i, q.coefficients i * left i
  let B : ℤ := ∑ j, q.coefficients j * right j
  let D : ℤ := ∑ ij : q.Index × q.Index, (q.coefficients ij.1 * q.coefficients ij.2) * both ij
  have ha : |A| ≤ (2:ℤ)^(15*L) := singleSubtotal hK L Finset.univ left leftBound
  have hb : |B| ≤ (2:ℤ)^(15*L) := singleSubtotal hK L Finset.univ right rightBound
  have hd : |D| ≤ (2:ℤ)^(21*L) := doubleSubtotal hK L Finset.univ both bothBound
  have la : ∑ i, (q.coefficients i:ℚ)*placedFold E (some (q.masks i)) none u = (A:ℚ) := by
    simp only [A,Int.cast_sum,Int.cast_mul]
    exact Finset.sum_congr rfl (fun i _ => congrArg _ (leftVal i))
  have lb : ∑ j, (q.coefficients j:ℚ)*placedFold E none (some (q.masks j)) u = (B:ℚ) := by
    simp only [B,Int.cast_sum,Int.cast_mul]
    exact Finset.sum_congr rfl (fun j _ => congrArg _ (rightVal j))
  have ld : ∑ i, ∑ j, ((q.coefficients i:ℚ)*(q.coefficients j:ℚ))*
      placedFold E (some (q.masks i)) (some (q.masks j)) u = (D:ℚ) := by
    simp only [D,Int.cast_sum,Int.cast_mul,Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
      (fun j _ => congrArg _ (bothVal (i,j))))
  obtain ⟨v,hv,value⟩ := binary_sum H w hw
  have hval : placedFold E none none u = (v:ℚ) := (input_exact π H w).trans value
  have h := q.decompose E u (input_supported (Round.mk H π none none) w)
  rw [la,lb,ld,hval] at h
  let P : ℤ := (2:ℤ)^(21*L)
  have h15 : (2:ℤ)^(15*L) ≤ P := pow_le_pow_right₀ (by norm_num) (by omega)
  have hv' : |(v:ℤ)| ≤ P := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    rw [←pow_mul,Nat.mul_comm L 9] at hv
    exact (by exact_mod_cast hv : (v:ℤ) ≤ 2^(9*L)).trans (pow_le_pow_right₀ (by norm_num) (by omega))
  refine ⟨(v:ℤ)-A-B+D,?_,?_⟩
  · calc
      _ ≤ |(v:ℤ)-A-B|+|D| := abs_add_le _ _
      _ ≤ (|(v:ℤ)-A|+|B|)+|D| := by gcongr; exact abs_sub _ _
      _ ≤ (|(v:ℤ)|+|A|+|B|)+|D| := by gcongr; exact abs_sub _ _
      _ ≤ P+P+P+P := add_le_add (add_le_add (add_le_add hv' (ha.trans h15)) (hb.trans h15)) hd
      _ = _ := by rw [pow_add]; dsimp [P]; ring
  · rw [traceProjection_correct]
    push_cast
    linarith

/-- Every projected contribution reached on a Boolean input has the same
signed word bound, with no growth in the number of preceding folds. -/
theorem traceProjection_on_trace {L : ℕ} {H H' : SimpleGraph V} {p : Plan H}
    {rs : List (Round L)} (_ : Trace L p H' rs) (π : Equiv.Perm V)
    (w : WeightKey (2^L) → ℚ) (hw : ∀ k, Binary (w k)) :
    ∃ z : ℤ, |z| ≤ (2:ℤ)^(21*L+2) ∧
      traceProjection L (windowExpansion (windowAt (Nat.card H'.edgeSet)) L)
        ((Round.mk H' π none none).inputs (follow rs w)) = (z:ℚ) :=
  traceProjection_integer (cutoffTable_spec H').2.2.1 L H' π (follow rs w) (follow_binary rs w hw)

/-- On every actual graph call the integer trace numerator is divisible by the
common binary denominator. The signed shift/subtract quotient returns exactly the
projected contribution. -/
theorem traceIntegerQuotient {K : ℕ} (hK : 4<K) (L : ℕ)
    (H : SimpleGraph V) (π : Equiv.Perm V) (w : WeightKey (2^L) → ℚ)
    (hw : ∀ k, Binary (w k)) :
    let q := windowExpansion K L
    let u := (Round.mk H π (none : Option (Mask L)) none).inputs w
    let z := TraceDyadic.numerator q.labels q.labels K K u
    let d : ℕ := (2^L)^2
    (d:ℤ) ∣ z ∧ (Quotient.signed z d:ℚ) = traceProjection L q u ∧
      |Quotient.signed z d| ≤ (2:ℤ)^(21*L+2) := by
  intro q u z d
  obtain ⟨v,hv,he⟩ := traceProjection_integer hK L H π w hw
  have hb (i) : Binary (u i) :=
    (Round.mk H π (none : Option (Mask L)) none).inputs_property w Binary (Or.inr rfl) hw i
  have hx := TraceDyadic.numerator_exact q.labels q.labels K K u hb
  have he' : doubleProjection q.labels q.labels q.diagonal q.diagonal u = (v:ℚ) :=
    (traceProjection_correct q u).symm.trans he
  have eq : z = v*(d:ℤ) := by
    have h : (z:ℚ) = ((v*(d:ℤ):ℤ):ℚ) := by
      rw [show (z:ℚ) = (TraceDyadic.D L : ℚ)^2 *
        doubleProjection q.labels q.labels q.diagonal q.diagonal u from hx,he']
      simp [d,TraceDyadic.D,mul_comm]
    exact_mod_cast h
  have hd : 0<d := by dsimp [d]; positivity
  have res : Quotient.signed z d = v := by rw [eq,Quotient.signed_exact _ _ hd]
  exact ⟨⟨v,eq.trans (mul_comm _ _)⟩,res ▸ he.symm,res ▸ hv⟩

end VWZClique.UniformFolds
end

/- IntegerFoldEvaluation -/
section
open VWZClique VWZClique.SparseProof
namespace VWZClique.UniformFolds

theorem integerPlan_cast (L : ℕ) {H : SimpleGraph V} (p : Plan H)
    (w : WeightKey (2^L) → ℚ) (hw : ∀ k, Binary (w k)) :
    (integerPlan L p w:ℚ) =
      evaluatePlan (fun H => windowExpansion (windowAt (Nat.card H.edgeSet)) L)
        (sparseLeaf L) (traceProjection L) p w := by
  induction p generalizing w with
  | leaf H hh => exact integerLeaf_cast L H hh w hw
  | split H π hp kids ih =>
    let K := windowAt (Nat.card H.edgeSet)
    let q := windowExpansion K L
    have htrace : (integerTrace K L H π w:ℚ) =
        traceProjection L q ((Round.mk H π none none).inputs w) :=
      (traceIntegerQuotient (cutoffTable_spec H).2.2.1 L H π w hw).2.1
    have hcall (d : Branch) (a b : Option (Mask L)) :
        (integerPlan L (kids d) ((Round.mk H π a b).apply w):ℚ) =
        evaluatePlan (fun G => windowExpansion (windowAt (Nat.card G.edgeSet)) L)
          (sparseLeaf L) (traceProjection L) (kids d) ((Round.mk H π a b).apply w) :=
      let r := Round.mk H π a b
      ih d (r.apply w) (updated_binary _ _ _ _ (r.inputs_property w Binary (Or.inr rfl) hw))
    simp only [integerPlan,evaluatePlan,Int.cast_add,Int.cast_sub,Int.cast_sum,Int.cast_mul]
    rw [htrace]
    simp_rw [hcall]
    rfl

theorem integerPlan_exact (L : ℕ) {H : SimpleGraph V} (p : Plan H) (w : WeightKey (2^L) → ℚ)
    (hw : ∀ k, Binary (w k)) : (integerPlan L p w:ℚ) = weightedSum H w :=
  (integerPlan_cast L p w hw).trans
    (evaluatePlan_correct _ _ _ (sparseLeaf_correct L) traceProjection_correct _ _)

/-- Apply the fixed plan to binary graph weights with an integer result. -/
theorem integerPlan_correct (L : ℕ) (H : SimpleGraph V) (w : WeightKey (2^L) → ℚ)
    (hw : ∀ k, Binary (w k)) : (integerPlan L (fixed H) w:ℚ) = weightedSum H w :=
  integerPlan_exact L (fixed H) w hw

theorem integerPlan_range (L : ℕ) {H : SimpleGraph V} (p : Plan H) (w : WeightKey (2^L) → ℚ)
    (hw : ∀ k, Binary (w k)) :
    0 ≤ integerPlan L p w ∧ integerPlan L p w ≤ (2:ℤ)^(9*L) := by
  obtain ⟨z,hz,h⟩ := binary_sum H w hw
  have h' : integerPlan L p w = (z:ℤ) := by
    exact_mod_cast (integerPlan_exact L p w hw).trans h
  rw [h']
  rw [←pow_mul,Nat.mul_comm L 9] at hz
  exact ⟨Nat.cast_nonneg _,by exact_mod_cast hz⟩

/-- Each actual recursive subproblem also returns an integer in the same range. -/
theorem integerPlan_subproblem {L : ℕ} {H H' : SimpleGraph V} {p : Plan H}
    {rs : List (Round L)} (_ : Trace L p H' rs) (p' : Plan H')
    (w : WeightKey (2^L) → ℚ) (hw : ∀ k, Binary (w k)) :
    0 ≤ integerPlan L p' (follow rs w) ∧ integerPlan L p' (follow rs w) ≤ (2:ℤ)^(9*L) :=
  integerPlan_range L p' _ (follow_binary rs w hw)

end VWZClique.UniformFolds
end

/- CliqueIntegerPlan -/
section
/-! Apply the integer recursion to the original graph at every input size. -/

namespace VWZClique.BlockReduction
open UniformFolds WeightedProof OAI.MatrixMultiplication.Arithmetic

theorem graphWeights_binary {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) (k : ℕ)
    (i : WeightKey (2^graphLength n k)) : Binary (graphWeights G hn k i) := by
  let w := weights (F := ℚ) (t := (k+8)/9) G k ⟨0,hn⟩
  have h (x : WeightKey (n^((k+8)/9))) : Binary (w x) := weights_binary G k _ x
  have zero : Binary (0:ℚ) := Or.inl rfl
  cases i with
  | inl a =>
    obtain ⟨u,x⟩ := a
    change Binary (literal w (padTag (.inl (u,x))))
    by_cases hx : x.val < n^((k+8)/9) <;> simp [padTag,hx,literal,h,zero]
  | inr a =>
    obtain ⟨u,v,x,y⟩ := a
    change Binary (literal w (padTag (.inr (u,v,x,y))))
    by_cases hx : x.val < n^((k+8)/9) ∧ y.val < n^((k+8)/9) <;> simp [padTag,hx,literal,h,zero]

theorem graph_integer_exact {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) (k : ℕ) :
    integerPlan (graphLength n k) (fixed ⊤) (graphWeights G hn k) = (count G k : ℤ) := by
  have bound := Nat.le_pow_clog (by decide : 1 < 2) (n^((k+8)/9))
  have correct := integerPlan_correct _ ⊤ _ (graphWeights_binary G hn k)
  have pad := weights_padded bound (⊤ : SimpleGraph V)
    (weights (F := ℚ) (t := (k+8)/9) G k ⟨0,hn⟩)
  have result := correct.trans (pad.trans (weighted_eq_count_ceil hn G k))
  exact_mod_cast result

end VWZClique.BlockReduction
end

/- NativeFoldRate -/
section
namespace VWZClique.NativeTraversal
open UniformFolds BlockReduction WeightedProof IntegerRAM IntegerRAM.Structured
open OAI.MatrixMultiplication.Arithmetic

/-- Per-pattern fixed word programs can spend an arbitrary fixed polynomial in
the dyadic bit length on each charged operation, including exact integer division. -/
theorem native_plan_rate {mm : ℕ→ℕ} {M : ℝ} (hM : 0<M)
    (hmm : ∀ n : ℕ, 1≤n → (mm n:ℝ)≤M*(n:ℝ)^(omega ℂ+(levelSaving 36).val/8))
    (T U G p : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ L : ℕ, ((L+1:ℕ):ℝ)^p*
      (planWork mm T U G L (fixed ⊤):ℝ) ≤ C*((2:ℝ)^L)^(3*omega ℂ-(levelSaving 36).val/4) := by
  let a := (levelSaving 36).val
  have ha : 0<a := (levelSaving 36).pos
  obtain ⟨D,hD,plan⟩ := planWork_allLengths (omega ℂ) (a/8) (MM.omega_two_le ℂ) (by positivity)
    mm M hM hmm T U G
  obtain ⟨P,hP,poly⟩ := absorb_word_length p (a/4) (by positivity)
  refine ⟨P*D,mul_pos hP hD,?_⟩
  intro L
  have h := plan L ⊤ (fun _ => 0)
  rw [traversedWork_eq] at h
  have both := mul_le_mul (poly L) h (Nat.cast_nonneg _) (by positivity)
  calc
    _ ≤ _ := both
    _ = _ := by
      rw [show P*((2:ℝ)^L)^(a/4)*(D*((2:ℝ)^L)^(3*omega ℂ-(levelSaving 36).val+4*(a/8))) =
          (P*D)*((((2:ℝ)^L)^(a/4))*(((2:ℝ)^L)^(3*omega ℂ-(levelSaving 36).val+4*(a/8)))) by ring]
      rw [←Real.rpow_add (by positivity)]
      congr 2
      dsimp [a]; ring

end VWZClique.NativeTraversal
open VWZClique VWZClique.NativeTraversal VWZClique.UniformFolds VWZClique.BlockReduction VWZClique.WeightedProof VWZClique.IntegerRAM VWZClique.IntegerRAM.Structured OAI.MatrixMultiplication.Arithmetic
theorem solution {mm : ℕ→ℕ} {M : ℝ} (hM : 0<M)
    (hmm : ∀ n : ℕ, 1≤n → (mm n:ℝ)≤M*(n:ℝ)^(omega ℂ+(levelSaving 36).val/8))
    {T U A : ℕ} (native : Realizes mm T U A) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K₀ : ℕ, ∀ k ≥ K₀, countsWithin k ((omega ℂ-δ)*(k:ℝ)/3) := by
  obtain ⟨cap,make⟩ := native
  let α := (levelSaving 36).val/4
  have hα : 0<α := by dsimp [α]; linarith [(levelSaving 36).pos]
  have hle : α≤1 := by dsimp [α]; linarith [(levelSaving 36).le_one]
  let e := 3*omega ℂ-α
  have he : 0≤e := by dsimp [e]; linarith [MM.omega_two_le ℂ]
  refine ⟨α/6,by positivity,max cap ⌈144/α⌉₊,?_⟩
  intro k hk
  have hk₀ : cap≤k := (le_max_left _ _).trans hk
  obtain ⟨machine,b,p,D,hb,hD,go⟩ := make k hk₀
  obtain ⟨C,hC,rate⟩ := native_plan_rate hM hmm T U A p
  have hpos : 0≤(omega ℂ-α/6)*(k:ℝ)/3 := by
    have h : 0≤omega ℂ-α/6 := by linarith [MM.omega_two_le ℂ]
    positivity
  apply Cutoff.countsWithin_of_large hk₀ hpos hb (show 0 < (D*C)*2^e by positivity) machine
  intro n G hn hn₀
  obtain ⟨f,out,ht,run,ans⟩ := go n G hn hn₀
  refine ⟨f,out,?_,run,ans.trans (graph_integer_exact G (by omega) k)⟩
  let N := n^((k+8)/9)
  let L := graphLength n k
  obtain ⟨l,large,approx⟩ := exists_pow_sandwich (Nat.one_le_pow ((k+8)/9) n (by omega))
  have bound : 2^L≤2*N := (Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow large)).trans approx
  have size : (2:ℝ)^L≤2*(N:ℝ) := by exact_mod_cast bound
  have scale := grouped_rpow hα (MM.omega_le_three ℂ) he ((le_max_right _ _).trans hk) (by omega : 1≤n)
  calc
    (f:ℝ) ≤ D*(((L+1:ℕ):ℝ)^p*(planWork mm T U A L (fixed ⊤):ℝ)) := by simpa only [mul_assoc] using ht
    _ ≤ D*(C*((2:ℝ)^L)^e) := mul_le_mul_of_nonneg_left (rate L) hD.le
    _ ≤ D*(C*(2*(N:ℝ))^e) := by gcongr
    _ = ((D*C)*2^e)*(N:ℝ)^e := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left scale (by positivity)


end
