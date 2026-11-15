-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.BlockProof.exact_block_identity
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:52:19.87095+00:00
-- url     : https://prove2.me/submissions/b4196a2d-cf6a-4d4a-8616-65c59e1dacbe

/- Generated from Solutions.BlockEncoding by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Theorems.Thm_QMAPerfectCompleteness_Main_BlockProof_cyclicOp_decomposition



/-! Algebraic ingredients of Lemma 3.6. All results in this file are proved from definitions;
no import of the open `exact_block_encoding` statement is used. -/

open Matrix
open scoped Kronecker

namespace QMAPerfectCompleteness.Main.BlockProof
end QMAPerfectCompleteness.Main.BlockProof
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.BlockProof

variable {G : GateSet} (V : Verifier G)

@[simp] theorem QMAPerfectCompleteness.Main.BlockProof.proofPart_initialState (p : V.Proof) : V.proofPart (V.initialState p) = p := by
  funext i
  simp [Verifier.proofPart, Verifier.initialState]

theorem QMAPerfectCompleteness.Main.BlockProof.initialState_injective : Function.Injective V.initialState := by
  intro p q hpq
  have := congrArg V.proofPart hpq
  simpa using this





/-- A flag controlled on P has block P between input flag one and output flag zero. -/
theorem QMAPerfectCompleteness.Main.BlockProof.flipIf_false_true (P : Clock V.proofQubits → V.Wire → Bool)
    (t' t : Clock V.proofQubits) (w' w : V.Wire) :
    V.flipIf P (t', w', false) (t, w, true) =
      if t' = t ∧ w' = w ∧ P t w = true then 1 else 0 := by
  simp only [Verifier.flipIf, Matrix.of_apply]
  cases h : P t w <;> simp [h]

@[simp] theorem QMAPerfectCompleteness.Main.BlockProof.indexHadamard_zero_left (k : ℕ) (j : Fin (2 ^ k)) :
    indexHadamard k 0 j = 1 / ((Real.sqrt 2 : ℝ) : ℂ) ^ k := by
  simp [indexHadamard]

@[simp] theorem QMAPerfectCompleteness.Main.BlockProof.indexHadamard_zero_right (k : ℕ) (j : Fin (2 ^ k)) :
    indexHadamard k j 0 = 1 / ((Real.sqrt 2 : ℝ) : ℂ) ^ k := by
  simp [indexHadamard]

/-- Multiplying the two uniform Hadamard amplitudes gives exactly 1/M. -/
theorem QMAPerfectCompleteness.Main.BlockProof.uniform_amplitudes (k : ℕ) :
    (1 / ((Real.sqrt 2 : ℝ) : ℂ) ^ k) *
      (1 / ((Real.sqrt 2 : ℝ) : ℂ) ^ k) = 1 / (2 : ℂ) ^ k := by
  rw [one_div_mul_one_div, ← mul_pow, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- Sandwiching the all-zero index register averages the branches uniformly. -/
theorem QMAPerfectCompleteness.Main.BlockProof.blockUnitary_zero_index (k : ℕ) (z : V.Proof) (a b : ℕ) (y x : V.Body) :
    V.blockUnitary k z a b (0, y) (0, x) =
      (1 / (2 : ℂ) ^ k) * ∑ j : Fin (2 ^ k), V.branch z a b j y x := by
  classical
  rw [Verifier.blockUnitary, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.kronecker_apply]
  have h : (indexHadamard k * Matrix.single j j (1 : ℂ) * indexHadamard k) 0 0 =
      1 / (2 : ℂ) ^ k := by
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul, mul_ite]
    simpa only [one_div] using uniform_amplitudes k
  rw [h]

/-- The zEmbed matrix selects one basis state for each history basis vector. -/
theorem QMAPerfectCompleteness.Main.BlockProof.zEmbed_apply (k : ℕ) (f : Bool) (y : V.BlockReg k) (x : History V) :
    V.zEmbed k f y x = if y = (0, bodyInitial V f x) then 1 else 0 := by
  simp only [Verifier.zEmbed, Matrix.of_apply, bodyInitial, Prod.ext_iff]

/-- Taking the designated input and output ancilla block is simply entry selection. -/
theorem QMAPerfectCompleteness.Main.BlockProof.zEmbed_sandwich (k : ℕ) (f g : Bool)
    (M : Matrix (V.BlockReg k) (V.BlockReg k) ℂ) (y x : History V) :
    ((V.zEmbed k f)ᴴ * M * V.zEmbed k g) y x =
      M (0, bodyInitial V f y) (0, bodyInitial V g x) := by
  classical
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, zEmbed_apply]





/-- A finite range of c identical branches contributes exactly c copies. -/
theorem QMAPerfectCompleteness.Main.BlockProof.sum_cutoff (N c : ℕ) (hc : c ≤ N) (v : ℂ) :
    (∑ j : Fin N, if (j : ℕ) < c then v else 0) = (c : ℂ) * v := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < c then v else 0)]
  calc
    (∑ j ∈ Finset.range N, if j < c then v else 0) =
        ∑ j ∈ Finset.range c, if j < c then v else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hc)
      intro j _ hj
      simp only [Finset.mem_range, not_lt] at hj
      simp [not_lt.mpr hj]
    _ = ∑ j ∈ Finset.range c, v := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range.mp hj]
    _ = (c : ℂ) * v := by simp

/-- The three nonzero index ranges have multiplicities a, 2a and b. -/
theorem QMAPerfectCompleteness.Main.BlockProof.sum_three_ranges (N a b : ℕ) (hfit : 3 * a + b ≤ N) (X Y Z : ℂ) :
    (∑ j : Fin N, if (j : ℕ) < a then X else
      if (j : ℕ) < 3 * a then Y else if (j : ℕ) < 3 * a + b then Z else 0) =
      (a : ℂ) * X + (2 * a : ℂ) * Y + (b : ℂ) * Z := by
  classical
  have hpoint (j : Fin N) :
      (if (j : ℕ) < a then X else if (j : ℕ) < 3 * a then Y else
        if (j : ℕ) < 3 * a + b then Z else 0) =
      (if (j : ℕ) < a then X - Y else 0) +
        (if (j : ℕ) < 3 * a then Y - Z else 0) +
        (if (j : ℕ) < 3 * a + b then Z else 0) := by
    split_ifs <;> first | omega | ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [sum_cutoff N a (by omega), sum_cutoff N (3 * a) (by omega),
    sum_cutoff N (3 * a + b) hfit]
  push_cast
  ring

/-- Certificate validity guarantees that all three ranges fit in the index register. -/
theorem QMAPerfectCompleteness.Main.BlockProof.certificate_ranges_fit (V : Verifier gatesG2) (a b : ℕ)
    (h : IsValidCertificate V a b) : 3 * a + b ≤ 2 ^ indexQubits V := by
  rcases h with ⟨_, _, _, _, _, ha, hb⟩
  omega









/-- The identity branch flips the flag and hence yields the identity history block. -/
theorem QMAPerfectCompleteness.Main.BlockProof.flagX_history_block (y x : History V) :
    V.flagX (bodyInitial V false y) (bodyInitial V true x) = (1 : Matrix (History V) (History V) ℂ) y x := by
  classical
  simp only [Verifier.flagX, bodyInitial, flipIf_false_true, and_true]
  simp [(initialState_injective V).eq_iff, Matrix.one_apply, Prod.ext_iff]

/-- The unused index branches leave the flag one and contribute zero to rejection. -/
theorem QMAPerfectCompleteness.Main.BlockProof.identity_history_block (y x : History V) :
    (1 : Matrix V.Body V.Body ℂ) (bodyInitial V false y) (bodyInitial V true x) = 0 := by
  classical
  simp [Matrix.one_apply, bodyInitial]







/-- The exact averaged block, with its branch multiplicities exposed. -/
theorem QMAPerfectCompleteness.Main.BlockProof.averaged_rejection_block (k : ℕ) (z : V.Proof) (a b : ℕ)
    (hfit : 3 * a + b ≤ 2 ^ k) :
    (V.zEmbed k false)ᴴ * V.blockUnitary k z a b * V.zEmbed k true =
      (1 / (2 : ℂ) ^ k) •
        ((a : ℂ) • (1 : Matrix (History V) (History V) ℂ) -
          (2 * a : ℂ) • forwardBlock V - (b : ℂ) • closingBlock V z) := by
  classical
  ext y x
  rw [zEmbed_sandwich, blockUnitary_zero_index]
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  congr 1
  have hbranches (j : Fin (2 ^ k)) :
      V.branch z a b j (bodyInitial V false y) (bodyInitial V true x) =
      if (j : ℕ) < a then (1 : Matrix (History V) (History V) ℂ) y x else
        if (j : ℕ) < 3 * a then -forwardBlock V y x else
          if (j : ℕ) < 3 * a + b then -closingBlock V z y x else 0 := by
    unfold Verifier.branch
    split_ifs <;> simp_all [flagX_history_block, identity_history_block,
      forwardBlock, closingBlock]
  simp_rw [hbranches]
  rw [sum_three_ranges _ _ _ hfit]
  ring







/-- The exact algebraic clause of Lemma 3.6. This does not assert existence of the uniform
circuit compiler from the second clause of the platform theorem. -/
theorem solution (V : Verifier gatesG2) (z : V.Proof) (a b : ℕ)
    (hvalid : IsValidCertificate V a b) :
    (V.zEmbed (indexQubits V) false)ᴴ * V.blockUnitary (indexQubits V) z a b *
        V.zEmbed (indexQubits V) true =
      ((a : ℂ) / (2 : ℂ) ^ indexQubits V) • (1 - V.cyclicOp z ((a : ℝ) / b)) := by
  have ha : (a : ℂ) ≠ 0 := by
    have : 0 < a := hvalid.1
    exact_mod_cast (Nat.ne_of_gt this)
  rw [averaged_rejection_block V _ z a b (certificate_ranges_fit V a b hvalid),
    cyclicOp_decomposition]
  have hcoef : (a : ℂ) * ((((a : ℝ) / b)⁻¹ : ℝ) : ℂ) = b := by
    simp only [inv_div, Complex.ofReal_div, Complex.ofReal_natCast]
    field_simp
  let M : ℂ := 2 ^ indexQubits V
  let g : ℂ := ((((a : ℝ) / b)⁻¹ : ℝ) : ℂ)
  have h1 : (1 / M) * (a : ℂ) = (a : ℂ) / M := by ring
  have h2 : (1 / M) * (2 * a : ℂ) = ((a : ℂ) / M) * 2 := by ring
  have h3 : (1 / M) * (b : ℂ) = ((a : ℂ) / M) * g := by
    calc
      (1 / M) * (b : ℂ) = ((a : ℂ) * g) / M := by rw [show (a : ℂ) * g = b from hcoef]; ring
      _ = ((a : ℂ) / M) * g := by ring
  change (1 / M) • ((a : ℂ) • 1 - (2 * a : ℂ) • forwardBlock V -
      (b : ℂ) • closingBlock V z) =
    ((a : ℂ) / M) • (1 - ((2 : ℂ) • forwardBlock V + g • closingBlock V z))
  simp only [smul_sub, smul_add, smul_smul, h1, h2, h3]
  abel
