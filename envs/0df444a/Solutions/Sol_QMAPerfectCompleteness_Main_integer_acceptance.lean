-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.integer_acceptance
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T12:17:34.448454+00:00
-- url     : https://prove2.me/submissions/2a4cbee0-0a88-4c98-8524-6452e5554cd3

import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic

set_option autoImplicit false

/- Flattened from Solutions.Dyadic -/
section

open Matrix
namespace QMAPerfectCompleteness.Main.Dyadic

/-- Matrices all of whose entries are rational integers embedded in the complexes. -/
def IntegerEntries {ι κ : Type*} (M : Matrix ι κ ℂ) : Prop :=
  ∀ i j, M i j ∈ (Int.castRingHom ℂ).range

lemma integerEntries_iff {ι κ : Type*} (M : Matrix ι κ ℂ) :
    IntegerEntries M ↔ ∃ Z : Matrix ι κ ℤ, M = Z.map (Int.cast : ℤ → ℂ) := by
  constructor
  · intro h
    classical
    choose Z hZ using h
    exact ⟨Z, by ext i j; exact (hZ i j).symm⟩
  · rintro ⟨Z, rfl⟩ i j
    exact ⟨Z i j, rfl⟩

lemma integerEntries_mul {ι κ τ : Type*} [Fintype κ]
    (A : Matrix ι κ ℂ) (B : Matrix κ τ ℂ)
    (hA : IntegerEntries A) (hB : IntegerEntries B) : IntegerEntries (A * B) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

lemma integerEntries_one {ι : Type*} [DecidableEq ι] :
    IntegerEntries (1 : Matrix ι ι ℂ) := by
  intro i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

lemma integerEntries_conjTranspose {ι κ : Type*} (A : Matrix ι κ ℂ)
    (hA : IntegerEntries A) : IntegerEntries Aᴴ := by
  intro i j
  obtain ⟨z, hz⟩ := hA j i
  refine ⟨z, ?_⟩
  simp only [Matrix.conjTranspose_apply, ← hz]
  simp

lemma gate_integer (g : Fin gatesG2.length)
    (y x : Basis (gatesG2.get g).arity) :
    ((2 : ℂ) ^ (if g.val = 3 then 1 else 0)) * (gatesG2.get g).matrix y x ∈
      (Int.castRingHom ℂ).range := by
  fin_cases g <;> dsimp [gatesG2, gateX, gateCNOT, gateToffoli, gateHH] at * <;> norm_num only
  · change Basis 1 at y x
    rw [one_mul]
    change ∃ z : ℤ, (z : ℂ) = if y = ![!x 0] then 1 else 0
    refine ⟨(if y = ![!x 0] then 1 else 0), ?_⟩
    split_ifs <;> norm_num
  · change Basis 2 at y x
    rw [one_mul]
    change ∃ z : ℤ, (z : ℂ) = if y = ![x 0, xor (x 1) (x 0)] then 1 else 0
    refine ⟨(if y = ![x 0, xor (x 1) (x 0)] then 1 else 0), ?_⟩
    split_ifs <;> norm_num
  · change Basis 3 at y x
    rw [one_mul]
    change ∃ z : ℤ, (z : ℂ) = if y = ![x 0, x 1, xor (x 2) (x 0 && x 1)] then 1 else 0
    refine ⟨(if y = ![x 0, x 1, xor (x 2) (x 0 && x 1)] then 1 else 0), ?_⟩
    split_ifs <;> norm_num
  · change Basis 2 at y x
    change ∃ z : ℤ, (z : ℂ) = 2 *
      (if xor (y 0 && x 0) (y 1 && x 1) then -(1 / 2) else 1 / 2)
    refine ⟨(if xor (y 0 && x 0) (y 1 && x 1) then -1 else 1), ?_⟩
    split_ifs <;> norm_num

/-- One factor of two clears the denominator of an H⊗H instruction. -/
lemma integerEntries_instruction {n : ℕ} (i : Instr gatesG2 n) :
    IntegerEntries (((2 : ℂ) ^ (if i.gate.val = 3 then 1 else 0)) • i.matrix) := by
  intro y x
  change (2 : ℂ) ^ (if i.gate.val = 3 then 1 else 0) *
    (if ∀ w, (∀ a, i.targets a ≠ w) → y w = x w then
      (gatesG2.get i.gate).matrix (y ∘ i.targets) (x ∘ i.targets) else 0) ∈ _
  by_cases hout : ∀ w, (∀ a, i.targets a ≠ w) → y w = x w
  · rw [if_pos hout]
    exact gate_integer i.gate _ _
  · rw [if_neg hout, mul_zero]
    exact Subring.zero_mem _

/-- The paper's induction: `2^g V` is an integer matrix. -/
lemma integerEntries_circuit {n : ℕ} (gs : List (Instr gatesG2 n)) :
    IntegerEntries (((2 : ℂ) ^ (gs.countP fun i => i.gate.val == 3)) • circuitMatrix gs) := by
  induction gs with
  | nil => simpa [circuitMatrix] using (integerEntries_one (ι := Basis n))
  | cons i gs ih =>
    have hc : (i :: gs).countP (fun i => i.gate.val == 3) =
        gs.countP (fun i => i.gate.val == 3) + (if i.gate.val = 3 then 1 else 0) := by
      by_cases h : i.gate.val = 3 <;> simp [List.countP_cons, h]
    rw [hc, circuitMatrix, pow_add]
    have heq : ((2 : ℂ) ^ (gs.countP fun i => i.gate.val == 3) *
        2 ^ (if i.gate.val = 3 then 1 else 0)) • (circuitMatrix gs * i.matrix) =
        (((2 : ℂ) ^ (gs.countP fun i => i.gate.val == 3)) • circuitMatrix gs) *
        (((2 : ℂ) ^ (if i.gate.val = 3 then 1 else 0)) • i.matrix) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [heq]
    exact integerEntries_mul _ _ ih (integerEntries_instruction i)

lemma integerEntries_ancillaZero {G : GateSet} (V : Verifier G) :
    IntegerEntries V.ancillaZero := by
  intro i j
  simp only [Verifier.ancillaZero, Matrix.of_apply]
  split_ifs <;> simp

lemma integerEntries_acceptProjector {G : GateSet} (V : Verifier G) :
    IntegerEntries V.acceptProjector := by
  intro i j
  simp only [Verifier.acceptProjector, Matrix.diagonal_apply]
  split_ifs <;> simp

/-- Corollary 3.2, with the exact platform type. This proof uses no open paper theorems. -/
theorem integer_acceptance (V : Verifier gatesG2) :
    ∃ Z : Matrix V.Proof V.Proof ℤ,
      ((2 : ℂ) ^ (2 * hhCount V)) • V.acceptanceOperator = Z.map (Int.cast : ℤ → ℂ) := by
  apply (integerEntries_iff _).1
  have hU : IntegerEntries (((2 : ℂ) ^ hhCount V) • V.unitary) :=
    integerEntries_circuit V.gates
  have hUt : IntegerEntries (((2 : ℂ) ^ hhCount V) • V.unitaryᴴ) := by
    simpa using integerEntries_conjTranspose _ hU
  have h := integerEntries_mul _ _
    (integerEntries_mul _ _
      (integerEntries_mul _ _
        (integerEntries_mul _ _ (integerEntries_conjTranspose _ (integerEntries_ancillaZero V)) hUt)
        (integerEntries_acceptProjector V)) hU) (integerEntries_ancillaZero V)
  convert h using 1 <;>
    simp only [Verifier.acceptanceOperator, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      two_mul, pow_add]

lemma integerEntries_int_smul {ι κ : Type*} (z : ℤ) (A : Matrix ι κ ℂ)
    (hA : IntegerEntries A) : IntegerEntries ((z : ℂ) • A) := by
  intro i j
  exact Subring.mul_mem _ ⟨z, rfl⟩ (hA i j)

lemma integerEntries_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : IntegerEntries A) (k : ℕ) : IntegerEntries (A ^ k) := by
  induction k with
  | zero => simpa using (integerEntries_one (ι := ι))
  | succ k ih => simpa [pow_succ] using integerEntries_mul _ _ ih hA

/-- The arithmetic part of Lemma 3.3, for any exponent and without the `g ≥ 1` restriction. -/
lemma integerEntries_scaled_doubled_pow (V : Verifier gatesG2) (k : ℕ) :
    IntegerEntries (((2 : ℂ) ^ (2 * hhCount V * k)) • (V.doubled ^ k)) := by
  have hE : IntegerEntries (((2 : ℂ) ^ (2 * hhCount V)) • V.acceptanceOperator) :=
    (integerEntries_iff _).2 (integer_acceptance V)
  have hA : IntegerEntries (((2 : ℂ) ^ (2 * hhCount V)) • V.doubled) := by
    convert integerEntries_int_smul 2 _ hE using 1
    simp only [Verifier.doubled, smul_smul, Int.cast_ofNat]
    rw [mul_comm]
  simpa only [smul_pow, ← pow_mul] using integerEntries_pow _ hA k

/-- In particular, the exact diagonal value has dyadic denominator `2^(hℓ)`. -/
theorem gamma_dyadic (V : Verifier gatesG2) (z : V.Proof) :
    ∃ n : ℤ, (2 : ℝ) ^ (2 * hhCount V * ell V.proofQubits) * V.gamma z = n := by
  obtain ⟨n, hn⟩ := integerEntries_scaled_doubled_pow V (ell V.proofQubits) z z
  refine ⟨n, ?_⟩
  change (n : ℂ) = (2 : ℂ) ^ (2 * hhCount V * ell V.proofQubits) *
    (V.doubled ^ ell V.proofQubits) z z at hn
  have hpre (q : ℕ) : ((2 : ℂ) ^ q).re = (2 : ℝ) ^ q := by
    induction q with
    | zero => simp
    | succ q ih => simp [pow_succ, Complex.mul_re, ih]
  have hpim (q : ℕ) : ((2 : ℂ) ^ q).im = 0 := by
    induction q with
    | zero => simp
    | succ q ih => simp [pow_succ, Complex.mul_im, ih]
  have hre := congrArg Complex.re hn
  simpa only [Complex.mul_re, hpre, hpim, zero_mul, sub_zero, Complex.intCast_re,
    Verifier.gamma] using hre.symm

end QMAPerfectCompleteness.Main.Dyadic
end


open Matrix QMAPerfectCompleteness.Main

/-- Corollary 3.2 (p. 7): for a verifier over `𝒢₂` with `g` gates `H ⊗ H`, the matrix `2^{2g} E`
has integer entries. -/
theorem solution (V : Verifier gatesG2) :
    ∃ Z : Matrix V.Proof V.Proof ℤ,
      ((2 : ℂ) ^ (2 * hhCount V)) • V.acceptanceOperator = Z.map (Int.cast : ℤ → ℂ) := by
  exact QMAPerfectCompleteness.Main.Dyadic.integer_acceptance V

#print axioms solution
