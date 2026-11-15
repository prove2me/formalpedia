-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.valid_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T12:17:38.346869+00:00
-- url     : https://prove2.me/submissions/d4a1514c-0f07-4b01-8b89-19c87b850865

import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding

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


/- Flattened from Solutions.Certificate -/
section

namespace QMAPerfectCompleteness.Main.Certificate

/-- The numerator/denominator rescaling in Lemma 3.7, separated from the spectral argument.
The same power of two multiplies both integers; the ratio is unchanged. -/
theorem rescale (a₀ b₀ n k : ℕ) (hb : 0 < b₀) (hgap : 2 * b₀ < a₀)
    (hsize : a₀ ≤ 2 ^ n) (hk : n + 4 ≤ k) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a < 2 ^ k ∧ b < 2 ^ k ∧
      2 ^ k ≤ 8 * a ∧ 4 * a ≤ 2 ^ k ∧ 2 * b ≤ a ∧
      (a : ℝ) / b = (a₀ : ℝ) / b₀ := by
  let u := Nat.clog 2 a₀
  let s := k - u - 2
  have ha : 1 < a₀ := by omega
  have hu : u ≤ n := Nat.clog_le_of_le_pow hsize
  have hu0 : 0 < u := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2
    simpa using ha
  have hs : s + u + 2 = k := by dsimp [s]; omega
  have haUpper : a₀ ≤ 2 ^ u := Nat.le_pow_clog (by decide) _
  have haLower : 2 ^ u ≤ 2 * a₀ := by
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) ha
    have heq : 2 ^ u = 2 * 2 ^ (u - 1) := by
      calc
        2 ^ u = 2 ^ ((u - 1) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (u - 1) := by rw [pow_succ]; omega
    rw [heq]
    dsimp [u] at *
    omega
  have hM : 2 ^ k = 4 * 2 ^ s * 2 ^ u := by
    rw [← hs, pow_add, pow_add]
    ring
  have hpow : 0 < 2 ^ s := by positivity
  have hapos : 0 < 2 ^ s * a₀ := Nat.mul_pos hpow (by omega)
  have hbpos : 0 < 2 ^ s * b₀ := Nat.mul_pos hpow hb
  have hupper : 4 * (2 ^ s * a₀) ≤ 2 ^ k := by
    rw [hM]
    nlinarith [Nat.mul_le_mul_left (4 * 2 ^ s) haUpper]
  have hlower : 2 ^ k ≤ 8 * (2 ^ s * a₀) := by
    rw [hM]
    nlinarith [Nat.mul_le_mul_left (4 * 2 ^ s) haLower]
  have hgap' : 2 * (2 ^ s * b₀) ≤ 2 ^ s * a₀ := by
    nlinarith [Nat.mul_le_mul_left (2 ^ s) (Nat.le_of_lt hgap)]
  refine ⟨2 ^ s * a₀, 2 ^ s * b₀, hapos, hbpos, by omega, by omega,
    hlower, hupper, hgap', ?_⟩
  push_cast
  rw [mul_div_mul_left _ _ (by positivity : (2 : ℝ) ^ s ≠ 0)]

/-- Lemma 3.7's arithmetic assembly for a chosen spectral witness. The remaining spectral
input is just `2 < Γ_z ≤ 2^ℓ`; the dyadic integrality is proved in `Dyadic.gamma_dyadic`. -/
theorem valid_certificate_of_diagonal (V : Verifier gatesG2) (z : V.Proof)
    (hgt : 2 < V.gamma z) (hle : V.gamma z ≤ 2 ^ ell V.proofQubits) :
    ∃ a b : ℕ, IsValidCertificate V a b ∧ (a : ℝ) / b = V.gamma z := by
  let h := 2 * hhCount V
  let l := ell V.proofQubits
  obtain ⟨q, hq⟩ := Dyadic.gamma_dyadic V z
  change (2 : ℝ) ^ (h * l) * V.gamma z = (q : ℝ) at hq
  let b₀ := 2 ^ (h * l)
  let a₀ := q.toNat
  have hb : 0 < b₀ := by dsimp [b₀]; positivity
  have hqpos : 0 < q := by
    have : (0 : ℝ) < q := by rw [← hq]; positivity
    exact_mod_cast this
  have hacast : (a₀ : ℝ) = (q : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hqpos))
  have hbcast : (b₀ : ℝ) = (2 : ℝ) ^ (h * l) := by dsimp [b₀]; norm_cast
  have hnum : (a₀ : ℝ) = (b₀ : ℝ) * V.gamma z := by rw [hacast, hbcast, hq]
  have hgap : 2 * b₀ < a₀ := by
    have hgapR : (2 : ℝ) * b₀ < a₀ := by
      rw [hnum]
      nlinarith [mul_lt_mul_of_pos_left hgt (by exact_mod_cast hb : (0 : ℝ) < b₀)]
    exact_mod_cast hgapR
  have hsize : a₀ ≤ 2 ^ ((h + 1) * l) := by
    have hsizeR : (a₀ : ℝ) ≤ (2 : ℝ) ^ ((h + 1) * l) := by
      calc
        (a₀ : ℝ) = (2 : ℝ) ^ (h * l) * V.gamma z := by rw [hnum, hbcast]
        _ ≤ (2 : ℝ) ^ (h * l) * 2 ^ l := mul_le_mul_of_nonneg_left hle (by positivity)
        _ = (2 : ℝ) ^ ((h + 1) * l) := by rw [← pow_add]; congr 1; ring
    exact_mod_cast hsizeR
  have hk : (h + 1) * l + 4 ≤ indexQubits V := by
    dsimp [indexQubits, h, l]
    omega
  obtain ⟨a, b, ha, hb', haM, hbM, hlow, hupp, hba, hratio⟩ :=
    rescale a₀ b₀ ((h + 1) * l) (indexQubits V) hb hgap hsize hk
  refine ⟨a, b, ⟨ha, hb', haM, hbM, hlow, hupp, hba⟩, hratio.trans ?_⟩
  apply (div_eq_iff (by exact_mod_cast (Nat.ne_of_gt hb) : (b₀ : ℝ) ≠ 0)).2
  rw [hnum]
  ring

end QMAPerfectCompleteness.Main.Certificate
end


/- Flattened from Solutions.EuclideanStates -/
section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QMAPerfectCompleteness.Main.VerifierAnalysis

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma euclidNorm_nonneg (v : ι → ℂ) : 0 ≤ euclidNorm v := Real.sqrt_nonneg _

lemma euclidNorm_sq (v : ι → ℂ) : euclidNorm v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma euclidNorm_smul (c : ℂ) (v : ι → ℂ) :
    euclidNorm (c • v) = ‖c‖ * euclidNorm v := by
  simp only [euclidNorm, Pi.smul_apply, norm_smul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

lemma euclidNorm_eq_zero_iff (v : ι → ℂ) : euclidNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hs : ∑ i, ‖v i‖ ^ 2 = 0 := by rw [← euclidNorm_sq, h]; norm_num
    funext i
    have hi : ‖v i‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hs i (Finset.mem_univ i)
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (v i)])
  · rintro rfl
    simp [euclidNorm]

lemma euclidNorm_pos (v : ι → ℂ) (hv : v ≠ 0) : 0 < euclidNorm v := by
  exact lt_of_le_of_ne (euclidNorm_nonneg v) (Ne.symm (mt (euclidNorm_eq_zero_iff v).mp hv))

/-- Normalize using the Euclidean norm, rather than the sup norm of a function type. -/
noncomputable def normalize (v : ι → ℂ) : ι → ℂ := ((euclidNorm v : ℂ)⁻¹) • v

lemma normalize_euclidNorm (v : ι → ℂ) (hv : v ≠ 0) : euclidNorm (normalize v) = 1 := by
  rw [normalize, euclidNorm_smul]
  simp [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (euclidNorm_nonneg v), ne_of_gt (euclidNorm_pos v hv)]

lemma normalize_kernel (B : Matrix κ ι ℂ) (v : ι → ℂ) (h : B *ᵥ v = 0) :
    B *ᵥ normalize v = 0 := by
  simp [normalize, Matrix.mulVec_smul, h]

/-- The rank-one matrix |v⟩⟨v|. -/
def pureDensity (v : ι → ℂ) : Matrix ι ι ℂ := vecMulVec v (star v)

lemma pureDensity_posSemidef (v : ι → ℂ) : (pureDensity v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

lemma pureDensity_trace [DecidableEq ι] (v : ι → ℂ) :
    (pureDensity v).trace = ((euclidNorm v ^ 2 : ℝ) : ℂ) := by
  rw [pureDensity, Matrix.trace_vecMulVec, euclidNorm_sq]
  simp [dotProduct, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma pureDensity_trace_one [DecidableEq ι] (v : ι → ℂ) (hv : euclidNorm v = 1) :
    (pureDensity v).trace = 1 := by rw [pureDensity_trace, hv]; norm_num

lemma pureDensity_expectation [DecidableEq ι] (E : Matrix ι ι ℂ) (v : ι → ℂ) :
    (E * pureDensity v).trace = star v ⬝ᵥ (E *ᵥ v) := by
  rw [pureDensity, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

/-- Squared norm as the quadratic form of a Gram matrix. -/
lemma gram_expectation [DecidableEq ι] (B : Matrix κ ι ℂ) (v : ι → ℂ) :
    star v ⬝ᵥ ((Bᴴ * B) *ᵥ v) = ((euclidNorm (B *ᵥ v) ^ 2 : ℝ) : ℂ) := by
  classical
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose,
    star_star, dotProduct_comm]
  simpa [pureDensity, Matrix.trace_vecMulVec] using pureDensity_trace (B *ᵥ v)

/-- The trace pairing of positive matrices is nonnegative even when they do not commute. -/
lemma trace_mul_posSemidef_nonneg [DecidableEq ι] (A R : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hR : R.PosSemidef) : 0 ≤ (A * R).trace.re := by
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.nonneg
  have hp := (hA.mul_mul_conjTranspose_same S).trace_nonneg
  have ht : (S * A * Sᴴ).trace = (A * (star S * S)).trace := by
    rw [Matrix.trace_mul_cycle, star_eq_conjTranspose, Matrix.trace_mul_comm]
  rw [ht] at hp
  exact (Complex.nonneg_iff.mp hp).1

/-- A uniform quadratic-form bound extends to every density matrix. -/
lemma mixed_bound_of_quadratic [DecidableEq ι] (E : Matrix ι ι ℂ) (q : ℝ)
    (hE : E.IsHermitian)
    (hq : ∀ v : ι → ℂ, q * euclidNorm v ^ 2 ≤ (star v ⬝ᵥ (E *ᵥ v)).re)
    (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    q ≤ (E * ρ).trace.re := by
  have hpos : (E - (q : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact hE.sub (Matrix.isHermitian_one.smul (show IsSelfAdjoint (q : ℂ) from by simp [IsSelfAdjoint]))
    · intro v
      apply Complex.nonneg_iff.mpr
      constructor
      · have hv := hq v
        have hs : star v ⬝ᵥ v = ((euclidNorm v ^ 2 : ℝ) : ℂ) := by
          rw [dotProduct_comm]
          simpa [pureDensity, Matrix.trace_vecMulVec] using pureDensity_trace v
        simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
          dotProduct_smul, hs, ← Complex.ofReal_pow] using sub_nonneg.mpr hv
      · exact ((hE.sub (Matrix.isHermitian_one.smul (show IsSelfAdjoint (q : ℂ) from by simp [IsSelfAdjoint]))).im_star_dotProduct_mulVec_self v).symm
  have hp := trace_mul_posSemidef_nonneg _ ρ hpos hρ
  simpa [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    htrace] using hp

end QMAPerfectCompleteness.Main.VerifierAnalysis
end


/- Flattened from Solutions.Cyclic -/
section

open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CyclicProof

variable {G : GateSet}

theorem history_ne_zero (V : Verifier G) (z : V.Proof) : V.historyVector z ≠ 0 := by
  intro h
  have h0 := congrFun h (0, z)
  simp [Verifier.historyVector] at h0

theorem acceptance_hermitian (V : Verifier G) : V.acceptanceOperator.IsHermitian := by
  have hP : V.acceptProjector.IsHermitian := by
    unfold Verifier.acceptProjector
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    ext w
    simp only [Pi.star_apply]
    split <;> simp
  have h := Matrix.isHermitian_conjTranspose_mul_mul (V.unitary * V.ancillaZero) hP
  simpa only [Verifier.acceptanceOperator, Matrix.conjTranspose_mul, Matrix.mul_assoc] using h

theorem doubled_hermitian (V : Verifier G) : V.doubled.IsHermitian := by
  exact (acceptance_hermitian V).smul (by norm_num : IsSelfAdjoint (2 : ℂ))

theorem gamma_eq_diagonal (V : Verifier G) (z : V.Proof) :
    (V.gamma z : ℂ) = (V.doubled ^ ell V.proofQubits) z z := by
  have h := (doubled_hermitian V).pow (ell V.proofQubits)
  have hz := congrArg (fun M : Matrix V.Proof V.Proof ℂ => (M z z).im) h.eq
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_im] at hz
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

theorem single_kronecker_mulVec {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (a b t : α) (p : β) (A : Matrix β β ℂ)
    (v : α × β → ℂ) :
    (((Matrix.single a b (1 : ℂ)) ⊗ₖ A) *ᵥ v) (t,p) =
      if t = a then (A *ᵥ fun q => v (b,q)) p else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.single_apply]
  by_cases h : t = a
  · subst t
    simp
  · simp [h, Ne.symm h]

theorem cyclic_mulVec_zero (V : Verifier G) (z : V.Proof) (Γ : ℝ)
    (v : History V → ℂ) (p : V.Proof) :
    (V.cyclicOp z Γ *ᵥ v) (0,p) =
      if p = z then (Γ⁻¹ : ℂ) * v (Fin.last (ell V.proofQubits),z) else 0 := by
  classical
  simp only [Verifier.cyclicOp, Matrix.add_mulVec, Matrix.sum_mulVec, Pi.add_apply,
    Finset.sum_apply, single_kronecker_mulVec]
  simp [Matrix.single_mulVec_eq, Fin.succ_ne_zero, Pi.single_apply, eq_comm]

theorem cyclic_mulVec_succ (V : Verifier G) (z : V.Proof) (Γ : ℝ)
    (v : History V → ℂ) (t : Fin (ell V.proofQubits)) (p : V.Proof) :
    (V.cyclicOp z Γ *ᵥ v) (t.succ,p) =
      (V.doubled *ᵥ fun q => v (t.castSucc,q)) p := by
  classical
  simp only [Verifier.cyclicOp, Matrix.add_mulVec, Matrix.sum_mulVec, Pi.add_apply,
    Finset.sum_apply, single_kronecker_mulVec]
  simp [Fin.succ_ne_zero]

/-- The cycle permutes the history summands exactly when its closing coefficient is honest. -/
theorem history_fixed (V : Verifier G) (z : V.Proof) (Γ : ℝ)
    (hΓ : Γ = V.gamma z) (hΓ0 : Γ ≠ 0) :
    V.cyclicOp z Γ *ᵥ V.historyVector z = V.historyVector z := by
  classical
  funext x
  obtain ⟨t,p⟩ := x
  refine Fin.cases ?_ (fun t => ?_) t
  · rw [cyclic_mulVec_zero]
    by_cases hp : p = z
    · subst p
      simp only [if_pos rfl, Verifier.historyVector, Fin.val_last, Fin.val_zero, pow_zero,
        Matrix.one_apply_eq]
      rw [← gamma_eq_diagonal V z, ← hΓ]
      simp [hΓ0]
    · simp [hp, Verifier.historyVector, eq_comm]
  · rw [cyclic_mulVec_succ]
    simp only [Verifier.historyVector, Fin.val_castSucc, Fin.val_succ, pow_succ',
      Matrix.mulVec, dotProduct, Matrix.mul_apply]

/-- Lemma 3.4(i), stronger than stated: the YES hypothesis is unnecessary once Γ is honest. -/
theorem history_kernel (V : Verifier G) (z : V.Proof) (Γ : ℝ)
    (hgamma : 2 < V.gamma z) (hΓ : Γ = V.gamma z) :
    V.historyVector z ≠ 0 ∧ (1 - V.cyclicOp z Γ) *ᵥ V.historyVector z = 0 := by
  refine ⟨history_ne_zero V z, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.one_mulVec,
    history_fixed V z Γ hΓ (by rw [hΓ]; linarith)]
  exact sub_self _

theorem cyclicOp_apply_zero (V : Verifier G) (z : V.Proof) (Γ : ℝ)
    (s : Clock V.proofQubits) (p q : V.Proof) :
    V.cyclicOp z Γ (0,p) (s,q) =
      if p = z ∧ s = Fin.last (ell V.proofQubits) ∧ q = z then ((Γ⁻¹ : ℝ) : ℂ) else 0 := by
  classical
  have h := cyclic_mulVec_zero V z Γ (Pi.single (s,q) 1) p
  simp only [Matrix.mulVec_single_one] at h
  by_cases hp : p = z <;> by_cases hs : s = Fin.last (ell V.proofQubits) <;>
    by_cases hq : q = z <;>
    simp_all [Pi.single_apply, Prod.mk.injEq]

theorem cyclicOp_apply_succ (V : Verifier G) (z : V.Proof) (Γ : ℝ)
    (t : Fin (ell V.proofQubits)) (s : Clock V.proofQubits) (p q : V.Proof) :
    V.cyclicOp z Γ (t.succ,p) (s,q) =
      if s = t.castSucc then V.doubled p q else 0 := by
  classical
  have h := cyclic_mulVec_succ V z Γ (Pi.single (s,q) 1) t p
  simp only [Matrix.mulVec_single_one] at h
  by_cases hs : s = t.castSucc
  · subst s
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Prod.mk.injEq, eq_comm] using h
  · simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Prod.mk.injEq, hs, Ne.symm hs] using h

open VerifierAnalysis

/-- The Euclidean triangle inequality, avoiding the sup norm on function types. -/
theorem euclidNorm_le_sub_add {ι : Type*} [Fintype ι] (v w : ι → ℂ) :
    euclidNorm v ≤ euclidNorm (v - w) + euclidNorm w := by
  have h := norm_add_le (WithLp.toLp 2 (v-w) : EuclideanSpace ℂ ι)
    (WithLp.toLp 2 w : EuclideanSpace ℂ ι)
  simpa only [← WithLp.toLp_add, sub_add_cancel, EuclideanSpace.norm_eq,
    PiLp.toLp_apply, euclidNorm] using h

/-- A contraction by 2/3 gives the paper's 1/3 lower bound for I-C. -/
theorem gap_of_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℂ) (hC : ∀ v, euclidNorm (C *ᵥ v) ≤ (2 / 3) * euclidNorm v)
    (v : ι → ℂ) : (1 / 3) * euclidNorm v ≤ euclidNorm ((1-C) *ᵥ v) := by
  have ht := euclidNorm_le_sub_add v (C *ᵥ v)
  have hc := hC v
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  linarith

/-- Squared norm of the rank-one closing transition is at most 4/9 times its input norm. -/
theorem closing_sq_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι) (Γ : ℝ) (hΓ : 2 ≤ Γ) (v : ι → ℂ) :
    (∑ p, ‖(if p = z then ((Γ⁻¹ : ℝ) : ℂ) * v z else 0)‖ ^ 2) ≤
      (4 / 9 : ℝ) * ∑ p, ‖v p‖ ^ 2 := by
  classical
  have hg : 0 < Γ := by linarith
  have hr : ‖((Γ⁻¹ : ℝ) : ℂ)‖ ≤ (2 / 3 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hg.le)]
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hΓ
    simp only [one_div] at hi
    linarith
  have hr2 : ‖((Γ⁻¹ : ℝ) : ℂ)‖ ^ 2 ≤ (4 / 9 : ℝ) := by
    nlinarith [norm_nonneg (((Γ⁻¹ : ℝ) : ℂ))]
  have hz : ‖v z‖ ^ 2 ≤ ∑ p, ‖v p‖ ^ 2 :=
    Finset.single_le_sum (fun p _ => sq_nonneg ‖v p‖) (Finset.mem_univ z)
  have heq : (∑ p, ‖(if p = z then ((Γ⁻¹ : ℝ) : ℂ) * v z else 0)‖ ^ 2) =
      ‖((Γ⁻¹ : ℝ) : ℂ)‖ ^ 2 * ‖v z‖ ^ 2 := by
    simp [apply_ite, norm_mul, mul_pow]
  rw [heq]
  exact mul_le_mul hr2 hz (sq_nonneg _) (by norm_num)

/-- The cyclic shift has disjoint output blocks, so blockwise contraction implies contraction
of the whole history. This is the norm argument in Eq. (4), written as a sum of squared norms. -/
theorem cyclic_contraction (V : Verifier G) (z : V.Proof) (Γ : ℝ) (hΓ : 2 ≤ Γ)
    (hA : ∀ v : V.Proof → ℂ,
      euclidNorm (V.doubled *ᵥ v) ≤ (2 / 3) * euclidNorm v) :
    ∀ v : History V → ℂ,
      euclidNorm (V.cyclicOp z Γ *ᵥ v) ≤ (2 / 3) * euclidNorm v := by
  intro v
  have hAsq (t : Fin (ell V.proofQubits)) :
      (∑ p, ‖(V.doubled *ᵥ fun q => v (t.castSucc,q)) p‖ ^ 2) ≤
        (4 / 9 : ℝ) * ∑ p, ‖v (t.castSucc,p)‖ ^ 2 := by
    have h := hA (fun q => v (t.castSucc,q))
    have hn := euclidNorm_nonneg (V.doubled *ᵥ fun q => v (t.castSucc,q))
    have hv := euclidNorm_nonneg (fun q => v (t.castSucc,q))
    rw [← euclidNorm_sq, ← euclidNorm_sq]
    nlinarith
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hAsq t)
  have hc := closing_sq_bound z Γ hΓ (fun p => v (Fin.last (ell V.proofQubits),p))
  simp only [Complex.ofReal_inv] at hc
  have htotal : euclidNorm (V.cyclicOp z Γ *ᵥ v) ^ 2 ≤
      (4 / 9 : ℝ) * euclidNorm v ^ 2 := by
    rw [euclidNorm_sq, euclidNorm_sq]
    simp only [Fintype.sum_prod_type]
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc (fun t => ∑ p, ‖v (t,p)‖ ^ 2)]
    simp only [cyclic_mulVec_zero, cyclic_mulVec_succ]
    rw [← Finset.mul_sum] at hs
    linarith
  have hn := euclidNorm_nonneg (V.cyclicOp z Γ *ᵥ v)
  have hv := euclidNorm_nonneg v
  nlinarith

/-- The soundness clause, with only the acceptance-operator contraction left as a hypothesis. -/
theorem cyclic_gap_of_doubled_contraction (V : Verifier G)
    (hA : ∀ v : V.Proof → ℂ,
      euclidNorm (V.doubled *ᵥ v) ≤ (2 / 3) * euclidNorm v)
    (z : V.Proof) (Γ : ℝ) (hΓ : 2 ≤ Γ) (v : History V → ℂ) :
    (1 / 3) * euclidNorm v ≤ euclidNorm ((1 - V.cyclicOp z Γ) *ᵥ v) := by
  exact gap_of_contraction _ (cyclic_contraction V z Γ hΓ hA) v

open scoped ComplexOrder

/-- Positivity of the acceptance operator follows directly from its compression formula. -/
theorem acceptance_posSemidef (V : Verifier G) : V.acceptanceOperator.PosSemidef := by
  have hp : V.acceptProjector.PosSemidef := by
    unfold Verifier.acceptProjector
    apply Matrix.PosSemidef.diagonal
    intro w
    change 0 ≤ (if w V.output then (1 : ℂ) else 0)
    split <;> simp
  have h := hp.conjTranspose_mul_mul_same (V.unitary * V.ancillaZero)
  simpa only [Verifier.acceptanceOperator, Matrix.conjTranspose_mul, Matrix.mul_assoc] using h

/-- Soundness bounds every eigenvalue, using a normalized pure eigenstate as the proof. -/
theorem acceptance_eigenvalue_le (V : Verifier G)
    (hno : V.AcceptsAllProofsAtMost (1 / 3)) (i : V.Proof) :
    (acceptance_hermitian V).eigenvalues i ≤ (1 / 3 : ℝ) := by
  let h := acceptance_hermitian V
  let v : V.Proof → ℂ := ⇑(h.eigenvectorBasis i)
  have hv : euclidNorm v = 1 := by
    have hv := h.eigenvectorBasis.orthonormal.1 i
    simpa only [EuclideanSpace.norm_eq, euclidNorm, v] using hv
  have hb := hno (pureDensity v) ⟨pureDensity_posSemidef v, pureDensity_trace_one v hv⟩
  change (V.acceptanceOperator * pureDensity v).trace.re ≤ (1 / 3 : ℝ) at hb
  rw [pureDensity_expectation] at hb
  rw [h.eigenvalues_eq]
  exact hb

open scoped Matrix.Norms.L2Operator

/-- The spectral theorem turns the eigenvalue interval [0,1/3] into a Euclidean operator bound. -/
theorem acceptance_opNorm_le (V : Verifier G)
    (hno : V.AcceptsAllProofsAtMost (1 / 3)) : ‖V.acceptanceOperator‖ ≤ (1 / 3 : ℝ) := by
  let h := acceptance_hermitian V
  rw [h.spectral_theorem, Unitary.conjStarAlgAut_apply]
  simp only [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)).2
  intro i
  change ‖((h.eigenvalues i : ℝ) : ℂ)‖ ≤ (1 / 3 : ℝ)
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ((acceptance_posSemidef V).eigenvalues_nonneg i)]
  exact acceptance_eigenvalue_le V hno i

/-- The NO-instance hypothesis gives precisely the contraction used in the paper. -/
theorem doubled_contraction (V : Verifier G) (hno : V.AcceptsAllProofsAtMost (1 / 3))
    (v : V.Proof → ℂ) :
    euclidNorm (V.doubled *ᵥ v) ≤ (2 / 3) * euclidNorm v := by
  have hn : ‖V.doubled‖ ≤ (2 / 3 : ℝ) := by
    rw [Verifier.doubled, norm_smul]
    norm_num
    linarith [acceptance_opNorm_le V hno]
  have hv := Matrix.l2_opNorm_mulVec V.doubled (WithLp.toLp 2 v)
  have heq (w : V.Proof → ℂ) : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ V.Proof)‖ = euclidNorm w := by
    rw [EuclideanSpace.norm_eq]
    rfl
  change ‖(WithLp.toLp 2 (V.doubled *ᵥ v) : EuclideanSpace ℂ V.Proof)‖ ≤
    ‖V.doubled‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ V.Proof)‖ at hv
  rw [heq, heq] at hv
  exact hv.trans (mul_le_mul_of_nonneg_right hn (euclidNorm_nonneg v))

/-- Lemma 3.4, proved without importing its platform placeholder. -/
theorem cyclic_constraint (V : Verifier gatesG2) :
    (V.AcceptsSomeProof (2 / 3) → ∀ (z : V.Proof) (Γ : ℝ), 2 < V.gamma z → Γ = V.gamma z →
      V.historyVector z ≠ 0 ∧ (1 - V.cyclicOp z Γ) *ᵥ V.historyVector z = 0) ∧
    (V.AcceptsAllProofsAtMost (1 / 3) → ∀ (z : V.Proof) (Γ : ℝ), 2 ≤ Γ → ∀ Ψ : History V → ℂ,
      (1 / 3) * euclidNorm Ψ ≤ euclidNorm ((1 - V.cyclicOp z Γ) *ᵥ Ψ)) := by
  constructor
  · intro _ z Γ hgamma hΓ
    exact history_kernel V z Γ hgamma hΓ
  · intro hno z Γ hΓ Ψ
    exact cyclic_gap_of_doubled_contraction V (doubled_contraction V hno) z Γ hΓ Ψ

end QMAPerfectCompleteness.Main.CyclicProof
end


/- Flattened from Solutions.CircuitUnitary -/
section

open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CircuitProof

/-- Split basis bits into the target bits of an instruction and untouched bits. -/
noncomputable def splitTargets {r n : ℕ} (e : Fin r ↪ Fin n) :
    Basis n ≃ Basis r × ({w : Fin n // w ∉ Set.range e} → Bool) := by
  classical
  let f : Basis n → Basis r × ({w : Fin n // w ∉ Set.range e} → Bool) :=
    fun x => (x ∘ e, fun w => x w)
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    funext w
    by_cases hw : w ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hw
      exact congrFun (congrArg Prod.fst h) a
    · exact congrFun (congrArg Prod.snd h) ⟨w,hw⟩
  · rintro ⟨a,b⟩
    let x : Basis n := fun w => if hw : w ∈ Set.range e then a (Classical.choose hw)
      else b ⟨w,hw⟩
    refine ⟨x, ?_⟩
    apply Prod.ext
    · funext j
      have hj : e j ∈ Set.range e := ⟨j,rfl⟩
      have hc : Classical.choose hj = j := e.injective (Classical.choose_spec hj)
      change (if hw : e j ∈ Set.range e then a (Classical.choose hw) else b ⟨e j,hw⟩) = a j
      rw [dif_pos hj, hc]
    · funext j
      change (if hw : (j : Fin n) ∈ Set.range e then a (Classical.choose hw)
        else b ⟨j,hw⟩) = b j
      simp [j.2]

@[simp] theorem splitTargets_fst {r n : ℕ} (e : Fin r ↪ Fin n) (x : Basis n) :
    (splitTargets e x).1 = x ∘ e := rfl

@[simp] theorem splitTargets_snd {r n : ℕ} (e : Fin r ↪ Fin n) (x : Basis n)
    (w : {w : Fin n // w ∉ Set.range e}) : (splitTargets e x).2 w = x w := rfl

lemma unaffected_iff {r n : ℕ} (e : Fin r ↪ Fin n) (x y : Basis n) :
    (∀ w, (∀ a, e a ≠ w) → y w = x w) ↔
      (splitTargets e y).2 = (splitTargets e x).2 := by
  classical
  constructor
  · intro h
    funext w
    exact h w (by simpa [Set.mem_range] using w.2)
  · intro h w hw
    exact congrFun h ⟨w, by simpa [Set.mem_range] using hw⟩

lemma instr_eq_submatrix {G : GateSet} {n : ℕ} (i : Instr G n) :
    i.matrix = (((G.get i.gate).matrix ⊗ₖ
      (1 : Matrix ({w : Fin n // w ∉ Set.range i.targets} → Bool)
        ({w : Fin n // w ∉ Set.range i.targets} → Bool) ℂ)).submatrix
      (splitTargets i.targets) (splitTargets i.targets)) := by
  classical
  ext y x
  simp only [Instr.matrix, Matrix.of_apply, Matrix.submatrix_apply, Matrix.kronecker_apply,
    splitTargets_fst, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, splitTargets_fst]
  by_cases h : ∀ w, (∀ a, i.targets a ≠ w) → y w = x w
  · have hr := (unaffected_iff i.targets x y).mp h
    rw [if_pos h, if_pos hr, mul_one]
  · have hr : (splitTargets i.targets y).2 ≠ (splitTargets i.targets x).2 :=
      mt (unaffected_iff i.targets x y).mpr h
    rw [if_neg h, if_neg hr, mul_zero]

lemma submatrix_unitary {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (A : Matrix β β ℂ) (hA : A ∈ Matrix.unitaryGroup β ℂ) :
    A.submatrix e e ∈ Matrix.unitaryGroup α ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix] at hA ⊢
  rw [Matrix.submatrix_mul_equiv A Aᴴ e e e, hA]
  simp

lemma kronecker_identity_unitary {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (A : Matrix α α ℂ) (hA : A ∈ Matrix.unitaryGroup α ℂ) :
    A ⊗ₖ (1 : Matrix β β ℂ) ∈ Matrix.unitaryGroup (α × β) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
  simp only [Matrix.star_eq_conjTranspose] at hA
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, hA, Matrix.one_mul,
    Matrix.one_kronecker_one]

/-- A placed instruction is unitary, including all untouched wires. -/
theorem instr_unitary {G : GateSet} {n : ℕ} (i : Instr G n) :
    i.matrix ∈ Matrix.unitaryGroup (Basis n) ℂ := by
  classical
  rw [instr_eq_submatrix]
  exact submatrix_unitary _ _ (kronecker_identity_unitary _ (G.get i.gate).unitary)

/-- Ordered products of placed gates are unitary. -/
theorem circuit_unitary {G : GateSet} {n : ℕ} (gs : List (Instr G n)) :
    circuitMatrix gs ∈ Matrix.unitaryGroup (Basis n) ℂ := by
  induction gs with
  | nil => exact one_mem _
  | cons g gs ih => exact mul_mem ih (instr_unitary g)

theorem verifier_unitary {G : GateSet} (V : Verifier G) :
    V.unitary ∈ Matrix.unitaryGroup V.Wire ℂ := circuit_unitary V.gates

theorem initialState_injective {G : GateSet} (V : Verifier G) :
    Function.Injective V.initialState := by
  intro p q hpq
  funext j
  have h := congrFun hpq (Fin.castAdd V.ancillaQubits j)
  simpa [Verifier.initialState] using h

/-- Initialization of the ancillas in zero is an isometry. -/
theorem ancillaZero_isometry {G : GateSet} (V : Verifier G) :
    V.ancillaZeroᴴ * V.ancillaZero = 1 := by
  classical
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Verifier.ancillaZero, Matrix.of_apply,
    apply_ite, star_one, star_zero, Matrix.one_apply]
  rw [Finset.sum_eq_single (V.initialState p)]
  · simp [initialState_injective V |>.eq_iff, eq_comm]
  · intro w _ hw
    simp [hw]
  · simp

open scoped ComplexOrder

/-- The complementary acceptance effect is positive, so all acceptance eigenvalues are ≤ 1. -/
theorem acceptance_complement_posSemidef {G : GateSet} (V : Verifier G) :
    (1 - V.acceptanceOperator).PosSemidef := by
  have hp : (1 - V.acceptProjector).PosSemidef := by
    have heq : 1 - V.acceptProjector =
        Matrix.diagonal (fun w : V.Wire => if w V.output then (0 : ℂ) else 1) := by
      ext y x
      by_cases hyx : y = x
      · subst x
        cases hy : y V.output <;> simp [Verifier.acceptProjector, hy]
      · simp [Verifier.acceptProjector, hyx]
    rw [heq]
    apply Matrix.PosSemidef.diagonal
    intro w
    change 0 ≤ (if w V.output then (0 : ℂ) else 1)
    split <;> simp
  have hu : V.unitaryᴴ * V.unitary = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (verifier_unitary V)
  have hj := ancillaZero_isometry V
  have hgram : (V.unitary * V.ancillaZero)ᴴ * (V.unitary * V.ancillaZero) = 1 := by
    calc
      _ = V.ancillaZeroᴴ * (V.unitaryᴴ * V.unitary) * V.ancillaZero := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hu, Matrix.mul_one]; exact hj
  have heq : (V.unitary * V.ancillaZero)ᴴ * V.acceptProjector *
      (V.unitary * V.ancillaZero) = V.acceptanceOperator := by
    simp only [Verifier.acceptanceOperator, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hc := hp.conjTranspose_mul_mul_same (V.unitary * V.ancillaZero)
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hgram, heq] using hc

end QMAPerfectCompleteness.Main.CircuitProof
end


/- Flattened from Solutions.DiagonalWitness -/
section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
namespace QMAPerfectCompleteness.Main.DiagonalProof
open CyclicProof VerifierAnalysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma psd_opNorm_le (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (s : ℝ)
    (hs : 0 ≤ s) (hbound : ∀ i, hA.1.eigenvalues i ≤ s) : ‖A‖ ≤ s := by
  rw [hA.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
  simp only [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hs).2
  intro i
  change ‖((hA.1.eigenvalues i : ℝ) : ℂ)‖ ≤ s
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)]
  exact hbound i

lemma quadratic_le_of_opNorm_le (A : Matrix ι ι ℂ) (s : ℝ) (hs : ‖A‖ ≤ s)
    (v : ι → ℂ) : (star v ⬝ᵥ (A *ᵥ v)).re ≤ s * euclidNorm v ^ 2 := by
  have hn (w : ι → ℂ) : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ ι)‖ = euclidNorm w := by
    rw [EuclideanSpace.norm_eq]
    rfl
  have hinner := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 v : EuclideanSpace ℂ ι)
    (WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ ι)
  have hmul := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 v)
  change ‖(WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ ι)‖ ≤
    ‖A‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ at hmul
  rw [hn, hn] at hmul
  rw [EuclideanSpace.inner_eq_star_dotProduct, hn, hn] at hinner
  change ‖(A *ᵥ v) ⬝ᵥ star v‖ ≤ euclidNorm v * euclidNorm (A *ᵥ v) at hinner
  rw [dotProduct_comm] at hinner
  have hre := Complex.re_le_norm (star v ⬝ᵥ (A *ᵥ v))
  have hb : euclidNorm (A *ᵥ v) ≤ s * euclidNorm v :=
    hmul.trans (mul_le_mul_of_nonneg_right hs (euclidNorm_nonneg v))
  nlinarith [euclidNorm_nonneg v]

/-- A mixed state accepted with probability c forces an eigenvalue at least c. -/
lemma exists_eigenvalue_ge (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (c : ℝ)
    (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1)
    (hc : c ≤ (A * ρ).trace.re) : ∃ i, c ≤ hA.1.eigenvalues i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ hA.1.eigenvalues Finset.univ_nonempty
  by_contra h
  push Not at h
  have hop := psd_opNorm_le A hA (hA.1.eigenvalues i) (hA.eigenvalues_nonneg i)
    (fun j => hi j (Finset.mem_univ j))
  have hquad := quadratic_le_of_opNorm_le A (hA.1.eigenvalues i) hop
  have hmixed := mixed_bound_of_quadratic (-A) (-hA.1.eigenvalues i) hA.1.neg
    (fun v => by
      have hv := hquad v
      simpa [Matrix.neg_mulVec, dotProduct_neg] using neg_le_neg hv) ρ hρ htrace
  simp only [Matrix.neg_mul, Matrix.trace_neg, Complex.neg_re] at hmixed
  linarith [h i]

lemma ell_lower_bound (m : ℕ) : 4 * (m+1) ≤ ell m := by
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) (4 * (m+1)+1)
  unfold ell clockQubits
  omega

lemma amplified_eigenvalue_lower_bound (m : ℕ) (mu : ℝ) (hmu : (4 / 3 : ℝ) ≤ mu) :
    (2 : ℝ) ^ (m+1) < mu ^ ell m := by
  have h4 : (2 : ℝ) < (4 / 3 : ℝ) ^ 4 := by norm_num
  have hp : (2 : ℝ) ^ (m+1) < ((4 / 3 : ℝ) ^ 4) ^ (m+1) := by
    exact pow_lt_pow_left₀ h4 (by norm_num) (by omega)
  calc
    (2 : ℝ) ^ (m+1) < ((4 / 3 : ℝ) ^ 4) ^ (m+1) := hp
    _ = (4 / 3 : ℝ) ^ (4*(m+1)) := (pow_mul _ _ _).symm
    _ ≤ (4 / 3 : ℝ) ^ ell m := pow_le_pow_right₀ (by norm_num) (ell_lower_bound m)
    _ ≤ mu ^ ell m := pow_le_pow_left₀ (by norm_num) hmu _

lemma trace_pow_eq_sum (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (n : ℕ) :
    (A ^ n).trace = ∑ i, ((hA.eigenvalues i : ℂ) ^ n) := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp [Matrix.diagonal_pow]

/-- The YES-instance diagonal witness in Lemma 3.3. No dyadic hypothesis is needed here. -/
theorem exists_diagonal_witness {G : GateSet} (V : Verifier G)
    (hyes : V.AcceptsSomeProof (2 / 3)) : ∃ z : V.Proof, 2 < V.gamma z := by
  obtain ⟨ρ, hρ, hc⟩ := hyes
  have hA : V.doubled.PosSemidef := by
    exact (acceptance_posSemidef V).smul (by norm_num : (0 : ℂ) ≤ 2)
  have hcA : (4 / 3 : ℝ) ≤ (V.doubled * ρ).trace.re := by
    have hc' : (2 / 3 : ℝ) ≤ (V.acceptanceOperator * ρ).trace.re := hc
    norm_num [Verifier.doubled, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re]
    linarith
  obtain ⟨i, hi⟩ := exists_eigenvalue_ge V.doubled hA (4 / 3) ρ hρ.1 hρ.2 hcA
  have htr : (2 : ℝ) ^ (V.proofQubits+1) <
      (V.doubled ^ ell V.proofQubits).trace.re := by
    calc
      (2 : ℝ) ^ (V.proofQubits+1) <
          (hA.1.eigenvalues i) ^ ell V.proofQubits :=
        amplified_eigenvalue_lower_bound V.proofQubits _ hi
      _ ≤ ∑ j, (hA.1.eigenvalues j) ^ ell V.proofQubits :=
        Finset.single_le_sum (fun j _ => pow_nonneg (hA.eigenvalues_nonneg j) _) (Finset.mem_univ i)
      _ = (V.doubled ^ ell V.proofQubits).trace.re := by
        rw [trace_pow_eq_sum _ hA.1]
        simp [← Complex.ofReal_pow]
  by_contra h
  push Not at h
  have hle : (V.doubled ^ ell V.proofQubits).trace.re ≤
      (2 : ℝ) ^ (V.proofQubits+1) := by
    calc
      (V.doubled ^ ell V.proofQubits).trace.re = ∑ z, V.gamma z := by
        simp [Matrix.trace, Verifier.gamma]
      _ ≤ ∑ _z : V.Proof, (2 : ℝ) := Finset.sum_le_sum (fun z _ => h z)
      _ = (2 : ℝ) ^ (V.proofQubits+1) := by
        simp [Verifier.Proof, Basis, pow_succ]
  linarith

/-- The gate-level verifier is a contraction, so its acceptance effect lies below identity. -/
lemma acceptance_eigenvalue_le_one {G : GateSet} (V : Verifier G) (i : V.Proof) :
    (acceptance_hermitian V).eigenvalues i ≤ 1 := by
  let h := acceptance_hermitian V
  let v : V.Proof → ℂ := ⇑(h.eigenvectorBasis i)
  have hv : euclidNorm v = 1 := by
    have hv := h.eigenvectorBasis.orthonormal.1 i
    simpa only [EuclideanSpace.norm_eq, euclidNorm, v] using hv
  have hp := trace_mul_posSemidef_nonneg _ (pureDensity v)
    (CircuitProof.acceptance_complement_posSemidef V) (pureDensity_posSemidef v)
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, pureDensity_trace_one v hv,
    Complex.sub_re, Complex.one_re, pureDensity_expectation] at hp
  rw [h.eigenvalues_eq]
  change (star v ⬝ᵥ (V.acceptanceOperator *ᵥ v)).re ≤ 1
  linarith

lemma acceptance_opNorm_le_one {G : GateSet} (V : Verifier G) :
    ‖V.acceptanceOperator‖ ≤ (1 : ℝ) := by
  exact psd_opNorm_le _ (acceptance_posSemidef V) 1 (by norm_num)
    (acceptance_eigenvalue_le_one V)

lemma gamma_nonneg {G : GateSet} (V : Verifier G) (z : V.Proof) : 0 ≤ V.gamma z := by
  have hA : V.doubled.PosSemidef :=
    (acceptance_posSemidef V).smul (by norm_num : (0 : ℂ) ≤ 2)
  have hp := (hA.pow (ell V.proofQubits)).diag_nonneg (i := z)
  exact (Complex.nonneg_iff.mp hp).1

lemma gamma_le_two_pow {G : GateSet} (V : Verifier G) (z : V.Proof) :
    V.gamma z ≤ (2 : ℝ) ^ ell V.proofQubits := by
  have hn : ‖V.doubled‖ ≤ (2 : ℝ) := by
    rw [Verifier.doubled, norm_smul]
    norm_num
    linarith [acceptance_opNorm_le_one V]
  have hpow : ‖V.doubled ^ ell V.proofQubits‖ ≤ (2 : ℝ) ^ ell V.proofQubits :=
    (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hn _)
  have hq := quadratic_le_of_opNorm_le (V.doubled ^ ell V.proofQubits)
    ((2 : ℝ) ^ ell V.proofQubits) hpow (Pi.single z 1)
  simpa [Verifier.gamma, Matrix.mulVec_single_one, euclidNorm, Pi.single_apply,
    dotProduct, apply_ite] using hq

end QMAPerfectCompleteness.Main.DiagonalProof
end


/- Flattened from Solutions.ValidCertificate -/
section

namespace QMAPerfectCompleteness.Main.Certificate

/-- Lemma 3.7: the spectral witness and exact rescaling produce an honest valid certificate. -/
theorem valid_certificate (V : Verifier gatesG2) (hyes : V.AcceptsSomeProof (2 / 3)) :
    ∃ (z : V.Proof) (a b : ℕ), IsValidCertificate V a b ∧
      (a : ℝ) / b = V.gamma z ∧ 2 < V.gamma z := by
  obtain ⟨z, hgt⟩ := DiagonalProof.exists_diagonal_witness V hyes
  obtain ⟨a,b,hvalid,hratio⟩ :=
    valid_certificate_of_diagonal V z hgt (DiagonalProof.gamma_le_two_pow V z)
  exact ⟨z,a,b,hvalid,hratio,hgt⟩

end QMAPerfectCompleteness.Main.Certificate
end


open Matrix QMAPerfectCompleteness.Main

/-- Lemma 3.7 (p. 11): on a YES instance there is a valid certificate with `a/b = Γ_z > 2`. -/
theorem solution (V : Verifier gatesG2) (hyes : V.AcceptsSomeProof (2 / 3)) :
    ∃ (z : V.Proof) (a b : ℕ), IsValidCertificate V a b ∧
      (a : ℝ) / b = V.gamma z ∧ 2 < V.gamma z := by
  exact QMAPerfectCompleteness.Main.Certificate.valid_certificate V hyes

#print axioms solution
