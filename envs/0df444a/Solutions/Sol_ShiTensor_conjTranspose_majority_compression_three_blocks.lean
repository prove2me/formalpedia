-- Prove2me | solution 1 for ShiTensor.conjTranspose_majority_compression_three_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-15T21:45:36.461151+00:00
-- url     : https://prove2.me/submissions/6292bd8c-308c-4865-badb-9622b9b2d1ce

/-
COMPR-1: the COMPRESSION IDENTITY for the three-block majority polynomial.

WHAT.  `W : Matrix (Bits m) (Bits w) ℂ` is a witness-embedding ISOMETRY
(`Matrix.conjTranspose W * W = 1`; `W` is NOT square, so `W * Matrix.conjTranspose W = 1` is
FALSE in general and is never used), `Pi = W ⊗ W ⊗ W`, and `P1, P2, P3` are the single-block
liftings `P ⊗ 1 ⊗ 1`, `1 ⊗ P ⊗ 1`, `1 ⊗ 1 ⊗ P` of one `P : Op m` in the amplitude-array form
of `Def_ShiTensor_Core` (identity blocks appear as index-agreement indicators).  Compressing
the majority polynomial yields that of `A = Matrix.conjTranspose W * P * W`.

WHY IT IS TRUE, AND WHERE THE ISOMETRY ENTERS.  Compression through a tensor product is
multiplicative slot-by-slot (`shiCp_compr`, which needs NO isometry): it is pure functoriality
of the amplitude-array product.  A product of liftings of DISTINCT blocks is again a single
tensor, e.g. `P1*P2 = P ⊗ P ⊗ 1`, so its compression is `(WᴴPW) ⊗ (WᴴPW) ⊗ (Wᴴ1W)`.  The ONLY
step that uses `conjTranspose W * W = 1` is the collapse of the UNTOUCHED slot,
`Wᴴ * 1 * W = Wᴴ * W = 1`; it is used exactly three times, once per quadratic term, and NOT AT
ALL for the cubic term `P1*P2*P3 = P ⊗ P ⊗ P`, which has no untouched slot.

`hW` IS LOAD-BEARING, NOT DECORATIVE.  Drop it and the statement is FALSE.  Witness: `m = w`,
`W = (1/2) • (1 : Op w)` (so `Wᴴ W = (1/4) • 1 =: B`, not `1`), `P = 1`.  Then every `Pk` is
`1` and `maj(P1,P2,P3) = 3 - 2 = 1`, so the left side is `Piᴴ Pi = B ⊗ B ⊗ B = (1/64) • 1`,
while `A = B` gives `maj(A1,A2,A3) = (3/16 - 2/64) • 1 = (5/32) • 1`.  `1/64 ≠ 5/32`.

NOT A GENERAL FACT.  Compression does NOT commute with products of liftings of the SAME
block: `Piᴴ P1^2 Pi = (Wᴴ P^2 W) ⊗ 1 ⊗ 1` while `(Piᴴ P1 Pi)^2 = (Wᴴ P W Wᴴ P W) ⊗ 1 ⊗ 1`,
differing unless `W Wᴴ = 1`.  Multilinearity of the majority polynomial in the three blocks is
exactly why it survives compression; the same failure at repeated factors is why `A` is a
genuine non-projector even for projector `P`.

FORMULATION: operator identity, not the scalar quadratic-form identity -- the latter is this
identity PLUS a generic transport of a quadratic form through a rectangular matrix.
`P1, P2, P3, A1, A2, A3, Pi` are variables pinned by EXPLICIT entrywise equations in
`leftBits`/`rightBits`, the idiom of `ShiTensor.mulVec_block_extend_tensor_eigenvector`.

Only platform theorem cited: `ShiTensor.sum_split_factor`.

Built against Mathlib at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Matrix
import Definitions.Def_ShiTensor_Core
import Theorems.Thm_ShiTensor_sum_split_factor

set_option autoImplicit false

open ShiShallow
open ShiTensor

/-- Amplitude-array tensor product of two RECTANGULAR matrices. -/
private def shiCp_kron {a b c d : ℕ}
    (X : Matrix (Bits a) (Bits b) ℂ) (Y : Matrix (Bits c) (Bits d) ℂ) :
    Matrix (Bits (a + c)) (Bits (b + d)) ℂ :=
  Matrix.of fun y u => X (leftBits y) (leftBits u) * Y (rightBits y) (rightBits u)

private lemma shiCp_kron_apply {a b c d : ℕ}
    (X : Matrix (Bits a) (Bits b) ℂ) (Y : Matrix (Bits c) (Bits d) ℂ)
    (y : Bits (a + c)) (u : Bits (b + d)) :
    shiCp_kron X Y y u
      = X (leftBits y) (leftBits u) * Y (rightBits y) (rightBits u) := rfl

/-- Functoriality of the amplitude-array product: the product of two krons is the kron of the
products.  The index sum over the middle register splits by `ShiTensor.sum_split_factor`. -/
private lemma shiCp_kron_mul {a b c d e f : ℕ}
    (X : Matrix (Bits a) (Bits b) ℂ) (X' : Matrix (Bits b) (Bits c) ℂ)
    (Y : Matrix (Bits d) (Bits e) ℂ) (Y' : Matrix (Bits e) (Bits f) ℂ) :
    shiCp_kron X Y * shiCp_kron X' Y' = shiCp_kron (X * X') (Y * Y') := by
  classical
  ext y u
  have hstep : ∀ z : Bits (b + e),
      shiCp_kron X Y y z * shiCp_kron X' Y' z u
        = (X (leftBits y) (leftBits z) * X' (leftBits z) (leftBits u))
          * (Y (rightBits y) (rightBits z) * Y' (rightBits z) (rightBits u)) := by
    intro z
    first
      | (simp only [shiCp_kron_apply]; ring; done)
      | (rw [shiCp_kron_apply, shiCp_kron_apply]; ring; done)
      | simp [shiCp_kron_apply, mul_assoc, mul_comm, mul_left_comm]
  calc (shiCp_kron X Y * shiCp_kron X' Y') y u
      = ∑ z : Bits (b + e), shiCp_kron X Y y z * shiCp_kron X' Y' z u :=
        Matrix.mul_apply
    _ = ∑ z : Bits (b + e),
          (X (leftBits y) (leftBits z) * X' (leftBits z) (leftBits u))
            * (Y (rightBits y) (rightBits z) * Y' (rightBits z) (rightBits u)) :=
        Finset.sum_congr rfl fun z _ => hstep z
    _ = (∑ p : Bits b, X (leftBits y) p * X' p (leftBits u))
          * ∑ q : Bits e, Y (rightBits y) q * Y' q (rightBits u) :=
        sum_split_factor (fun p => X (leftBits y) p * X' p (leftBits u))
          (fun q => Y (rightBits y) q * Y' q (rightBits u))
    _ = shiCp_kron (X * X') (Y * Y') y u := by
        first
          | (rw [shiCp_kron_apply, Matrix.mul_apply, Matrix.mul_apply]; done)
          | (simp only [shiCp_kron_apply, Matrix.mul_apply]; done)
          | rw [shiCp_kron_apply, Matrix.mul_apply, Matrix.mul_apply]

/-- The conjugate transpose of a kron is the kron of the conjugate transposes. -/
private lemma shiCp_conjTranspose_kron {a b c d : ℕ}
    (X : Matrix (Bits a) (Bits b) ℂ) (Y : Matrix (Bits c) (Bits d) ℂ) :
    Matrix.conjTranspose (shiCp_kron X Y)
      = shiCp_kron (Matrix.conjTranspose X) (Matrix.conjTranspose Y) := by
  ext u y
  first
    | (simp only [Matrix.conjTranspose_apply, shiCp_kron_apply, star_mul']; done)
    | (simp only [Matrix.conjTranspose_apply, shiCp_kron_apply, star_mul, mul_comm]; done)
    | simp [Matrix.conjTranspose_apply, shiCp_kron_apply, star_mul']

/-- SLOT-BY-SLOT COMPRESSION, needing NO isometry hypothesis: conjugating a kron of operators
by a kron of (rectangular) matrices compresses each slot separately. -/
private lemma shiCp_compr {a b c d : ℕ}
    (X : Matrix (Bits a) (Bits b) ℂ) (Y : Matrix (Bits c) (Bits d) ℂ)
    (S : Op a) (T : Op c) :
    Matrix.conjTranspose (shiCp_kron X Y) * shiCp_kron S T * shiCp_kron X Y
      = shiCp_kron (Matrix.conjTranspose X * S * X) (Matrix.conjTranspose Y * T * Y) := by
  rw [shiCp_conjTranspose_kron, shiCp_kron_mul, shiCp_kron_mul]

/-- Three-slot compression through `W ⊗ W ⊗ W`.  Still isometry-free. -/
private lemma shiCp_compr3 {m w : ℕ} (W : Matrix (Bits m) (Bits w) ℂ) (S T U : Op m) :
    Matrix.conjTranspose (shiCp_kron (shiCp_kron W W) W)
        * shiCp_kron (shiCp_kron S T) U * shiCp_kron (shiCp_kron W W) W
      = shiCp_kron (shiCp_kron (Matrix.conjTranspose W * S * W)
          (Matrix.conjTranspose W * T * W)) (Matrix.conjTranspose W * U * W) := by
  rw [shiCp_compr (shiCp_kron W W) W (shiCp_kron S T) U, shiCp_compr W W S T]

/-- Three-slot products multiply slotwise. -/
private lemma shiCp_slots_mul {m : ℕ} (S T U S' T' U' : Op m) :
    shiCp_kron (shiCp_kron S T) U * shiCp_kron (shiCp_kron S' T') U'
      = shiCp_kron (shiCp_kron (S * S') (T * T')) (U * U') := by
  rw [shiCp_kron_mul, shiCp_kron_mul]

/-- **Compression of the three-block majority polynomial through a witness-embedding
isometry.**  `Pi = W ⊗ W ⊗ W`; `P1, P2, P3` are the single-block liftings of `P : Op m` to the
three-copy circuit register and `A1, A2, A3` those of the compression
`A = Matrix.conjTranspose W * P * W` to the three-copy witness register, all given by explicit
entrywise formulas in `ShiTensor.leftBits`/`ShiTensor.rightBits` (an identity block appears as
the indicator of its two index halves agreeing).  The isometry hypothesis is used only to
collapse the one slot left untouched by each quadratic term. -/
theorem solution {m w : ℕ}
    (W : Matrix (Bits m) (Bits w) ℂ)
    (hW : Matrix.conjTranspose W * W = (1 : Op w))
    (P : Op m) (A : Op w) (hA : A = Matrix.conjTranspose W * P * W)
    (Pi : Matrix (Bits (m + m + m)) (Bits (w + w + w)) ℂ)
    (hPi : Pi = Matrix.of fun (y : Bits (m + m + m)) (u : Bits (w + w + w)) =>
      W (leftBits (leftBits y)) (leftBits (leftBits u))
        * W (rightBits (leftBits y)) (rightBits (leftBits u))
        * W (rightBits y) (rightBits u))
    (P1 P2 P3 : Op (m + m + m))
    (hP1 : P1 = Matrix.of fun y z =>
      P (leftBits (leftBits y)) (leftBits (leftBits z))
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * (if rightBits y = rightBits z then 1 else 0))
    (hP2 : P2 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * P (rightBits (leftBits y)) (rightBits (leftBits z))
        * (if rightBits y = rightBits z then 1 else 0))
    (hP3 : P3 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * P (rightBits y) (rightBits z))
    (A1 A2 A3 : Op (w + w + w))
    (hA1 : A1 = Matrix.of fun y z =>
      A (leftBits (leftBits y)) (leftBits (leftBits z))
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * (if rightBits y = rightBits z then 1 else 0))
    (hA2 : A2 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * A (rightBits (leftBits y)) (rightBits (leftBits z))
        * (if rightBits y = rightBits z then 1 else 0))
    (hA3 : A3 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * A (rightBits y) (rightBits z)) :
    Matrix.conjTranspose Pi
        * (P1 * P2 + P2 * P3 + P3 * P1 - (2 : ℂ) • (P1 * P2 * P3)) * Pi
      = A1 * A2 + A2 * A3 + A3 * A1 - (2 : ℂ) • (A1 * A2 * A3) := by
  classical
  subst hA
  -- Step 1: recognise the seven explicit entrywise matrices as krons.
  have kPi : Pi = shiCp_kron (shiCp_kron W W) W := by
    rw [hPi]
    ext y u
    first
      | (simp only [Matrix.of_apply, shiCp_kron_apply]; done)
      | rfl
  have kP : P1 = shiCp_kron (shiCp_kron P (1 : Op m)) (1 : Op m)
      ∧ P2 = shiCp_kron (shiCp_kron (1 : Op m) P) (1 : Op m)
      ∧ P3 = shiCp_kron (shiCp_kron (1 : Op m) (1 : Op m)) P := by
    rw [hP1, hP2, hP3]
    refine ⟨?_, ?_, ?_⟩ <;>
      (ext y z; simp only [Matrix.of_apply, shiCp_kron_apply, Matrix.one_apply])
  have kA : A1 = shiCp_kron (shiCp_kron (Matrix.conjTranspose W * P * W) (1 : Op w)) (1 : Op w)
      ∧ A2 = shiCp_kron (shiCp_kron (1 : Op w) (Matrix.conjTranspose W * P * W)) (1 : Op w)
      ∧ A3 = shiCp_kron (shiCp_kron (1 : Op w) (1 : Op w))
          (Matrix.conjTranspose W * P * W) := by
    rw [hA1, hA2, hA3]
    refine ⟨?_, ?_, ?_⟩ <;>
      (ext y z; simp only [Matrix.of_apply, shiCp_kron_apply, Matrix.one_apply])
  obtain ⟨k1, k2, k3⟩ := kP
  obtain ⟨l1, l2, l3⟩ := kA
  -- Step 2: the four compressions.  Each quadratic term collapses ONE untouched slot via `hW`;
  -- the cubic term uses no slot collapse at all.
  have e12 : Matrix.conjTranspose Pi * (P1 * P2) * Pi = A1 * A2 := by
    rw [kPi, k1, k2, l1, l2]
    first
      | (simp only [shiCp_slots_mul, shiCp_compr3, Matrix.mul_one, Matrix.one_mul, hW]; done)
      | simp [shiCp_slots_mul, shiCp_compr3, hW]
  have e23 : Matrix.conjTranspose Pi * (P2 * P3) * Pi = A2 * A3 := by
    rw [kPi, k2, k3, l2, l3]
    first
      | (simp only [shiCp_slots_mul, shiCp_compr3, Matrix.mul_one, Matrix.one_mul, hW]; done)
      | simp [shiCp_slots_mul, shiCp_compr3, hW]
  have e31 : Matrix.conjTranspose Pi * (P3 * P1) * Pi = A3 * A1 := by
    rw [kPi, k3, k1, l3, l1]
    first
      | (simp only [shiCp_slots_mul, shiCp_compr3, Matrix.mul_one, Matrix.one_mul, hW]; done)
      | simp [shiCp_slots_mul, shiCp_compr3, hW]
  have e123 : Matrix.conjTranspose Pi * (P1 * P2 * P3) * Pi = A1 * A2 * A3 := by
    rw [kPi, k1, k2, k3, l1, l2, l3]
    first
      | (simp only [shiCp_slots_mul, shiCp_compr3, Matrix.mul_one, Matrix.one_mul]; done)
      | simp [shiCp_slots_mul, shiCp_compr3]
  -- Step 3: compression is linear, so distribute it over the polynomial.  The distributive
  -- laws MUST be the `Matrix.*` ones: `Matrix.conjTranspose Pi * _` is the RECTANGULAR `HMul`,
  -- which the `Distrib`/`MulOneClass` lemmas `mul_add`/`mul_one` cannot match.
  first
    | (rw [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.sub_mul,
        Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, e12, e23, e31, e123]; done)
    | (simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.smul_mul, e12, e23, e31, e123]; done)
    | simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.smul_mul, e12, e23, e31, e123]
