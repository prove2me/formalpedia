-- Prove2me | solution 1 for ShiShallow.quadratic_form_transport_and_two_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-15T22:54:40.699818+00:00
-- url     : https://prove2.me/submissions/0bd83238-1a17-4558-a233-409ccd34c074

/-
CGLU-1: TWO GLUE LEMMAS, bundled as one conjunction.

WHY BOTH, WHY TOGETHER.  `ShiTensor.conjTranspose_majority_compression_three_blocks` (COMPR-1)
is an OPERATOR identity on the three-copy registers,

  Piᴴ * (P1*P2 + P2*P3 + P3*P1 - (2 : ℂ) • (P1*P2*P3)) * Pi
    = A1*A2 + A2*A3 + A3*A1 - (2 : ℂ) • (A1*A2*A3),

while `ShiShallow.majority_weight_eq_conj_majority_quadratic_form` is a SCALAR identity whose
right-hand side is the quadratic form of the majority polynomial, and which writes its cubic
term as `2 * (...)` -- a MATRIX numeral times a matrix, not a scalar `•`.  Two mismatches
therefore stand between the two accepted results, and neither is about majority polynomials:

* the operator-to-scalar step is a transport of a quadratic form through the RECTANGULAR `Q`
  (here `Pi`), moving `⟪Q psi, X (Q psi)⟫` on the big register to `⟪psi, (Qᴴ X Q) psi⟫` on the
  small one -- this is the generic adjoint relation, valid for any rectangular `Q` with no
  isometry hypothesis (isometry is what COMPR-1 already consumed internally);
* the numeral step is `(2 : Op N) * X = (2 : ℂ) • X`, reconciling the `2 * _` spelling of the
  accepted scalar theorem with the `(2 : ℂ) • _` spelling of the compression identity and of
  the spectral bound.

They are bundled because each is a three-line consequence of Mathlib and a compile on this
tower is expensive; nothing in either conjunct depends on the other, and the conjunction is
exactly as usable as the two separate statements.

CONJUNCT 1 IS NOT `Matrix.dotProduct_mulVec` RESTATED.  The two `∑` are over DIFFERENT index
types (`Bits M` left, `Bits N` right), so no rewriting inside a single sum can produce it; the
route is to recognise both sums as `dotProduct`s against `star`red vectors, push `Qᴴ` across
with `Matrix.dotProduct_mulVec` and `Matrix.vecMul_conjTranspose`, and undo the double star.
The `.re` is taken last, by `congrArg`, so no reality hypothesis on `X` is needed.

CONJUNCT 2 IS ABOUT A NUMERAL.  On the SQUARE type `Op N` the notation `_ * _` resolves through
the generic `instHMul` from `Mul (Matrix n n α)` (Mathlib gives `Matrix`'s rectangular `HMul`
the LOWER `default_instance 100` priority, `Data/Matrix/Mul.lean:291-295,302`), so `Op N` is
seen as a `NonAssocSemiring` and `two_mul` applies directly; the numeral is never unfolded to
`1 + 1` or `Nat.cast 2` by hand.  Both sides are routed through `X + X`.

No platform theorem is cited: both conjuncts are pure Mathlib matrix algebra, stated in the
`Bits`/`Op`/`QState` vocabulary of `Def_ShiShallow_Matrix` so they can be applied verbatim.

Parts A and B lift `shiWA_mulVec_conj` and `shiWA_adjoint` from the accepted `WACC-1`
(`ShiClassQMA` witness-space acceptance operator) unchanged except for the `shiGl_` prefix;
they were already stated there for a general rectangular `V : Matrix iota kappa ℂ`.

Built against Mathlib at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

open ShiShallow

/-! ### Part A: the conjugated operator, applied to a vector -/

/-- `(Vᴴ P V) psi = Vᴴ (P (V psi))`, as vectors.  Pure associativity of `mulVec`. -/
private lemma shiGl_mulVec_conj {iota kappa : Type} [Fintype iota] [Fintype kappa]
    (V : Matrix iota kappa ℂ) (P : Matrix iota iota ℂ) (psi : kappa → ℂ) :
    Matrix.mulVec (Matrix.conjTranspose V * P * V) psi
      = Matrix.mulVec (Matrix.conjTranspose V)
          (Matrix.mulVec P (Matrix.mulVec V psi)) := by
  first
  | (simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]; done)
  | (rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; done)
  | rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-! ### Part B: the adjoint relation across the sesquilinear pairing -/

/-- Moving `Vᴴ` across the pairing: the two sums live over DIFFERENT index types, and the
bridge is `dotProduct`. -/
private lemma shiGl_adjoint {iota kappa : Type} [Fintype iota] [Fintype kappa]
    (V : Matrix iota kappa ℂ) (psi : kappa → ℂ) (z : iota → ℂ) :
    (∑ u : kappa, (starRingEnd ℂ) (psi u) * Matrix.mulVec (Matrix.conjTranspose V) z u)
      = ∑ y : iota, (starRingEnd ℂ) (Matrix.mulVec V psi y) * z y := by
  have hL : (∑ u : kappa, (starRingEnd ℂ) (psi u)
        * Matrix.mulVec (Matrix.conjTranspose V) z u)
      = dotProduct (star psi) (Matrix.mulVec (Matrix.conjTranspose V) z) := by
    first
    | rfl
    | (simp only [dotProduct, Pi.star_apply, starRingEnd_apply]; done)
  have hR : (∑ y : iota, (starRingEnd ℂ) (Matrix.mulVec V psi y) * z y)
      = dotProduct (star (Matrix.mulVec V psi)) z := by
    first
    | rfl
    | (simp only [dotProduct, Pi.star_apply, starRingEnd_apply]; done)
  rw [hL, hR, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]

/-! ### Part C: the two glue statements -/

/-- **Two glue lemmas connecting the compression identity to the scalar majority theorem.**

The first conjunct transports a quadratic form through a RECTANGULAR matrix `Q`: the value of
the form of `X` at `Q psi` on the big register `Bits M` equals the value of the form of
`Qᴴ X Q` at `psi` on the small register `Bits N`.  No isometry, Hermitian-ness or normalisation
hypothesis is needed -- it is the adjoint relation and nothing more.

The second conjunct is the scalar bridge `(2 : Op N) * X = (2 : ℂ) • X`, identifying the matrix
numeral `2` acting by multiplication with the complex scalar `2` acting by `•`.  It is needed
because `ShiShallow.majority_weight_eq_conj_majority_quadratic_form` spells its cubic majority
term `2 * (...)` whereas the compression identity and the spectral bound spell theirs
`(2 : ℂ) • (...)`. -/
theorem solution {M N : ℕ} :
    (∀ (Q : Matrix (Bits M) (Bits N) ℂ) (X : Op M) (psi : QState N),
        (∑ y : Bits M, (starRingEnd ℂ) (Matrix.mulVec Q psi y)
              * Matrix.mulVec X (Matrix.mulVec Q psi) y).re
          = (∑ u : Bits N, (starRingEnd ℂ) (psi u)
              * Matrix.mulVec (Matrix.conjTranspose Q * X * Q) psi u).re)
      ∧ (∀ X : Op N, (2 : Op N) * X = (2 : ℂ) • X) := by
  refine ⟨?_, ?_⟩
  · intro Q X psi
    have hv : Matrix.mulVec (Matrix.conjTranspose Q * X * Q) psi
        = Matrix.mulVec (Matrix.conjTranspose Q)
            (Matrix.mulVec X (Matrix.mulVec Q psi)) :=
      shiGl_mulVec_conj Q X psi
    have hadj := shiGl_adjoint Q psi (Matrix.mulVec X (Matrix.mulVec Q psi))
    have hsum : (∑ u : Bits N, (starRingEnd ℂ) (psi u)
          * Matrix.mulVec (Matrix.conjTranspose Q * X * Q) psi u)
        = ∑ u : Bits N, (starRingEnd ℂ) (psi u)
            * Matrix.mulVec (Matrix.conjTranspose Q)
                (Matrix.mulVec X (Matrix.mulVec Q psi)) u := by
      first
      | exact Finset.sum_congr rfl fun u _ =>
          congrArg (HMul.hMul ((starRingEnd ℂ) (psi u))) (congrFun hv u)
      | (rw [hv]; done)
      | exact Finset.sum_congr rfl fun u _ => by rw [congrFun hv u]
    first
    | exact congrArg Complex.re (Eq.trans hadj.symm hsum.symm)
    | (refine congrArg Complex.re ?_; rw [hsum]; exact hadj.symm)
  · intro X
    first
    | (rw [two_mul X, two_smul ℂ X]; done)
    | (rw [two_smul ℂ X]; exact two_mul X)
    | (rw [two_mul X, two_smul]; done)
    | (simp only [two_mul, two_smul]; done)
    | (rw [two_mul X, ← one_add_one_eq_two, add_smul, one_smul]; done)
    | rw [two_mul X]
