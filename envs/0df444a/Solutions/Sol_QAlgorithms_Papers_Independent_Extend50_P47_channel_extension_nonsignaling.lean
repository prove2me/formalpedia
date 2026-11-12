-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P47.channel_extension_nonsignaling
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T02:37:52.354961+00:00
-- url     : https://prove2.me/submissions/8c2054f1-fc69-4bf0-9cf2-f92c5486f46d

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P47

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

variable {G S R P T A B C D R2 S2 : Type*}
variable [Fintype G] [Group G] [DecidableEq G]
variable [Fintype S] [DecidableEq S] [Nonempty S]
variable [Fintype R] [DecidableEq R] [Nonempty R]
variable [Fintype P] [DecidableEq P] [Nonempty P]
variable [Fintype T] [DecidableEq T] [Nonempty T]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype B] [DecidableEq B] [Nonempty B]
variable [Fintype C] [DecidableEq C] [Nonempty C]
variable [Fintype D] [DecidableEq D] [Nonempty D]
variable [Fintype R2] [DecidableEq R2] [Nonempty R2]
variable [Fintype S2] [DecidableEq S2] [Nonempty S2]

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P47 in
theorem solution [Nonempty S] [Nonempty R] [Nonempty R2] [Nonempty S2] (N : Superop S S2) (hN : IsChannel N)
    (M : Superop (R × S) (R2 × S2)) (hM : ChannelExtension N M) :
    ∀ X : Mat (R × S), traceLeft (M X) = traceLeft (M (replaceReference X)) := by
  intro X
  rw [hM.2, hM.2]
  congr 1
  have hR : (Fintype.card R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  ext b b'
  simp only [replaceReference, QAlgorithms.traceLeft, Matrix.of_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hR, one_mul]

end
