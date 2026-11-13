-- Prove2me | solution 1 for ThreeSigma.Upper.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T17:10:23.207277+00:00
-- url     : https://prove2.me/submissions/25e342d5-7b6f-4e7d-87a9-d46f38fa4355

import Mathlib
import Definitions.Def_ThreeSigma_Upper_Geometry

section
/-!
# Spencer's discrepancy theorem: complete upper and lower bounds

Self-contained (relative to Mathlib) combination of the original
`SpencerUpperBound.lean` and `SpencerLowerBound.lean` sources.

Requested toolchain: `leanprover/lean4:v4.36.0-rc2`.
The sources were originally developed against Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The final two theorem declarations are:
* `Stoc393.theorem_1_1 : Stoc393.LowerBoundClaim`
* `Stoc393.theorem_1_2 : Stoc393.UpperBoundClaim`

The proofs needed by earlier corollaries are named
`Stoc393.lowerBoundClaim_proof` and `Stoc393.upperBoundClaim_proof`.
-/

/- BEGIN original module: Stoc393.Basic -/
section

/-! Definitions and the nearest-sign rounding argument (Lemma 3.2).
The norm on `Fin d → ℝ` is the maximum absolute coordinate norm.
-/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

def InCube {n : ℕ} (z : Fin n → ℝ) : Prop := ∀ j, |z j| ≤ 1

def EntryBounded {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) : Prop :=
  ∀ i j, |A i j| ≤ 1

noncomputable def residual {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  n - ∑ j, z j ^ 2

noncomputable def nearestSign {n : ℕ} (z : Fin n → ℝ) (j : Fin n) : ℝ :=
  if 0 ≤ z j then 1 else -1

theorem sq_le_abs_of_abs_le_one {t : ℝ} (ht : |t| ≤ 1) : t ^ 2 ≤ |t| := by
  have h := mul_le_mul_of_nonneg_left ht (abs_nonneg t)
  nlinarith [sq_abs t]

theorem nearestSign_distance {n : ℕ} {z : Fin n → ℝ} (hz : InCube z)
    (j : Fin n) : |nearestSign z j - z j| = 1 - |z j| := by
  have h := abs_le.mp (hz j)
  unfold nearestSign
  split_ifs with hj
  · rw [abs_of_nonneg hj, abs_of_nonneg (by linarith)]
  · have hj' : z j < 0 := lt_of_not_ge hj
    rw [abs_of_neg hj', abs_of_nonpos (by linarith)]
    ring

theorem rounding_distance_le_residual {n : ℕ} {z : Fin n → ℝ} (hz : InCube z) :
    (∑ j, |nearestSign z j - z j|) ≤ residual z := by
  calc
    (∑ j, |nearestSign z j - z j|) = ∑ j, (1 - |z j|) := by
      apply Finset.sum_congr rfl
      intro j _
      exact nearestSign_distance hz j
    _ ≤ ∑ j, (1 - z j ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      linarith [sq_le_abs_of_abs_le_one (hz j)]
    _ = residual z := by simp [residual, Finset.sum_sub_distrib]

theorem row_action_le_l1 {d n : ℕ} {A : Matrix (Fin d) (Fin n) ℝ}
    (hA : EntryBounded A) (v : Fin n → ℝ) (i : Fin d) :
    |A.mulVec v i| ≤ ∑ j, |v j| := by
  calc
    |A.mulVec v i| = |∑ j, A i j * v j| := rfl
    _ ≤ ∑ j, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |v j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_right (hA i j) (abs_nonneg (v j))

theorem matrix_action_le_l1 {d n : ℕ} {A : Matrix (Fin d) (Fin n) ℝ}
    (hA : EntryBounded A) (v : Fin n → ℝ) :
    ‖A.mulVec v‖ ≤ ∑ j, |v j| := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _))).mpr
  intro i
  simpa only [Real.norm_eq_abs] using row_action_le_l1 hA v i

/-- Lemma 3.2, with the paper's residual and its specified tie-breaking at zero. -/
theorem lemma_3_2 {d n : ℕ} {A : Matrix (Fin d) (Fin n) ℝ}
    (hA : EntryBounded A) {z : Fin n → ℝ} (hz : InCube z) :
    ‖A.mulVec (nearestSign z)‖ ≤ ‖A.mulVec z‖ + residual z := by
  have hdecomp : A.mulVec (nearestSign z) =
      A.mulVec z + A.mulVec (nearestSign z - z) := by
    rw [Matrix.mulVec_sub]
    abel
  rw [hdecomp]
  exact (norm_add_le _ _).trans (add_le_add le_rfl
    ((matrix_action_le_l1 hA _).trans (rounding_distance_le_residual hz)))

end Stoc393

end
/- END original module: Stoc393.Basic -/

/- BEGIN original module: Stoc393.Targets -/
section

/-! Exact main targets. `UpperBound.lean` proves `UpperBoundClaim`;
`LowerBound.lean` proves `LowerBoundClaim`.
The lower-bound probability is represented by exact uniform counting of all
random replacement matrices. The all-signings event is the meaning of
`disc(A) > threshold`, without needing to choose a minimizer.
-/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.Targets -/

/- BEGIN original module: Stoc393.CappedTrace -/
section

/-! The capped trace argument underlying Lemma 3.4.
The orthonormal-basis construction follows the proof in the PDF, with the
heavy/light decomposition also used in the earlier local Spencer3.lean file.
-/

open scoped BigOperators
open Module
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.CappedTrace -/

/- BEGIN original module: Stoc393.ScalarReduction -/
section

/-! Algebraic implications surrounding the scalar inequality.
The comparison is an explicit hypothesis in this abstract reduction.
`ScalarBarrier.lean` proves it for the paper's concrete function.
-/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.ScalarReduction -/

/- BEGIN original module: Stoc393.ScalarCalculus -/
section

/-! Elementary scalar calculus from Appendix C.
No assertion of the unproved equation (27) is made in this module.
-/

set_option autoImplicit false

namespace Stoc393

open scoped Topology

end Stoc393

end
/- END original module: Stoc393.ScalarCalculus -/

/- BEGIN original module: Stoc393.ScalarPQ -/
section

/-! Analytic proof supplied by the user on 2026-10-30: the P + Q estimates. -/

open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.ScalarPQ -/

/- BEGIN original module: Stoc393.ScalarBarrier -/
section

/-! Equation (27), completing the analytic argument supplied by the user.
The proof uses exact real inequalities and algebra, not sampled values.
-/

set_option autoImplicit false
namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.ScalarBarrier -/

/- BEGIN original module: Stoc393.SecondVariation -/
section

/-! The second variation of the reciprocal-sinh potential, Lemma 3.5.
The abstract curve rule adapts the checked local Spencer3.lean construction.
-/

open scoped Topology BigOperators
open Filter
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.SecondVariation -/

/- BEGIN original module: Stoc393.PotentialCompact -/
section

/-! The extended-real barrier, including its infinite boundary values, and compact minimization. -/

open scoped Topology BigOperators ENNReal
open Filter Set
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.PotentialCompact -/

/- BEGIN original module: Stoc393.FaceTrace -/
section

/-! Capped trace after imposing the single orthogonality constraint on a cube face. -/

open scoped BigOperators
open Module
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.FaceTrace -/

/- BEGIN original module: Stoc393.MinimizerGeometry -/
section

/-! Feasible variations on cube faces and the contradiction at an interior minimizer. -/

open scoped Topology BigOperators ENNReal
open Filter Set Module
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.MinimizerGeometry -/

/- BEGIN original module: Stoc393.UpperBound -/
section

/-! Proposition 3.6 and the full upper bound (Theorems 1.2 and 3.1). -/

open scoped Topology BigOperators ENNReal
open Filter Set
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.UpperBound -/

/- BEGIN original module: Stoc393.UpperCorollaries -/
section

/-! Discrepancy, the square-matrix bound, and its explicit numerical constants. -/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

end Stoc393
end
end

section
namespace ThreeSigma.Upper

theorem Dev32.rowProduct_eq {d n : ℕ} (A : Fin d → Fin n → ℝ) (z : E n) :
    rowProduct A z = (Matrix.of A).mulVec (WithLp.ofLp z) := by
  funext i; simp [rowProduct, Matrix.mulVec, dotProduct]

theorem Dev32.R_eq {n : ℕ} (z : E n) : R z = Stoc393.residual (WithLp.ofLp z) := by
  simp [R, Stoc393.residual, EuclideanSpace.real_norm_sq_eq]

theorem Dev32.nearestSign_eq {n : ℕ} (z : E n) :
    WithLp.ofLp (nearestSign z) = Stoc393.nearestSign (WithLp.ofLp z) := by
  funext j; simp [nearestSign, Stoc393.nearestSign]

theorem chk_lemma_3_2 {d n : ℕ} (A : Fin d → Fin n → ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) (z : E n) (hz : ∀ j, |z j| ≤ 1) :
    ‖rowProduct A (nearestSign z)‖ ≤ ‖rowProduct A z‖ + R z := by
  rw [Dev32.rowProduct_eq, Dev32.rowProduct_eq, Dev32.R_eq, Dev32.nearestSign_eq]
  exact Stoc393.lemma_3_2 (A := Matrix.of A) (fun i j => hA i j) (fun j => hz j)

end ThreeSigma.Upper
end

theorem solution : type_of% @ThreeSigma.Upper.chk_lemma_3_2 := @ThreeSigma.Upper.chk_lemma_3_2
