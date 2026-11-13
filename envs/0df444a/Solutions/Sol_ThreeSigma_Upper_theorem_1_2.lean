-- Prove2me | solution 1 for ThreeSigma.Upper.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T17:10:24.27534+00:00
-- url     : https://prove2.me/submissions/701c918c-0dfc-4387-8e03-3efd9e8cd77d

import Mathlib
import Definitions.Def_ThreeSigma_Upper_Geometry
import Theorems.Thm_ThreeSigma_Upper_lemma_3_2
import Theorems.Thm_ThreeSigma_Upper_proposition_3_6

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

def IsSigning {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ j, x j = 1 ∨ x j = -1

def EntryBounded {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) : Prop :=
  ∀ i j, |A i j| ≤ 1

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

theorem signing_small_dimension {d n : ℕ} {A : Matrix (Fin d) (Fin n) ℝ}
    (hA : EntryBounded A) (hn : n ≤ 4) {D : ℝ} (hD : 0 ≤ D) :
    ∃ x : Fin n → ℝ, IsSigning x ∧ ‖A.mulVec x‖ ≤ D + 4 := by
  refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
  have h := matrix_action_le_l1 hA (fun _ => 1)
  simp only [abs_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  have hn' : (n : ℝ) ≤ 4 := by exact_mod_cast hn
  linarith

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

/-- The decimal 2.9992 in the abstract, proved with an exact Taylor lower bound. -/
theorem scalar_constant_lt_decimal : Real.sqrt (3*Real.arsinh 10) < 3749/1250 := by
  let u : ℝ := (3749/1250)^2/3
  have he := Real.sum_le_exp_of_nonneg (x := u) (by norm_num [u]) 16
  have he' : (401 : ℝ)/20 < Real.exp u := by
    norm_num [u, Finset.sum_range_succ, Nat.factorial] at he
    linarith
  have hinv : Real.exp (-u) < 20/401 := by
    rw [Real.exp_neg]
    exact (inv_lt_comm₀ (Real.exp_pos u) (by norm_num)).mpr (by linarith)
  have hsinh : (10 : ℝ) < Real.sinh u := by
    rw [Real.sinh_eq]
    linarith
  have hasinh : Real.arsinh 10 < u := by
    apply Real.sinh_lt_sinh.mp
    simpa only [Real.sinh_arsinh] using hsinh
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3749/1250)).mpr
  dsimp [u] at hasinh
  linarith

end Stoc393
end
end

section
namespace ThreeSigma.Upper

/-- The first assertion of Theorem 1.2: Proposition 3.6 then Lemma 3.2 (n > 4),
and the all-ones signing when n ≤ 4. -/
theorem Dev12.upper (n d : ℕ) (A : Fin d → Fin n → ℝ) (hA : ∀ i j, |A i j| ≤ 1) :
    ∃ x : Fin n → ℝ, (∀ j, x j = 1 ∨ x j = -1) ∧
      ∀ i, |∑ j, A i j * x j| ≤
        Real.sqrt (3 * (n : ℝ) * Real.arsinh (10 * (d : ℝ) / (n : ℝ))) + 4 := by
  by_cases hn : n ≤ 4
  · obtain ⟨x, hx, hb⟩ := Stoc393.signing_small_dimension (A := Matrix.of A)
      (fun i j => hA i j) hn (Real.sqrt_nonneg
        (3 * (n : ℝ) * Real.arsinh (10 * (d : ℝ) / (n : ℝ))))
    refine ⟨x, hx, fun i => le_trans ?_ hb⟩
    have h := norm_le_pi_norm ((Matrix.of A).mulVec x) i
    simpa [Matrix.mulVec, dotProduct, Real.norm_eq_abs] using h
  · obtain ⟨z, hzK, hR⟩ := proposition_3_6 (by omega) A hA
    have h32 := lemma_3_2 A hA z hzK.1
    have hrow : ‖rowProduct A z‖ ≤ delta n d := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr (fun i => ?_)
      rw [Real.norm_eq_abs]; exact hzK.2 i
    refine ⟨fun j => WithLp.ofLp (nearestSign z) j, fun j => ?_, fun i => ?_⟩
    · simp only [nearestSign]; split_ifs <;> simp
    · have h := norm_le_pi_norm (rowProduct A (nearestSign z)) i
      rw [Real.norm_eq_abs] at h
      have : |∑ j, A i j * WithLp.ofLp (nearestSign z) j| ≤ delta n d + 4 :=
        h.trans (h32.trans (add_le_add hrow hR))
      simpa [delta] using this

theorem chk_theorem_1_2 :
    (∀ (n d : ℕ) (A : Fin d → Fin n → ℝ), (∀ i j, |A i j| ≤ 1) →
      ∃ x : Fin n → ℝ, (∀ j, x j = 1 ∨ x j = -1) ∧
        ∀ i, |∑ j, A i j * x j| ≤
          Real.sqrt (3 * (n : ℝ) * Real.arsinh (10 * (d : ℝ) / (n : ℝ))) + 4) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ A : Fin n → Fin n → ℝ,
      (∀ i j, |A i j| ≤ 1) →
      ∃ x : Fin n → ℝ, (∀ j, x j = 1 ∨ x j = -1) ∧
        ∀ i, |∑ j, A i j * x j| ≤
          (Real.sqrt (3 * Real.arsinh 10) + 4 / Real.sqrt (n : ℝ)) *
            Real.sqrt (n : ℝ)) ∧
    (∀ (n : ℕ), 10 ^ 8 ≤ n →
      Real.sqrt (3 * Real.arsinh 10) + 4 / Real.sqrt (n : ℝ) < 3) := by
  refine ⟨Dev12.upper, fun n hn A hA => ?_, fun n hn => ?_⟩
  · obtain ⟨x, hx, hb⟩ := Dev12.upper n n A hA
    refine ⟨x, hx, fun i => (hb i).trans_eq ?_⟩
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by positivity)
    rw [mul_div_cancel_right₀ _ hnR,
      show 3 * (n : ℝ) * Real.arsinh 10 = (3 * Real.arsinh 10) * n by ring,
      Real.sqrt_mul (by
        have h := Real.arsinh_pos_iff.mpr (show (0 : ℝ) < 10 by norm_num)
        positivity)]
    field_simp
  · have hs : (10000 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; exact_mod_cast hn)
    have hdiv : (4 : ℝ) / Real.sqrt n ≤ 4 / 10000 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
    have hc := Stoc393.scalar_constant_lt_decimal
    linarith

end ThreeSigma.Upper
end

theorem solution : type_of% @ThreeSigma.Upper.chk_theorem_1_2 := @ThreeSigma.Upper.chk_theorem_1_2
