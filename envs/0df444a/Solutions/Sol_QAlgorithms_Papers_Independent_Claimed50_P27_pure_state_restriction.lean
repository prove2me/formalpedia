-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P27.pure_state_restriction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:46:24.883289+00:00
-- url     : https://prove2.me/submissions/a37a3b7d-dfc2-4086-9a66-1c8582589eb2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P27
noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.3: the restriction of B to a pure input and memory |+>.
This is the displayed identity; the separate optimal-state-cloning criterion
is not introduced, since the paper attributes that optimization to [19]. -/
theorem solution (d : ℕ) (hd : 2 ≤ d)
    (psi : EuclideanSpace ℂ (Fin d)) (hpsi : IsState psi) :
    optimalPost d (Matrix.kronecker (pureDensity psi) (pureDensity (ket true))) =
      (((d : ℝ) / sectorDim d true : ℝ) : ℂ) •
        (sectorProjector d true *
          Matrix.kronecker (pureDensity psi) (1 : Matrix (Fin d) (Fin d) ℂ) *
            sectorProjector d true) := by
  have hpos : 0 < sectorDim d true := by
    unfold sectorDim
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    simp only [if_true]
    positivity
  have hblock : ∀ i j : Bool,
      (fun a b => (Matrix.kronecker (pureDensity psi) (pureDensity (ket true))) (a, i) (b, j)) =
        if i = true ∧ j = true then pureDensity psi else 0 := by
    intro i j
    funext a b
    cases i <;> cases j <;> simp [Matrix.kronecker, Matrix.kroneckerMap_apply, pureDensity, ket]
  unfold optimalPost
  simp only [hblock, Fintype.sum_bool]
  simp only [and_self, if_true, and_false, false_and, if_false, Matrix.zero_kronecker,
    Matrix.mul_zero, Matrix.zero_mul, smul_zero, add_zero, zero_add]
  rw [Real.sqrt_mul_self hpos.le]
  simp


end
